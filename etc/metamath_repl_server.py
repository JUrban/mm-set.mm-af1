#!/usr/bin/env python3
import json
import os
import re
import signal
import socket
import subprocess
import threading
import time
import selectors
import pty
from typing import Tuple, Optional

SOCK_DEFAULT = "/tmp/metamath_repl.sock"

# Metamath prompts (interactive + proof assistant)
PROMPT_RE = re.compile(r"(?:^|\n)(MM(?:-PA)?>)\s*$")

# Exact pager line you showed (match at end of text; allow whitespace/newlines before end)
PAGER_RE = re.compile(
    r"Press\s*<return>\s*for\s*more,\s*Q\s*<return>\s*to\s*quit,\s*S\s*<return>\s*to\s*scroll\s*to\s*end\.\.\.\s*$",
    re.IGNORECASE | re.MULTILINE,
)

class MetamathReplPTY:
    def __init__(self, cmd):
        self.cmd = cmd
        self._lock = threading.Lock()
        self._start()

    def _start(self):
        master_fd, slave_fd = pty.openpty()

        # Run metamath attached to a PTY so it behaves interactively (prints MM> etc.)
        self.p = subprocess.Popen(
            self.cmd,
            stdin=slave_fd,
            stdout=slave_fd,
            stderr=slave_fd,
            text=False,          # read bytes from PTY master
            close_fds=True,
            preexec_fn=os.setsid # isolate process group
        )
        os.close(slave_fd)
        self.master_fd = master_fd

        self.sel = selectors.DefaultSelector()
        self.sel.register(self.master_fd, selectors.EVENT_READ)

        out, ok = self._read_until_prompt(timeout_s=5.0, autopage=True)
        self.banner = out if ok else (out + "\n[server] warning: did not see initial prompt\n")

    def _read_chunk(self, timeout_s: float) -> Optional[bytes]:
        events = self.sel.select(timeout=timeout_s)
        if not events:
            return None
        try:
            return os.read(self.master_fd, 65536)
        except OSError:
            return b""

    def _send_keys(self, s: str):
        try:
            os.write(self.master_fd, s.encode("utf-8"))
        except Exception:
            pass

    def _read_until_prompt(self, timeout_s: float, autopage: bool) -> Tuple[str, bool]:
        buf = b""
        deadline = time.time() + timeout_s

        # Stall-based nudge + pager handling
        last_data_time = time.time()
        pager_actions = 0

        while time.time() < deadline:
            if self.p.poll() is not None:
                more = b""
                try:
                    more = os.read(self.master_fd, 65536)
                except Exception:
                    pass
                text = (buf + more).decode("utf-8", errors="replace")
                return (text + "\n[server] Metamath process exited.\n", False)

            chunk = self._read_chunk(timeout_s=0.2)
            if chunk is None:
                # If we've gotten output but no prompt for a while, Metamath may be waiting on pager input.
                # As a gentle fallback, hit "S<return>" to dump to end.
                if autopage and buf and (time.time() - last_data_time) > 0.8 and pager_actions < 1:
                    self._send_keys("S\n")
                    pager_actions += 1
                continue

            if not chunk:
                continue

            buf += chunk
            last_data_time = time.time()

            text = buf.decode("utf-8", errors="replace")

            # If we see the explicit pager prompt, answer with "S<return>" to scroll to end.
            if autopage and PAGER_RE.search(text) and pager_actions < 2:
                self._send_keys("S\n")
                pager_actions += 1
                # keep reading; prompt will appear after paging completes

            m = PROMPT_RE.search(text)
            if m:
                start = m.start(1)
                out = text[:start].rstrip("\r")
                return (out, True)

        text = buf.decode("utf-8", errors="replace")
        return (text + "\n[server] TIMEOUT waiting for Metamath prompt.\n", False)

    def eval(self, text: str, timeout_s: float = 20.0) -> Tuple[str, bool]:
        with self._lock:
            if self.p.poll() is not None:
                return ("[server] Metamath REPL is not running.\n", False)

            if not text.endswith("\n"):
                text += "\n"

            try:
                os.write(self.master_fd, text.encode("utf-8"))
            except Exception as e:
                return (f"[server] Failed writing to Metamath PTY: {e}\n", False)

            return self._read_until_prompt(timeout_s=timeout_s, autopage=True)

    def reset(self) -> str:
        with self._lock:
            try:
                self.p.terminate()
            except Exception:
                pass
            try:
                self.p.wait(timeout=1.0)
            except Exception:
                try:
                    self.p.kill()
                except Exception:
                    pass

            try:
                self.sel.unregister(self.master_fd)
            except Exception:
                pass
            try:
                os.close(self.master_fd)
            except Exception:
                pass

            self._start()
            return "[server] reset ok\n"

    def close(self):
        with self._lock:
            try:
                self.p.terminate()
            except Exception:
                pass
            try:
                self.p.wait(timeout=1.0)
            except Exception:
                try:
                    self.p.kill()
                except Exception:
                    pass
            try:
                self.sel.unregister(self.master_fd)
            except Exception:
                pass
            try:
                os.close(self.master_fd)
            except Exception:
                pass


def serve(sock_path: str, cmd):
    if os.path.exists(sock_path):
        os.unlink(sock_path)

    print(f"[server] starting metamath: {' '.join(cmd)}", flush=True)
    repl = MetamathReplPTY(cmd)

    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
        s.bind(sock_path)
        os.chmod(sock_path, 0o600)
        s.listen(8)
        print(f"[server] listening on {sock_path}", flush=True)

        def shutdown(*_):
            try:
                s.close()
            except Exception:
                pass
            repl.close()
            if os.path.exists(sock_path):
                os.unlink(sock_path)
            raise SystemExit(0)

        signal.signal(signal.SIGINT, shutdown)
        signal.signal(signal.SIGTERM, shutdown)

        def safe_send(conn: socket.socket, resp: dict):
            try:
                conn.sendall((json.dumps(resp) + "\n").encode("utf-8"))
            except (BrokenPipeError, ConnectionResetError):
                return

        def handle(conn: socket.socket):
            with conn:
                data = b""
                while True:
                    chunk = conn.recv(65536)
                    if not chunk:
                        return
                    data += chunk
                    while b"\n" in data:
                        line, data = data.split(b"\n", 1)
                        if not line.strip():
                            continue
                        try:
                            req = json.loads(line.decode("utf-8"))
                        except Exception as e:
                            safe_send(conn, {"ok": False, "error": f"bad json: {e}", "output": ""})
                            continue

                        cmd_name = req.get("cmd", "eval")
                        if cmd_name == "eval":
                            text = req.get("text", "")
                            timeout_s = float(req.get("timeout_s", 30.0))  # help can be long
                            out, ok = repl.eval(text, timeout_s=timeout_s)
                            safe_send(conn, {"ok": ok, "output": out})
                        elif cmd_name == "reset":
                            safe_send(conn, {"ok": True, "output": repl.reset()})
                        elif cmd_name == "ping":
                            safe_send(conn, {"ok": True, "output": "pong\n" + repl.banner})
                        else:
                            safe_send(conn, {"ok": False, "error": f"unknown cmd: {cmd_name}", "output": ""})

        while True:
            conn, _ = s.accept()
            threading.Thread(target=handle, args=(conn,), daemon=True).start()


def main():
    sock_path = os.environ.get("METAMATH_REPL_SOCK", SOCK_DEFAULT)
    mm_cmd = os.environ.get("METAMATH_REPL_CMD", "").strip()
    cmd = mm_cmd.split() if mm_cmd else ["metamath"]
    serve(sock_path, cmd)

if __name__ == "__main__":
    main()
