#!/usr/bin/env python3
import json
import os
import socket
import sys

SOCK_DEFAULT = "/tmp/metamath_repl.sock"

USAGE = """Usage:
  metamath_repl_client.py 'READ demo0.mm'
  metamath_repl_client.py 'SHOW LABELS' --defaults
  metamath_repl_client.py --reset
  metamath_repl_client.py --ping

Multi-line (bash $'..\\n..' quoting):
  metamath_repl_client.py $'SHOW LABELS\\n\\n'
  metamath_repl_client.py $'SHOW LABELS\\n*\\n\\n'

Flags:
  --defaults        Append '\\n\\n' to the command text (answers "default" to two common prompts).
                    Useful for commands like SHOW LABELS / SEARCH that ask questions.
  --answers <text>  Append arbitrary answer text to the command (e.g. --answers $'\\n\\n' or $'*\\n\\n').
  --timeout <sec>   Override timeout seconds (default: 10, or 30 for long commands if you set it).
"""

def main():
    sock_path = os.environ.get("METAMATH_REPL_SOCK", SOCK_DEFAULT)

    if len(sys.argv) < 2:
        print(USAGE, end="")
        sys.exit(2)

    # Simple control commands
    if sys.argv[1] == "--reset":
        req = {"cmd": "reset"}
        return do_req(sock_path, req)
    if sys.argv[1] == "--ping":
        req = {"cmd": "ping"}
        return do_req(sock_path, req)

    # Positional command text
    text = sys.argv[1]

    # Optional flags (order-insensitive)
    defaults = False
    answers = ""
    timeout_s = 10.0

    i = 2
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg == "--defaults":
            defaults = True
            i += 1
        elif arg == "--answers":
            if i + 1 >= len(sys.argv):
                print("[client] --answers requires a value\n", file=sys.stderr)
                sys.exit(2)
            answers += sys.argv[i + 1]
            i += 2
        elif arg == "--timeout":
            if i + 1 >= len(sys.argv):
                print("[client] --timeout requires a value\n", file=sys.stderr)
                sys.exit(2)
            try:
                timeout_s = float(sys.argv[i + 1])
            except ValueError:
                print("[client] --timeout must be a number\n", file=sys.stderr)
                sys.exit(2)
            i += 2
        else:
            print(f"[client] unknown argument: {arg}\n", file=sys.stderr)
            print(USAGE, end="", file=sys.stderr)
            sys.exit(2)

    if defaults:
        # Two default answers: (1) accept default match <*> by pressing Enter
        # (2) accept default / nothing by pressing Enter
        answers += "\n\n"

    full_text = text + answers

    req = {"cmd": "eval", "text": full_text, "timeout_s": timeout_s}
    return do_req(sock_path, req)

def do_req(sock_path: str, req: dict) -> None:
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
            s.connect(sock_path)
            s.sendall((json.dumps(req) + "\n").encode("utf-8"))
            buf = b""
            while b"\n" not in buf:
                chunk = s.recv(65536)
                if not chunk:
                    break
                buf += chunk
    except FileNotFoundError:
        print(f"[client] socket not found: {sock_path}", file=sys.stderr)
        print("[client] is the server running?", file=sys.stderr)
        sys.exit(1)
    except ConnectionRefusedError:
        print(f"[client] connection refused: {sock_path}", file=sys.stderr)
        sys.exit(1)

    if not buf:
        print("[client] no response from server", file=sys.stderr)
        sys.exit(1)

    line = buf.split(b"\n", 1)[0].decode("utf-8", errors="replace")
    try:
        resp = json.loads(line)
    except json.JSONDecodeError as e:
        print(f"[client] bad JSON response: {e}", file=sys.stderr)
        print(line, file=sys.stderr)
        sys.exit(1)

    out = resp.get("output", "")
    if out:
        sys.stdout.write(out)
        if not out.endswith("\n"):
            sys.stdout.write("\n")

    if not resp.get("ok", False):
        err = resp.get("error", "[client] request failed")
        sys.stderr.write(err + "\n")
        sys.exit(1)

if __name__ == "__main__":
    main()
