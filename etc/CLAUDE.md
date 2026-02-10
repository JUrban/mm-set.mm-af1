# Rules for Working on set.mm (Metamath via client/server)

**All Metamath interaction MUST go through the persistent client (which talks to the persistent server)**:
- `metamath_repl_client.py` (one-shot command runner)
- behind the scene is a server (runs once, keeps state)

## STRICT PROHIBITIONS

### ⛔ **ONLY edit in the file set.mm after line 502024**
- Everything after line 502024 in that file is by default in the Topology section and can be edited (even very high line numbers).
- **NEVER edit any other files** (except updating this `CLAUDE.md` if asked).
- **NEVER run Metamath operations for more than 60 seconds.**
  - Proof search (especially `IMPROVE` / `IMPROVE ALL`) can be extremely inefficient.
  - Therefore **every client call that could be slow MUST include `--timeout 60`**.

### ⛔ No “compilation mode”
- **DO use** `metamath_repl_client.py` exclusively for Metamath commands.


### Always use absolute paths for READ/WRITE

* The server’s working directory may differ from the client’s.
* **Always** use `"$PWD/set.mm"` or a full path.

### Hard 60-second limit

* For checking / proof operations:

  metamath_repl_client.py "READ $PWD/set.mm" --timeout 60

### Recovery after timeouts or dialog confusion

Metamath can enter interactive dialogs; if a command times out or you see errors like it is answering a previous question (e.g. `?Expected / or nothing.`), the session may be stuck inside an unfinished prompt.

**Recovery procedure:**

1. `metamath_repl_client.py --reset`
2. `metamath_repl_client.py "READ $PWD/set.mm" --timeout 60`
3. Re-issue the intended command in a dialog-free form.
4. This is dangerous and loses current state! Should be avoided as much as possible.

## Never throw away useful work

0. Save you work **very often** when working interactively! Long interactive sessions are very dangerous and you may lose all of your work if you don't save often as follows:

metamath_repl_client.py "SAVE NEW" --timeout 60
metamath_repl_client.py "WRITE SOURCE $PWD/set.mm" --timeout 60
metamath_repl_client.py "EXIT"

1. You should almost never revert to previous backups (you can use temporary admits when something is hard).
2. If there is a really major reason for reverting, you have to salvage all the useful work done in between.
3. In particular, you have to ensure that all compiling theorems and definitions added since are kept.
4. If you later discover such screwup, you have to immedially start working on salvaging the lost work.
5. **SIMPLE CHECK**: after each backup, run wc on the current and previous backup. If the current backup is smaller, you have to explicitly justify (in the CHANGES file) the decrease and explain that you have not thrown out useful work.


## Metamath Language Details

* You can read the whole metamath.tex manual if you get into serious trouble. It also describes all the commands usable with the metamath binary.
* Learn from related proofs that you can display. Example (now via client/server):

  ```bash
  metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
  metamath_repl_client.py "SHOW PROOF iscmp" --timeout 60
  ```

### Logic System

* A lot of useful topology is in set.mm — grep it often for existing defs and theorems.
* You can/should search for useful lemmas in set.mm.
* You should **AVOID** duplicating lemmas that are readily available unless it's reasonably useful/justified. “Building up infrastructure” is typically not a good justification.

### Syntax Rules

* **Only use `$( … $)` for comments** - no other comment syntax; no `$` inside comments.

## Checking / “Compilation” 

### Primary check command 

metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
metamath_repl_client.py "VERIFY PROOF *" --timeout 60

**Run checking frequently** to catch errors early.


## Proof Assistant Operations (always via client/server)

### Start proof of theorem FOO

```bash
metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
metamath_repl_client.py "PROVE FOO" --timeout 60
```

### Delete (completely reset) a partial proof of theorem FOO

metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
metamath_repl_client.py "PROVE FOO" --timeout 60
metamath_repl_client.py "DELETE ALL" --timeout 60
metamath_repl_client.py "SAVE NEW" --timeout 60
metamath_repl_client.py "WRITE SOURCE $PWD/set.mm" --timeout 60
metamath_repl_client.py "EXIT" --timeout 60

### Progress in a new/partial proof by applying previous lemma/def BLA

metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
metamath_repl_client.py "PROVE FOO" --timeout 60
metamath_repl_client.py "ASSIGN LAST BLA" --timeout 60
metamath_repl_client.py "SAVE NEW" --timeout 60
metamath_repl_client.py "WRITE SOURCE $PWD/set.mm" --timeout 60
metamath_repl_client.py "EXIT" --timeout 60

### Help

Prefer targeted help:

```bash
metamath_repl_client.py "HELP ASSIGN" --timeout 60
```

The server handles the Metamath pager automatically (it will send `S<return>` when prompted).


## Critical Metamath REPL Discipline (avoid hangs)

Metamath has:

1. long output paging prompts (handled by server),
2. **interactive dialogs** that ask questions and wait for input.

### Rule: avoid interactive dialog commands

**Prefer explicit, dialog-free forms**.

Examples:

* ✅ `SHOW LABELS *`  (do NOT run `SHOW LABELS` alone)
* ✅ `SEARCH <pattern>` (do NOT run `SEARCH` alone)
* ✅ `SHOW STATEMENT <label>`
* ✅ `SHOW PROOF <label>`
* ✅ `SHOW USAGE <label>`

If you must answer a dialog, send all answers in one call using multi-line input:

metamath_repl_client.py $'SHOW LABELS\n*\n\n' --timeout 60

But again: **prefer the dialog-free forms**.


* Unification dialogs are not paging. Do not assume the server will handle them.

* If a command may prompt for unification choices, either:
-- prefer / NO_UNIFY, or
-- rerun with --answers $'A\n' (or R\n, Q\n) as needed.

## Adding new lemma/definition/theorem stubs in set.mm

To start a new lemma or definition etc, write it at the end of `set.mm` like:

```
${
  mpcom.1 $e |- ( ps -> ph ) $.
  mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
  $( Modus ponens inference with commutation of antecedents.  Commuted form
     of ~ mpd .  (Contributed by NM, 17-Mar-1996.) $)
  mpcom $p |- ( ps -> ch ) $=
    ? $.
$}
```

Then use the Proof Assistant commands above to gradually replace `?` with a real proof.


## Backups / CHANGES discipline

* Often do numbered backups of set.mm like `bck0007` (followed by `pigz bck0007` to save space). Even when it doesn't compile.
* With each numbered backup, also write the numbered summary changes file like `CHANGES0007` (a real summary, not just a diff).
* Never overwrite an older backup file. The numbering has to continue from the latest number. Find it by:

  ls bck* | sed 's/[^0-9]*//g' | sort -n | tail -n 1

## Work Strategy

* You can do the following things in any order but you should always progress and produce some more code.
* Keep carefully fixing any incorrect/bad definitions/theorems you find (note that this may lead to fixing some proofs, etc).
* Keep eliminating stubs, replacing them with more complete theorems and definitions (gradual/partial approaches are ok when needed).
* Keep replacing `?` inside the proof body (unfinished proofs) with more complete proofs by invoking Proof Assistant commands. This may also lead to adding more auxiliary lemmas/theorems.
* Doing easy things initially is OK; however, don’t endlessly jump around — that wastes time.
* Balance simple infrastructure theorems with more challenging results.
* Strong focus: finish major well-known theorems ASAP (like Urysohn). Prioritize them over many minor examples.

### Current formalization goal

* Your current formalization goal is theorem 41.4: **metrizable implies paracompact**.
* Follow `topology.tex` for proof structure.
* You may introduce necessary definitions/lemmas, but **must not duplicate** what is already available (including anything in metric.ml / existing library).
* Development is finished when theorem 41.4 is proved and there are **no uses of `?`** in the development.

### Proof style discipline

* Avoid rebuilding standard machinery.
* Structure long proofs into many smaller toplevel lemmas with shorter proofs.


## Important Word of Advice

1. Re-read (and then remember/follow) this `CLAUDE.md` frequently.
2. Structure long proofs into many small top-level lemmas so things don’t get messy.
3. Never throw partially finished work away; do frequent numbered backups.

### ⛔ Server control is forbidden
- The Metamath server is managed externally and is assumed to be running.
- **NEVER try to start the server** 
- **NEVER try to stop/kill/restart the server** 
- Interact with Metamath **ONLY** via `metamath_repl_client.py ...`.

### Server health check (allowed)
If Metamath seems unresponsive, you may only do:
metamath_repl_client.py --ping

- `--reset` is a LAST-RESORT recovery tool.
- Claude MUST NOT use `--reset` unless:
  1) the server fails `--ping`, or
  2) Metamath is clearly stuck in a dialog state that cannot be exited, or
  3) the human explicitly requests a reset.
- After every `--reset`, Claude MUST immediately:
  - READ set.mm
  - VERIFY PROOF *


## Command Quick Reference (Client/Server Metamath)

### Reset & reload (SAFE RECOVERY SEQUENCE)

Use this whenever something times out, hangs, or looks confused.

```bash
metamath_repl_client.py --reset
metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
```


### Check / “compile” the database

metamath_repl_client.py "READ $PWD/set.mm" --timeout 60
metamath_repl_client.py "VERIFY PROOF *" --timeout 60



### Inspect existing material (dialog-free)

metamath_repl_client.py "SHOW STATEMENT th1"
metamath_repl_client.py "SHOW PROOF th1" --timeout 60
metamath_repl_client.py "SHOW USAGE th1"
metamath_repl_client.py "SHOW LABELS *" --timeout 60


### Start / work on a proof

metamath_repl_client.py "PROVE FOO" --timeout 60
metamath_repl_client.py "SHOW NEW_PROOF"
metamath_repl_client.py "SHOW NEW_PROOF / UNKNOWN"

### Modify a proof

metamath_repl_client.py "ASSIGN FIRST BAR" --timeout 60
metamath_repl_client.py "ASSIGN LAST BAR" --timeout 60
metamath_repl_client.py "UNDO"

### Save proof back to set.mm

metamath_repl_client.py "SAVE NEW" --timeout 60
metamath_repl_client.py "WRITE SOURCE $PWD/set.mm" --timeout 60
metamath_repl_client.py "EXIT"

### Help (safe; pager handled automatically)

metamath_repl_client.py "HELP ASSIGN" --timeout 60

### ABSOLUTE DO-NOTS (Quick)

* ❌ Do NOT run `metamath "read set.mm" ...` directly for normal work
* ❌ Do NOT run interactive commands without arguments (e.g. `SHOW LABELS`)
* ❌ Do NOT exceed `--timeout 60`
* ❌ Do NOT edit `set.mm` before line 502024
