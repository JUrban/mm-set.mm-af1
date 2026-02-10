# Rules for Working on set.mm

## STRICT PROHIBITIONS

### ⛔ **ONLY edit in the file set.mm after line 502024**
- Everything after line 502024 in that file is by default in the Topology section and can be edited (even very high line numbers).
- **NEVER edit any other files**
- **NEVER run the checker (metamath) for more than 60 seconds** : The
  proof search used by IMPROVE and IMPROVE ALL is very inefficient and
  it's a huge waste of time. So always run with timeout 60 : `timeout 60 metamath ...` .

## Never throw away useful work
1. You should almost never revert to previous backups (you can use temporary admits when something is hard).
2. If there is a really major reason for reverting, you have to salvage all the useful work done in between.
3. In particular, you have to ensure that all compiling theorems and definitions added since are kept.
4. If you later discover such screwup, you have to immedially start working on salvaging the lost work.
5. **SIMPLE CHECK**: after each backup, run wc on the current and previous backup. If the current backup is smaller, you have to explicitly justify (in the CHANGES file) the decrease and explain that you have not thrown out useful work.

## Metamath Language Details
- Btw, you can read the whole metamath.tex manual if you get into
  serious trouble. It also describes all the commands usable with the
  metamath binary we ask you to run.
- You can/should learn from related proofs that you can display e.g. (for theorem iscmp) as follows:
`tiemout 60 metamath "read set.mm" "show proof iscmp " exit`

### Logic System
- A lot of useful topology is in set.mm - grep it often for existing defs and theorems.
- You can/should also search for useful lemmas in set.mm.
- You should **AVOID** duplicating lemmas that are readily available unless it's reasonably useful/justified. "Building up infrastructure" is typically not a good justification.


### Syntax Rules
- **Only use `$( … $)` for comments** - no other comment syntax; no `$` inside comments


## Compilation Checking
- The checking is done by running `metamath "read set.mm" "ve pr *" exit`
- This will typically show you the errors in the proof that you are writing.
- To delete (completely reset) a partial proof of theorem FOO:
`timeout 60 metamath "read set.mm" "pr FOO" "delete all" "save new" "write source set.mm" "exit" "exit"`
- To progress in a new/partial proof by applying previous theorem/lemma/def BLA do this:
`timeout 60 metamath "read set.mm" "pr FOO" "assign last BLA" "save new" "write source set.mm" "exit" "exit"`
- Note that the above two commands should often suffice but you can also "assign" other things - see "HELP ASSIGN" below - when needed.

- In general you can do various commands instead of just delete and assign and you can look them up by useing "HELP" instead (follows e.g. by HELP ASSIGN). Read the help frequently, it's good.

- To start a new lemma or definition etc you need to write it at the end of the set.mm file like this:

 ${
    mpcom.1 $e |- ( ps -> ph ) $.
    mpcom.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Modus ponens inference with commutation of antecedents.  Commuted form
       of ~ mpd .  (Contributed by NM, 17-Mar-1996.) $)
    mpcom $p |- ( ps -> ch ) $=
      ? $.
  $}

Where the first two lines ( $e ... $. statements) are the assumptions, then there is the comment and then the ( $p ... $= ... $. ) conclusion. (It could be just the conclusion). The question mark is an empty (admitted ) proof that you will be later constructing as explained above with ./metamath ... .


- **Run the checking frequently** to check for compilation errors

- Often do numbered backups of set.mm like bck0007 (followed by pigz bck0007 to save space). Even when it doesn't compile. Saving you partial attempts is important for not running in circles!
- With each numbered backup, also write the numbered summary changes file like CHANGES0007 (it should really be a summary, not just a simple diff).
- You can lookup your previous work in these CHANGES files when unsure how to continue.
- Never overwrite an older backup file. The numbering has to continue from the latest number. You must find it by running: ls bck* | sed 's/[^0-9]*//g' | sort -n | tail -n 1.



## Work Strategy
- You can do the following things in any order but you should always progress and produce some more code. 
- Keep carefully fixing any incorrect/bad definitions/theorems you find (note that this may lead to fixing some proofs, etc).
- Keep eliminating stubs, replacing them with more complete theorems and definitions (gradual/partial approaches are ok when needed).
- Keep replacing ? inside the proof body  (unfinished proofs) with more complete proofs by invoking the edditor and adding more proof steps. This may also lead to adding more auxiliary lemmas/theorems.
- While doing the above, remember that:
- Doing easy things is initially OK, however, don't be afraid to try to do (gradually/partially if needed) some harder theorems too. Don't endlessly jump around looking for easy things - that wastes time.
- Balance simple infrastructure theorems with more challenging results
- Your **strong focus** should be on finishing the major well-known theorems ASAP (like Urysohn). Prioritize them (even if they are hard) over doing many examples/exercises.
- Use gradual/partial approaches for difficult theorems when needed (and don't delete such started partial proofs - use temporary ? in their various branches and keep gradually eliminating those). Also, structure bigger proofs into useful top-level/helper lemmas wherever possible.
- Also, always grep all current definitions and theorems in set.mm  before creating a new one. Be sure to remove/avoid duplicities.

- Your current formalization goal there is the 41.4 theorem: metrizable implies paracompact. 
- For the formalization, try to follow the file topology.tex which describes the proofs and constructions. 
- You can introduce more necessary definitions and lemmas, however they must never duplicate anything done in metric.ml (all other available lemmas) already. Anything you newly introduce must be aligned with set.mm .
- You development will be finished when the  theorem 41.4 is proved and there are no uses of ? (empty/admitted proof ) in the development.
- "Building up infrastructure" is typically not a good justification for duplicating lemmas that already exist in the library and are available to you.

### PROOF STRATEGY RULES
- Avoid rebuilding standard machinery.

### Proof style discipline

- Try to structure longer proofs into many top-level lemmas with shorter proofs. Long proofs are very easy to get messy.


## Important Word of Advice
1. Re-read (and then remember/follow) CLAUDE.md frequently. 
2.  Structure the long proofs into many smaller toplevel lemmas so
that things don't get so complex and you don't throw away finished
work over and over.
3. Never throw partially finished things away and do frequent backups.
