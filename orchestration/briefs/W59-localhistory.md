# Brief W59 — large fields: fix `localHistory` (lineage localization) and Part III Lean P1–P2

**Goal.**
1. **`localHistory` design fix.** The landed `localHistory M K k Z` (W48,
   `Balaban/LargeField/History/LocalHistory.lean`) intersects the raw, un-overwritten step records with
   `fineSet k Z`; records of components removed below `Z` could leak into it if later cubes re-cover their
   fine sites (W55 report). W55 built the correct lineage localization `locRH H k Z : RegionHistory`
   (`Balaban/LargeField/History/LocalRegion.lean`, `locRH_Zpre`, `locRH_derived`, `locRH_fine_subset`).
   Either prove that no leak occurs in admissible histories (equality of the fine records), or redefine
   `localHistory` from `locRH` (the localized history 𝔥_k(Z) of `notes/phase1/LF-RECONSTRUCTION.md` Def I.4.4
   must be the lineage of `Z`), and adapt every consumer (`Balaban/LargeField/Operators/Variables.lean`:
   `InternalVars`, `refMeasure`, `multiscaleField`). Keep the public names; say which route you took.
2. If budget remains: Part III Lean items P1–P2 of `LF-RECONSTRUCTION.md` §III.L (the window/composition
   items that "can be drafted now": read the table and do P1 and P2 as listed there).

**Ownership.** Edits to `Balaban/LargeField/History/LocalHistory.lean`, `Balaban/LargeField/Operators/*`,
and new files under `Balaban/LargeField/` in your worktree `/home/scott/Balaban-worktrees/W59`
(branch `w59-localhistory`), plus import lines in `Balaban.lean`. Worker W58 is writing
`Balaban/LargeField/Characteristic/*`: do not touch. Never import `Balaban/Frozen/Roots/*` or
`Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Item 1 (item 2 if budget remains), or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; route taken; changed statements; checks and results; axioms; last commit hash.
