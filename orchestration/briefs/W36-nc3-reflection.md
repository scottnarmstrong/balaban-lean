# Brief W36 — NC3 by reflection (Neumann-cube interior pointwise and Hölder bounds)

**Goal.** Formalize NC3 of `notes/phase1/LOCALIZATION.md` v2 §3.1 following the route of
`notes/phase1/NC3-astra.md` (reflection for cube scale `m ≥ 2`, bounded-scale NC2 for `m = 1`), in the
order of its "Lean implementation order" table, items 0–7: the regimes and the `m = 1` case from the
landed `green_G2i_cut_green`, `cut_pointwise_crude`, `laplacian_eq_of_cut`
(`Balaban/Multiscale/Cut*.lean`); the coordinate fold of the cube and its fibres; folding of blocks;
the **reflected generating set** (a new `GeneratingSet` on the doubled torus, with R1: nestedness,
separation, layer and spacing identities, potential and mass caps); `pathDist` under folding (R2);
the intertwining of the cut operator with the reflected uncut operator on even functions (R3); the
Green's function identity (R4); then `NC3.pointwise_cut_cube` (from the landed `prop48`) and the
two-center Hölder statement (from `holder_pair_decay`, `Balaban/Multiscale/HolderGlobal.lean`).
The note recommends proving R0, then R1 and R3 first in a one-dimensional finite interval with one
block scale, to fix the interfaces; follow that.

Use the landed localization geometry where it fits (`Balaban/Localization/CubeAligned.lean`
`CubeAligned`, `dropTop`; `Cover.lean` `InBox`; `Balaban/Multiscale/CutCube.lean` `cubeCut`,
`BlockAligned`). The final theorems take a rectangular aligned cube with an explicit embedded chart
(the note's `AlignedCube`), not a bare cut set.

**Ownership.** New files under `Balaban/Localization/` or `Balaban/Multiscale/` (e.g.
`Reflection.lean`, `ReflectedGeneratingSet.lean`, `NC3.lean`) in your worktree
`/home/scott/Balaban-worktrees/W36` (branch `w36-nc3-reflection`), plus import lines in
`Balaban.lean`. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** Items 0–7, or about 4,000 lines, or a precise obstruction (a property of the
reflected generating set or the intertwining that fails — quote it and stop). If you stop early,
items 0–3 are the priority.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; checks and results; axioms;
open questions; last commit hash.
