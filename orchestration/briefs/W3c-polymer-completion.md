# Brief W3c — completing the polymer-expansion theorem

**Goal.** Finish the items of `notes/phase1/POLYMER.md` (revised, with "Review dispositions") not
covered by the landed `Balaban/Polymer/*` (W3b: `pe_xi_eq_exp`, `pe_summable`, `pe_clusterBound`,
`logSeries_eq_sum_PY`, `PY_congr`, `pe_PY_bound`, `pe_differentiableOn` (one parameter),
`pe_lattice`, `pe_blockTorus`, `card_animals_le`). In priority order:

1. **Holomorphy in several parameters (PE (d)).** Activities analytic on an open set of a
   finite-dimensional complex space with uniform bounds ⇒ `L` and every `P(Y)` analytic there
   (`AnalyticOnNhd`), using `Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn`
   (`Balaban/Analysis/AnalyticLimit.lean`). Also the Cauchy-estimate corollary for derivatives
   (`Balaban/Analysis/Cauchy.lean`).
2. **The bridge to the frozen geometry.** Relate `BlockPolymer` (block sets) on the block torus of
   side `m` to the frozen `Balaban.IsPolymer d ℓ s X` (site sets in `Torus d ℓ` that are unions of
   blocks of side `s`, nearest-neighbour connected; `Balaban/Frozen/Geometry/IsPolymer.lean`) for
   `ℓ = s·m`: a bijection `X ↦` its set of blocks, with `X.card = s^d · #blocks`, connectivity
   preserved. State `pe_blockTorus` in the frozen language (sums over `X : Finset (Torus d ℓ)` with
   `IsPolymer`, decay `e^{−κ X.card / s^d}`), so Root-F's provider can use it directly.
3. **Transport / torus independence (PE (f)).** For two tori and a finite set of blocks in a
   common box (no winding), if the activities agree under the identification then the local
   terms `P(Y)` agree (POLYMER.md (f) and review R15).
4. **PE-M (marked version) and the truncated-expectation corollary** (POLYMER.md §2.4–2.5, §4.1),
   stated conditionally on the MY form (3.11) with the hypotheses (H-MY) listed there.
5. **Hole version** with the Steiner size (POLYMER.md §3.6 "Hole"), if budget remains.

**Ownership.** New files under `Balaban/Polymer/` in your worktree
`/home/scott/Balaban-worktrees/W3c` (branch `w3c-polymer`), plus import lines in `Balaban.lean`.
Small additions to landed `Balaban/Polymer/*` files are allowed (say which). You may import the
frozen definitions (`Balaban/Frozen/Geometry/IsPolymer.lean`, `Balaban/Frozen/Model/Torus.lean`),
never `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`. Copy freely from any of the author's
repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–4 (5 if possible), or about 3,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
