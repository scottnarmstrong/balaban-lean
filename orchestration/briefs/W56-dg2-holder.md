# Brief W56 — localization: the Hölder part of DG2, and (d) on X₀ for I-4a

**Goal.**
1. **DG2 Hölder part** (`notes/phase1/LOCALIZATION.md` v3 §3.1, (DG2): the Hölder seminorm of
   `∂(G_s f)` in the P2 (3.17) convention, `HolderSeminormLE` of `Balaban/Multiscale/HolderGlobal.lean`):
   the step W39 did not do — a two-point weighted summation of the NC3 pair bounds
   (`Balaban.Reflection.holder_pair_cut_cube`, `small_holder_pair_cut`, extended to the cover cubes as in
   W39's `cube_star`/`cube_weighted`), a Hölder bound for `∂χ_z` at arbitrary displacements (a direct
   Lipschitz estimate of the B-spline bump `Balaban/Localization/CubeBump.lean`, since a lattice path between
   touching blocks can leave Ω₁ where (Cov3) is unavailable), and the Leibniz step for the seminorm.
   Then the Hölder part of I-4a (c) for `δφ(s)` (W47 open point 2).
2. **I-4a (d) on X₀** (W47 open point 3): the geometric step that the scaled distance from `X₀` to `W`
   is at least `(r₀ − 6)M₁`, giving `e^{−γ_w r₁ M₁}K₃δ₁` on `X₀` from the landed `i4a_close`.

Landed inputs: `Balaban/Localization/Decoupled*.lean` (W39 `dg2_all`, `dg2_sup`, `DGSetting`; W47
`i4a_close`, specs), `Balaban/Localization/{NC3,NC3Small,Cover,CubeBump}.lean`,
`Balaban/Multiscale/HolderGlobal.lean`, `Balaban/Background/Calculus.lean`.

**Ownership.** New files under `Balaban/Localization/` (e.g. `DecoupledHolder.lean`,
`DecoupledFieldX0.lean`) in your worktree `/home/scott/Balaban-worktrees/W56` (branch
`w56-dg2-holder`), plus import lines in `Balaban.lean`. Worker W52 is writing
`Balaban/Localization/DecoupledBackground*.lean` / `DecoupledCompose*.lean`: do not touch. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–2, or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; last commit hash.
