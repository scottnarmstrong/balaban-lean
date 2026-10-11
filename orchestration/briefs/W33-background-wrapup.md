# Brief W33 — background fields VI: I-1(e) Hölder bound and the linear response of `bgFieldC`

**Goal.** Finish the I-1 interface of `notes/phase1/BACKGROUND.md` v2 on top of the landed
`Balaban/Background/*` (W30: `Def5.lean` `bgField`, `bgFieldC`, `bgMult`, `bgMultC`, `theorem71`,
`theorem72`, `theorem72_analytic`, `theorem72_real`; `Theorem52*.lean`, `Perturb.lean`,
`ExistenceBounds.lean` `BgBounds`; W23: `LinearResponse.lean` `linearResponse`,
`green_sub_constrainedOp_posSemidef`, `linearResponse_sup`; W21: `Balaban/Multiscale/HolderGlobal.lean`
`global_g2iv`, `HolderSeminormLE`):

1. **I-1(e)** (BACKGROUND v2 §5.2, "I-1(e) (Hölder, separate item)"; P2 (1.15) line 3): for a fixed
   `θ ∈ (0,1)`, the Hölder seminorm `|∂φ|_{(θ),2−θ} ≤ C_θ K₁ δ` for the small solution (`bgFieldC`),
   from the (EL) equation `φ = G(α)(S − …)`, `global_g2iv`, and the `BgBounds`. State it as a separate
   theorem (it must not gate Theorems 7.1/7.2).
2. **Prop 5.4 for `bgFieldC`**: the derivative of `D ↦ (bgFieldC, bgMultC)` along a tangent vector of
   the data, expressed through `G` and `Π` (`linearResponse` applied to the analytic family of
   `theorem72_analytic`), with the sup bounds; add it as `theorem72_linearResponse`.
3. If cheap: the statement that `bgFieldC c₀` does not depend on `c₀` for `c₀` in the admissible range
   (uniqueness in the smaller class), as BACKGROUND v2 §7 remarks.

**Ownership.** New files under `Balaban/Background/` (e.g. `Holder.lean`, `Def5Response.lean`) in
your worktree `/home/scott/Balaban-worktrees/W33` (branch `w33-background-wrapup`), plus import lines
in `Balaban.lean`. Worker W28 owns `Balaban/Background/CompositionDomain.lean` /
`ScaledComposition.lean`: do not touch. Never import `Balaban/Frozen/Roots/*` or
`Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–2 (3 if cheap), or about 1,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
