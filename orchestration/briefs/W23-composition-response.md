# Brief W23 — background fields III: composition identities (I-2) and linear response

**Goal.** Formalize the parts of `notes/phase1/BACKGROUND.md` v2 that do not need the existence
theorem (Theorem 5.2, which waits for W22's approximate solution):

1. **Composition (I-2), §6.1–6.5 and §6.7 algebraic parts:** the weights family (6.1), condition
   (C1), the explicit `composeField` (6.2) for any `φ′` (BACKGROUND v2 §7: `composeField` is an
   explicit function), the averages `𝒬_B`, `a^{(p)}` (6.5), the composed system `𝒮` (6.6); Theorem 6.1
   (ii) and the identities of (iv) (pointwise algebra: if `(φ′, α′)` solves the `𝔹′_k` system with
   datum `ψ′`, then its restriction solves the `𝔹_j` system with datum `composeField`, for real and
   complex data), and (iii) as uniqueness for `𝒮` with `|α|′₂ < c₀` (§6.5, using (C1) and the
   uniqueness part of `prop51_exists_unique`); Prop 6.4 for `g ≡ 0` (the perturbed composition),
   under the smallness hypothesis of BACKGROUND v2 (V-02 fix). Domain membership (Lemmas 6.2/6.3)
   is **not** in this package unless cheap.
2. **Linear response, §5.5, Prop 5.4:** the derivatives `φ̇, α̇` of a solution along a tangent
   vector of the data, expressed through `G` and the constrained operator `Π`, and `G − Π ⪰ 0` for
   real data; on top of the landed `constraintForm_isUnit`, `constrainedOp_eq_dirichlet`,
   `constrained_sup`, `prop51_analytic`. State it for any analytic solution family (it becomes a
   statement about `bgFieldC` once Theorem 5.2 exists).

Data types: `Balaban/Background/Data.lean` (landed by W20: `BgData`, `source`, `action`, `IsEL`,
`IsSmallSolution`, `IsMinimizer`, `InPsiTilde`, `InPsiTildeC`, …), `Calculus.lean`,
`Contraction.lean` (`Prop51Hyp`, `IsPerturbed`, `prop51_exists_unique`), `ContractionAnalytic.lean`.
Worker W22 is writing `Balaban/Background/{BlockGeometry,BSpline,Interpolation,Approximate}.lean` (or
similar) in parallel: do not create files with those names; do not edit W20's files (if you need a
change, stop and report).

**Ownership.** New files under `Balaban/Background/` (e.g. `Composition.lean`,
`LinearResponse.lean`) in your worktree `/home/scott/Balaban-worktrees/W23` (branch
`w23-composition-response`), plus import lines in `Balaban.lean`. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** Items 1–2, or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions (full Lean text of `composeField` and `𝒮`); main theorem names with
statements; checks and results; axioms; open questions; last commit hash.
