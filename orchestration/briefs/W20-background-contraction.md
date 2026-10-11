# Brief W20 — background fields I: data, calculus, the perturbed system (BACKGROUND.md Prop 5.1)

**Goal.** Start the Lean formalization of the background fields at λ = ∞ following
`notes/phase1/BACKGROUND.md` v2 (reviewed: `BACKGROUND-review.md`; plan §9). This package is the
modules `Data`, `Calculus` and `Contraction` of §9:

1. **Data** (§1): the lifted fields, the collar, `BgData` (layer-constant `Ψ`, block-constant
   `h̃`, values off `Ω₁ ∪ C` set to 0 by the constructors), the predicates `Ψ̃`, `Ψ̃^c` ((R1)–(R4),
   (C1)–(C3)), the source `S` (1.1), the action (1.2), the Euler–Lagrange system (EL), and the
   Def-5 predicates `IsEL`, `IsSmallSolution c₀`, `IsMinimizer` (§7; definitions only — the
   functions `bgField`, `bgFieldC` come after the `∃!` theorems, not in this package). Build on the
   landed `GeneratingSet` (`Balaban/Multiscale/GeneratingSet.lean`), `dirichletOperator`, and the
   field conventions of `Balaban/Multiscale/Constraint*.lean` (`IsSmoothField`, `svec`, `vn`).
   Faithfulness matters here: these are freeze candidates; every definition must say in its
   docstring which equation of P2/BACKGROUND.md it is.
2. **Calculus** (§3): the norms `|·|_σ`, `|∂·|₁` on `Ω₁` with zero extension, the Leibniz identity
   (3.1), Lemmas 3.1–3.3, the wall-in-layer-1 lemma, and the bridge lemma of V-01 (the wall-bond
   factor `L` and the `√N`/`N` factor) connecting the landed `global_bound`
   (`Balaban/Multiscale/GlobalBound.lean`) and `constrained_sup` (`ConstraintSup.lean`) to the norm
   `‖G f‖_* = |Gf|₀ + |∂Gf|₁ ≤ B₁|f|₂` that Prop 5.1 uses.
3. **Contraction** (§5.1, Prop 5.1): the perturbed system with independent data: `δφ(δα)`, the
   identity (5.2), the map `𝒩`, the estimates, the fixed point (use
   `Balaban.Analysis.exists_analytic_fixedPoint` or the landed contraction lemmas), analyticity in
   the data, uniqueness with `|δα|₂ < c₆`, all norms `≤ K₂δ₁`. Exact hypotheses as in BACKGROUND.md v2
   (ranges of `α`: `coerciveConst d /(2ℓ²)`; separation `2d log L ≤ (agmonRate d/4)(ϱ−1)`;
   `μ L^{2k} ≤ 1`; constants depending on `d, L, N`).

**Ownership.** New files under `Balaban/Background/` (e.g. `Data.lean`, `Calculus.lean`,
`Contraction.lean`; `Contraction.lean` may already exist as a name in `Balaban/Analysis` — check
and avoid clashes) in your worktree `/home/scott/Balaban-worktrees/W20` (branch
`w20-background-contraction`), plus import lines in `Balaban.lean`. Small additions to landed files
only if unavoidable (say which). Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.
Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 3,000 lines, or a precise obstruction (a definition of §1
that cannot be written faithfully, or an inequality of Prop 5.1 that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; every definition of item 1 with its full Lean text; main theorem names with
statements; checks and results; axioms; open questions; last commit hash.
