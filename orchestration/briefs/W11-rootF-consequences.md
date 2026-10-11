# Brief W11 — consequences of Root-F's statement (CORRELATIONS packages C, D, E, F)

**Goal.** Formalize `notes/phase1/CORRELATIONS.md` (revised) §1 and §4: everything that follows
from the *statement* of Root-F alone — the one- and two-point bounds and the thermodynamic limit
along tori with side divisible by `q^n`. Root-F (`Balaban/Frozen/Roots/LogPartitionMultiscale.lean`)
is a DRAFT anchor and **must not be imported**. Instead:

1. **The predicate.** In a non-frozen file, define `RootFClauses` (name as you like, e.g.
   `Balaban.Correlations.MultiscaleRep`): for fixed `d N L M β ν h kf κ c₉ δ` and a family
   `T : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → (Fin N → ℂ)`, the
   conjunction of exactly the clauses Root-F asserts about `T` (copy them from the frozen file:
   vanishing off polymers, locality, analyticity, the bound on `Σ Σ |g| ≤ 1/2`, the identity, the
   agreement clause). Prove an equivalence lemma stating that Root-F's conclusion is
   `∃ δ > 0, ∀ κ c₉, ∃ L M β₀, ∀ β ≥ β₀, … ∃ kf, … ∃ T, RootFClauses …` (by `Iff.rfl`/unfolding, in a
   probe that elaborates Root-F's *type* by copying it — the probe must not import the root file;
   if this is awkward, skip the equivalence lemma and report).
2. **Package C (geometry).** Lemma 1.1 (polymer counting through a point with the block-count
   decay, `κ* = 2 log(8d²)`-type constants; use the landed animal bound
   `Balaban.Polymer.card_animals_le` and the frozen `IsPolymer`), Lemma 1.2 (diameter:
   `n(X) s_j ≥ d_ℓ(x,y) + 1`).
3. **Package D (Prop 1.5, Cor 1.6).** From `RootFClauses` and W10's derivative identities
   (`Balaban.fderiv_logPartition_zero`, `Balaban.fderiv_fderiv_logPartition_zero`), Cauchy estimates
   (`Balaban/Analysis/Cauchy.lean`) on `Σ Σ |g| ≤ 1/2`: `|onePoint − h| ≤ 3c₉`-type bound and the
   decay bound `|twoPointTruncated| ≤ C(c₉)(1+|x−y|)^{−θ} e^{−c′√ν|x−y|}`, uniform in the torus,
   with constants as CORRELATIONS.md (revised, D-05) states them.
4. **Package F (series).** Lemma 1.3 (the summation lemma), Tannery-type lemma if used, geometric
   sums.
5. **Package E (§4, Theorem 4.1).** The thermodynamic limit: from the agreement clause, the
   one- and two-point functions at fixed `x, y ∈ ℤ^d` (read mod `ℓ`) converge along tori with
   side divisible by `q^n` (`q = ML`), with the lcm lemma (Lemma 3.0′). State the convergence in
   the ε–`n₀` form Root-C uses (`∀ ε > 0, ∃ n₀, ∀ ℓ [NeZero ℓ], q ^ n₀ ∣ ℓ → |…| < ε`).

Order: 2, 4, 3, 5 (1 first if cheap). This is the conditional development of Root-C; record the
recorded reason in the module docstrings: "conditional on the clauses of Root-F; consumed by the
Root-C provider" (AGENTS.md rules 3–4: these lemmas take Root-F's *clauses* as hypotheses under a
distinct name; they are not source theorems and are never used to prove Root-F).

**Ownership.** New files under `Balaban/Correlations/` in your worktree
`/home/scott/Balaban-worktrees/W11` (branch `w11-rootF-consequences`), plus import lines in
`Balaban.lean`. Import frozen definitions and landed modules freely; never
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`. Copy freely from any of the author's
repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 2–5, or about 3,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
