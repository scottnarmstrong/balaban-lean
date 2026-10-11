# Brief W33b — I-1(e): mixed second differences of the approximate field and the Hölder bound

**Goal.** Finish I-1(e) of `notes/phase1/BACKGROUND.md` v2 (the Hölder bound
`|∂φ|_{(θ),2−θ} ≤ C_θ K₁ δ` for the small solution `bgFieldC`, one fixed `θ ∈ (0,1)`), which W33 could
not close: the landed `bgFieldC_increment_holder` (`Balaban/Background/Holder.lean`) bounds the
Hölder seminorm of `φ − φ₀` only. What is missing is the Hölder seminorm of `∂φ₀` for the
approximate field `φ₀ = approxField` (`Balaban/Background/{Approximate,ApproxField,Interpolation,
Weights,Normalize,BSpline,Bump,ApproxLocal}.lean`, W22, following `notes/phase1/LEMMA53-astra.md`).

1. **Extend Lemma 5.3 (A3) to all second differences:** `|Δ_μΔ_ν φ₀(x)| ≤ C δ / ℓ(x)²` for all pairs
   `μ, ν` (mixed and pure, both signs), through `normalize ∘ interp ∘ locSol`: mixed second differences
   of the quotient weights `bump/denom` (the bump factorizes over coordinates), a four-point version of
   `normalize_bounds`, and the layer/path geometry for diagonal neighbours (`layer_bounds_of_dist`,
   `chain_box`). Constants depending on `(d, L)` only.
2. **Hölder reduction:** for `‖z‖ ≲ ℓ(x)` the Hölder quotient of `∂φ₀` is bounded by the mixed second
   differences (sum along a lattice path of length `‖z‖`), for `‖z‖ ≳ ℓ` by the sup bound on `∂φ₀`;
   hence `HolderSeminormLE G (svec G φ₀ · i) θ (2−θ) (C δ)` (the landed predicate,
   `Balaban/Multiscale/HolderGlobal.lean`).
3. **I-1(e):** combine with `bgFieldC_increment_holder`: the Hölder bound for `bgFieldC` itself, as a
   separate theorem (it must not gate Theorems 7.1/7.2).

**Ownership.** New files under `Balaban/Background/` (e.g. `ApproxSecond.lean`, `HolderFull.lean`)
in your worktree `/home/scott/Balaban-worktrees/W33b` (branch `w33b-mixed-differences`), plus import
lines in `Balaban.lean`. Additions (new lemmas) to W22's files only if unavoidable (say which).
Worker W35 is writing `Balaban/Background/Theorem73.lean`: do not touch. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
