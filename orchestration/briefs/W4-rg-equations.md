# Brief W4 — the renormalization-group equations (I-7): solution by analytic contraction, γ_∞

**Goal.** Formalize the solution of Balaban's renormalization conditions as a system of
equations for the running coefficients, P4 §5 (pp. 707–718; Prop 5.1, (5.17)–(5.33)), in the
hard-spin case `λ = ∞` (the λ-equation is vacuous; P5–P7 use the choice `c = 0`, `d = b`; see
`review/BIG_PICTURE.md` §7 item 13 and roadmap §3.3 I-7), as an abstract theorem the small-field
flow will instantiate:

1. **One step.** The system `ξ + c(ξ) = f(ξ)` (P4 (5.23)) on a polydisc of radius `r₀`, with
   triangular linear part (diagonal entries bounded below as in (5.22)), quadratic remainder
   `|c_i| ≤ K₅C₄ε²` (5.24) and `|f_i| ≤ …` (5.25): unique solution in the polydisc, analytic in the
   data, with the bounds (5.31)–(5.32). Use `Balaban.Analysis.exists_analytic_fixedPoint`
   (`Balaban/Analysis/Contraction.lean`, landed) — reformulate the triangular system as a
   contraction and prove the hypotheses.
2. **Iteration.** The running coefficients `β_{k+1} = β_k L^{d−2}/(1 + ξ₃)`,
   `ν_{k+1} = ν_k L²(1 + ξ₃)/(1 + ξ₂)` (P4 (5.28)) with `|ξ^{(k)}| ≤ (c₈/4) L^{−2γ(k+1)}`; the bounds
   `γ_k^{±1}, δ_k^{±1} < exp(c₈ Σ_{j≤k} L^{−2γj})` (P4 (H.6)), and the limits `γ_∞`, `δ_∞` with
   `|γ_∞ − 1| ≤ C c₈` (P4 (5.33)), via `Balaban.Analysis.exists_tendsto_prod_inv_one_add`
   (`Balaban/Analysis/InfiniteProduct.lean`).
3. **Consequence for Root-C's normalization:** `β_j^{−1} = (βγ_∞)^{−1} L^{−j(d−2)} + O(β^{−1}) L^{−j(d−2+2γ)}`
   (P9 (4.18), p. 519), stated for the sequence of item 2.

State the system abstractly (vector of unknowns, linear part, nonlinearity with bounds as
hypotheses taken from P4's displayed estimates); do not try to derive (5.24)–(5.25) from the
effective actions — those come from the small-field flow later. Transcribe P4 §5 carefully from
the page images (`sources/Balaban.pdf`, PDF page = journal page − 674; Read tool with `pages`,
≤ 20 pages per call; it is a scan, the text layer is unreliable) and the review
`review/papers/P4-*.md` (its §3 summarizes (5.17)–(5.41)). Record in each module docstring which
P4 display each hypothesis transcribes.

**Ownership.** New files under `Balaban/Flow/` (e.g. `RGEquations.lean`, `RunningCoefficients.lean`)
in your worktree `/home/scott/Balaban-worktrees/W4` (branch `w4-rg-equations`), plus import lines
in `Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed).

**Checks.** `lake build` of your modules only (at most one build at a time; compiles are
throttled machine-wide and may wait; never bypass the throttle); zero warnings; `#print axioms`
standard; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Items 1–3, or about 2,000 lines, or a precise obstruction (e.g. a P4 display
that cannot be read or is inconsistent — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; the transcription of P4's system as you stated it (display by display); main
theorem names with statements; checks and results; axioms; open questions; last commit hash.
