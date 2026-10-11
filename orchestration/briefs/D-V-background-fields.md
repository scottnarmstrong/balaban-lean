# Brief D-V — background fields at λ = ∞ (`notes/phase1/BACKGROUND.md`)

You are a mathematical analyst writing a phase-1 document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model, **hard spins (λ = ∞)**. Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics on paper; you do not write or run
Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context

The background fields are the minimizers of Balaban's variational problems: given block spins ψ
on a generating set 𝔹_k, minimize the action `A(ψ, φ) = ½ a‖ψ − Q(𝔹_k)φ‖² + ½‖∂φ‖² + (ν/2)‖φ − h‖²`
over `φ` with the hard-spin constraint `|φ(x)| = 1`, plus the multiscale versions
`ψ^{(j)}_k`, `ψ(𝔹_j, 𝔹'_k; ψ')` and the composition identities. P2 (CMP 175, `sources/BF02099510.pdf`, a
scan — read page images; PDF page = journal page − 606) treats soft spins λ < ∞ (Prop 1.1, Cor 1.1,
Prop 2.1, Lemma 2.1, Lemma 3.1, Prop 3.1, Prop 4.1, (4.21), (4.39)) and the λ → ∞ limit only
implicitly. Roadmap `review/FORMALIZATION_ROADMAP.md` §3.3 I-1, I-2 and Def-5 (defined only after
the ∃! theorem, with a characterization theorem); review `review/papers/P2-*.md`; GREEN.md §2 C1–C3
(which bounds P2 consumes; C3 disappears at λ = ∞).

**Landed Lean you should build the proofs on** (read the statements): constant configurations at
λ = ∞ `Balaban/Background/ConstantConfig*.lean` (explicit minimizer `w/√(w·w)`, analytic extension,
bounds, covariance); the O(N) reduction `Balaban/Symmetry/*`; the multiscale setting and Green's
function layer `Balaban/Multiscale/*` (generating sets, `dirichletOperator`, coercivity incl.
`_sharp`, Agmon decay `green_G2i`, pointwise `prop48`, locality `green_sub_green_locality`,
analyticity `analyticOnNhd_green_apply`, the constrained operator `constrainedOp`,
`constrained_G2v`); the global weighted bound G-2(iv) (in progress, W16: `|Gf|_0 + |∂Gf|_1 + |Δ^D Gf|_2 ≤ B₀|f|_2`);
the analytic contraction `Balaban.Analysis.exists_analytic_fixedPoint`.

## Task: write `/home/scott/Balaban/notes/phase1/BACKGROUND.md`

1. **The problems at λ = ∞.** Precise statements of the variational problems (the generating-set
   problem of P2 (1.10)–(1.12) and its multiscale relatives), the Euler–Lagrange system with the
   multiplier field `α` (`H_D(α)φ = aQ^*ψ + νh` type, `|φ| = 1`), the domains of data
   (P2's `Ψ̃^c(𝔹_k; δ, ε)` at λ = ∞), and what "solution" means for complex data.
2. **I-1 (P2 Prop 1.1 / Cor 1.1 / Prop 3.1 at λ = ∞).** Existence, uniqueness (`∃!` form, real data:
   unique minimizer), analyticity in the data, and the bounds P2 (1.15)–(1.16), with a complete proof
   at λ = ∞ built on the landed Green layer: the reduction to a fixed-point problem around a
   constant/locally constant approximate solution (P2 Lemma 3.1 analogue: the approximate solution
   `φ₀, α₀` and its error `f₀`), the Neumann-series/contraction step using G-2(iv) and the constrained
   operator, and the perturbed system with independent data (Prop 3.1, which P3–P7 reuse).
3. **I-2 (P2 Prop 4.1)**: `ψ(𝔹_j, 𝔹'_k; ψ')`, formula (4.21), composition identities (4.39), at λ = ∞.
4. **Def-5**: the definitions of the background fields from the `∃!` theorems, and their
   characterization theorems, stated so they can be frozen.
5. **What changes at λ = ∞** relative to P2 (which bounds disappear, which new constraint terms appear —
   the constrained operator Π), and every place P2's proof is sketched or wrong (check
   `notes/ERRATA.md` P2 rows).
6. **Lean plan and size estimate**, against the landed modules.
7. **Questions**, if any.

Standards: exact page/equation references; distinguish proved / cited / sketched; mark doubts
"UNCERTAIN:". Plain mathematical prose; no marketing words; avoid "calibration", "robust",
"leverage", "crucially". LaTeX in $...$. Expect 6,000–12,000 words; write the file section by
section as you go.

Rules: write only `/home/scott/Balaban/notes/phase1/BACKGROUND.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/bg/ allowed). Do not edit any other file, do not commit, do not run
Lean or lake. When done, reply with: the statements of I-1, I-2, Def-5 (one line each), which proofs
are complete, the main risk, and any questions.
