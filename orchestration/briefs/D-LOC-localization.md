# Brief D-LOC — localization at λ = ∞ (`notes/phase1/LOCALIZATION.md`; roadmap I-4, I-5)

You are a mathematical analyst writing a phase-1 document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model, **hard spins (λ = ∞)**. Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics on paper; you do not write or run
Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context
P3 = Balaban, "Localization expansions. I", CMP 182 (1996) 33–82 (`sources/BF02506385.pdf`; map
`review/SOURCES.md`; review `review/papers/P3-localization-I.md`; errata rows in `notes/ERRATA.md`,
e.g. ER-046, ER-053). Roadmap `review/FORMALIZATION_ROADMAP.md` §3.3 I-4 (analytic decoupling
extensions of δφ_k, δα_k, ψ(𝔹_j,𝔹′_k) and C^{(k)1/2} in |s_□| ≤ e^{κ₁}, with localization and
bounds; P3 Props 2.1–2.3, 3.1) and I-5 (the localization expansion of
𝓔(X; ψ^{(j)}_k(ψ^{(k)}(θ)+ψ′)) with bound E e^{−κ₀ d_j(X) − 2κ d̃_{k+1}(Y)}, including the "simple
variations" of P3 p. 81 used in P6 Lemma 4.1).

`notes/phase1/GREEN.md` leaves one design decision open (§3 G-3, "Option A" = P3's random-walk
expansion with Neumann cubes, keep G-3; "Option B" = no walk expansion, single/multi-block locality
G-2(vi), (vi′), (vi″) with an explicit m! and analyticity; open question Q2: whether Option B
reproduces P3's (H.5) with exponent κ−1 (ER-053) and the analytic extensions in the parameters s).
Background fields: `notes/phase1/BACKGROUND.md` v2 (I-1, I-2, Def-5, Prop 5.1, linear response
Prop 5.4). Polymer expansions: `notes/phase1/POLYMER.md`. Landed Lean you may rely on (statements):
`Balaban/Multiscale/*` (G-2(i)–(vi), `constrained_*`, `global_bound`, `prop48`, `prop49`,
analyticity `analyticOnNhd_green_apply`, locality `green_sub_green_le_sum`), W18b (in progress:
G-2(vi′) locality and analyticity of Π via a kernel algebra 𝒜_γ), `Balaban/Polymer/*`.

## Task: write `/home/scott/Balaban/notes/phase1/LOCALIZATION.md`
1. **The objects at λ = ∞**: the decoupling parameters s_□, the interpolated operators, the
   analytic extensions that I-4 is about, and exactly which P3 statements P4–P7, P9 consume (with
   page/equation references at each consumer).
2. **Decide Option A vs Option B** (GREEN.md Q2) with an argument: does Option B (no walk expansion)
   give the bounds P3 (H.5)/(2.11)/(3.12)–(3.20) and the s-analyticity that the consumers need, with
   which exponent? If Option A is needed, specify the walk expansion completely (index restrictions
   P3 (3.17), ER-046; the M⁻¹ factor; Neumann cubes by even reflection) so it can be formalized.
3. **I-4 statements and proofs** (P3 Props 2.1–2.3, 3.1 at λ = ∞), built on the landed Green layer and
   BACKGROUND.md; the constrained covariance C^{(k)1/2} (GREEN.md C12, C17; the square root by the
   resolvent integral).
4. **I-5 statement and proof** (P3 Prop 4.3) including the simple variations of P3 p. 81.
5. **Interfaces for freezing**: exact statements (carriers, quantifier order, constants), which
   objects need an ∃!/characterization first, and which statements are internal.
6. **What changes at λ = ∞**, errata (check `notes/ERRATA.md` P3 rows), places where P3 is sketched.
7. **Lean plan and size estimate**, against landed modules; **questions**.

Standards: exact page/equation references (P3 is a scan or text — say which pages you read as
images); distinguish proved / cited / sketched; mark doubts "UNCERTAIN:". Plain mathematical prose;
avoid "calibration", "robust", "leverage", "crucially". LaTeX in $...$. Expect 8,000–14,000 words;
write the file section by section as you go.

Rules: write only `/home/scott/Balaban/notes/phase1/LOCALIZATION.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/loc/ allowed). Do not edit any other file, do not commit, do not
run Lean or lake. When done, reply with: the A/B decision and its reason, the statements of I-4 and
I-5 (one line each), which proofs are complete, the main risk, and any questions.
