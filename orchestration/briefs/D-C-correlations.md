# Brief D-C — deriving Root-C from the flow (`notes/phase1/CORRELATIONS.md`)

You are a mathematical physicist writing a phase-1 document of the Lean formalization of
Balaban's RG analysis of the low-temperature O(N) model (hard spins). Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics on paper; you do not write or
run Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context

- Frozen roots: Root-C `Balaban/Frozen/Roots/LowTemperatureCorrelations.lean` (P9 Thm 1.1 for hard
  spins: magnetization, decay bounds, infinite-volume limits along tori with side divisible by
  q^n, the ν ↓ 0 limits and the Goldstone asymptotics with γ_∞) and Root-F
  `.../LogPartitionMultiscale.lean` (the multiscale representation of log Z(g)/Z(0), with
  torus independence). Read both and the definitions they import, and the decision record
  `notes/phase0/surface-v1-for-approval.md`.
- Landed Lean you should build on (read the statements): `Balaban/Gaussian/Multiscale.lean`
  (`laplacian_inv_eq_multiscale`: exact k-step decomposition of (−Δ+ν)^{-1}),
  `Balaban/Flow/RunningCoefficients.lean` (`exists_gamma_infty`,
  `exists_inv_betaSeq_asymptotics`: β_j^{-1} = (βγ_∞)^{-1}L^{-j(d-2)} + O(β^{-1})L^{-j(d-2+2γ)}),
  `Balaban/Analysis/Cauchy.lean` (Cauchy and mixed-derivative estimates).
- Sources: P9 (`sources/s002200050510.pdf`, text layer usable; journal pp. 493–520, PDF page =
  journal − 492), especially §2 ((H.1)–(H.2), Lemmas 1–2), §3 (Prop 3.1), §4 ((4.1)–(4.18));
  P4 §6 and p. 720 (thermodynamic limit remarks); P5 (1.45)–(1.46). Reviews
  `review/papers/P9-*.md`, `P4-*.md`, `P5-*.md`; roadmap §3.3 (C-1, C-2, C-3) and the polymer
  document `notes/phase1/POLYMER.md` (PE-M proves P9 (3.13) given the MY form).

## Task: write `/home/scott/Balaban/notes/phase1/CORRELATIONS.md`

1. **What Root-F gives and what it does not.** Derive, with proofs, every consequence of Root-F's
   statement alone for the one- and two-point functions (Cauchy estimates on ‖g‖ ≤ 1/2; sums over
   polymers with block-count decay; uniformity in ν and the torus), and the thermodynamic limit
   along tori with side divisible by q^n from the torus-independence clause. State precisely
   which parts of Root-C follow from Root-F alone (e.g. |m − 1| small, decay bounds?) and which do
   not (the Goldstone asymptotics, which need P9's explicit leading terms).
2. **The extra outputs of the flow that Root-C needs.** P9's inductive descriptions (H.1)–(H.2)
   (the explicit main terms m_k φ_k and C_k = Σ β_{j−1}^{-1} m_k G^{(j)} m_k, the remainders R^{ij}
   with their bounds) and the last-step identities (4.7)–(4.11). State them as precise interface
   statements (candidates for C-1) in a form a Lean statement could take, at λ = ∞ (where the
   longitudinal main term vanishes).
3. **The derivation of Root-C** from those interfaces, Root-F, `laplacian_inv_eq_multiscale` and
   the γ_∞ asymptotics: the transverse leading term m²/(βγ_∞)(−Δ)^{-1} via P9 (4.14)–(4.18)
   (check the index shift P9 leaves unexplained, and the formula for a_j printed with a_0 = ∞),
   Lemma 1's summation, the ν ↓ 0 limits (P9 (4.15) dominated convergence argument, written out),
   the identification of the Green's function G of Root-C (−ΔG = δ₀, G → 0 at infinity) with the
   limit of the multiscale sum. Complete proofs where the argument is short; detailed plans
   otherwise.
4. **The thermodynamic limit (C-3)**, for all quantities Root-C mentions, with complete proofs.
5. **What no source proves**, with your confidence.
6. **Lean plan and size estimate.**
7. **Questions**, if any.

Standards: exact page/equation references; distinguish proved / cited / sketched; mark doubts
"UNCERTAIN:". Plain mathematical prose; no marketing words; avoid "calibration", "robust",
"leverage", "crucially". LaTeX in $...$. Expect 5,000–10,000 words; write the file section by
section as you go.

Rules: write only `/home/scott/Balaban/notes/phase1/CORRELATIONS.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/corr/ allowed). Do not edit any other file, do not commit, do not
run Lean or lake. When done, reply with: which parts of Root-C follow from Root-F alone, the list
of extra interfaces (one line each), what no source proves, and any questions.
