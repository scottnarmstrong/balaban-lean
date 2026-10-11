# Orchestration ledger

| Date | Item | Status | Notes |
|---|---|---|---|
| 2026-10-11 | Phase 0 scaffold | done | toolchain v4.35.0-rc2, Mathlib 065356127b1d, checkers from FroehlichSpencer adapted to the `Balaban` namespace |
| 2026-10-11 | Draft Def-1, Def-2, Root-F, Root-C | superseded by freeze below | package `notes/phase0/surface-v1-for-approval.md` v1.2 (audit FAIL on v1.0 → fixed; re-audit: statements approved as written); code in `/home/scott/Balaban-scratch/p0/tree` |
| 2026-10-11 | Questions for Roland, batch 1 | ready to send | `notes/QUESTIONS-ROLAND-1.md` (roadmap 5–10, new 11–12) |
| 2026-10-11 | Errata ledger | done | `notes/ERRATA.md`, 231 rows (16 orchestrator-verified) |
| 2026-10-11 | Freeze surface v1 | done | approved "all defaults"; 8 definitions SEALED, Root-F and Root-C DRAFT_SORRY; guard, ABI, statement closure, module checks pass |
| 2026-10-11 | Roland answers 5–12 | recorded | `review/ROLAND_ANSWERS.md` batch 2; open: β-dependence of P9 constants |
| 2026-10-11 | Phase 1 start | in progress | `notes/phase1/PLAN.md`; documents D-LF, D-G, D-PE being written; briefs W1, W3a |
| 2026-10-11 | Agent cap | rule | author: at most 4 Sonnet + 1 Opus subagents, no sub-subagents |
| 2026-10-11 | W3a BKAR port | landed | `975347f` (55 files, modules, v4.35.0-rc2; proof-only repairs `dif_pos/dif_neg → dite_eq_left/right`, `if_pos/if_neg → ite_eq_left/right`, one trailing `rfl`; statements unchanged, checked by diff against `a07f44a`); axioms standard |
| 2026-10-11 | W2a Combes–Thomas | running | Sonnet, worktree W2a |
| 2026-10-11 | W2a Combes–Thomas | landed | non-Hermitian coercive kernels with exponential decay: `combesThomas`, `combesThomas_restrict`, `perturbation_decay`, `greenFn_resolvent_identity` (`Balaban/Green/`, 724 lines); axioms standard |
| 2026-10-11 | W1 lattice/Gaussian | landed | `99dc252`: blocks, block averaging (Q, Q*, projection), Gaussian integral with determinant (complex source), Gaussian measure and moments, Schur/Woodbury, block-spin identity with minimizer, composition, weighted form (1,103 lines); axioms standard; target 6 open → W1b |
| 2026-10-11 | D-PE polymer document | draft, in review | `notes/phase1/POLYMER.md` (Sonnet); review → `POLYMER-review.md` |
| 2026-10-11 | W1b multiscale | landed | torus Laplacian matrix, one-step splitting `A⁻¹ = M⁻¹ + HΔ⁻¹Hᵀ`, exact k-step decomposition `laplacian_inv_eq_multiscale`, positivity (≈410 lines); axioms standard |
| 2026-10-11 | D-PE polymer document | revised | review R1–R12 addressed (`## Review dispositions`); ready for PE interface drafting and W3b |
| 2026-10-11 | W7 holomorphy | landed | Cauchy estimates (ball, polydisc, mixed i≠j), several-variable Weierstrass (uniform limits analytic), `exists_analytic_fixedPoint`, `exists_tendsto_prod_inv_one_add` (≈900 lines); axioms standard |
| 2026-10-11 | W2b coercivity | landed | block Poincaré (const d/2), single-scale coercivity with complex α (`blockHamiltonianC_isCoercive`), Schur variational form, `unconstrainedUnitOperator_lower` (γ ≥ 1/(8d+3)) (≈1,470 lines); constrained (λ=∞) operator and multiscale item 4 open |
| 2026-10-11 | W4 RG equations | landed | `4985fa7` via land.sh: `Balaban.Flow.exists_rg_solution` (P4 Prop 5.1, λ=∞), triangular form, running coefficients, (H.6) bounds, `exists_gamma_infty` (5.33), `exists_inv_betaSeq_asymptotics` (P9 (4.18)) (≈710 lines); axioms standard |
| 2026-10-11 | W2c G-4 tails | landed | `0f2d7b5`: Lemma 4.10 `sum_tail_le`, G-4(b) `domain_difference`, G-4(c) `perturbation_tails`, ℓ¹ ball sums (≈700 lines); axioms standard |
| 2026-10-11 | D-G Green's function document | final | re-review APPROVE-WITH-CHANGES, N-1..N-6 applied; freeze-candidate list in §3 |
| 2026-10-11 | W5 constant configs, O(N) reduction | landed | `05e2eb7`: λ=∞ constant configurations (unique minimizer/EL solution, complex analytic extension, P2-type bounds, covariance), analytic O(N) reduction `exists_invariant_reduction` (≈1,700 lines); axioms standard |
| 2026-10-11 | W8a multiscale coercivity | landed | `7130c2c`: `GeneratingSet`, layers, spacing, averaging form (1.4), `dirichletOperator` (1.6), `pathDist` (1.9), `multiscale_coercive` (c₁ = 1/(2d)), invertibility (≈750 lines) |
| 2026-10-11 | W3b polymer expansion | landed | `9c1989a`: abstract KP theorem (`pe_xi_eq_exp`, `pe_clusterBound`, `pe_PY_bound`, one-parameter `pe_differentiableOn`), Ursell sign/tree bound by vertex removal (no BKAR needed), animals for degree-Δ graphs, `pe_lattice`, `pe_blockTorus` (≈3,200 lines); axioms standard |
| 2026-10-11 | D-C correlations document | revised | review D-01..D-13 addressed; Lean packages A–F startable from Root-F's statement |
| 2026-10-11 | W8b Agmon decay | landed | `65e44ec`: path-metric bounds (Lemma 4.3), Agmon estimate, block decay, `green_G2i` with scale mismatch (≈2,160 lines) |
| 2026-10-11 | W10 model basics | landed | sphere-measure invariance, model symmetries, `exists_block_structure` (finite-volume Root-C structure), `analyticOnNhd_logPartition`, derivatives = correlation functions (≈1,100 lines) |
| 2026-10-11 | W9 lattice Green | landed | heat-kernel construction, `latticeGreen_existsUnique` (Root-C's G: −ΔG = δ₀, G → 0, unique), Lemma K bounds `latticeGreen_le_rpow`, first and second differences (≈2,190 lines) |
| 2026-10-11 | W3c polymer completion | landed | `pe_analyticOnNhd`, `pe_blockTorus_frozen` (frozen IsPolymer language), `frozenPY_boxMap` (torus independence), marked/truncated moments, `pe_hole` (Steiner size) (≈2,350 lines); MY and GAS open |
| 2026-10-11 | W8d G-2(vi) | landed | `analyticOnNhd_green_apply`, counting Lemma 4.4 `sum_siteWeight_decay_le`, `green_sub_green_locality` (product form, rate ε₀/6), `sqrt_sqNorm_le_of_supp` (≈1,000 lines) |
| 2026-10-11 | W11 Root-F consequences | landed | `RootFStatement` (checked definitionally equal to frozen Root-F by a scratch probe), `abs_onePoint_sub_le`, `exists_abs_twoPointTruncated_le`, `twoPoint_tendsto_along_multiples` (thermodynamic limit), lcm lemma (≈2,350 lines); conditional on Root-F's clauses |
| 2026-10-11 | W3d Mayer and GAS | landed | `mayer_integral_eq`, `mayer_activity_bound`, `mayer_pe`, `gas_eq`, `gas_activity_bound` (constant +3, correcting POLYMER.md §3.9's +2), `gas_pe`, `pe_size`, `mayer_marked` (P9 Prop 3.1 instance-free) (≈2,640 lines); polymer package complete |
| 2026-10-11 | W8c constrained operator | landed | `constrainedOp_posSemidef`, `constrained_complex_lower`, `unitKernel_bound`, `constrained_G2v` (≈3,600 lines); G-2(v′) open (needs pointwise G-2(iv)) |
| 2026-10-11 | W13 G-5 | landed | `oneScale_blockDecay`, `fineToBlockKernel_decay` (block L²), `coarseGreen_decay`, Lipschitz in ν ∈ [0,2], `infiniteVolume_limits` (subsequential; uniqueness → W13b) (≈2,200 lines) |
| 2026-10-11 | W14 x-variant | landed | `xVariant_reduction`, `constrained_green_eq` (G_c = G − Π), `xVariant_constrained_reduction`, x-variant coercivity uniform in x, `green_G2i_x` (rate depends on L) (≈1,660 lines); α₀ range below P3's a_{k+1}L⁻²/12 by a d-factor → sharp Poincaré W2d |
| 2026-10-11 | W12 pointwise bounds | landed | `lemma_loc_a`, `lemma_loc_b` (interior estimates), `lemmaP`, `prop48` (G-2(ii) pointwise decay of u and ∂u, K₂(d,L)) (≈3,460 lines); Loc (c)/Hölder (needs third differences of C) and η-scaling open |
| 2026-10-11 | W15 Gaussian bookkeeping | landed | `sum_rule_matrix`, `mul_prolong` (3.2), `goldstone_rewriting` ((4.18) step), `KernelHyp.tsum_eq_latticeGreen` ((G4): Σ t_j = Root-C's G, conditional on kernel hypotheses G1–G3, G5 from W13/W13b) (≈1,250 lines) |
