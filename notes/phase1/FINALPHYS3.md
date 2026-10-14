# FINALPHYS3: decision D for the last integral's interaction (leaf E4)
14 October 2026. PROVED = source statement read on the PDF text layer, or landed declaration, or elementary argument shown;
OPEN = missing bridge; REFUTED = invalid inference. Read: P7 `sources/s002200050486.pdf` printed pp. 529-533 (PDF p. 37-41),
P4 `sources/Balaban.pdf` printed pp. 719-720, FINALPHYS2, FINALFAM2, `Green/FinalLocalityAE.lean`, `External/BKAR/Smoothness.lean`.
P3 (localization expansions, 2.8) was NOT read here; every statement about it is marked.

## 0. Verdict
**R1, in a corrected form (R1').** The cutoff goes into the reference measure as a cutoff on the REAL Gaussian variable psi,
independent of s; the interaction needs analyticity only on a polydisc of radius B_C * rho around 0, not an entire function with a
Gaussian bound. R2 (BKAR real interpolation) is not chosen. **OPEN** (not decided by the sources): the tail region where the
cutoff fails (section 2d); it is what the large-field regions of P7 (4.1), (4.12)-(4.13) handle, and Lean has no counterpart yet.

## 1. What P7 section 4 does (answer to (1))
**PROVED (P7 p. 529, (4.1)).** The integral over psi_k is written as sum over large-field regions Z_k of
int dpsi_k rho_k(Z_k) chi_k(Z_k) exp(A_k(Z_k^c) + F_k(Z_k^c) + R^(k)(Z_k^c)). The interaction terms F_k, R^(k) are functions on
Z_k^c ONLY, where chi_k restricts psi to |psi_k - h| < (5L+3) delta_k (P4 (6.2), p. 719). The large-field region is explicit
in the density; it is not obtained by cutting a global interaction.
**PROVED (P7 p. 529-531).** The mass nu_k > 7/8 L^-2 makes the variational problem (4.3) massive; background psi_0^(k) = Q phi_{k,0}
with phi_{k,0} = h + delta phi_{k,0}. The fluctuation integral is done "exactly as in Sect. 3 [5]" ((3.18)), no renormalization.
P7 prints NO cut matrix and NO square-root family (FINALFAM2 line 13 confirmed). The s-interpolation of the covariance is
therefore not in P7 at all; it is the repository's own device (Lemma AE with complex s).
**PROVED (P4 p. 720, (6.6)).** After the change of variables phi' = beta^(-1/2) C^(1/2) psi the integral carries the
characteristic function chi({|psi| < p_1(beta_k)}) on the unit-Gaussian variable. This is the cutoff in the reference measure.
**PROVED (P7 p. 532, (4.12)-(4.13)).** Activities of the polymer expansion: product over large-field components Z_ir of
exp(-p_2(beta) - H_k|Z| + E|Z| + 2 B_0 K_0 eps^-1 (M)^-1 d|Z|), times eps exp(-(3/2 kappa - kappa_0) d(X_i)); the term -H_k|Z| of
(1.31)[5], unused until now, gives the decay in arbitrarily large Z; eps^-2 = 3^d K_0 exp(3/2 d L kappa); H_0 large.
So the large-field part is bounded absolutely (Gaussian tail e^{-p_2} and e^{-H_k|Z|}), not by analytic continuation in a cut.

## 2. R1' in detail (answer to (2))
(a) **REFUTED (as stated in FINALPHYS2 R1).** "Entire in psi with |F| <= C e^{c|psi|^2}" is not available and not needed: the
interaction F_k (H7 [4], (1.35) [5]) is analytic only on a complex neighbourhood of the small-field ball |psi - h| < (5L+3)delta_k,
with exponential tree bounds; nothing in P7 p. 529-533 asserts entireness. I found no source statement to the contrary.
(b) **PROVED (elementary, from landed).** Let `x` be a site, `‖s p‖ <= e^kappa`. `taggedCfin_row_bound` (r = 0) gives
sum_y ‖taggedCfin s x y‖ <= B := 4/3 (2 e^{H kappa} ballConst(eps/2))/sqrt(finalGap) (FinalTaggedSqrt.lean:267; the same B bounds
the entries in `abstract_expansion_taggedCfin_final`). Hence for COMPLEX s and REAL (even complex) psi with sup|psi| <= rho,
sup_x |(C(s) psi)(x)| <= B rho. So the argument of F stays in the sup-ball of radius B rho: an s-independent cutoff
sup|psi| <= rho keeps C(s)psi inside the H7 analytic domain provided that domain has radius >= B rho in the field variable.
The cutoff p_1(beta) of P4 (6.6) is of the same order as the domain radius (P4 (6.1)-(6.2): Xi(1,delta) between Psi(delta/K) and
Psi(3 delta)); the factor B e^{H kappa} is a constant, so an enlargement of the analytic domain by a constant factor is needed.
**OPEN:** that the H7 domain radius at k_f exceeds B(kappa) p_1 for the constants of Root-F (kappa fixed by Lemma AE, kappa >= 1);
it is a comparison of constants between P4 (6.1) and the landed `pdB`, `pdH`, `ballConst`; not done here.
(c) **PROVED (elementary).** Since the cutoff 1_{sup|psi|<=rho} does not depend on s, J_rho(s) = int 1_{sup|psi|<=rho} F(C(s)psi) dgamma
is analytic on the polydisc as soon as F is analytic and bounded on the radius-B rho ball: differentiation under the integral over a
compact set of psi (Morera/dominated convergence), |J_rho| <= sup|F| * gamma(cutoff). Locality of coef J_rho: through the landed
`coef_taggedCfinU_congr_of_agree` / `localityAE_taggedCfinU` as in FINALPHYS2 E4 (the cutoff factorizes over blocks if chosen as a
product of block cutoffs, which does not change the argument).
(d) **OPEN, the real gap.** Region sup|psi| > rho. Option T1: expand 1 = prod_z (chi_z + (1 - chi_z)) over the cubes z; the
resulting large-field sets Z play the role of Z_k in P7 (4.1)/(4.12). On Z the interaction is NOT evaluated (the Z_k^c-localized
F_k); the weight of Z is bounded absolutely at the physical s = 1 by the tail estimate. What is not settled: whether the
s-expansion of P3 treats the large-field blocks through the same C(s) (then F(C(s)psi) is needed off-domain) or only through the
real covariance. This is the P3/P5 localization question; I did not read P3 2.8. Option T2: absolute bound only, no
decoupling for Z; this suffices for Root-F only if the large-field activities are summed as separate polymers (P7 (4.14)).
Cutoff placement: product of block cutoffs in psi, in the Gaussian reference measure, exactly P4 (6.6) / P7 (4.1).

## 3. R2 (answer to (3))
**REFUTED (cheap version).** Landed G_fin(s) is one-sided (FINALFAM2 REFUTED symmetric), so s in [0,1]^P gives no Gaussian
covariance; a symmetrized family S(s) = 1/2(C(s) + C(s)^T) is symmetric but its positivity for s in [0,1]^P is not proved (the
Stieltjes integral is of one-sided tagged parametrices; no sign argument is landed). Not tested on a computer here.
**PROVED (obstruction, Smoothness.lean:44, KF0-INFL section 1).** `BKARContDiff rho` is `ContDiff R infty rho` on ALL of
Edge V -> R. A covariance interpolation is defined only on its positive domain; it must be extended smoothly outside (with
determinant and mean). The smooth extension is a new construction with uniform control of every mixed derivative; the whole
landed pipeline (`abstract_expansion`, `abstract_expansion_taggedCfin_final`, complex polydisc, Cauchy) would be bypassed.
**OPEN:** nothing shows R2 is impossible, but it requires a new positive family, a new smooth extension and a new
forest-to-activity bound. R1' reuses `taggedCfin`, `localityAE_taggedCfinU`, `abstract_expansion` unchanged.

## 4. First two Lean leaves of R1' (answer to (4)), no new definitions, each <= 200 lines
**L-A (box lemma).** In `Green/FinalLocalityAE.lean` hypotheses of `abstract_expansion_taggedCfin_final`, for
`ψ : L1Torus d N₀ → ℂ`, `ρ ≥ 0`, `(∀ y, ‖ψ y‖ ≤ ρ)`, `s` with `∀ p, ‖s p‖ ≤ Real.exp κ`, every `x`:
`‖∑ y, taggedCfin d L N₀ k M v a s x y * ψ y‖ ≤ B * ρ`, B as in that theorem. Proof: triangle inequality, `taggedCfin_row_bound`
with `r = 0`. (Vector-valued field: componentwise.)
**L-B (analytic parameter integral on the box).** Generic: `ι`, `Λ` finite-dimensional complex, `G : (ι → ℂ) → ℂ`,
`AnalyticOnNhd ℂ G (closedBall-polydisc 0 R)` and `‖G w‖ ≤ B'` there; `T : (P → ℂ) → ((ι → ℝ) → (ι → ℂ))` with each
`T s` real-linear in ψ... concretely: `Φ : (P → ℂ) → (ι → ℝ) → ι → ℂ` jointly analytic in s for each ψ (as the matrix-vector product
of `taggedCfin` with real ψ), `∀ s ∈ polydisc, ∀ ψ ∈ box ρ, Φ s ψ ∈ polydisc 0 R`. Conclusion:
`AnalyticOnNhd ℂ (fun s => ∫ ψ in box ρ, G (Φ s ψ) ∂γ) (polydisc 0 (e^κ))` and the norm bound `B' * γ(box ρ)`.
Template: `Localization/ParameterAnalytic.lean:analyticOnNhd_integral_step`, `Localization/DecoupledCovParam.lean:analyticOnNhd_integral_Ioi`.
Check first whether a parameter-integral analyticity lemma on a finite measure already exists (the two above are for intervals).

## 5. Risk and status
- Leaves L-A, L-B are PROVABLE from landed material (high confidence); they establish only the cutoff part J_rho.
- **Medium-low risk on the whole route:** (i) constants: H7 domain radius versus B(kappa) p_1 (2b); (ii) the tail (2d), P3 not read.
- Next, if R1' is accepted: L-C compares the H7 radius with B rho (constants only, orchestrator/author item), L-D the tail by
  T1 with absolute Gaussian-tail bound (P7 (4.12)), E4 then = J_rho expansion + large-field polymers.
- Question for the author-side agent (text-ready): "In the last step, is the localization expansion of the covariance applied to
  the large-field blocks Z_k, or only to Z_k^c, where chi_k bounds |psi - h| < (5L+3) delta_k? (P7 (4.1), (4.12))"

## W789 status (14 October 2026)
- `Balaban/Green/FinalInteractionCutoff.lean`: L-A `norm_taggedCfin_mulVec_le` (row bound at r = 0, B as in `abstract_expansion_taggedCfin_final`) PROVED.
- L-B `analyticOnNhd_integral_box` PROVED via the landed `analyticAt_integral_of_continuousOn` (Analysis/ParamIntegralAnalytic.lean); needs joint continuity of Phi on polydisc x box.
- `cutoffInteraction_final`: J(s) = int_{box rho} F(C_fin(s) psi) dgamma analytic, bounded by B' gamma(box), Lemma AE conclusions (sum, coefficient bounds), value at s = 1 via sqrtMat; needs B rho < R, F analytic and bounded on radius R.
- `localityAE_cutoffInteraction`, `coef_cutoffInteraction_congr_of_agree`: datum-dependent locality (taggedCfinU), any F, gamma. Still open: L-C (constants), L-D (tail).

## W790 status (14 October 2026)
- `Balaban/Green/FinalConstants.lean`: L-C. In the variable psi the physical field is phi_0 + beta^{-1/2} C(s) psi, so an interaction analytic on the radius-Rphys polydisc around phi_0 has radius beta^{1/2} Rphys in psi; the condition B rho < R becomes B(kappa) beta^{-1/2} p_1 < Rphys (`cutoffInteraction_final_phys`, `cutoffInteraction_final_fluctRadius` with Rphys = landed `fluctRadius`).
- Which side wins: the landed hypothesis of Lemma 2.5 is B_5 beta^{-1/2} p_1 <= fluctRadius; here B_5 is replaced by B(kappa) >= 8/3 e^{pdH kappa}/sqrt(finalGap), pdH 3 = 13357 (`pdH_three`). For fixed p_1 it holds for beta >= (B p_1/Rphys)^2 + 1 (`cutConst_mul_lt_of_large`); if p_1 is taken proportional to beta^{1/2} delta it is a smallness condition on that proportionality constant.
- NOT done: the identification of the actual F_{k_f} (an F on the polydisc of radius fluctRadius around the background, bounded) with a landed declaration; F, phi_0, B' stay hypotheses. L-D (tail) open.
