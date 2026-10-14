# FINALPHYS2: route to the localized last integral after W753-W784
14 October 2026. PROVED = landed declaration or elementary argument shown; OPEN = missing bridge; REFUTED = invalid
inference. Reads: FINALPHYS.md (status sections W753-W784), FINALFAM2 T4, FINALMAP, Root-F statement, the signatures in
`Green/FinalLogDetLocal.lean`, `GaussianChangeGeneral.lean`. The papers (P7 pp. 529-531, P4 pp. 719-720) were not re-read here;
FINALFAM2 records that they print no final cut matrix and no square-root family.

## 0. Verdict
**REFUTED (the premise of the question).** The localized last integral does not need a square-root family for the change of
variables. The change `psi = C phi` is made ONCE, at the physical parameter, with `C = sqrtMat U` real symmetric positive
definite (`lintegral_pd_gaussian_change`, landed; the old leaf "gaussian_change_cut" with `C(s)` not a square root is dropped).
The cut family `s |-> taggedCfin s` then enters only as the argument of the interaction, `J(s) = int F(C(s) phi) dgamma(phi)`;
it needs analyticity, bounds, locality (all landed), not invertibility and not a determinant. `taggedCfin 0 = 0` is harmless:
`J(0) = F(0)` is the decoupled value. The determinant is needed only for the RATIO `det(U+E)/det U` (section 1a).
**OPEN, the real obstruction (not the square root): the domain of `F`.** `F(C(s) phi)` for complex `|s p| ~ e^kappa` and
unbounded real Gaussian `phi` leaves the H7 analyticity domain (`Im(C(s)phi)` is not small), and the cutoff in `psi` is not
analytic. Two ways out, to be decided before L4: (R1) write `F` as a function of `psi` that is analytic on the whole complex
`psi` in the form the cut family produces (entire Gaussian-type bound on the interaction after the cutoff is moved into the
reference measure); (R2) real interpolation `s in [0,1]^P` with the forest formula (`Balaban/External/BKAR`), which needs a
SYMMETRIC POSITIVE interpolated covariance; the landed `G_fin(s)` is one-sided (FINALFAM2, REFUTED symmetric), so R2 needs a new
symmetric positive family. Neither is landed or proved here. This is the cheapest decisive question for the author-side agent.

## 1. Answers (a), (b)
**(a) Normalization.** Root-F is a statement about `Z(g)/Z(0)`, so the bulk constants cancel and `det(U_0)^{-1/2}` itself is
never localized. What must be localized is `det(U_0+E)^{-1/2} / det(U_0)^{-1/2}`, `E` the inherited interaction/saddle
perturbation (nonconstant background, `WSmall r eta E`, `eta < finalGap`). Use the SAME parametrix `G_*` (boxes of `finalOp`)
and the defect `K_E(s) = 1 - (finalOp+E) G_*(s)`. Then (W784 pattern, E = 0 landed)
`det(finalOp+E) det(B) = prod_C exp(coef ell_E C)` and `det(finalOp) det(B) = prod_C exp(coef ell_0 C)` with the same block
factor `B = sum_z chi_z G_z`, so `B` CANCELS in the ratio: `det(finalOp+E)/det(finalOp) = prod_C exp(coef (ell_E - ell_0) C)`.
No cluster expansion of `det B` alone is needed (W784 "NOT DONE" item is not on the critical path). Row sums of `K_E`:
`<= 1/4 + eta_E` for `E` small, the series route of W784 (`eq_neg_tsum_taggedK` is stated for any matrix) goes through.
Half power: `ell_E(1)` is REAL for real `E` (series of real traces at `s = 1`, `t = 0`), so `exp(-ell/2)` is the positive root;
for complex `g` define it as `exp(-ell/2)`, analytic on a simply connected polydisc with `ell(0) = 0`: no branch issue.
**(b) Interaction.** Via the cut family on the covariance factor `C(s)` inside `F` (section 0), `F` the zero-region interaction
(class terms, `E`, `M`), plus the Gaussian ratio of (a) as an extra local factor. Locality: `coef_taggedCfinU_congr`,
`coef_eq_of_agree_on_region`; vanishing at separated supports: `coef_eq_zero_of_separated_taggedK`, `coef_taggedCfin_final_eq_zero_of_separated`.

## 2. Revised leaf list (dependency order; Sonnet unless noted; each <= 300 lines; no new definitions)
**D (gate, author-side agent / orchestrator, no Lean).** Decide R1 versus R2 of section 0 and record whether the interaction's
analytic domain is in `psi` or in the cut parameter. Everything marked [gate] below waits for it; D reads P3 (2.8), P4 (6.4)-(6.6).
**E1. Perturbed defect row sum (start now).** `K_E`: for `finalOp`, `WSmall r eta E`, `eta <= eta_0(d,L)`, `s` in the closed
polydisc `||s p|| <= e^kappa`, `t >= 0`: `forall x, sum_y ||(1 - (finalOp+E) * taggedGfin s t) x y|| <= 1/4 + c eta` and
`K_E = K + (E * taggedGfin)` with `E`-row bound from `taggedG_column_sum` and `WSmall`. Uses `taggedK_row_sum`,
`taggedGfin_column_bound_same_rate`, `taggedDefect_isUnit_inv_weighted` (landed W782), generic-matrix W759.
**E2. Localized perturbed determinant ratio (after E1; ~250 lines).** Package `exists_series_log_det_taggedDefect` for `K_E`
(generic `det_one_sub_eq_exp_tsum_trace` + `eq_neg_tsum_taggedK` need only row sums `q < 1`): analytic `ell_E` with
`ell_E 0 = 0`, `coef ell_E C` local on `Y(C)^2` agreeing with `ell_0` off the support of `E`, bound `|C| B_D/(e^kappa-1)^|C|`
(W784 factor `|C|` stays), and `det(finalOp+E)/det(finalOp) = prod_C exp(coef (ell_E - ell_0) C)` using
`det_mul_det_boxResolvent_eq_prod_exp_coef` for `E = 0` and its `E`-version (same proof).
Note the support of `coef (ell_E - ell_0) C` is contained in `region(C) meets supp E`: only polymers touching the perturbation
carry activity, which is exactly the P7 (4.9) form. `E` varying with `h(z)`: take `E` as an arbitrary matrix with the row bound
(no translation invariance used: `coef_eq_of_agree_on_region` is stated for any two matrices).
**E3. Gaussian reduction (start now, ~120 lines; mostly landed).** `Z[F]/Z[1] = int F(sqrtMat U phi) dgamma(phi)` for real
positive definite `U` and bounded measurable `F`; wrapper of `lintegral_pd_gaussian_change`; with `U = finalOp + E` real at real `g`.
The `U`-dependence of `sqrtMat` inside `F` is the issue of section 0, not of this leaf.
**E4 [gate]. Activity per polymer.** `J(s) = int F(taggedCfin s *v phi) dgamma(phi)`: analytic on the polydisc, locality
`coef J C` depends on `u|Y(C)` via `coef_taggedCfinU_congr`, bound `B_J exp(-kappa|X|/(M L^J)^d)` by `abstract_expansion_on`.
Statement shape as the old L4(ii); the domain problem of section 0 sits here. Inputs: interaction read-set (FINALMAP P4), E2 for
the Gaussian-ratio factor, `isLocExp_of_coeffFamily_renTheta_tower` for datum dependence.
**E5 [after E4]. Bound of activities / derivative in the source** (old L5): `4 sqrt N B_J <= c9 L^{-J((d-2)/2+delta)}`, Cauchy on
the open unit ball, combined with the E2 ratio bound; feeds `logPartition_multiscale` (zero-region part only).
**E6 [after E4]. Two-torus equality** (old L7), unchanged; the determinant ratio part is new: `coef (ell_E - ell_0) C` on tori
`N0, N0'` for nonwinding `C`; template `coef_eq_of_agree_on_region` plus the torus lift of `finalOp` entries.
**E7 (wait). Physical joins** (old L8): P1 Hessian bridge, P2 cutoff coverage, P3 complex chart, P5 nonempty large-field region;
needs the LF lane and author item 17 (`k_f = 0`).
**Dropped or demoted:** old L1 (generic-matrix interface) is superseded by W759 plus E1; old L2/L3 (invertibility, log det of the
cut family) are REFUTED/closed by W757, W779, W782, W784; old L6 landed (W753); old L4(i) `gaussian_change_cut` is dropped.

## 3. Start now versus gated
**Start now (generator-neutral):** E1, E3; then E2 after E1. D can run in parallel (no Lean).
**Gated on D:** E4, E5, E6; **wait:** E7.
**Confidence.** High on (a) (algebra of W784 plus cancellation of `B`; the row sum for `K_E` is the only estimate to check, by
perturbation of landed bounds). High that the square root is not needed. Medium-low on E4: the analytic domain of the
interaction under complex cut parameters is unverified and may force R2.

## W787 status (14 October 2026)
E1, E2, E3 PROVED in `Green/FinalDetRatio.lean` and `Green/FinalGaussianReduction.lean`. Correction to section 1a: the landed `taggedK` of `finalOp+E` uses the boxes of `finalOp+E`, so its block factor differs; the ratio needs the MIXED defect `K_E = tagged(R_z - E chi_z G_z)` with the boxes of `finalOp` (`1 - K_E(1) = 1 - (U+E+t) sum chi_z G_z`). Row sums `<= B e^{H kappa}/M + e^{H kappa}(2/g)eta ballConst(3 eps/4)` (`taggedKE_row_sum`); `taggedKE_isUnit_inv_weighted` (inverse weighted bound 2).
`exists_det_ratio_localized`: `det(finalOp+E+t) = det(finalOp+t) prod_C exp(coef ellE C - coef ell0 C)`, locality (E = 0 on Y(C)^2), separated vanishing, bound `2|C|(8M+1)^d/(e^kappa-1)^|C|`. Extra hypotheses: `WSmall rE eta E` with `pdEps/4 <= rE`, and `4 e^{H kappa}(2/g)eta ballConst(3 eps/4) <= 1`.
E3: `lintegral_pd_gaussian_ratio`: `Z[F]/Z[1] = int F(pdSqrtInv K psi) dgamma` (ENNReal, any F; the matrix is `K^{-1/2}`, not `sqrtMat K`). Not done: E4-E7 (gate D unchanged).

## W791 status (14 October 2026)
E6 (a) and (b) PROVED in `Polymer/TwoTorusFinal.lean`. Margins: cells of `C` have coordinate indices in `[4, J]` and `2(J+6)M <= N, N'` (then `Y(C)` has residues in `(2M, (J+3)M)`: no wrap through 0, diameter below `N/2`); `f x = (x.val)`, `e` = identity on indices `<= J+4`. The torus data enter only through correspondence hypotheses on `Y(C)^2`.
(a) `coef_detRatio_eq_twoTorus`: `coef ellE C - coef ell0 C = coef ellE' (e C) - coef ell0' (e C)` for the `exists_det_ratio_localized` logarithms, given `U, E` (`finalOp`, the perturbation) corresponding on `Y(C)^2`; general form `coef_eq_of_agree_taggedKE_twoTorus` (log-uniqueness on the convex set of `C`-supported parameters, then `coef_relabel_injOn`). Exact transport of cells, `macChi`, boxes, tags, box resolvents (`boxG_transport`), determinants (`det_taggedKE_twoTorus`).
(b) `coef_cutoffInteraction_eq_twoTorus` (and `_final_` for `taggedCfin`): entries of `taggedCfinU` vanish off `Y(C)^2` and correspond on it (`taggedCfinU_entry_twoTorus`); `J` and `J'` equal when `F, F'` correspond on fields supported on `Y(C)` (`hF`), are measurable, and the box-restricted reference measures have equal images under `psi |-> psi|_{Y(C)}` (`hγ`); `J` analytic on the polydisc `R > 1`.
Not done: that the final operators and the reference Gaussians of two tori correspond on `Y(C)^2` (`hU`, `hγ` are hypotheses; they hold up to winding terms, not exactly).

## W792 status (14 October 2026)
`Green/FinalTermBound.lean`: (1) `card_le_card_mul_of_subset_biUnion`, `coefDecay_site` (cell decay `A e^{-(kappa-1)n}` to `exp(-(kappa-1)/cov |X|/(M L^j)^d)`), `detRatioCoef_decay` (`2nD/(e^kappa-1)^n`, `e^kappa>3`, rate `log((e^kappa-1)/2)`); (2)+(3) `finalTerm_bound`: Cauchy radius `r <= 1/2` (`norm_kf0Deriv_le_radius`), `A <= C0 betaK^{-2}`, `betaK_inv_sq_le`; condition `L^((d-2)/2+delta) <= (c9 r/(K C0)) beta0^2`.
Inputs kept as hypotheses: F analytic on the ball with `‖F‖ <= K A e^{-kappa1 n}` (the sum over macro families, K their number; the product of the det-ratio exponential with J is NOT assembled: the det-ratio coefficients carry no beta^{-2}, the amplitude must come from the E-smallness or from J), `A <= C0 betaK^{-2}` (no landed F_{kf}), site count `|X| <= n cov a`. Route A radius sqrt N/2 exceeds 1/2, not covered by the landed Cauchy lemma.

## W804 note (14 October 2026): where the amplitude of the final term comes from
Status: from landed code and the notes FINALPHYS, FINALMAP, FINALPHYS3; the papers (P7 section 4, P4 (2.50)-(2.54)) were NOT re-read in this task, so the scaling of eta in beta is OPEN, not proved.
1. E is the difference of two Hessians of the same quadratic form: `finalOp` is the (real, constant-field) final operator, E the perturbation `E(z)` of FINALPHYS (line 15): the Hessian of the action at the physical background (inherited small-field terms, `h(z)` varying with the point of the source ball) minus `finalOp`. In `exists_det_ratio_localized` it is an arbitrary complex matrix with `WSmall rE eta E` (weighted row/column sums of `|E x y| e^{rE dist}` at most `eta`), `pdEps/4 <= rE`, and `4 e^{H kappa}(2/g) eta ballConst(3 eps/4) <= 1`.
2. Scaling. The only analytic ingredient landed is that `eta` enters the coefficients of `ellE - ell0` through the mixed defect `K_E` with row sums `B e^{H kappa}/M + e^{H kappa}(2/g) eta ballConst`; the bound `2|C|(8M+1)^d/(e^kappa-1)^|C|` of `exists_det_ratio_localized` is independent of `eta` because it only uses `eta` through the smallness condition. The source-dependence of E (E = O(g) at the field `h` of size O(g) with `g` the source of the correlation, E smooth in `h` with E(0) = 0) is the expected origin of `eta`; its beta-dependence (a factor beta_k^{-1} or beta_k^{-2} per unit of h through the second derivative of the interaction in the scaled variable) is NOT checked against P7/P4.
3. How a factor eta reaches the coefficients (PROVED, `Green/FinalAmplitude.lean`): if the perturbation is `t E` and `ellE_t` is analytic in `(t, s)` on `|t| < T` times the polydisc, vanishes at `t = 0` (then `ellE_0 = ell0`), and is bounded by `B`, then the Schwarz lemma in `t` gives `|ellE_t(s) - ell0(s)| <= B |t|/T` and Cauchy in `s` gives `||coef (ellE_t - ell0) C|| <= B (|t|/T)/(e^kappa-1)^|C|`. With `T = eta0/eta` (so `t = 1` at E itself) this is a factor `eta/eta0`.
4. Conclusion: the det-ratio coefficients carry the amplitude `eta/eta0` (small perturbation), not `beta^{-2}`; so for `finalTerm_bound` the factor `A <= C0 beta_k^{-2}` must be supplied by J (the interaction F_{kf}) or by the size of eta in g/beta; the product of the det-ratio exponential with J is the assembly still missing. Obstruction for the t-analyticity: `exists_log_det_taggedKE` gives `ellE` only as an existential for one fixed E, so joint analyticity in `(t, s)` is not available from the landed statement; it needs the log of the determinant (polynomial in `(t, s)`, nonzero on the product) built as a jointly analytic function on a simply connected domain.
