# FINALPHYS: connecting the physical last integral to the landed parametrix family
13 October 2026. PROVED = landed declaration or
elementary argument shown; OPEN = missing bridge; REFUTED = invalid inference. Sources: P7 §4 pp. 529-531;
P4 (2.23)-(2.24) p. 687, (6.4)-(6.6) pp. 719-720; P3 (2.8). Landed files read: `Balaban/Green/Final*.lean`,
`UnitLattice.lean`, `Flow/StopIndex.lean`; notes FINAL, FINALMAP, FINALCUT, FINALFAM, FINALFAM2, FINAL-COLUMNS.

## 1. The physical final operator against the reference operator

**PROVED (matrix level; P4 (2.23), (6.4)-(6.5)).** The covariance of P4 (6.4)-(6.6) at the stopping index
k = k_f > 0, at the constant saddle (phi = h, alpha = 0, |h| = 1), is
`finalHessian d (N0*L^k) (L^k) N0 (n k) a h0 = a P_h + U (1 - P_h)` (`finalHessian_eq_split`, FinalHessian.lean),
with `U = unconstrainedUnitOperator d (N0*L^k) (L^k) N0 v a` (Schur complement, scalar in spin, no next-scale
term). `finalOp d L N0 k v a` is exactly `U.map (algebraMap R C)` on `L1Torus d N0` (FinalMassGreen.lean).
The complex version is `finalHessianC` (`hessC N a (finalOp + E z) h`), analytic in `(z, h)` for `h.h != 0`,
`WSmall r eta (E z)`, `eta < finalGap` (`finalPert_hessC_inv_analytic`, `finalPert_hessC_sqrt_analytic`).

**Hypotheses of the reference operator (every landed `tagged*` bound is stated for `finalOp` itself, not a
generic `U`):** `0 < d`, `1 <= k`, `0 <= v <= 1`, `1/2 <= a <= 2`, mass window `7/8 * (L^2)^-1 < v`
(`finalMass_isCoercive`: `IsCoercive (finalOp ..) (finalGap d L)`, `finalGap = 7/(8 L^2 (8d+3))`), real symmetric
and translation invariant (constant `a`, `v` on the whole torus), locality range infinite but exponential
(`finalMass_entry_decay`, rate `finalRate d L`, torus-uniform; no finite range), spin structure only through
`P_h` (the cut acts on the scalar factor `U`; the `a P_h` term is spatially diagonal). Block structure: macro
cover `MacIdx d N0 M` with `4 pdB d L exp(pdH d kappa) <= M` and `8 kappa 7^d <= pdEps d L * M`.

**Verdict on (1).** The matrix the paper integrates at the stop equals the reference operator, with the
reference hypotheses exactly the stopped-flow bounds (`a` in [1/2,2], `v <= 1`, mass at the stop:
`kStop_spec`, `finalMass_at_stop`), so the reference hypotheses are satisfied PROVIDED the physical density's
quadratic coefficient is that matrix. That identification is **OPEN** (FINALMAP leaf P1, `FINAL-HESSIAN-BRIDGE`):
no landed theorem defines the physical stopped density or extracts its Taylor coefficient. Three gaps
independent of P1: (a) off the constant saddle the Hessian is `finalOp + E(z)` with variable `h(z)` and
inherited interaction `E, M`; `E` is not translation invariant, so the row/column/analytic bounds (stated for
`finalOp`) do not apply verbatim (**OPEN**, leaf L1); (b) `k_f = 0` is outside the reference (`finalOp` needs
`1 <= k`; `KF0Reference.lean` covers that branch with a different family, author item 17); (c) in the nonempty
large-field region the operator is a different Schur complement (P7 (4.11)-(4.14), FINALMAP leaf P5), which the
reference family does not cover. **REFUTED:** the zero region alone gives Root-F (FINAL.md section 4).

## 2. Lean leaves, dependency order (each <= 300 lines; no new definitions unless stated)

Landed base: `taggedGfin_final` (`pdB d L * exp(pdH d kappa)/M <= 1/4`, `IsUnit (1 - taggedK ..)` on the
polydisc `||s p|| <= exp kappa`), `taggedG_column_sum`, `taggedGfin_column_bound_same_rate`,
`taggedCfin_analyticOnNhd` (on `||s p|| < exp kappa`), `taggedCfin_row_bound`, `taggedCfin_column_bound_same_rate`,
`localityAE_macBox_of_agree`, `abstract_expansion_taggedCfin_final` (value `sqrtMat (finalOp ..)` at `s = 1`,
bound `B/(e^kappa-1)^|C|`, `kappa >= 1`), `taggedCfinU_congr_of_agree_on_region`, `coef_taggedCfinU_congr`.
**L1. Generic-matrix interface (OPEN, start now, Sonnet, ~250 lines).** Generalize `taggedK_row_sum`,
`taggedG_column_sum`, `taggedCfin_row_bound` from `finalOp` to `U` with `hU : IsCoercive U g`,
`hUdec : forall x y, ||U x y|| <= A exp(-r dist x y)` (instances: `finalOp`; `finalOp + E` with
`WSmall r eta E`, `eta < g`, from `finalPert_resolvent_decay`). Landed statements become corollaries (rule: no
copied proofs). Needed only if the physical Gaussian absorbs `E(z)`; if `E` is left in the interaction (FINALMAP
P4), L1 is skipped and the cut family is `taggedCfin` as landed.
**L2. Cut family and radius for the final operator (PROVED for the E-free case; no leaf).** The cut family is
`s |-> taggedCfin d L N0 k M v a s` (Stieltjes parametrix of `U`); analytic on the polydisc of radius `exp kappa`
(`taggedCfin_analyticOnNhd`), bounded by `B_C` (`abstract_expansion_taggedCfin_final`), `s = 1` is `sqrtMat`.
Numerical radius: `M >= max(4 pdB exp(pdH kappa), 8 kappa 7^d/pdEps)`, `kappa >= 1`, depending only on `d, L`.
Remaining for the physical cut family (statement-level, ~120 lines, Sonnet, start now):
`taggedCfin_sq_mul_final : taggedCfin s * taggedCfin s * finalOp = 1 + R s` with `||R s||_{wt} <= q < 1` on the
polydisc, i.e. `taggedCfin s` is invertible there with weighted inverse bound (needed by L3; uses
`weightedRow_inv_le`, `taggedK_row_sum`). Whether `R s` is small for large `|s|` is **OPEN** (risk: only
`||K|| <= 1/4` is proved for the resolvent, not for the integrated square root).
**L3. Localized determinant (OPEN, strong, ~280 lines, start after L2).** Statement:
`exists ell : (MacIdx d N0 M -> C) -> C, AnalyticOnNhd C ell (polydisc 0 (fun _ => exp kappa)) /\
 (forall s in polydisc, det (taggedCfin s) = exp (ell s)) /\ ell 1 = -(1/2) * log det (finalOp ..) /\
 (forall u C, ||coef ell C|| <= B_D/(exp kappa-1)^|C|) /\ locality (as `LocalityAE` via
`localityAE_macBox_of_agree`)`. Route: `ell(s) = integral over t of tr[...]`, or `log det (1 - K(s,t))` summed as
`-sum_n tr K^n/n` (K has norm <= 1/4 and tags give support); tools: `analyticOnNhd_logMat_fam`, `taggedK_entry_le_sum`,
`tagMon_zero_of_not_subset`. FINALCUT `finalCutDetLog` is the same target.
**L4. Localized Gaussian integral, activity per polymer (OPEN, strong, 2 x ~290 lines; after L2, L3, FINALMAP G3).**
(i) `gaussian_change_cut : integral (F (taggedCfin s *v phi)) dgauss * det (taggedCfin s) = Z_s[F]` generalizing
`lintegral_good_gaussian_change` to a non-square-root matrix `C(s)` with `C(1) K C(1) = 1`. (ii) the coefficient
map `s |-> ` integral of the zero-region interaction (class terms, `E, M`) against it is analytic and local:
for `C` connected, `coef (F u) C` depends only on `u|region(C)` (`coef_taggedCfinU_congr`) and
`||coef|| <= B_J exp(-kappa |X|/(M L^J)^d)` via `abstract_expansion_on`. Inputs from the physical side: the
interaction's read-set (FINALMAP P4); `isLocExp_of_coeffFamily_renTheta_tower` for the datum dependence.
**L5. Bound of the activities (OPEN, strong, ~250 lines; after L4).** `4 sqrt N B_J <= c9 L^{-J((d-2)/2+delta)}`
and the derivative in the source (Cauchy on the open unit ball), to feed `logPartition_multiscale` (zero-region
part only). Constants: `B_C` above and the L3 `B_D`.
**L6. Connected supports (OPEN, strong, ~200 lines, start now, independent).** `isConnectedFamily_macBox` in
FinalLocalityAE declares every family connected, so the coefficient sum proves no geometric connectedness. Leaf:
`coef (F u) C = 0` unless the region of `C` is connected in the macroblock adjacency, from
`tagMon_zero_of_not_subset` and path tags `macTags z x y` (tags of a nonzero word form a connected chain of
boxes); gives the polymer-support statement P7 (4.9) needs.
**L7. Two-torus equality (OPEN, strong, 2 x ~290 lines; after L4).** For nonwinding supports `X` (diameter below
half the torus), `p_X` computed on tori `N0` and `N0'` agrees: `taggedCfin` entries on the lifted pair
`(x, y)` agree up to the winding term. Needs: torus lift of `finalOp` entries (`finalMass_entry_decay` is
torus-uniform; exact equality of finite-range truncations: templates `genKernelTrunc_eq_zero`, `kf0CR_torus_eq`),
then the same for `macBoxF`, `boxG`, tags, and Stieltjes integral. FINALCUT `finalCutTorusGrades`.
**L8. Physical joins (OPEN, wait; not generator-neutral).** P1 (Hessian bridge: `finalHessian` = quadratic
coefficient of the stopped density), P2 (cutoff coverage; algebra in FinalCutoff: `p4_cutoff_xi`, `p4_cutoff_reg`),
P3 (complex chart: `E, h` holomorphic, `WSmall r eta (E z)`, `eta < finalGap`), P5 (nonempty large-field
region). These need the LF characteristic / flow lane; FINALMAP lists the exact statements.

## 3. Start now versus author answer (item 18)
**Start now (generator-neutral, no author answer):** L1 (if E is absorbed), the invertibility statement in L2,
L6, the `gaussian_change_cut` part (i) of L4, L3 after L2. Also FINALMAP G1-G3, S1-S3.
**Need the author's answer to item 18** (is the cut family P3 (2.8) or the macroblock parametrix, and is it applied to
the Schur complement `U` or a sparser operator): the choice of cover `macCore/macBox/macChi/macPath/macTags`
fixes the constants `pdB, pdH, pdEps, M` and the read-set in L4(ii), L6, L7. If the answer is "P3 (2.8) with a
different cover", keep `boxH/boxG`, tagged algebra, weighted Neumann, Stieltjes integration, `coef_congr`, and
redo the cover geometry (FINALFAM2). L8 additionally waits for the LF lane and author item 17 (`k_f = 0`).
**Confidence.** High on section 1 matrix claims and the landed-family summary; medium on L2 invertibility and L3
(the integrated square root need not stay close to `U^{-1/2}` away from `s = 1`).

**W753 status (L6 done).** `Balaban/Green/FinalConnectedSupport.lean`: `coef_taggedGfin_final_eq_zero_of_separated`
(and `_of_not_connected`), `coef_taggedCfin_final_eq_zero_of_separated`: the coefficient at `C` vanishes when
`C = A ⊔ (C \ A)`, both nonempty, `macRegion A` disjoint from `macRegion (C \ A)` (adjacency = boxes meet).
Key facts: a nonzero entry of `χ_z G_z` or `R_z` has `y ∈ B_z` (so tags are connected via the end cell,
`macTags_subset_or`; x need not lie in `B_z`), then `G_fin(s) = G_fin(s|_A) + G_fin(s|_B)` (`taggedGfin_split_of_separated`)
and `coef_eq_zero_of_split`. Not done: the converse (nonvanishing) and a graph-connectedness phrasing of `C`.

**W757 status (L2 remainder; `Balaban/Green/FinalCfinInverse.lean`).** REFUTED on polydiscs centred at 0: every tag set `macTags z x y` is nonempty, so `taggedCfin 0 = 0`, `R 0 = -1` (`taggedCfin_sq_mul_final_zero`), `taggedCfin 0` is not invertible, and no bound `||R s|| <= q < 1` holds on any polydisc `{||s p|| <= rho}`, `rho >= 0` (hence also no analytic `log det` of the cut family on a polydisc around 0: L3 needs another parametrization).
PROVED (nearest true): `||R s||_wt <= B` on `||s p|| <= e^kappa` with `B = B_C^2 A_U + 1` independent of `M` (`taggedCfin_sq_mul_final_weighted_bound`); `R` analytic, `R 1 = 0`; Schwarz on lines through `1` gives `||R s||_wt <= B delta/(e^kappa - 1)` for `||s p - 1|| <= delta < e^kappa - 1` (`taggedCfin_sq_mul_final_near_one`); for `B delta <= (e^kappa-1)/2`, `taggedCfin s` is invertible with weighted inverse bound `2 B_C A_U` (`taggedCfin_isUnit_near_one`).
Largest radius: polydisc centred at 1 of radius `delta = (e^kappa-1)/(2B)`, any `M` allowed by the landed hypotheses; it exceeds the unit-distance neighbourhood only through `kappa`. Open: smallness of `R` at generic `|s p| = 1` (tags are phases that do not cancel; no proof either way).
