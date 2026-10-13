# UNITH: arbitrary unit external field h in Root-F (W744, reading task, 2026-10-13)

Question (LEDGER NOTE 2026-10-13): Z_h(g) = Z_{e0}(Q^T g), T^h(x,X;g) = Q T^{e0}(x,X;Q^T g)
(`RotateUnit.lean`: `orthogonal_to_unitVec`, `rot_cmat_xiCData`), but Q^T can enlarge the entrywise
l1 norm sum_y sum_i |g y i| by up to sqrt N. Can the e0 chain run at a larger source radius R?

## Verdict: route A, R = sqrt N (with the rho-lane already landed). No Lean change in the step.

Radius arithmetic (per site, Q real orthogonal, g y in C^N): ||Q^T g y||_1 <= sqrt N ||Q^T g y||_2
= sqrt N ||g y||_2 <= sqrt N ||g y||_1. Summing: sum||g||_1 < 1 gives sum||Q^T g||_1 < sqrt N, and
sum||g||_1 <= 1/2 gives sum||Q^T g||_1 <= sqrt N / 2. So the e0 chain is needed with
analyticity and the identity on {sum||g||_1 < R}, R = sqrt N, and the bound on {sum||g||_1 <= R/2}.
R depends only on N (fixed before kappa, c9, L, M, beta0 in Root-F), so beta0 may depend on R.
R = sqrt N is sharp for the chain: Q^T maps the l1 unit ball into the l1 ball of radius sqrt N, and
no smaller ball works unless Q is a signed permutation.

## Why R is a free parameter (why the unit ball is a normalization)
The step never evaluates the class at the physical source g. It evaluates it at the scaled slice
g/beta: `sourceSlice_mem_restricted_rho` (`Fluctuation/SourceRadius.lean`): sum|g| < q <= rho and
max 1 rho <= beta give g/beta in `l1BallEta (q/beta)` (subset of the unit ball `l1Ball`). The unit
balls `l1Ball`, `Def6.l1 g < 1` (this one is the per-site l2 sum, sum_x vn(g x), `Def6.lean:159`)
are therefore on the scaled variable and stay at 1. Each scale j is a separate zero-class step at
its birth scale (`rootTermFamily_obs_birthScale_fromTowerG`), so no composition of classes
re-imposes radius 1 at the next scale. The threshold becomes daThreshold((C_E + rho C_F)/4):
`sourceAmp_doubled_hDA_rho(_general)` (`Inhabited/SourceAmpRadius.lean`).

## Inventory: where radius 1 (or q <= 1) appears
(a) parameter, any rho, constants depend on rho (rho-version LANDED, rho = 1 is the landed one):
 `l1BallRho`, `physSΛRho`, `physVRho`, `physVqRho`, `physFibreRho` (+ mono, open, star-shaped:
 `SourceRadiusCarriers.lean`); `sourceSlice_mem_restricted_rho`; `physInclScaled_image_subset_rho`,
 `sourceFamilyRelative_scale(_fromTower(G))_rho`; `sourceDirectTerms_scale_rho`,
 `stepActivityBound_zeroClass_source_scaled_rho` (`SourceDirectTermsScale.lean`, needs q/beta <= 1);
 `sourceDirectTerms_scale_fromTower(G)_ray(_full)_rho`; `stepActivityBound_zeroClass_source_scale_cutoff_rho`,
 `sourceActivityC_scale_fromTower(G)_rho`; `sourceExponentFamily_fromTower(G)_rho`;
 `sourceWitness_*_rho`, `commonWitness_joint_fromTower(G)_rho(_full)`; `activityFamilyAnalytic_fromTower(G)_rho`;
 `zeroSourceActivity_common_*_rho`; `wone_chartIdentity_fromTower(G)_rho`, `W1_eq_physVal_rho`,
 `W2_eq_physVal_sub_rho`; `thm31b_*_rho(G)` (`Thm31bFromTower`, `Thm31bKernelSupport`,
 `Thm31SiteDomains`, `ObsUnconditional`); `obsMarks_*_ksupp_rho(G)`, `obsRayEps_bound_fromTower(G)_rho`,
 `obsRay_hray_fromTower(G)_rho`; `nonvanishing_zeroClass_fromTower_freeDatum_rho` (Z(g) != 0 for the log).
(a-open) parameter, rho-version NOT yet landed (all state q <= 1 and `physVq`, ~12 files, theorem
 bodies carry the proof, binder q <= 1 is used only as q <= rho and q/beta <= 1, beta >= max 1 rho):
 `ObsCoeffAnalytic` (1365 lines, 20 thm; `obsEv_fromTower(G)`, `obsFamilies_of_Ev(G)`,
 `obsCoeffParam_analytic_of_Ev(G)`, `obsCoeffParam_norm_le_of_Ev(G)`, `obsCoeffParam_fromTower(G)`),
 `ObsCoeffFamily`, `ObsCoeffLocal`, `ObsCoeffExactSites` (physVq in locality/exactness clauses),
 `ObsTiltFamily`, `ObsTiltLabels` (amplitude eps_H with q C_F), `ObsFamilyJoint` (1623; `obsFamily_full_fromTower(G)`
 and its joint/coeff/fibre corollaries), `ObsFamilyPrefactor`, `StepIdentityFibreObs`,
 `PhysicalZeroJoin`, `OffFibreM0Activity` (line 87: g<q<=1 gives l1Ball; becomes l1BallRho),
 `RenormM0SiteRecord`, `RenormPhysicalRecord` (q <= 1 only as hypotheses, 12), `StepPiecesJoint/RenSol/RenSolG`,
 and the top: `RootTermZeroClass` (`rootTermFamily_obs_core`, `_fromTower(G)`, `_prefactor_`, `_birthScale_`:
 analytic on {sum||g|| < 1}, bound on {<= 1/2}, identity on {< 1}, `hval`).
(b) structural at 1, correct as is (scaled variable): `l1Ball` (`InteractionFPart.lean:128`),
 `l1BallEta`, `Def6.l1 g < 1` in `ClassRegularObsC`, `GeneralClassRegularC`, `GeneralObsMarks`, `Def6v2`,
 `ClassOldTermInputM`, `ClassOldTermSiteSums:216` (l1Ball -> Def6.l1 < 1), `StepRegDomain`, `Prop33`
 (`prop33EpsEta` with eta = q/beta <= 1), `Def7Variants` limM/limR.
(c) normalization the root could rescale: the root-level statements in `RootTermZeroClass` (domain 1,
 half ball 1/2) and the q <= 1 binders listed under (a-open). Rescaling the root is equivalent to R.

## Part 2: rotation-invariant reduction (route C)
Qt acts blockwise: (Qt g)(y) = Qt (g y), and the pairing sum_i g y i T_i(g) = sum_i (Qt g)(y)_i T^{e0}_i(Qt g). Locality, support, polymer shape pass unchanged. Per-site l2 norms are preserved; the class domain
Def6.l1 (per-site l2 sum) is rotation invariant already. But the chain's bounds use the entrywise l1
norm of g as the norm of the source in the Cauchy/amplitude estimates (q C_F, `l1Ball*`, physVq open
sets, `prop33EpsEta`), and a per-site-l2 chain needs a new carrier (`l1Ball` replaced by an l2-sum
ball): a changed landed definition, all (a) and (a-open) restated, constants change by sqrt N anyway.
Route C is therefore route A with worse bookkeeping. It is used only for the radius computation above.

## Part 3: routes
- A (chosen): sqrt N along the chain. Work = the (a-open) list: generalise in place, landed theorem
 = corollary at rho = 1 (`physVqRho_one`, `l1BallRho_one` are rfl). Replace `physVq S .. q` by
 `physVqRho S .. rho q`, `q <= 1` by `q <= rho` and beta0 by a bound depending on rho; thresholds via
 `sourceAmp_doubled_hDA_rho`. Estimate 2500-3500 lines changed/new over ~13 files (about 4 workers,
 largest `ObsFamilyJoint`, `ObsCoeffAnalytic`, `ObsTiltLabels`, `PhysicalZeroJoin`, `RenormPhysicalRecord`,
 `RootTermZeroClass`), no new definitions. Plus the rotation file: ~150 lines
 (Z_h(g) = Z_e0(Qt g), T^h = Q T^e0(Qt .), the l1 estimate above, torus independence and locality transfer).
- B (step at a constant h): `unitVec` occurs 358 times in 56 files (unitBg witnesses, `StepActivity*Witness*`,
 `DetOutputTermsWitnessG`, `hh₀ : S.h₀ = unitVec`); `StepSetting` already has `h₀`, `rot_cmat_xiCData` gives the
 chart, but covariance only moves the problem to (D.rot Q, g) = Q (D, Qt g): the e0 terms are still evaluated at
 Qt g, so the radius issue is NOT removed. Strictly more work (est. 4000-6000 lines) for no gain. Rejected.
- C: see Part 2. Rejected.
Risk for A: `OffFibreM0Activity`, `ObsTiltLabels` use g < q <= 1 to land in `l1Ball`; they must go through
`sourceSlice_mem_restricted_rho` (landed) instead. No obstruction found. Z-side nonvanishing at radius R: landed (rho).
