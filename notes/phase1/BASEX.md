# BASEX: the x-dependent resolvent of the first step (leaf G1), design note (W823)

Reading task, no Lean edits. Claims: PROVED = landed declaration, OPEN, REFUTED. Files under `Balaban/`.

## 1. What the step's x-variant proofs use of the symbols (read from proof bodies)
`xS1 A x = A x/(A+x)`, `xS2 A b x = A (x+b)/(A+x+b)` (`Multiscale/XVariant.lean:53,56`) enter the operator only through
`xAvgMatrix G a s1 s2`; every landed statement is written with `xS1 (a k) x`, `xS2 (a k) (aT/L^2) x` spelled out (about 70 occurrences, 18 files).
- PROVED, used by coercivity (`xSymbols_cases`, `xCore_real_of_ak`, `top_ineq`): P1 `0 <= s1`; P2 `0 <= s2 - s1`; P3 `s2 - s1 >= 1/(4L^2)` or `s1 >= 1/18` (from `1/2 <= A`, `aT in [1/2,2]`, `L >= 3`). Only `mass : 0 <= nu` is used of the mass, no upper bound.
- PROVED, used by the Agmon commutator (`xAvg_diff_ge_of_ak` line 274, `XCommutator.lean:521`): P4 `s2 <= 2` (via `xS2_le`, `A <= 2`). The error of the top layer is `B s2 L^(-2k) ||v||^2`.
- Used elsewhere: P5 continuity of `x -> s1, s2` on `[0,inf)` (`DecoupledCovCont`); P6 limits `s1, s2 -> A` as `x -> inf` (`DecoupledLimit`: `H0`, `M0`, only for the covariance `decCov`); P7 the series identity `A x/(A+x)` behind `coeff_xS1/2`, `covT_mul_covA` (only for `decCov`, `decCovSqrt`).
- For `s1 = x`, `s2 = x + b` (`b = aT/L^2`): P1, P2, P3 (first alternative: `s2 - s1 = b >= 1/(2L^2)`), P5 hold; P4 FAILS for `x > 2 - b`; P6, P7 are meaningless (no limit, no series).
- Not used by the Gsx chain (`Decoupled2X*`, `DecoupledX*`): `massLe` (`nu L^(2K) <= 1`). Checked by grep: `.massLe` occurs only in the non-x files (`DecoupledCube`, `DecoupledCubeHolder`, `CubeBlockBoundsMixed`, `Decoupled2Close`, `DecoupledClose`, `DecoupledFieldClose`, I5*), none in `Decoupled2X*`, `DecoupledX*`, `XVariant*`, `Decoupled2One/Field`, `DecoupledCov*`.

## 2. Is the first step's `(A_e + x)^-1` the a_0 -> inf limit?
- `A_e + x = Q_e((H+x) (x) I)Q_e + (1+x)P_e`, and `H + x` is `H` with `nu` replaced by `nu + x`: `latticeLaplacian d l nu = (2d + nu) 1 - shifts` (`Lattice/Laplacian.lean:35`). So the shift is a MASS shift, not an `alpha` shift.
- Matrix level at `k = 0` (one layer, `Omega_1 = layer 1`, `Icc 1 0 = {}`, `L^0 = 1`): `xAvgMatrix = s1 * (layer-1 identity) + (s2 - s1) * layerBlockMatrix G 1 1`. The first-step `avgMatrix` is `(a_1/L^2) * layerProjMatrix G 1`, same matrix as `layerBlockMatrix G 1 1`. Hence `cutOperator G a nu' cut alpha` is `cutXOperator` with `(s1, s2) = (0, a_1/L^2)`, `nu' = nu`; and `H + x` has `(s1, s2) = (x, x + a_1/L^2)` or, equivalently, `(0, a_1/L^2)` with `nu' = nu + x`. OPEN as a Lean statement (leaf L1), identity by inspection.
- a_0 -> inf: `xS1 A x -> x`, `xS2 A b x -> x + b`. So the answer to (2) is YES as matrices in the limit (`s1 = x` is a mass on `Omega_1`, equal to `nu -> nu + x`), but REFUTED as a route: the landed estimates need `A <= 2` (`XCover.hak2`, P4), so no limit can be taken from them. a_0 -> 0: `s1, s2 -> 0` for every x, the x dependence disappears; not the object.
- W822's `a_0 = 1` instance: `s1 = x/(1+x) < 1`, a different operator (REFUTED as the first step, as the orchestrator note says).

## 3. Routes
- (a) abstract symbols `(s1, s2)` with P1-P4: REFUTED as cheap. P4 fails for `s1 = x`; at `k = 0` the `s1` term is a multiplication operator, its conjugation error and its commutator vanish exactly, so a `k = 0` lemma with `s2 - s1 <= 2` would work, but every statement of the 18 files above changes signature (about 2 to 3k lines of churn, not 300-line leaves). The covariance layer (`decCov`, P6, P7) does not apply to `s1 = x` and is not what G1 needs (decCov at `s = 1` is `(x + calA)^-1` with `calA` built from `a_k`, not `(A_e + x)^-1`).
- (b) alpha shift `alpha + x` plus a large-x argument: REFUTED. `AdmPot` is `|alpha| <= c/(2 l^2)` (`Decoupled.lean:150`), `l = L` on layer 1, so only `x <= c/(2L^2)` is covered. A Neumann series for large `x` needs `x > ||H(s)||`, of size `4d + nu + O(1)` times `(1 + |s|)`; it survives complex `s` (norm argument, no coercivity), but the middle range `x` in `[c/(2L^2), 4d]` stays uncovered. Also the non-x sup bounds (`baseParametrix_supBounds`) use `massLe`, false for large mass.
- (c) RECOMMENDED: mass shift through the `x' = 0` member of the landed x-variant. At `k = 0`, `x' = 0`: `s1 = xS1 A 0 = 0`, `s2 - s1 = A b'/(A + b')`, `b' = aT/L^2`. With `A = a_0 = 2` and `aT = 2 a_1 L^2/(2L^2 - a_1)` (in `(1, 1.06]` for `a_1 = 1`, inside `[1/2,2]`) this equals `a_1/L^2` exactly. Then `xDirichletOperator G a aT 0 nu' alpha = dirichletOperator G a_1 nu' alpha` for every `nu' >= 0`, and the physical x enters as `nu' = nu + x`. The L^2 chain (`Decoupled2X*`: `dg1x`, `Gsx` analytic/bounded/close/local, `Gsx_one`, `decM_isUnit_cover`) has constants independent of `nu` (`cstarX`, `xAgmonRate`, `commXConst` depend on `d, L, Cx` only) and handles complex `s` (`|s_P| <= e^kappa`) through the cube cover, which is what W770 found missing for coercivity alone.

## 4. Leaves of (c), dependency order (each <= 300 lines, no new definitions)
- L1 (about 120): `cutXOperator_zero_eq_cutOperator`, `xDirichletOperator_zero_eq_dirichletOperator` at `k = 0`, `A = 2`, `aT` as above, any `nu' >= 0`, any cut. Uses `xS1_zero`, `xS2` at `0`, `layerBlockMatrix G 1 1 = layerProjMatrix G 1`.
- L2 (about 250, EDITS landed files, W818-style statement change, needs the orchestrator): move `massLe` from `Dec2.OpSetting` (`Decoupled2.lean:120`) to `Dec2.CoverBase`; add it at the `CoverBase` constructors (`Decoupled2Self:121`, `Decoupled2Solve:35`, `DecoupledSolve:176`, P6Pair*, `LocalizationSettings`); `XCover` then holds for `nu' L^2 > 1`. Consumers `S.massLe` at `CoverBase` level are unchanged.
- L3 (about 150): `base_xCover_massShift_exists`: `Dec2.XCover (coverOf G) G a aT nu' (Cchi d L)` at `k = 0` for all `nu' >= 0` (generalizes `base_xCover_exists`, `BaseXCover.lean:26`, which has `a_0 = 1`, `aT = 1`, `nu' L^2 <= 1`).
- L4 (about 150): algebra `baseOp N e H + x = baseOp-form with (H + x, (1+x) P_e)` and the constrained inverse `(A_e + x)^-1 = (1+x)^-1 P_e + G_x - G_x e M_x^-1 N_x` with `G_x = (H + x)^-1`; generalizes `baseOp_mul_constrainedCov` (`BaseConstrainedCov.lean:367`, `ring_aux`).
- L5 (about 300): `baseConstrainedCovX` entries analytic on `DecDom`, bounded, equal to `baseResolvent` at `s = 1`, from `Gsx` (`Decoupled2XAnalytic`, `Gsx_one`, `decM_isUnit_cover` at `x' = 0`, `nu' = nu + x`), uniform in `x >= 0`.
- OPEN after L5 (not in this route's scope): weighted comparison and exact core agreement (`Decoupled2XClose`, `Decoupled2XLocal` applied at `x' = 0`, about 200 lines each), square root and logarithm of `A_e + x` (Stieltjes from the decay `resolvent_block_decay`, `sqrtMat_block_decay`; the step's `decCovSqrt` does NOT transfer, see 3(a)), torus lift.

## 5. Risks
- L2 is the only edit to landed statements; if refused, no route avoids it (the non-x chain needs `nu' L^2 <= 1`).
- Not checked in Lean: that no lemma outside the grep (a library lemma called with `S.toOpSetting`) uses `massLe` indirectly; L2/L3 settle it by compilation.

## W824 status
- L1 PROVED (`Base/BaseMassShift.lean`): x-variant at x = 0, k = 0, a0 = 2, aT = 2 a1 L^2/(2 L^2 - a1) equals the first-step (cut) Dirichlet operator, any mass nu, hypotheses 2 <= L, 0 <= a1 <= 2.
- L2 NOT DONE: moving `massLe` out of `OpSetting` breaks standalone-`OpSetting` consumers that need it (`dirichlet_weighted` Decoupled2Close:64, `cubeBlockBounds_mixed` CubeBlockBoundsMixed:98,153, CubeActionBound, CubeActionRealBound, InteractionLevelPair, MassResponseHyp, MassChangeRegion, ...): their statements would need an extra hypothesis. The x chain (Decoupled2X*, DecoupledX*) uses none of them.
- L3 PARTIAL: `base_xCover_massShift_exists_of_massLe` (XCover at k = 0 with a0 = 2, a1 = 1, L1's aT) under nu L^2 <= 1; the hypothesis drops once L2 is done.

## W832 status
- L4 PROVED (`BaseConstrainedCov.lean`): `baseOp_add_smul_one`, `shiftedOp_mul_constrainedCov`, `baseOp_shift_mul_constrainedCov` ((A_e + x)^-1 = (1+x)^-1 P_e + G - G e M^-1 N, G = (H + x)^-1); `baseOp_mul_constrainedCov` is now its x = 0 application (statement unchanged).
- L5 PROVED (`Base/BaseXCov.lean`): `baseCovX_one` (covariance at s = 1 is `baseResolvent`), `baseCovX_analytic` (entries analytic on `DecDom`), `baseCovX_bound` and `baseResolvent_entry_bound` (entry bound B(d, L, kappa), independent of x, nu, a, aT, G).
- No obstruction: the Gsx chain constants (`valConstX`, `kConstX`, `smallConstX`, `cstarX`) do not involve the mass or x'; the regime `cstarX e^(N0 kappa) <= L^m1` and `delta^2 smallConstX <= 1/4` is independent of x.

## W835 status
- Square root PROVED (`Base/BaseXSqrt.lean`): x-decay `‖C_x(s) entry‖ ≤ B/(1+x)` (`baseCovX_decay`, B(d,L,kappa), uniform in x, nu, s on the discs `|s_P| ≤ e^kappa`; proof: cube operators at mass nu+x are `(L^-2/8 + x)`-coercive by the mass shift `cutXOperator_add_mass`, then `Gstarx_sqNorm_le`, `Gsx_sqNorm_le`, `decPi_sqNorm_le`).
- `baseCovX_sqrt`: on `DecDom` the integrand `x^{-1/2} C_x(e)` is dominated by `B x^{-1/2}(1+x)^{-1}`, integrable, and every entry of `pi^-1 ∫ x^{-1/2} C_x(e) dx` is analytic on `DecDom` and bounded by B.
- `baseCovX_sqrt_one`: at `s = 1` the integral is `sqrtMat A_e` (principal inverse square root of `A_e = baseOp`), its square is `baseResolvent .. 0 = A_e^{-1}`; `A_e + x` is a unit for all `x >= 0`. For `s != 1` the integral is the analytic continuation off s = 1, not an inverse square root of a defined operator.
- Open: weighted comparison/exact core agreement of the sqrt family, logarithm of `A_e + x`, torus lift (unchanged from "OPEN after L5").
