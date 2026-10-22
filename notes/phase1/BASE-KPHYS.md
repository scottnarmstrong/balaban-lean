# BASE-KPHYS: row (b), the physical base kernel `K̃^w e^{b₀}` of the first step (design, C1, Q24)

Sources: LFR Def. II.7.6, (II.7.4), Lemma II.7.7, II.7.8 (`LF-RECONSTRUCTION.md` l. 4317-4378); P5 (2.47), P6 (3.2), p. 14.
Carrier: `BaseSmallFieldInput` (`LargeField/Base/BaseSmallField.lean`); product form `BaseProductData` (`Base/BaseCarrierProduct.lean`).

## 0. What the carrier already has, and what a population must supply
`BaseProductData.toInput` turns `Kt` (real, `>= 0`, one per witness `w`) and `b` (one exponent, all `w`) into every field of
`BaseSmallFieldInput` (`Kphys = Kt * exp b`), with `Kphys_cross` (D4) and `baseKC_toInput` proved. So row (b) is the definition
of `Kt a w o x hv` and `b a g o x hv` plus the remaining fields of `BaseProductData` (meas, outside, dom, rot, euclid_Kt, b_meas,
b_outside, b_analytic, b_zero_real, b_real, b_supp, b_suppV, b_rot, b_euclid, b_bound, Kt_nonneg).

## 1. (i) Definition of `K̃^w` and `b₀`
The first density: `baseRho1_eq_sum_firstP` (P-sum, weights `W P = prod_{c in P}(1-chi') prod_{c notin P} chi'`),
`baseRho1_eq_sum_firstP_Q` (adds Q), `baseRho1_eq_sum_firstP_conditional_recordInterior` (retained spins `ret = blocks not in Z' or
not in br.Omega` as sphere variables, interior integrated: `baseRetained_disintegrate`), `baseChartIntegral_retained` (the interior
as a chart Gaussian integral, `R = pdSqrtInv K_U`, `det R`), the all-good term `baseAllGood_endToEnd` (`P = empty`), the cutoff
transfer `bond_transfer/block_transfer/val_transfer` (`BaseBgClose`), `sector_bond_margin`. Landed splitting of `chi'`:
`chiPrimeZero = chiBlockA * chiBondB` (A = block, B = bond+site), `baseA`, `baseF` (`BaseWitness`), `basePCubes`, `baseOCubes`, `BaseW`.
* `Kt^w` (large-field factor, source-free, real): the integrand of `baseChartIntegral_retained` at `g = 0`, h-dependence kept, WITHOUT the
  factors `A(c)` (they are `baseF`), i.e. per cube of `P`: `w c = true` (blk): `1 - A` is in `baseF`, nothing else in `Kt`; `w c = false`: `A` in `baseF`, `1 - B(c)` in `Kt`; cubes of `baseOCubes`: `A` in `baseF`, `B(c)` in `Kt`;
  times `baseKernel` (the Gibbs weight with `g = 0`: `exp(-A_1(Z'; psi))` on `Omega^c`), the chart Jacobian `chartJac`, the cube product
  `baseSectorCubeProduct`, the Gaussian normalization (`gaussCut`), `chiNew`. It is `>= 0` by `baseKernel_nonneg`, `charFn_nonneg'`, `chartJac` > 0.
* `b₀(g)`: (1) the vacuum/normalization constants (`log` of the Gaussian normalizations, `BaseChartGaussianNormalization`, `baseGaussCutMass`);
  (2) the renormalization term `beta_1 C^(1)` on layer 0 (`baseMainAction`); (3) the corrections of the background change, domains in `Z'`
  (`BaseBgClose`, `BaseXLog*`); (4) the small-field terms with domains in `Z'` (P6 p. 14): the output of the general step at `k=0`
  (`BaseFirstChart`, `KF0*`), NOT yet a Lean object; (5) the source `<g|_{Z'}, phi>` on the sites of `Omega^c cap Z'`, `|phi_x| = 1`.
Only (5) and the factor `chiNew` are fully determined by landed objects; (1)-(3) are definable now (sizes below); (4) is the content of
Proposition II.7.9 / `LF-BASE-KF0` (blocker 2 side), so `b₀` is defined as `b₀ = bTrivial + bSmall` where `bSmall` is a PARAMETER of the
population (a function with its own typing clauses), exactly as `Kphys` was a carrier parameter.

## 2. (ii) Field by field (size = lines of new Lean)
| clause | status | by / missing |
|---|---|---|
| `Kt_nonneg`, `Kt_meas`, `Kt_outside`, `Kt_rot` | provable once `Kt` is defined | factors measurable/`O(N)`-invariant: `measurable_chartMapPi`, `baseKernel_*`, `rotOut`; ~250 |
| `Kt_dom` (zero off `chiNew`) | by definition (`chiNew` is a factor) | ~40 |
| `euclid_Kt` (S4/S5 covariance) | needs the torus symmetry on the cubes and the chart (equivariance of `baseSectorCenter`) | ~400, open |
| `b_meas`, `b_outside`, `b_rot`, `b_euclid`, `b_suppV`, `b_supp` | follow from the shape of each summand (source only through `g` on `Z'`) | ~200 |
| `b_analytic` | entire in `g` for (5); for (4) from `thm31g_*`/S4 pattern (`IsLocExp`) | (5): 40; (4): wait |
| `b_zero_real`, `b_real` | real arguments give real terms; (4) needs reality of the small-field terms | (5): 30 |
| `b_bound` | see (iv) | |
| (S2) = Lemma II.7.8 | gains P landed (`baseMainAction_bond_gain`, `_site_gain`, `baseBlock_gain`), Q/R/S in `BaseWitnessGain*`; assembling `sum_w m^w int S^w <= e^{-kappa0}` needs the volume factors, `Kt` majorants, and `bSmall` bound | ~700, after `Kt` |

## 3. (iii) The D4 cross-witness identity
`Kphys_cross` is proved in product form for ANY `Kt`, `b` (`BaseProductData.toInput`): `Kt^w e^{b(g)} Kt^{w'} e^{b(0)} = Kt^{w'} e^{b(g)} Kt^w e^{b(0)}`.
So (iii) costs nothing once `b` does not depend on `w`: the work is to define `b` independent of `w`. This holds because the witness only
selects the source-free indicators: `A`, `1-B` (above), and `bSmall` is defined from the cube sum before the witness split.

## 4. (iv) `Kphys_bound`
`|Kphys(g)| <= Kphys(0).re * exp(||g|_{Z'}||_1)` iff `Re(b(g) - b(0)) <= ||g|_{Z'}||_1` (`BaseProductData.b_bound`). Part (5) satisfies it
exactly (`|e^{<g,phi>}| <= e^{||g||_1}` pointwise, unit spins; this includes sites of `Omega \ Omega''` where phi is the chart image of
`psi'_0`). Part (4) carries source dependence through the observable terms `M̃` of the small-field integral with domains in `Z'`, with
`|M̃| <= cbar` per site (P6 p. 14), so only `Re(b(g)-b(0)) <= (1+cbar)||g|_{Z'}||_1` is available. **Forced form unless the `M̃` terms are
assigned to `B^(1)` (domains meeting `Z_1^c`) instead of `b₀`.**
Ruling request (to send): "In `BaseSmallFieldInput.Kphys_bound` and `BaseProductData.b_bound` replace `exp(||g|_{Z'}||_1)` by
`exp((1+cbar)||g|_{Z'}||_1)`, `cbar >= 0` a constant of the typing (the bound of Lemma II.7.7 (b) on the source part of the small-field
terms of `b₀` with domains in `Z'`, P6 p. 14; `cbar` independent of `beta`, `Z'`). Reason: `b₀` contains the source parts of the small-field
integral, which are not unit-spin pairings; the unit-spin part alone gives `cbar = 0`. Downstream (S2) uses only `|b₀| <= (C_b log beta + C_b)|Z'|_1`
(Lemma II.7.8 proof) which is unchanged; `||g||_1 < 1` makes `e^{(1+cbar)||g||_1} <= e^{1+cbar}`, absorbed in `C_b`. Alternatively state: the
`M̃` terms with domains in `Z'` go to `B^(1)`; then `cbar = 0` and the carrier is unchanged."

## 5. Plan (item 2, in order)
1. (done by `baseF_decomposition`, `BaseWitness.lean`, which is the witness split with exactly the `Kt` factors `prod_{P,w=bd}(1-B) prod_O B`.)
2. `Base/BaseKtDef.lean`: `baseKtOf` (the integrand factor without `A`) and its four clauses `nonneg/meas/outside/dom`: ~300.
3. `Base/BaseBSource.lean`: `bSource` = (5), with `b_analytic`, `b_real`, `b_supp`, `b_rot`, `b_bound` with constant 1: ~250.
4. The Gaussian/vacuum part (1)-(3) and the assembly `BaseProductData` with `bSmall` as parameter: ~600; (S2) after.

## 6. Plan B (Kt indexed by `a`), Option C pieces (decision of 2026-10-22; `BaseProductData` unchanged)
C1. `Base/BaseFluctGauss.lean` (done): `baseFluctBlocks a`, `siteGaussDensity N v = (2 pi)^(-N/2) exp(-|v|^2/2)`,
    `baseFluctGauss a N x = prod_{y in baseFluctBlocks a} siteGaussDensity N (subFluctVarField N x 0 y)`; `_nonneg`, `measurable_`, `_rot`.
C2. `baseFluctSpin`: the spins on `(Omega \ Omega'') cap Z'` from `psi'_0`: `phi_x = chartMapPi e he (beta^(-1/2) (Cloc^(1/2) psi'_0))_x` with `e` the
    centre `locPhi`/`baseFieldHat` and `Cloc^(1/2) = pdSqrtInv K_U` of the component (`BaseComponentCovariance`); statement: `baseFluctSpin` is Borel,
    `O(N)`-equivariant, unit-norm values (`chartMapPi` lands in the sphere), and reads `(o, x, hv)` only through `locPhi` (so through `a` and the lifted data).
C3. `baseChartJacLoc a o x hv = |det pdSqrtInv K_U| * prod_x (1 - |xi_x|^2)^(-1/2)` (`chartJac`, `BaseComponentDeterminant`): `>= 0`, Borel, `O(N)`-invariant.
C4. `KtFull H hH Z' w o x hv := 1[ChiNewAt] * baseFluctGauss * baseChartJacLoc * exp(-baseMainAction) * (prod_{P,w=bd}(1-B) prod_O B)(phi) * 1[D_R]`,
    for `(H, hH, Z')`, with `phi = baseFieldHat`; clauses `nonneg, meas, outside, dom, rot` of `BaseProductData` for `KtFull`.
C5. Localization: `KtFull_congr : (e : H.localHistory M K 1 Z' = H'.localHistory M K 1 Z'') -> KtFull H hH Z' w o x hv =
    KtFull H' hH' Z'' (cast e w) (transOut e o) (transNew e x) hv`  (`transNew` of `QuietLocalRest`; needs the factors to read `H, Z'` only through `locHist`
    (`locHist_locRH` is `rfl`); the cutoff/`ChiNewAt` already reads `H.locRH`, so the same statement for `ChiNewAt`).
C6. `Kt a w o x hv := if h : exists H hH Z', H.localHistory M K 1 Z' = a then KtFull (choose h) ... else 0` (via C5, independent of the choice).
    `euclid_Kt` for `Kt` needs: (R) realizability is invariant under `HistImage sigma` (`a = H.localHistory`, `HistImage sigma a a'` => `a'` realizable) --
    otherwise `Kt a' = 0` while `Kt a != 0`. NEEDED FROM THE UNLANDED BRANCH: nothing of `canonHist` (a `choose` suffices); (R) is new, needs the action of
    `TorusSym` on `RegionHistory` (is there `RegionHistory.map sigma`? if not, ~300 lines). If (R) fails, ask the ruling for Option A.
