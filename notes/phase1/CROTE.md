# CRotE: which complex rotations the renormalization chain needs (W875, blocker 6)

## 1. The matrices that occur

`hsf.rotE` is applied with a complex orthogonal `M` (class `IsCRot`) at exactly four places:
`Eaux_rot` (Def6BridgeLift 249), `EauxC_rot` (Def6AvgLiftC 116), `Eaux_rotA` (RenormAnisoBridge 429),
`EauxC_rotA` (RenormClassGE 111). (`Eaux_orth`, `EauxC_orth`, `Eaux_orthA`, `EauxC_orthA` reduce `det = -1` to
`det = 1` by one real reflection and call these. The other users of `rotE` use real `Q`.)
`M` is `A Bᵀ` (`LiftCtx.witness`), `A, B` complex orthogonal with entries `<= ma, mb` (the frames of
`RenormRot.exists_normalizing_rot`, entries `<= 40`), `N ma mb <= rotB N = 64000 N²`. It relates the pairs
`(fieldOf u, hOf u)` and `(fieldOf u', hOf u')`, `u' = rotCfgL M u`, both `u, u'` in the ball of radius `rho`
around `refPt i₀` (so the field is `e_{i₀}` within `rho` on the blocks of `X'`, equal to `e_{i₀}` elsewhere,
`h = b/nu_j` within `rho/nu_j` of `e_{i₀}`). Consequence (`hMe` in the proofs): `|M e_{i₀} - e_{i₀}| <= rho (1 + N B)`.
No other information on `M`.

## 2. Near a real rotation? No. (refuted)

`Def6RotFrames.boost3` (N = 3): `M = [[5/4, 3i/4, 0], [-3i/4, 5/4, 0], [0, 0, 1]]` (cosh t = 5/4, e^t = 2) is complex
orthogonal (`boost3_orth`), fixes `e₃` (`boost3_fix`), maps `e₃ + rho (1, i, 0)` to `e₃ + (rho/2)(1, i, 0)`
(`boost3_pair`), and is at entry distance `>= 3/4` from every real matrix (`boost3_far_from_real`). Both points are
in the ball of radius `rho` for every `rho`; `M = A Bᵀ` with `A = M, B = 1` is an admitted witness (entries `< 40`;
`cosh t <= 40` is allowed). So `M = Q exp(A)` with `|A| <= C eps` is FALSE for the landed frames: the landed frame
bound is too crude to give it. In the source the normalizing rotation (Rodrigues, `R p = u e_{i₀}`, `p = psi(0)` with
small imaginary part) should be near real; this was not checked and is not needed.

## 3. What is true and proved (hypothesis-free)

`M` complex orthogonal. Polar decomposition `M = Q H`, `H = sqrt(Mᴴ M)`, `Q` real orthogonal (any det), `H` Hermitian
positive, `Hᵀ H = 1` (`RotFrames.exists_polar`, CFC square root; `Hᵀ = H⁻¹` by uniqueness of the positive root).
`H = cay(S) = (1 - S)⁻¹ (1 + S)`, `S` complex antisymmetric (`RotFrames.frame_decomp`), `1 - sS` invertible on `[0,1]`.
The path `s ↦ cay(sS) = g_s(H)`, `g_s(l) = ((1+s)l + 1-s)/((1-s)l + 1+s)`, satisfies
`|cay(sS) u|² <= |u|² + |M u|²` and `|cay(sS) e - e| <= |Mᴴ M e - e|` (spectral, scalar bounds `g_s² <= 1 + l²`,
`|g_s - 1| <= |l² - 1|`). Hence (`exists_cay_path_near`, `x = N B`, `eta0 >= |M e - e|`, `e` real):
`|v - e| <= rho, |M v - e| <= rho'  =>  |cay(sS) v - e| <= rho + rho' + (1 + 2x) eta0`.
The family `w ↦ cay(A(w))` is analytic where `det(1 - A(w)) ≠ 0` and real orthogonal at real `w` near 0;
`eq_of_rotation_family_local` (identity theorem with analyticity along the segment only) and
`rotE_eq_of_cay_path` give invariance along `Q cay(S)`. Results (Def6RotFrames):
`rotE_of_near` (any analytic `F` real-invariant on `D`) and `SFTermClauses.rotE_of_near` (`Tm.E`, from the real clause
`hT.rotE` and `hT.analyticE`). Hypotheses: `M` orthogonal, `|M_ij| <= B`, `e` real, closeness radii
`r, r', rh, rh', re` of `Psi, M Psi, h, M h, M e`, a class `P'` closed under all matrices (block-constant `Psi`,
constant `h`), `D ∋ (Psi', h')` for `P'` within `r1 >= sqrt N (r + r' + (1+2NB) re)`, `r1h >= sqrt N (rh + rh' + (1+2NB) re)`
of `e`, `D` a neighbourhood of `(Psi, h)`.

## 4. Replacement plan

No `hCR : CRotE ...` can be discharged as stated (it asks for every `R` relating two domain points; no path in the
domain is known). Each `hCR` is removed by replacing the four call sites:
1. In `Eaux_rot`, `EauxC_rot`, `Eaux_rotA`, `EauxC_rotA`: replace `hsf.rotE j hj1 hjk x₀ (Ypoly j X') hX hx₀ M hM _ _ hXi hXirot`
   by `hT.rotE_of_near ...` with `e = Pi.single i₀ 1`, `r = rho`, `re = rho (1+NB) min(1, 1/nu_j)`, `r' = max(rho, re)` (`|M e - e|` from
   `psi` and from `b/nu_j`), `rh = rh' = rho/nu_j`, `P' = (Psi block-constant) ∧ (h constant)`, `hDm` from `xiDom_of_field` with
   `rho2 := r1 = sqrt N rho (3 + 4x + 2x²)`, `x = N rotB N`, `B = rotB N`. (The `b`-radius is `nu_j r1h <= rho sqrt N (3+3x+2x²)`.)
2. The radius relation `N rho2 < delta²` is met by shrinking `liftRadius` (and `anisoRadius`) by the constant
   `sqrt N (3 + 4x + 2x²)/(1 + x)` (depends on `N` only). `Eaux_orth`/`EauxC_orth`(A) become `Eaux_rot...` with `M` orthogonal of
   any determinant (the reflection step is not needed: `Q` of the polar decomposition is any real orthogonal matrix).
3. The four theorems and their callers (`fp_mem_xiDom`, `xiDom_of_field`, `LiftCtx`, `Represents`, `IsSFFamily.premisesTerm`,
   Def6AvgLiftC, RenormClassGE, RenormAnisoBridge(Inf), Def6v2Renorm ~12 uses of `toLanded hCR`, Def6v2Bridge 245/359,
   LayerV2RenormFirst 125, RegionalAlignedSource 342) take `hT : SFTermClauses P (xiFieldDom ...) Tm` in place of
   `hsf : IsSF ...` (only `gs_spec`, `analyticE`, `localE`, `rotE` are used; the density clause is not used by the bridges),
   then `isSF_of_termClauses` and every `hC/hCR` disappear; the landed `IsSF` versions become corollaries via
   `IsSF.termClauses`. `Def6v2RenormCompare` (`CRotE` of the landed class) stays valid.

W1091 (2026-10-18): REPAIRED. The four call sites no longer use `CRotE` (deleted, with every `hCR`/`hC`): isotropic `Eaux_rot`, `EauxC_rot` by `E_rot_at` (polar path, `rotE_of_near_within`); anisotropic `Eaux_rotA`, `EauxC_rotA`, `shiftTerm_rotA` by `rotE_aniso_of_xiFieldDom` (`RenormAnisoRot.lean`), the two-stage Cayley path of `Def6RotFramesAniso.lean`.
Why two stages: the polar path alone does not stay in the anisotropic domain (longitudinal radius `r²`); `T = cay(A)`, `A = (v eᵀ - e vᵀ)/(1 + e·v)`, `v = M e`, takes `e` to `v`, and `T⁻¹M` fixes `e`, so `cay e = e` and the longitudinal coordinate is exact.  Needs `ν_j ≤ 1` (from `Admissible.νbar_le`, `CoeffBounds.nu_le`): `aniK N B = 60 N √N (1 + N B)²`, `anisoRadius`/`liftRadius` shrunk by constants depending on `N` only.
Changed statements: `IsSF.rotE` now for real `IsRot` (the source clause; `IsSF.termClauses` is trivial), radius conditions, `hνb : ν ≤ 1` threaded through the IrrelTorus chain (discharged by `CoeffBounds.nu_le_one` at the class level).
