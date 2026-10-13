# SHARPJOIN2 — exact-locality joins after leaf 1

**PROVED (snapshot).** Read-only statement inspection of `/home/scott/Balaban` at `0ac9420` (2026-10-13); no build. `PhysicalVRawY.vblock_fan_local_rawY`, `PhysicalFNuRawY.fsite_exact_local` and `nuBlock_exact_local`, `RawAgreeSites`, and W575's `MarkedVRawY.evDec_local_rawY` are on main. The proposed joins below are **OPEN**, even where their inputs have landed; W572–W574 were not found as completed exact-locality declarations on this snapshot.

## T1 — `DirectTermsRawY` (leaf 3)

**PROVED (current interface).** `DirectTerms` takes both agreement relations as parameters and stores `𝒴`, `T`, `b`, `loc`, `dom`, `bd`, `mem`, `agΘ`, `xw`, `ag`, `meas` (`Balaban/Fluctuation/HatLabelsDirect.lean:51-72`). Its `LocInt.loc` says, for `Y∈𝒴`, two admitted ray pairs, `‖σ‖<Rσ`, and `Θ,Θ′∈SΛ`, that `AgΘ Y Θ Θ′` and `AgF Y` in *both* ray coordinates imply equality of `T Y` (`Balaban/Fluctuation/InteractionLoc.lean:36-47`). The physical instances use `physAgΘ S` and `AgFDirPair S` (`PhysicalTerms.lean:63-78`; `SharpAssemblyEta.lean:1070-1089`; `SharpAssemblyScaled.lean:1506-1541`; `Inhabited/SourceDirectTermsFromTower.lean:102-137,349-390`). The former means raw agreement on `thickSet S.G′ Y` plus source agreement on `Y`; the latter is hat equality at unit points of `Y` in each coordinate.

**OPEN (exact worker statement).** Define the proposed relation, for `Θ=(raw,g)`,
```lean
physAgΘRawY S Y Θ Θ' := agreeOn Y Θ.1 Θ'.1 ∧ ∀ x ∈ Y, Θ.2 x = Θ'.2 x
```
and prove `physical_directTerms_eta_rawY` and its scaled variant with the **same** `SΛ`, `XW`, `val`, `𝒴`, `T`, and `b` as the corresponding thick physical instance, but type `DirectTerms … val (physAgΘRawY S) (AgFDirPair S)`. The new `LocInt.loc` is the sole mathematical change; copied fields require `agΘ` for the base datum and the existing `ag` for hats. Inputs: landed V/F/ν raw-Y congruences, W573's fan F/ν, W574's generalized `i5_functional_hat_dir_of_fan` and V expansion, plus `SharpAssemblyEta/Scaled`. Do not choose a second family of `T Y`.

**PROVED (record logic); OPEN (physical construction).** One Lean value cannot literally have two `DirectTerms` types with different `AgΘ` parameters. Reconstruct two records using the *same* `𝒴,T,b,val` and their respective `loc` fields (or derive the old thick record from the sharp one using `Y⊆thickSet Y`). Then strengthen `sourceDirectTerms_scale_fromTower[_rho]` and `sourceWitness_fromTower[_rho]` so their existing `val,𝒴,Tt` witness carries both locality certificates; a separately existential sharp witness would not identify the old activity with the new terms (`Inhabited/SourceDirectTermsFromTower.lean:296-390`; `SourceWitnessJoint.lean:45-141,465-566`).

**OPEN (first consumer).** For that sharp record and the same `labelActFamilyOn`, prove
```lean
labelActFamilyOn_local_scaled_rawY … (he : e ∈ V) (he' : e' ∈ V)
  (w : {Y // Y ∈ I.𝒴})
  (hr : agreeOn w.1 (e.1 : RawData …) (e'.1 : RawData …))
  (hg : ∀ x ∈ w.1, e.2 x = e'.2 x) (u : ℂ) :
  (labelActFamilyOn … e u).H w = (labelActFamilyOn … e' u).H w
```
because `physInclScaled` preserves raw data and scales equal sources equally. This replaces the `agreeOn (thickSet S.G′ w.1)` input of `ObsSourceLocal.labelActFamilyOn_local_scaled` (`Balaban/Inhabited/ObsSourceLocal.lean:43-85`) without changing label terms.

## T2 — `EnergyCoeffSites` (leaf 4)

**OPEN (exact conclusion).** Strengthen the *same* `c` returned by `e1CoeffFamily_value_fromTower` with, for every cube set `C` and `θ,θ′∈physV S S.a₁ S.ν T.t`, the clause
```lean
physRestrict (sitesOf C) (physIncl 2 S θ) =
  physRestrict (sitesOf C) (physIncl 2 S θ') → c θ C = c θ' C.
```
Keep its formula, analytic, bound, support, and every-fibre-datum value clauses (`Balaban/Inhabited/E1CoeffFamily.lean:236-344`). Add this as a new conjunct inside the existing `∀ C` result; retain the old thick clause for clients and derive it from the sharp clause. Prove it in the current assembly with `paramMarked_analytic_local_bound`, rather than selecting another `F₁,Sol,A₀,c` (`E1CoeffFamily.lean:380-457`; `Balaban/Fluctuation/ParamCarrierLocal.lean:138-194`).

**OPEN (the two exact premises).** Set `π θ := physRestrict (sitesOf C) (physIncl 2 S θ)`. Reprove `hA`: equality of π gives raw and source agreement on `sitesOf C` (`RawAgreeSites.physRestrict_physIncl_eq_iff`, lines 73-92); for every contributing label `y`, `Lab.ysite y ⊆ Yhat Set.univ (sitesOf C) = sitesOf C` (`RootActiveSize.Yhat_univ`, lines 66-68), so T1 gives the `commonAct (zeroSourceAct …)` equality. Reprove `hG`: the **PROVED** `MarkedVRawY.evDec_local_rawY` is about the same `evDec` (`Balaban/Fluctuation/MarkedVRawY.lean:342-408`); pass it through `decMarkG`, `decMarkCorr`, `markedOutDec` and `e1MarkGParam`. For a bridge label, each constituent domain lies in the bridge by `subset_bridge` (`MarkedRootGeometry.lean:117-122`), then in `sitesOf C`. These replace the thick `hπ` premises of `E1ParamRawLocal.commonAct_zeroSourceAct_hA` and `markedOutDec_decMarkCorrTerm_hG` (`Balaban/Inhabited/E1ParamRawLocal.lean:253-337`) at the calls in `E1CoeffFamily.lean:400-442`.

## T3 — observable leaves 5–6

**PROVED (present limit).** `obsEv_fromTower` returns one `Ev` with analytic, bound, half-record, and ray-identity clauses, but its `hd` assumes `AgHatDir`, whose raw component still reads `thickSet Y` (`Balaban/Inhabited/ObsCoeffAnalytic.lean:262-332`; `Balaban/Fluctuation/SharpAE.lean:46-51`).

**OPEN (exact `ObsEvRawY` statement).** In that *same* existential package, add
```lean
∀ Y u∈XiCRaw×hatDisc, ∀ u'∈XiCRaw×hatDisc,
  agreeOn Y u.1 u'.1 ∧
  (∀ y∈Y, ∀ i, u.2 (unitPt S.hG' y,i) = u'.2 (unitPt S.hG' y,i)) →
  Ev Y u = Ev Y u'.
```
Use the W573 F/ν fan congruences and W574's relation-parametric engine, then retain the old `hd` as a consequence. A new `Ev` chosen in a separate theorem would not automatically be the one used by `obsCoeffParam`, `ObsMarkHalf`, and `ObsRayIdentity`.

**OPEN (exact `ObsCoeffSites` statement).** For the single `obsCoeffParam` and fixed `A,Lab,Ev` of `obsFamily_joint_fromTower`, require for every `T′` and `θ,θ′∈physVq S S.a₁ S.ν T.t q`:
```lean
physRestrict (sitesOf T') (physIncl 2 S θ) =
  physRestrict (sitesOf T') (physIncl 2 S θ') →
  obsCoeffParam … θ T' = obsCoeffParam … θ' T'.
```
In W557's `obsCoeffParam_congr_of_local` (worker branch, absent on this main snapshot), sharpen all three inputs: (1) activity labels by T1, raw **and source** equality on their own sites; (2) `obsHker (hatCoeff (Ev Y) … (obsUnitVec S m))` by the sharp `Ev` clause and `Y⊆sitesOf T′`; (3) remainder marks, including `obsGrFam`/`obsRemLab` and the first-order mark, by their own-site congruences and the block-support condition. The generic finite coefficient lemma then uses identical terms, rather than changing the analytic/value family (`ObsFamilyJoint.lean:89-190`; `ObsCoeffFamily.lean:133-194,375-488`). Check the exact W557 premise syntax when that branch lands.

## T4 — determinant and the actual full energy object

**REFUTED (wrong target).** Exact locality of `e0 θ C := dz θ C + c θ C` on `sitesOf C` does not follow: `dz` only has `thickSet (Yhat univ (sitesOf C))` locality (`Balaban/Inhabited/E0CoeffFamily.lean:53-75,265-310`). The determinant's exact-locality term is the *collar-grouped* term on `renYs`, using `detGrouped_local` and `renFibreMap` (`Balaban/Fluctuation/DetCollarHull.lean:372`; `Balaban/Inhabited/RenormE0FibreDetRadius.lean:97-207`).

**OPEN (precise target form).** For each root `z` and common chart `Dom`, radius `r`, and rate `κ≤min(T.κ′,3T.κdec/2)`, use the site-domain cover
```lean
Ys := (Finset.univ.image (fun C : Finset CubeB => finOf (sitesOf C))) ∪
      renYs (renCube S.G' (X1 S.G' 1 k (fam 1 (blockSite k z)))) S.G' 1
        (X1 S.G' 1 k (fam 1 (blockSite k z))).
```
Define the energy term at `Y` as the zero extension of the mark coefficient reindexed through the injective `sitesOf` map, plus the zero extension of the determinant's `renFibreMap` sum. On `Ys`, prove `IsLocExp` for the sum of the marked energy and determinant functions: `sum_eq`, joint analyticity, `RawAgree Y` locality at equal ξ, and the sum of the two bounds. Inputs for marks: the *same* `c` of T2, `MarkFibreSitesOf`/`Thm31SiteDomains.sitesOf_regroup`, and `RawAgreeSites.local_of_physRestrict`, `renDY_eq_dExt_of_isPolyDom` (`Balaban/Fluctuation/RawAgreeSites.lean:39-163`). Inputs for determinant: `renE0_fibre_det_at` and `renDY_eq_sizeJ`; union and rate changes use `LocExpUnion.extend`, `add_union`, `congr_dY` with their sign premises (`Balaban/Fluctuation/LocExpUnion.lean:37-114`). Nonzero domains must be `IsDj 1 (k+1)` and contain the root box; zero coefficients at other index sets are harmless. This is the zero-class exact-locality shape of Theorem 3.1(a), with the two summands indexed on their *own* site domains.

**PROVED (determinant record's actual scope).** `renE0_fibre_det_at` supplies `IsLocExp.sum_eq` for `renE0θ_det e E z D ξ` on `Dom = XiCOneReal S.G′ (compWeight 3 1) ν e`, `‖ξ‖<R.r₀`, `0<e≤R.t`; its determinant record has chart radius `2R.t` (`RenormE0FibreDetRadius.lean:97-124,185-207`). At `D=S.D′`, `ξ=0`, it identifies that function with `−½Σ_{y∈blockU z}Σ_i logAC(y,i)(y,i)` (`:107-112`; `RenormThetaDatum.lean:210-243`). `DetExpansionLocC.sum_eq` at **every** datum of its complex chart identifies `Σ_C E.term D C` with `rootTrace … D`, and `renThetaDatum_zero` makes the determinant function this sum at `ξ=0` (`DetOutputTerms.lean:141-155`; `RenormThetaDatum.lean:91-94,210-220`).

**REFUTED (statement attribution); OPEN (fibre bridge).** The displayed `renE0_fibre_det_at` identity is **not** a statement that the `renYs` sum equals the `S.withDatum D′` logarithm for every fibre datum `D′`: it names only `S.D′`. To get that assertion, prove a separate `rootTrace_one_eq_logAC` bridge for `S.withDatum D′` under its constant-`h₀` and chart hypotheses, and show `D′∈XiCOneReal … e` (or use a compatible domain). The marked `E1locC` value in `e1CoeffFamily_value_fromTower` holds for every complex fibre datum at `ξ=0`, but does not itself provide an `IsLocExp.sum_eq` for all `D∈XiCOneReal` and `‖ξ‖<r`; its `physV` chart has radius `T.t`, while the determinant construction uses a `2T.t` chart. The common chart/radius and parameterized marked-value bridge remain **OPEN**. Reality, symmetry, and the paper's numerical prefactor/rate still require separate checks against `notes/phase1/FLUCTUATION.md:394-408`.

## T5 — ordered worker leaves (each target ≤300 Lean lines)

1. **OPEN W573, `FNuFanRawY`:** promote landed `fsite_exact_local` and `nuBlock_exact_local` to the marked physical F/ν fan locality. Input: `PhysicalFNuRawY`, marked support, row lemmas.
2. **OPEN W574, `EngineRawY`:** make `i5_functional_hat_dir_of_fan` relation-parametric in place; instantiate it with `vblock_fan_local_rawY` to give the same V terms exact locality. Input: `PhysicalVRawY`.
3. **OPEN `MarkBridgeRawY`:** propagate the **PROVED** W575 theorem `MarkedVRawY.evDec_local_rawY` through `decMarkG`, `decMarkCorr`, and `markedOutDec` for the same marks; leave `MarkedBlockExpansionDecPair` unchanged. Input: `MarkedVRawY.lean:342-408`, `E1ParamRawLocal`.
4. **OPEN W572, `SiteLocExpGeneric`:** finish the generic coefficient-to-`IsLocExp` package on site domains. Input: `RawAgreeSites`, `LocExpUnion`; exact coefficient locality remains a hypothesis.
5. **OPEN `DirectTermsRawY`:** build the relation-parametric physical direct-terms certificate on the same `val,𝒴,Tt`; carry it into `sourceWitness_fromTower` and `labelActFamilyOn_local_scaled_rawY`. Inputs: 1–2.
6. **OPEN `EnergyCoeffSites`:** combine 3 and 5 through `commonAct`/`zeroSourceAct` and the corrected marks, then add exact-site clause to `e1CoeffFamily_value_fromTower`. Inputs: 3,5.
7. **OPEN `ObsEvRawY`:** add the sharp `hd` to the same `obsEv_fromTower` witness. Inputs: 1–2.
8. **OPEN `ObsCoeffSites`:** discharge W557's three premises and add exact-site locality to the same `obsFamily_joint_fromTower` family. Inputs: 5,7 and the W557 branch.
9. **OPEN `EnergyChartJoin` and `ObsChartJoin` (two leaves):** supply the common `Dom/r` parameterization and every-datum value/analyticity needed by the `IsLocExp` terms; for energy, bridge the determinant at `S.withDatum D′` and the marked value at nonzero ξ. Inputs: 6–8 and the landed determinant record.
10. **OPEN `SiteLocExpJoin`:** use 4, 9, the two exact coefficient clauses, root/support/size identities, and `LocExpUnion` to give zero-class (a) and (b) expansions on their paper site domains with exact locality. State separately which remaining paper clauses (reality, symmetry, constants, general classes) are proved. Inputs: 4,6–9.

**OPEN (confidence).** High confidence in the landed interface facts, the same-witness requirements, and the determinant/base-datum distinction; medium confidence in the proposed finite assembly until W572–W574 and W557 are inspected on main. No assertion here that the final exact-locality Theorem 3.1 is already proved.
