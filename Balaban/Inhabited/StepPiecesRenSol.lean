/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.ChartDetJointFromTower
public import Balaban.Inhabited.MarksNumericsFromTower
public import Balaban.Inhabited.MarkedFamilyAllRoots
public import Balaban.Inhabited.MarkedRootAssemblyFromTower
public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Inhabited.RenormRadiusInput
public import Balaban.Inhabited.StepOutputPhysical
public import Balaban.Fluctuation.DetGroupedAnalytic

/-!
# The landed step pieces at one tower with the renormalized solution

* `exists_stepTowerRenSol_hull`: the joint tower `StepTowerRenSol stepHullMin` exists.
* `StepTowerRenSol.T`: its projection to the base record `StepTower`, with `rfl` facts that the
  fields are those of the extension, so that theorems stated for `StepTower` apply.
* `stepPieces_fromTowerRenSol`: one threshold `β₀` above the thresholds of `StepTower.scale`,
  `stepPieces_fromTower` and `exists_beta0_marks`, after which, at every admissible scale, the
  per-scale package exists and the conclusions of the landed from-tower theorems hold together.
  Every conjunct is copied from the landed theorem, with the tower `T` replaced by `R.T`.
* `stepPieces_instance_renSol`: the statement at `k = 1`, `N₁ = 18`, `ν = 1/81`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover
  Filter Topology Matrix Metric Set Balaban.Localization.DecEquiv

section Tower

variable {κmin : ℝ}

/-- The joint tower exists at the hull rate. -/
theorem exists_stepTowerRenSol_hull : Nonempty (StepTowerRenSol stepHullMin) :=
  exists_stepTowerRenSol stepHullMin

/-- The base tower underlying a tower with the renormalized solution. -/
abbrev StepTowerRenSol.T (R : StepTowerRenSol κmin) : StepTower κmin :=
  R.toStepTowerRenEnd.toStepTowerRen.toStepTower

theorem StepTowerRenSol.T_m₁ (R : StepTowerRenSol κmin) : R.T.m₁ = R.m₁ := rfl
theorem StepTowerRenSol.T_t (R : StepTowerRenSol κmin) : R.T.t = R.t := rfl
theorem StepTowerRenSol.T_κ (R : StepTowerRenSol κmin) : R.T.κ = R.κ := rfl
theorem StepTowerRenSol.T_κ0 (R : StepTowerRenSol κmin) : R.T.κ0 = R.κ0 := rfl
theorem StepTowerRenSol.T_κdec (R : StepTowerRenSol κmin) : R.T.κdec = R.κdec := rfl
theorem StepTowerRenSol.T_κ' (R : StepTowerRenSol κmin) : R.T.κ' = R.κ' := rfl
theorem StepTowerRenSol.T_BG (R : StepTowerRenSol κmin) : R.T.BG = R.BG := rfl
theorem StepTowerRenSol.T_BG₂ (R : StepTowerRenSol κmin) : R.T.BG₂ = R.BG₂ := rfl
theorem StepTowerRenSol.T_δ (R : StepTowerRenSol κmin) : R.T.δ = R.δ := rfl
theorem StepTowerRenSol.T_step (R : StepTowerRenSol κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (ν β p₁ : ℝ) : R.T.step k hk N₁ ν β p₁ = R.toStepTower.step k hk N₁ ν β p₁ := rfl

end Tower

section Pieces

variable {κmin : ℝ}

open Classical in
/-- **The landed step pieces at the joint tower.**  For `R : StepTowerRenSol κmin` with
`stepHullMin ≤ κmin`: the hull-rate inequality and the constants record of `stepOutputPhysical`;
then one threshold `β₀` and amplitude constants such that, at every admissible scale, the per-scale
package of `R.T` exists and, for it, the following hold at the step `R.T.step k hk N₁ ν β p₁`:
(i) the conclusions of `stepPieces_fromTower` (source activity, determinant package, exponential
chart identity, source family); (ii) the smallness of `exists_beta0_marks`; (iii) the conclusion of
`markReal_slice_allRoots`; (iv) that of `markedRootAssembly_zero_fromTower`; (v) that of
`sourceExponentFamily_fromTower`; (vi) that of `detGrouped_chart_family_fromTower`; (vii) the
renormalized solution with the three localization fields (`renLoc_fields_scale_of_tower`) and the
expansions of `thm31g_C1_scale_of_tower`, `thm31g_C2_scale_of_tower`, at
`κ_a = κ_b = 3/2 κ_dec`. -/
theorem stepPieces_fromTowerRenSol (R : StepTowerRenSol κmin) (hT : stepHullMin ≤ κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
                3 / 2 * R.T.κdec ≤ hullRate 3 3
          ((R.T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) ∧
        (∃ C : StepOutputConsts 3 3, C.k0 = R.T.κ0 ∧ C.kdec = R.T.κdec ∧ C.k' = R.T.κ' ∧
          C.kout = 3 / 2 * R.T.κdec ∧ C.kH = 2 * R.T.κdec - 1 ∧ C.kapp = R.T.κ ∧
          C.kdet = (R.T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18 ∧
          C.Bhull = collarB 3 3 ∧ C.lhull = hullRate 3 3 C.kdet ∧
          C.Kc = 2 * (K0 3 3 R.T.κ0 + 1) ∧
          C.Kall = max (2 * K0 3 3 R.T.κ0) (rootUnionK 3 3 1 R.T.m₁ R.T.κ0) ∧ C.Ktot = C.Kc + C.Kall) ∧
    ∃ β₀ CE CF CE' CF' : ℝ, 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < CE' ∧ 0 < CF' ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      Nonempty (StepScaleData R.T k hk N₁ ν β p₁) ∧
      ∀ D : StepScaleData R.T k hk N₁ ν β p₁,
      -- (i)
      (
              (∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))),
                ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
                ∀ g : Fld 3 3 N₁ R.T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ R.T.m₁ (k + 1) 2 →
                ∃ BR : StepActivityBound (R.T.step k hk N₁ ν β p₁)
                    (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)) g,
                ∃ BC : StepActivityBoundC (R.T.step k hk N₁ ν β p₁)
                    (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)) g,
                  BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
                  HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
                  HEq BR.BS ((R.T.step k hk N₁ ν β p₁).blockSplit 1 hp0) ∧ HEq BC.BS BR.BS ∧
                  BR.κ0 = R.T.κ0 ∧ BC.κ0 = R.T.κ0 ∧ BR.κ' = R.T.κ' ∧ BC.κ' = R.T.κ' ∧
                  BR.κH = 2 * R.T.κdec - 1 ∧ BC.κH = BR.κH ∧
                  BR.Kc = 2 * (K0 3 3 R.T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
                  BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                    CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) ∧
              (
              ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1))),
                  DetExpansionLocC (R.T.step k hk N₁ ν β p₁) 1 z R.T.t (towerDetRate R.T.κ)
                    (towerDetConst R.T.κ),
                (∀ z D T', (E z).term D T' = ∑ y ∈ (R.T.step k hk N₁ ν β p₁).blockU z,
                  detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 R.T.BG R.T.κ) D y T') ∧
                (∀ z (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.T.m₁)
                      (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull, (E z).detGrouped D X =
                    rootTrace (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a 1 ν
                      (unitQ (R.T.step k hk N₁ ν β p₁).G') (unitP (R.T.step k hk N₁ ν β p₁).G')
                      ((R.T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
                      (svec (R.T.step k hk N₁ ν β p₁).G' (bgFieldC (R.T.step k hk N₁ ν β p₁).G'
                        (R.T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D))
                      (bgMultC (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D)) ∧
                (∀ z (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  ∀ X : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)),
                    ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate R.T.κ) (towerDetConst R.T.κ) *
                      Real.exp (-hullRate 3 3 (towerDetRate R.T.κ) * sizeJ 1 (k + 1) X)) ∧
                (∀ z (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  ∀ X : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)), (E z).detGrouped D X ≠ 0 →
                    IsPolyDom 1 (k + 1) X ∧
                      box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 R.T.m₁ (k + 1)) ⊆ X) ∧
                (∀ z (D D₂ : BgData (R.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D₂ →
                  ∀ X : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)),
                    (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
                    (E z).detGrouped D X = (E z).detGrouped D₂ X) ∧
                (∀ {σ : Equiv.Perm (CTorus 3 3 N₁ R.T.m₁ (k + 1))},
                  GenSymm 3 N₁ R.T.m₁ (k + 1) (k + 1) 1 σ →
                  ∃ Sy : LatSymm (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).G' σ,
                    (∀ D : BgData (R.T.step k hk N₁ ν β p₁).G' 2,
                      XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                      XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t (Sy.sym D)) ∧
                    ∀ z, (∀ (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2) T',
                        (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
                      ∀ (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2)
                        (X : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))),
                        (E (rootAct σ z)).detGrouped (Sy.sym D) (σ '' X) = (E z).detGrouped D X) ∧
                (∀ z (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  ∀ {Rm : Matrix (Fin 2) (Fin 2) ℂ}, Rmᵀ * Rm = 1 →
                    (∀ T', (E z).term (D.rot Rm) T' = (E z).term D T') ∧
                    ∀ X : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)),
                      (E z).detGrouped (D.rot Rm) X = (E z).detGrouped D X) ∧
                (∀ (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  ∀ {Q : Matrix (Fin 2) (Fin 2) ℝ}, Qᵀ * Q = 1 →
                    XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t
                      (D.rot (cmat Q)))) ∧
              (
              ∃ Jr : (R.T.step k hk N₁ ν β p₁).JointRep R.T.t (2 * p₁),
              ∃ val : ((((R.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) ×
                    ((R.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ))) →
                  (((R.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((R.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
                    ℂ → (RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 ×
                      (CTorus 3 3 N₁ R.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ,
                (∀ x w σ Θ, val x w σ Θ =
                  (-((R.T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3
                    (hatFun (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a₁
                      (R.T.step k hk N₁ ν β p₁).ν R.T.t (R.T.step k hk N₁ ν β p₁).hG'
                      (((R.T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                      (interactionOne (R.T.step k hk N₁ ν β p₁).hG (R.T.step k hk N₁ ν β p₁).hG'
                        (le_refl (k + 1)) (R.T.step k hk N₁ ν β p₁).a₁ (R.T.step k hk N₁ ν β p₁).ν R.T.t))
                    taylorWeight x.1 w.1 σ Θ.1 +
                  ((R.T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ R.T.m₁ (k + 1) × Fin 2,
                    Θ.2 s.1 s.2 *
                    dirTermSrc (hatFun (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a₁
                      (R.T.step k hk N₁ ν β p₁).ν R.T.t (R.T.step k hk N₁ ν β p₁).hG'
                      (((R.T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                      (onXi (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a₁
                        (R.T.step k hk N₁ ν β p₁).ν R.T.t
                        (fun D' ψ' => svec (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁))
                          (flFieldOne (R.T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁))
                            R.T.BG₂ R.T.κ (R.T.step k hk N₁ ν β p₁).a₁ (R.T.step k hk N₁ ν β p₁).ν D' ψ')
                          s.1 s.2)))
                      (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
                ∀ (g : Fld 3 3 N₁ R.T.m₁ (k + 1) 2) (x : (R.T.step k hk N₁ ν β p₁).EC),
                  (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
                  ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
                    Jr.W2 (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)) g
                        (rawOf (R.T.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
                      val (x, x) (x, x) (τ : ℂ)
                          (rawOf (R.T.step k hk N₁ ν β p₁).D',
                            fun y i => g y i / ((R.T.step k hk N₁ ν β p₁).β : ℂ)) -
                        val (x, x) (x, x) (τ : ℂ) (rawOf (R.T.step k hk N₁ ν β p₁).D', 0)) ∧
              (∀ q : ℝ, 0 < q → q ≤ 1 →
                ∀ S : StepSetting 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁), S = R.T.step k hk N₁ ν β p₁ →
                ∀ hp : 0 < S.p₁,
                ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
                      ℂ → (RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ R.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
                    (𝒴 : Finset (Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))))
                    (Tt : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
                      ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
                      (RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ R.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
                    (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                          (S.β * prop33EpsEtaScaled 3 3 2 R.T.m₁ k 1 S.a₁ R.T.BG R.T.BG₂ R.T.κ R.T.t
                            (lvR R.T.κ R.T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * R.T.κdec - 1)
                          (rawOf S.D', (0 : CTorus 3 3 N₁ R.T.m₁ (k + 1) → Fin 2 → ℂ))
                          (physSΛEta S S.a₁ S.ν R.T.t (q / S.β))
                          (physXW S (lvCpsi R.T.κ R.T.t (β * 3 ^ k)) 2 2 (lvR R.T.κ R.T.t (β * 3 ^ k) p₁)) val (physAgΘ S)
                          (AgFDirPair S)),
                    I.𝒴 = 𝒴 ∧ I.T = Tt ∧
                    ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
                        (physVq S 1 ν R.T.t q),
                      (∀ g : Fld 3 3 N₁ R.T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
                        ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν R.T.t q,
                          physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                            (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                          (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = Tt) ∧
                      ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 R.T.m₁ k 1 S.a₁ R.T.BG R.T.BG₂ R.T.κ R.T.t
                            (lvR R.T.κ R.T.t (β * 3 ^ k) p₁) 0 0 (q / S.β),
                        4 * (S.β * prop33EpsEtaScaled 3 3 2 R.T.m₁ k 1 S.a₁ R.T.BG R.T.BG₂ R.T.κ R.T.t
                            (lvR R.T.κ R.T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                          CE' * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                            q * CF' * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
                        ∀ {Kc : ℝ} (hKc : K0 3 3 R.T.κ0 ≤ Kc),
                        (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                            (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              R.T.κ0_ent hKc r.1 r.2).H y Φ)
                            (physVq S 1 ν R.T.t q ×ˢ ball (0 : ℂ) 2)) ∧
                        (∀ e (he : e ∈ physVq S 1 ν R.T.t q) (u : ℂ),
                          labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              R.T.κ0_ent hKc e u =
                            dtAct S 1 (I.atThetaOn S 1 _ hF he)
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              R.T.κ0_ent hKc u) ∧
                        (∀ e ∈ physVq S 1 ν R.T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                          ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                          (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              R.T.κ0_ent hKc e u).H y Φ =
                            I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                              (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                              (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)))) ∧
      -- (ii)
      (∀ ε : ℝ, ε ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) →
        ε ≤ (stepOutputPhysical R.T hT).theta ∧
        ε ≤ stepTheta 3 3 R.T.marksKc' (2 * R.T.κdec - 1) R.T.κ0 R.T.κ') ∧
      -- (iii)
      (
            ∃ (𝒴 : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1))) →
              Finset (Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))))
            (Ev : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)) →
              RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ R.T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ),
            (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
              (XiCRaw (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t ×ˢ FlBall (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁)) R.T.t)) ∧
            (∀ zb, ∀ Θ ∈ XiCRaw (R.T.step k hk N₁ ν β p₁).G' (R.T.step k hk N₁ ν β p₁).a (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t,
              ∀ ψ' ∈ FlBall (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁)) R.T.t,
              blockEnergyOne (R.T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁)) (R.T.step k hk N₁ ν β p₁).a₁ (R.T.step k hk N₁ ν β p₁).ν R.T.BG₂ R.T.κ R.T.t k zb
                (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
            (∀ zb Y, ∀ u ∈ XiCRaw (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t ×ˢ
                FlBall (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁)) R.T.t,
              ∀ u' ∈ XiCRaw (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t ×ˢ
                FlBall (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁)) R.T.t,
              agreeOn (thickSet (R.T.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
                (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
            (∀ zb Y, ∀ u ∈ XiCRaw (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t ×ˢ
                FlBall (stepG 3 3 N₁ R.T.m₁ k (rhoSep R.T.m₁)) R.T.t,
              ‖Ev zb Y u‖ ≤ energyBdScaled 3 3 2 (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) k
                (cK2' 3 3 2 (famConst 3 3 R.T.BG₂ R.T.κ) * R.T.t) R.T.t (rho4 3 3 2 R.T.BG R.T.κ) *
                Real.exp (-2 * R.T.κdec * treeLenCov (R.T.step k hk N₁ ν β p₁).G' 1 Y)) ∧
            (∀ x : (R.T.step k hk N₁ ν β p₁).E, ‖x‖ ≤ p₁ →
              ∃ Q : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 → (R.T.step k hk N₁ ν β p₁).EC,
                AnalyticOnNhd ℂ Q (XiCRaw (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t) ∧
                (∀ (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2) (hDh : ∀ y i, D.h y i = ((R.T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t D →
                  Q (rawOf D) = ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) ∧
                (∀ Θ ∈ XiCRaw (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) (R.T.step k hk N₁ ν β p₁).ν (k + 1) 1 R.T.t, ∀ b : (R.T.step k hk N₁ ν β p₁).U,
                  vn (fun i => Q Θ (b, i)) ≤
                    markedRad 3 3 2 k (R.T.step k hk N₁ ν β p₁).a₁ R.T.κ p₁ ((((R.T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
                ∀ (z : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1))))
                  (zb : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1)))) (Y : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))),
                AnalyticOnNhd ℂ (fun w : (physParam 2 (R.T.step k hk N₁ ν β p₁) × ℂ) × ℂ =>
                    markedBlockTerm (Ev zb Y) taylorWeight
                      (liftC (R.T.step k hk N₁ ν β p₁).hG' (w.1.2 • Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2)))
                      (liftC (R.T.step k hk N₁ ν β p₁).hG' ((R.T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2))))
                      (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2) w.2)
                  ((physV (R.T.step k hk N₁ ν β p₁) (R.T.step k hk N₁ ν β p₁).a₁ (R.T.step k hk N₁ ν β p₁).ν R.T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ×ˢ Metric.ball (0 : ℂ) (1 / 16)) ∧
                AnalyticOnNhd ℂ (fun w : physParam 2 (R.T.step k hk N₁ ν β p₁) × ℂ => deriv (markedBlockTerm (Ev zb Y) taylorWeight
                    (liftC (R.T.step k hk N₁ ν β p₁).hG' (w.2 • Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2)))
                    (liftC (R.T.step k hk N₁ ν β p₁).hG' ((R.T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2))))
                    (w.1.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2)) 0)
                  (physV (R.T.step k hk N₁ ν β p₁) (R.T.step k hk N₁ ν β p₁).a₁ (R.T.step k hk N₁ ν β p₁).ν R.T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ∧
                ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < 1 / 16 → ∀ e ∈ physV (R.T.step k hk N₁ ν β p₁) (R.T.step k hk N₁ ν β p₁).a₁ (R.T.step k hk N₁ ν β p₁).ν R.T.t, ∀ u : ℂ,
                  ‖u‖ < 17 / 16 →
                  ‖deriv (markedBlockTerm (Ev zb Y) taylorWeight
                    (liftC (R.T.step k hk N₁ ν β p₁).hG' (u • Q (e.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2)))
                    (liftC (R.T.step k hk N₁ ν β p₁).hG' ((R.T.step k hk N₁ ν β p₁).maskUC z (Q (e.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2))))
                    (e.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2)) 0‖ ≤
                    3 * (energyBdScaled 3 3 2 (compWeight 3 (R.T.step k hk N₁ ν β p₁).a₁) k
                      (cK2' 3 3 2 (famConst 3 3 R.T.BG₂ R.T.κ) * R.T.t) R.T.t (rho4 3 3 2 R.T.BG R.T.κ) *
                      Real.exp (-2 * R.T.κdec * treeLenCov (R.T.step k hk N₁ ν β p₁).G' 1 Y)) /
                      ((lvR R.T.κ R.T.t (β * 3 ^ k) p₁ / 4) ^ 3 * t₀)) ∧
            ∀ (D : BgData (R.T.step k hk N₁ ν β p₁).G' 2)
            (hDh : ∀ y i, D.h y i = ((R.T.step k hk N₁ ν β p₁).h₀ i : ℂ))
            (_hD : XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D)
            {x : ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).E} (_hx : ‖x‖ ≤ p₁)
            (z : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1),
            HasDerivAt (fun t : ℂ => ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
                (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁))
                (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).markedTangentC z (s : ℂ) t x))
              (-(((R.T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
                deriv (markedBlockTerm (Ev zb Y) taylorWeight
                  (liftC ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    ((s : ℂ) • ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
                  (liftC ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
                      (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
                  (rawOf ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) 0 ∧
            (fderiv ℂ (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
                (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)))
                ((s : ℂ) • ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)
              (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
                (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
              -(((R.T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
                deriv (markedBlockTerm (Ev zb Y) taylorWeight
                  (liftC ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    ((s : ℂ) • ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
                  (liftC ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
                      (((R.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
                  (rawOf ((R.T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0)) ∧
      -- (iv)
      (∀ S : StepSetting 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁), S = R.T.step k hk N₁ ν β p₁ →
      ∃ (Ev : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ R.T.m₁ (k + 1)) →
          RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ R.T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ)
        (M : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2 → Matrix (S.U × Fin 2) (S.U × Fin 2) ℂ),
        (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 R.T.t)) ∧
        (∀ (D' : BgData S.G' 2) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' (compWeight 3 1) ν (k + 1) 1 R.T.t D' → ∀ x : S.E,
          (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D') *ᵥ yhat x) =
            (S.withDatum D' hD').shiftUC x) ∧
        ∀ (z : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1)))) (x : S.E), ‖x‖ ≤ p₁ →
          (∀ (D' : BgData S.G' 2) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' (compWeight 3 1) ν (k + 1) 1 R.T.t D' →
            (S.withDatum D' hD').MarkRealAt R.T.t 2 x) ∧
          S.MarkedRootFamily z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev 1 ν R.T.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
                (cK2' 3 3 2 (famConst 3 3 R.T.BG₂ R.T.κ) * R.T.t) R.T.t (rho4 3 3 2 R.T.BG R.T.κ)‖ /
                ((lvR R.T.κ R.T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + R.T.m₁)) ^ 3) *
              ((nFibre 3 3 : ℝ) * Real.exp ((2 * R.T.κdec - 1) * cBr 3 3))) (2 * R.T.κdec - 1) ∧
          S.MarkedRootAssembly z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev R.T.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (|β| * (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
                (cK2' 3 3 2 (famConst 3 3 R.T.BG₂ R.T.κ) * R.T.t) R.T.t (rho4 3 3 2 R.T.BG R.T.κ)‖ /
                ((lvR R.T.κ R.T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + R.T.m₁)) ^ 3) *
              ((nFibre 3 3 : ℝ) * Real.exp ((2 * R.T.κdec - 1) * cBr 3 3)))) (2 * R.T.κdec - 1)) ∧
      -- (v)
      (∀ S : StepSetting 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁), S = R.T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep R.T.t (2 * p₁)) (𝒴 : Finset (Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))))
        (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y) (εU : ℝ),
        εU = β * prop33EpsEtaScaled 3 3 2 R.T.m₁ k 1 1 R.T.BG R.T.BG₂ R.T.κ R.T.t
          (lvR R.T.κ R.T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧ 0 ≤ εU ∧
        ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibre S S.a₁ S.ν R.T.t → ℝ × ℝ →
            LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
              (4 * εU) (2 * R.T.κdec - 1) R.T.κ0 (2 * (K0 3 3 R.T.κ0 + 1)),
          (∀ (e : physParam 2 S) (he : e ∈ physFibre S S.a₁ S.ν R.T.t), ∀ p ∈ stepSegments,
            ∀ᵐ x ∂S.nuFl,
              Jr.W1 (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                Jr.W2 (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
              ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
          (∀ g : Fld 3 3 N₁ R.T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
            ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
                physFibre S S.a₁ S.ν R.T.t,
              ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)) p.1 x +
                  S.WtwoC (zeroClass 3 3 N₁ R.T.m₁ k 2 (rhoSep R.T.m₁)) g p.2 x =
                ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                  ((S.blockSplit 1 hp).restr x))) ∧
      -- (vi)
      (
            ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.T.m₁ * 3 ^ (k + 1 - (k + 1))),
                DetExpansionLocC (R.T.step k hk N₁ ν β p₁) 1 z R.T.t (towerDetRate R.T.κ)
                  (towerDetConst R.T.κ),
              (∀ z D T', (E z).term D T' = ∑ y ∈ (R.T.step k hk N₁ ν β p₁).blockU z,
                detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 R.T.BG R.T.κ) D y T') ∧
              ∀ z (X : Set (CTorus 3 3 N₁ R.T.m₁ (k + 1))),
                AnalyticOnNhd ℂ (fun e : rawSub 2 (R.T.step k hk N₁ ν β p₁).G' =>
                    (E z).detGrouped (bgOfRaw e.1 e.2) X)
                  (((↑) : rawSub 2 (R.T.step k hk N₁ ν β p₁).G' →
                      RawData 3 3 (N₁ * 3 ^ R.T.m₁) (k + 1) 2) ⁻¹'
                    XiCRaw (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t) ∧
                AnalyticOnNhd ℂ (fun e : physParam 2 (R.T.step k hk N₁ ν β p₁) =>
                    (E z).detGrouped (bgOfRaw e.1.1 e.1.2) X)
                  (physV (R.T.step k hk N₁ ν β p₁) 1 ν R.T.t) ∧
                (∀ D : BgData (R.T.step k hk N₁ ν β p₁).G' 2,
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate R.T.κ) (towerDetConst R.T.κ) *
                    Real.exp (-hullRate 3 3 (towerDetRate R.T.κ) * sizeJ 1 (k + 1) X)) ∧
                (∀ D D₂ : BgData (R.T.step k hk N₁ ν β p₁).G' 2,
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D →
                  XiCData (R.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 R.T.t D₂ →
                  (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
                    (E z).detGrouped D X = (E z).detGrouped D₂ X)) ∧
      -- (vii) renormalization lane
      (∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
        IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
          (8 * R.t) F ∧
        (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
          HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
            (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
                (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec) 1
            (fun D _ => bgClass (lvTop N₁ R.m₁ k (rhoSep R.m₁)) ν
              (renCK 3 3 2 R.BG R.κ * R.t) D)
            (fun D φ ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
            (fun D _ => bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν
              (bgC0 3 3 2) D)) ∧
        (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
          HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
            (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
                (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec) 1
            (fun _ ξ => pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))
              (bgK1 3 3 2 * (xiC1 3 * R.t) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀
                + 2) (renMassU ν ξ))
            (fun _ v ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
            (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
              bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
                (F ((D.Ψ, D.h), ξ)).2))) ∧
        (∀ p : (lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2,
          HasLocPrinciple (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
            (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
                (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                  (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
              (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
            (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec) 1
            (fun _ ξ => {v | SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) v
              (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))})
            (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))) ∧
      (∀ {εR : ℝ}, εR ≤ R.r₀ → ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
      ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
        (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) εR
        (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
        (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * R.t) ^ 2 *
          blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) *
          εR ^ 1)
        (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t
          (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
          (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term) ∧
      (∀ {εR : ℝ}, 0 ≤ εR → εR ≤ R.r₀ → ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
      ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
        IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
          (8 * R.t) F ∧
        ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
        (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) εR
        (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
        (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * R.t) +
          renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀ + 2)) *
          (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t)) ^ 2)) *
          blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) *
          εR ^ 2)
        (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
          (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
          (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
            (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term)
  := by
  classical
  obtain ⟨βray, hβray, hscale⟩ := R.T.scale hA p
  obtain ⟨hull, hC, β₁, CE, CF, CE', CF', h2, hCE, hCF, hCE', hCF', H⟩ :=
    stepPieces_fromTower R.T hT hA p
  obtain ⟨β₂, hβ₂, hmarks⟩ := exists_beta0_marks R.T hT p hCE.le hCF.le
  refine ⟨hull, hC, max (max βray β₁) β₂, CE, CF, CE', CF', le_trans hβ₂ (le_max_right _ _),
    hCE, hCF, hCE', hCF', ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hβ2 : β₂ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ1 : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβr : βray ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ3 : 3 ≤ β := le_trans hβ₂ hβ2
  obtain ⟨D⟩ := hscale k hk N₁ h3N hN ν hν0.le hν β hβr p₁ hp0 hp₁
  refine ⟨⟨D⟩, fun D => ?_⟩
  have hκa : 3 / 2 * R.κdec ≤ 2 * R.κdec := by
    have := R.κdec_lower; have := R.κ0_nonneg; linarith
  obtain ⟨F, hF, l1, l2, l3⟩ := renLoc_fields_scale_of_tower R k hk N₁ h3N hN hν0.le hν hκa hκa
  refine ⟨H k hk N₁ h3N hN ν hν0 hν β hβ1 p₁ hp0 hp₁ D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    exact hmarks β k hβ2 ε hε
  · exact markReal_slice_allRoots R.T D hN hp0 hν0.le hν
  · intro S hS
    exact markedRootAssembly_zero_fromTower R.T D hN hν0.le hν (by linarith) hp0 hS
  · intro S hS hp
    exact sourceExponentFamily_fromTower R.T k hk N₁ h3N hN ν hν0 hν β (by linarith) p₁ hp0 D S
      hS hp
  · exact detGrouped_chart_family_fromTower R.T k hk N₁ h3N hN hν0.le hν β p₁
  · exact ⟨F, hF, l1, l2, l3⟩
  · intro εR hεR z
    exact thm31g_C1_scale_of_tower R k hk N₁ h3N hN hν0.le hν hκa hεR z
  · intro εR hεR0 hεR z
    exact thm31g_C2_scale_of_tower R k hk N₁ h3N hN hν0.le hν hκa hεR0 hεR z

end Pieces

section Instance

open Classical in
/-- **Non-vacuity of `stepPieces_fromTowerRenSol` at `k = 1`, `N₁ = 18`, `ν = 1/81`, `p₁ = 1`.**
For the joint tower at the hull rate there is a coupling `β ≥ 3` above the common threshold (with
`A₁ = 1`, `p = 0`) at which the per-scale package exists and which carries the renormalized
solution `F`, the zero-source determinant family, and the smallness of the mark record for the
zero amplitude. -/
theorem stepPieces_instance_renSol :
    ∃ R : StepTowerRenSol stepHullMin, ∃ β : ℝ, 3 ≤ β ∧
      Nonempty (StepScaleData R.T 1 le_rfl 18 (1 / 81) β 1) ∧
      3 / 2 * R.T.κdec ≤ hullRate 3 3
        ((R.T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) ∧
      0 ≤ (stepOutputPhysical R.T le_rfl).theta ∧
      (∃ F : RawData 3 3 (18 * 3 ^ R.m₁) (1 + 1) 2 × (Fin 3 → ℂ) →
          ((lvTop 18 R.m₁ 1 (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop 18 R.m₁ 1 (rhoSep R.m₁)).Ω 1 → ℂ),
        IsRenSol (N := 2) (lvTop 18 R.m₁ 1 (rhoSep R.m₁)) (compWeight 3 1) (1 / 81) R.t R.t R.r₀
          (8 * R.t) F) := by
  classical
  obtain ⟨R⟩ := exists_stepTowerRenSol_hull
  obtain ⟨βray, hβray, hscale⟩ := R.T.scale (A₁ := 1) one_pos 0
  obtain ⟨hull, -, β₀, CE, CF, CE', CF', h3, hCE, hCF, -, -, H⟩ :=
    stepPieces_fromTowerRenSol R le_rfl (A₁ := 1) one_pos 0
  have hβ : β₀ ≤ max β₀ βray := le_max_left _ _
  have hp : (1 : ℝ) ≤ pLog 1 0 (max β₀ βray * 3 ^ 1) := by simp [pLog]
  obtain ⟨-, hall⟩ := H 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num)
    (by norm_num) (max β₀ βray) hβ 1 one_pos hp
  obtain ⟨D⟩ := hscale 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num)
    (by norm_num) (max β₀ βray) (le_max_right _ _) 1 one_pos hp
  obtain ⟨-, hm, -, -, -, -, ⟨F, hF, -⟩, -⟩ := hall D
  exact ⟨R, max β₀ βray, le_trans h3 hβ, ⟨D⟩, hull, (hm 0 (by simp only [mul_zero, pow_zero, mul_one]; positivity)).1, F, hF⟩

end Instance

end Balaban.Inhabited
