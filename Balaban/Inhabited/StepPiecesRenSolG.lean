/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.ChartDetJointFromTower
public import Balaban.Inhabited.MarksNumericsFromTower
public import Balaban.Inhabited.MarkedFamilyAllRoots
public import Balaban.Inhabited.MarkedRootAssemblyFromTower
public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Inhabited.RenormRadiusInput
public import Balaban.Inhabited.RenormRadiusLoc
public import Balaban.Fluctuation.DetGroupedAnalytic

/-!
# The landed step pieces at one general tower with the renormalized solution

`StepTowerRenSolG.stepPieces_fromTowerRenSolG`: the general-`d`, `L`, `N` form of
`stepPieces_fromTowerRenSol`.  One threshold `β₀` above the thresholds of `StepTowerG.scale`,
`StepTowerG.stepPieces_fromTowerG` and `StepTowerG.exists_beta0_marks`, after which, at every
admissible scale, the per-scale package exists and the conclusions of the general from-tower
theorems hold together.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover
  Filter Topology Matrix Metric Set Balaban.Localization.DecEquiv

open Classical in
/-- **The landed step pieces at the joint general tower.**  For `R : StepTowerRenSolG d L N κmin`
with `R.m₀ = 1`, odd `L = 2 q₀ + 1` and the hull hypothesis on the interpolation rate: the
hull-rate inequality and a constants record `C` (as in `StepTowerG.stepPieces_fromTowerG`); then one
threshold `β₀` and amplitude constants such that, at every admissible scale, the per-scale package
of `R.toStepTowerG` exists and, for it, at the step `R.toStepTowerG.step k hk N₁ ν β p₁`:
(i) the conclusions of `StepTowerG.stepPieces_fromTowerG`; (ii) the smallness of
`StepTowerG.exists_beta0_marks`; (iii) that of `StepTowerG.markReal_slice_allRootsG`; (iv) that of
`StepTowerG.markedRootAssembly_zero_fromTowerG`; (v) that of `sourceExponentFamily_fromTowerG`;
(vi) that of `StepTowerG.detGrouped_chart_family_fromTowerG`; (vii) the renormalized solution
with the three localization fields (`renLoc_fields_scale_of_towerG`) and the expansions of
`thm31g_C1_scale_of_towerG`, `thm31g_C2_scale_of_towerG`, at `κ_a = κ_b = 3/2 κ_dec`.  The fixed
`stepPieces_fromTowerRenSol` has the same conjuncts at `R.toG`. -/
theorem StepTowerRenSolG.stepPieces_fromTowerRenSolG_rho {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (hm₀ : R.m₀ = 1) {q₀ : ℕ} (hLq : L = 2 * q₀ + 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * R.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    3 / 2 * R.κdec ≤ hullRate d L
      ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L)) ∧
    ∃ C : StepOutputConsts d L, C.k0 = R.κ0 ∧ C.kdec = R.κdec ∧ C.k' = R.κ' ∧
      C.kout = 3 / 2 * R.κdec ∧ C.kH = 2 * R.κdec - 1 ∧ C.kapp = R.κ ∧
      C.kdet = (R.κ - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L) ∧
      C.Bhull = collarB d L ∧ C.lhull = hullRate d L C.kdet ∧
      C.Kc = 2 * (K0 d L R.κ0 + 1) ∧
      C.Kall = max (2 * K0 d L R.κ0) (rootUnionK d L R.m₀ R.m₁ R.κ0) ∧
      C.Ktot = C.Kc + C.Kall ∧
    ∃ CE CF CE' CF' : ℝ, 0 < CE ∧ 0 < CF ∧ 0 < CE' ∧ 0 < CF' ∧
    ∀ ρ : ℝ, 0 < ρ → ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ρ ≤ β₀ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ R.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      Nonempty (StepScaleDataG R.toStepTowerG k hk N₁ ν β p₁) ∧
      ∀ D : StepScaleDataG R.toStepTowerG k hk N₁ ν β p₁,
      -- (i)
      (
      (∃ 𝒴 : Finset (Set (CTorus d L N₁ R.m₁ (k + 1))),
        ∃ hdom : ∀ Y ∈ 𝒴, IsDj R.m₀ (k + 1) Y,
        ∀ g : Fld d L N₁ R.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ R.m₁ (k + 1) N ρ →
        ∃ BR : StepActivityBound (R.toStepTowerG.step k hk N₁ ν β p₁)
            (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g,
        ∃ BC : StepActivityBoundC (R.toStepTowerG.step k hk N₁ ν β p₁)
            (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g,
          BR.m₀ = R.m₀ ∧ BC.m₀ = R.m₀ ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧
          BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS ((R.toStepTowerG.step k hk N₁ ν β p₁).blockSplit R.m₀ hp0) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = R.κ0 ∧ BC.κ0 = R.κ0 ∧ BR.κ' = R.κ' ∧ BC.κ' = R.κ' ∧
          BR.κH = 2 * R.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 d L R.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
          BR.εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
              Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
            ρ * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
              Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) ∧
      (∃ E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
          DetExpansionLocC (R.toStepTowerG.step k hk N₁ ν β p₁) 1 z R.t
            ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
            ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))),
        (∀ z D T', (E z).term D T' = ∑ y ∈ (R.toStepTowerG.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N R.BG R.κ) D y T') ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
              (K := k + 1) 1 (k + 1) Set.univ))).image (detCollarHullC q₀),
            (E z).detGroupedC q₀ D X =
            rootTrace (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a 1 ν
              (unitQ (R.toStepTowerG.step k hk N₁ ν β p₁).G') (unitP (R.toStepTowerG.step k hk N₁ ν β p₁).G')
              ((R.toStepTowerG.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
              (svec (R.toStepTowerG.step k hk N₁ ν β p₁).G' (bgFieldC (R.toStepTowerG.step k hk N₁ ν β p₁).G'
                (R.toStepTowerG.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D))
              (bgMultC (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D)) ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)),
            ‖(E z).detGroupedC q₀ D X‖ ≤
              hullConst d L
                  ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                  ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
                    (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
                Real.exp (-hullRate d L
                  ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  sizeJ 1 (k + 1) X)) ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)), (E z).detGroupedC q₀ D X ≠ 0 →
            IsPolyDom 1 (k + 1) X ∧
              box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide L 1 R.m₁ (k + 1)) ⊆ X) ∧
        (∀ z (D D₂ : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D₂ →
          ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)),
            (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGroupedC q₀ D X = (E z).detGroupedC q₀ D₂ X) ∧
        (∀ {σ : Equiv.Perm (CTorus d L N₁ R.m₁ (k + 1))},
          GenSymm L N₁ R.m₁ (k + 1) (k + 1) 1 σ →
          ∃ Sy : LatSymm (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).G' σ,
            (∀ D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N,
              XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
              XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t (Sy.sym D)) ∧
            ∀ z, (∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N) T',
                (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
              ∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N)
                (X : Set (CTorus d L N₁ R.m₁ (k + 1))),
                (E (rootAct σ z)).detGroupedC q₀ (Sy.sym D) (σ '' X) =
                  (E z).detGroupedC q₀ D X) ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ {Rm : Matrix (Fin N) (Fin N) ℂ}, Rmᵀ * Rm = 1 →
            (∀ T', (E z).term (D.rot Rm) T' = (E z).term D T') ∧
            ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)),
              (E z).detGroupedC q₀ (D.rot Rm) X = (E z).detGroupedC q₀ D X) ∧
        (∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ {Q : Matrix (Fin N) (Fin N) ℝ}, Qᵀ * Q = 1 →
            XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t
              (D.rot (cmat Q)))) ∧
      (∃ Jr : (R.toStepTowerG.step k hk N₁ ν β p₁).JointRep R.t (2 * p₁),
      ∃ val : ((((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ) ×
            ((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ))) →
          (((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ) × ((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ)) →
            ℂ → (RawData d L (N₁ * L ^ R.m₁) (k + 1) N ×
              (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) → ℂ,
        (∀ x w σ Θ, val x w σ Θ =
          (-((R.toStepTowerG.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3
            (hatFun (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a₁
              (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t (R.toStepTowerG.step k hk N₁ ν β p₁).hG'
              (((R.toStepTowerG.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne (R.toStepTowerG.step k hk N₁ ν β p₁).hG (R.toStepTowerG.step k hk N₁ ν β p₁).hG'
                (le_refl (k + 1)) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t))
            taylorWeight x.1 w.1 σ Θ.1 +
          ((R.toStepTowerG.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus d L N₁ R.m₁ (k + 1) × Fin N,
            Θ.2 s.1 s.2 *
            dirTermSrc (hatFun (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a₁
              (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t (R.toStepTowerG.step k hk N₁ ν β p₁).hG'
              (((R.toStepTowerG.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a₁
                (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t
                (fun D' ψ' => svec (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
                  (flFieldOne (R.toStepTowerG.step k hk N₁ ν β p₁).G' (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
                    R.BG₂ R.κ (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν D' ψ')
                  s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        ∀ (g : Fld d L N₁ R.m₁ (k + 1) N) (x : (R.toStepTowerG.step k hk N₁ ν β p₁).EC),
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
          ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
            Jr.W2 (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g
                (rawOf (R.toStepTowerG.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
              val (x, x) (x, x) (τ : ℂ)
                  (rawOf (R.toStepTowerG.step k hk N₁ ν β p₁).D',
                    fun y i => g y i / ((R.toStepTowerG.step k hk N₁ ν β p₁).β : ℂ)) -
                val (x, x) (x, x) (τ : ℂ) (rawOf (R.toStepTowerG.step k hk N₁ ν β p₁).D', 0)) ∧
      (∀ q : ℝ, 0 < q → q ≤ ρ →
        ∀ S : StepSetting d L N₁ R.m₁ k N (rhoSepG d L R.m₁), S = R.toStepTowerG.step k hk N₁ ν β p₁ →
        ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
              ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
              (RawData d L (N₁ * L ^ R.m₁) (k + 1) N ×
                (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
            (𝒴 : Finset (Set (CTorus d L N₁ R.m₁ (k + 1))))
            (Tt : Set (CTorus d L N₁ R.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
              ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
              (RawData d L (N₁ * L ^ R.m₁) (k + 1) N ×
                (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
            (I : DirectTerms S R.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                  (S.β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ S.a₁ R.BG R.BG₂ R.κ R.t
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))
                  (2 * R.κdec - 1)
                  (rawOf S.D', (0 : CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ))
                  (physSΛEta S S.a₁ S.ν R.t (q / S.β))
                  (physXW S (lvCpsiG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val (physAgΘ S)
                  (AgFDirPair S)),
            I.𝒴 = 𝒴 ∧ I.T = Tt ∧
            ∃ hF : DirectTermsFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
                (physVqRho S 1 ν R.t ρ q),
              (∀ g : Fld d L N₁ R.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
                ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVqRho S 1 ν R.t ρ q,
                  physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                    (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                  (I.atThetaOn S R.m₀ _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S R.m₀ _ hF hg).T = Tt) ∧
              ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ S.a₁ R.BG R.BG₂ R.κ R.t
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β),
                4 * (S.β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ S.a₁ R.BG R.BG₂ R.κ R.t
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) ≤
                  CE' * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
                      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
                    q * CF' * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
                      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
                ∀ {Kc : ℝ} (hKc : K0 d L R.κ0 ≤ Kc),
                (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit R.m₀ hp).Ωb b),
                  AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
                    (labelActFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc r.1 r.2).H y Φ)
                    (physVqRho S 1 ν R.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
                (∀ e (he : e ∈ physVqRho S 1 ν R.t ρ q) (u : ℂ),
                  labelActFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc e u =
                    dtAct S R.m₀ (I.atThetaOn S R.m₀ _ hF he)
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc u) ∧
                (∀ e ∈ physVqRho S 1 ν R.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                  ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit R.m₀ hp).Ωb b),
                  (labelActFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc e u).H y Φ =
                    I.T y.1 (S.hatOf R.m₀ p₁ hp Φ, S.hatOf R.m₀ p₁ hp Φ)
                      (S.hatOf R.m₀ p₁ hp Φ, S.hatOf R.m₀ p₁ hp Φ) u
                      (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e)))
      ) ∧
      -- (ii)
      (∀ ε : ℝ, ε ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          ρ * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) →
        ε ≤ C.theta ∧
        ε ≤ stepTheta d L (2 * (K0 d L R.κ0 + 1) + rootUnionK d L R.m₀ R.m₁ R.κ0)
          (2 * R.κdec - 1) R.κ0 R.κ') ∧
      -- (iii)
      (
    ∃ (𝒴 : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ R.m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ R.m₁ (k + 1)) →
      RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ) → ℂ),
    (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t)) ∧
    (∀ zb, ∀ Θ ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t,
      ∀ ψ' ∈ FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      blockEnergyOne (R.toStepTowerG.step k hk N₁ ν β p₁).G' (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.BG₂ R.κ R.t k zb
        (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ
        FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      ∀ u' ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ
        FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      agreeOn (thickSet (R.toStepTowerG.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
        (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ
        FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      ‖Ev zb Y u‖ ≤ energyBdScaled d L N (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) k
        (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ) *
        Real.exp (-2 * R.κdec * treeLenCov (R.toStepTowerG.step k hk N₁ ν β p₁).G' 1 Y)) ∧
    (∀ x : (R.toStepTowerG.step k hk N₁ ν β p₁).E, ‖x‖ ≤ p₁ →
      ∃ Q : RawData d L (N₁ * L ^ R.m₁) (k + 1) N → (R.toStepTowerG.step k hk N₁ ν β p₁).EC,
        AnalyticOnNhd ℂ Q (XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t) ∧
        (∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N) (hDh : ∀ y i, D.h y i = ((R.toStepTowerG.step k hk N₁ ν β p₁).h₀ i : ℂ)),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D →
          Q (rawOf D) = ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) ∧
        (∀ Θ ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t, ∀ b : (R.toStepTowerG.step k hk N₁ ν β p₁).U,
          vn (fun i => Q Θ (b, i)) ≤
            markedRad d L N k (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ R.κ p₁ ((((R.toStepTowerG.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
        ∀ (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))))
          (zb : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) (Y : Set (CTorus d L N₁ R.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun w : (physParam N (R.toStepTowerG.step k hk N₁ ν β p₁) × ℂ) × ℂ =>
            markedBlockTerm (Ev zb Y) taylorWeight
              (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' (w.1.2 • Q (w.1.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)))
              (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' ((R.toStepTowerG.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N))))
              (w.1.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N) w.2)
          ((physV (R.toStepTowerG.step k hk N₁ ν β p₁) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ×ˢ Metric.ball (0 : ℂ) (1 / 16)) ∧
        AnalyticOnNhd ℂ (fun w : physParam N (R.toStepTowerG.step k hk N₁ ν β p₁) × ℂ => deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' (w.2 • Q (w.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)))
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' ((R.toStepTowerG.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N))))
            (w.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)) 0)
          (physV (R.toStepTowerG.step k hk N₁ ν β p₁) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ∧
        ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < 1 / 16 → ∀ e ∈ physV (R.toStepTowerG.step k hk N₁ ν β p₁) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t, ∀ u : ℂ,
          ‖u‖ < 17 / 16 →
          ‖deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' (u • Q (e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)))
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' ((R.toStepTowerG.step k hk N₁ ν β p₁).maskUC z (Q (e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N))))
            (e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)) 0‖ ≤
            3 * (energyBdScaled d L N (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) k
              (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ) *
              Real.exp (-2 * R.κdec * treeLenCov (R.toStepTowerG.step k hk N₁ ν β p₁).G' 1 Y)) /
              ((lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * t₀)) ∧
    ∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N)
    (hDh : ∀ y i, D.h y i = ((R.toStepTowerG.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (_hD : XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D)
    {x : ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).E} (_hx : ‖x‖ ≤ p₁)
    (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1),
    HasDerivAt (fun t : ℂ => ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁))
        (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).markedTangentC z (s : ℂ) t x))
      (-(((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) 0 ∧
    (fderiv ℂ (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)))
        ((s : ℂ) • ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)
      (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
        (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
      -(((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0)
      ) ∧
      -- (iv)
      (∀ S : StepSetting d L N₁ R.m₁ k N (rhoSepG d L R.m₁),
        S = R.toStepTowerG.step k hk N₁ ν β p₁ →
      ∃ (Ev : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ R.m₁ (k + 1)) →
          RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ) → ℂ)
        (M : RawData d L (N₁ * L ^ R.m₁) (k + 1) N → Matrix (S.U × Fin N) (S.U × Fin N) ℂ),
        (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
          (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 R.t)) ∧
        (∀ (D' : BgData S.G' N) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' (compWeight L 1) ν (k + 1) 1 R.t D' → ∀ x : S.E,
          (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D') *ᵥ yhat x) =
            (S.withDatum D' hD').shiftUC x) ∧
        ∀ (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E), ‖x‖ ≤ p₁ →
          (∀ (D' : BgData S.G' N) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' (compWeight L 1) ν (k + 1) 1 R.t D' →
            (S.withDatum D' hD').MarkRealAt R.t 2 x) ∧
          S.MarkedRootFamily z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev 1 ν R.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (3 * ‖energyBdScaled d L N (compWeight L 1) k
                (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ)‖ /
                ((lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 d L * (((L : ℕ) : ℝ) ^ (1 + R.m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * R.κdec - 1) * cBr d L))) (2 * R.κdec - 1) ∧
          S.MarkedRootAssembly z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev R.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (|β| * (3 * ‖energyBdScaled d L N (compWeight L 1) k
                (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ)‖ /
                ((lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 d L * (((L : ℕ) : ℝ) ^ (1 + R.m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * R.κdec - 1) * cBr d L)))) (2 * R.κdec - 1)
      ) ∧
      -- (v)
      (∀ S : StepSetting d L N₁ R.m₁ k N (rhoSepG d L R.m₁),
        S = R.toStepTowerG.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
    ∃ (Jr : S.JointRep R.t (2 * p₁)) (𝒴 : Finset (Set (CTorus d L N₁ R.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj R.m₀ (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ 1 R.BG R.BG₂ R.κ R.t
        (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (ρ / β) ∧ 0 ≤ εU ∧
      ∃ Aseg : ∀ e : physParam N S, e ∈ physFibreRho S S.a₁ S.ν R.t ρ → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit R.m₀ hp).Ωb
            (4 * εU) (2 * R.κdec - 1) R.κ0 (2 * (K0 d L R.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physFibreRho S S.a₁ S.ν R.t ρ), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁))
                ((e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) e.2
                ((e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit R.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ R.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ R.m₁ (k + 1) N ρ →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibreRho S S.a₁ S.ν R.t ρ,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) p.1 x +
                S.WtwoC (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit R.m₀ hp).restr x))
      ) ∧
      -- (vi)
      (
    ∃ E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTowerG.step k hk N₁ ν β p₁) 1 z R.t
          ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (R.toStepTowerG.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N R.BG R.κ) D y T') ∧
      ∀ z (X : Set (CTorus d L N₁ R.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun e : rawSub N (R.toStepTowerG.step k hk N₁ ν β p₁).G' =>
            (E z).detGroupedC q₀ (bgOfRaw e.1 e.2) X)
          (((↑) : rawSub N (R.toStepTowerG.step k hk N₁ ν β p₁).G' →
              RawData d L (N₁ * L ^ R.m₁) (k + 1) N) ⁻¹'
            XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t) ∧
        AnalyticOnNhd ℂ (fun e : physParam N (R.toStepTowerG.step k hk N₁ ν β p₁) =>
            (E z).detGroupedC q₀ (bgOfRaw e.1.1 e.1.2) X)
          (physV (R.toStepTowerG.step k hk N₁ ν β p₁) 1 ν R.t) ∧
        (∀ D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N,
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ‖(E z).detGroupedC q₀ D X‖ ≤
            hullConst d L
                ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
              Real.exp (-hullRate d L
                ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                sizeJ 1 (k + 1) X)) ∧
        (∀ D D₂ : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N,
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D₂ →
          (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGroupedC q₀ D X = (E z).detGroupedC q₀ D₂ X)
      ) ∧
      -- (vii) renormalization lane
      (
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      (∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec) 1
          (fun D _ => bgClass (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) ν
            (renCK d L N R.BG R.κ * R.t) D)
          (fun D φ ξ => renC1On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t
            (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
          (fun D _ => bgFieldC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν
            (bgC0 d L N) D)) ∧
      (∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec) 1
          (fun _ ξ => pertClass (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
            (renCK d L N R.BG R.κ * (cK2 d L N * (8 * R.t * ‖ξ‖)))
            (bgK1 d L N * (xiC1 d * R.t) + renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t) * R.r₀
              + 2) (renMassU ν ξ))
          (fun _ v ξ => renC2On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1)
            (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
          (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
            bgMultC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D +
              (F ((D.Ψ, D.h), ξ)).2))) ∧
      (∀ p : (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N,
        HasLocPrinciple (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
                (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
              (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec) 1
          (fun _ ξ => {v | SupBounds (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) v
            (renCK d L N R.BG R.κ * (cK2 d L N * (8 * R.t * ‖ξ‖)))})
          (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))
      ) ∧
      (∀ {εR : ℝ}, εR ≤ R.r₀ → ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
    ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) εR
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
        (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
        (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec)
      (1 * ((d + 6) * (renCK d L N R.BG R.κ * R.t) ^ 2 *
        blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (blockSites d L N₁ R.m₁ (k + 1) k z)) *
        εR ^ 1)
      (fun D ξ => renC1On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t
        (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h
        (bgFieldC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D) ξ) term
      ) ∧
      (∀ {εR : ℝ}, 0 ≤ εR → εR ≤ R.r₀ → ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) εR
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
        (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
        (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec)
      (1 * (17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * R.t) +
        renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t) * R.r₀ + 2)) *
        (renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t)) ^ 2)) *
        blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (blockSites d L N₁ R.m₁ (k + 1) k z)) *
        εR ^ 2)
      (fun D ξ => renC2On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1)
        (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
        (bgMultC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D +
          (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term
      ) := by
  classical
  obtain ⟨βray, hβray, hscale⟩ := R.toStepTowerG.scale hA p
  obtain ⟨hull, hC, CE, CF, CE', CF', hCE, hCF, hCE', hCF', H⟩ :=
    R.toStepTowerG.stepPieces_fromTowerG_rho hLq hhull hA p
  obtain ⟨C, hk0, hkdec, hk', hkout, hkH, hkapp, hkdet, hBh, hlh, hKc, hKall, hKtot⟩ := hC
  refine ⟨hull, C, hk0, hkdec, hk', hkout, hkH, hkapp, hkdet, hBh, hlh, hKc, hKall, hKtot,
    CE, CF, CE', CF', hCE, hCF, hCE', hCF', fun ρ hρ => ?_⟩
  obtain ⟨β₁, h2, hρβ, H⟩ := H ρ hρ
  obtain ⟨β₂, hβ₂, hmarks⟩ := R.toStepTowerG.exists_beta0_marks R.m₀ C hKc hKall hkH hk0 hk' p
    hCE.le (mul_pos hρ hCF).le
  refine ⟨max (max βray β₁) β₂, le_trans hβ₂ (le_max_right _ _),
    hρβ.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro k hk N₁ _ hLN hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hβ2 : β₂ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ1 : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβr : βray ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ3 : 3 ≤ β := le_trans hβ₂ hβ2
  obtain ⟨D⟩ := hscale k hk N₁ hLN hN ν hν0.le hν β hβr p₁ hp0 hp₁
  refine ⟨⟨D⟩, fun D => ?_⟩
  have hκa : 3 / 2 * R.κdec ≤ 2 * R.κdec := by
    have := R.κdec_lower; have := R.κ0_nonneg; linarith
  obtain ⟨F, hF, l1, l2, l3⟩ := renLoc_fields_scale_of_towerG R k hk N₁ hLN hN hν0.le hν hκa hκa
  refine ⟨H k hk N₁ hLN hN ν hν0 hν β hβ1 p₁ hp0 hp₁ D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    exact hmarks β k hβ2 ε hε
  · exact R.toStepTowerG.markReal_slice_allRootsG hm₀ D hN hp0 hν0.le hν rfl rfl
  · intro S hS
    exact R.toStepTowerG.markedRootAssembly_zero_fromTowerG hm₀ D hN hν0.le hν (by linarith) hp0
      rfl hS
  · intro S hS hp
    exact sourceExponentFamily_fromTowerG_rho R.toStepTowerG k hk N₁ hLN hN ν hν0 hν ρ hρ β
      (max_le (by linarith) (hρβ.trans hβ1)) p₁ hp0 D rfl S (heq_of_eq hS) hp
  · exact R.toStepTowerG.detGrouped_chart_family_fromTowerG hLq k hk N₁
      (by simpa [hm₀] using hLN) hN hν0.le hν β p₁
  · exact ⟨F, hF, l1, l2, l3⟩
  · intro εR hεR z
    exact thm31g_C1_scale_of_towerG R k hk N₁ hLN hN hν0.le hν hκa hεR z
  · intro εR hεR0 hεR z
    exact thm31g_C2_scale_of_towerG R k hk N₁ hLN hN hν0.le hν hκa hεR0 hεR z

open Classical in
/-- The landed statement: the case `ρ = 1`. -/
theorem StepTowerRenSolG.stepPieces_fromTowerRenSolG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) (hm₀ : R.m₀ = 1) {q₀ : ℕ} (hLq : L = 2 * q₀ + 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * R.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    3 / 2 * R.κdec ≤ hullRate d L
      ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L)) ∧
    ∃ C : StepOutputConsts d L, C.k0 = R.κ0 ∧ C.kdec = R.κdec ∧ C.k' = R.κ' ∧
      C.kout = 3 / 2 * R.κdec ∧ C.kH = 2 * R.κdec - 1 ∧ C.kapp = R.κ ∧
      C.kdet = (R.κ - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L) ∧
      C.Bhull = collarB d L ∧ C.lhull = hullRate d L C.kdet ∧
      C.Kc = 2 * (K0 d L R.κ0 + 1) ∧
      C.Kall = max (2 * K0 d L R.κ0) (rootUnionK d L R.m₀ R.m₁ R.κ0) ∧
      C.Ktot = C.Kc + C.Kall ∧
    ∃ β₀ CE CF CE' CF' : ℝ, 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < CE' ∧ 0 < CF' ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ R.m₀ ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      Nonempty (StepScaleDataG R.toStepTowerG k hk N₁ ν β p₁) ∧
      ∀ D : StepScaleDataG R.toStepTowerG k hk N₁ ν β p₁,
      -- (i)
      (
      (∃ 𝒴 : Finset (Set (CTorus d L N₁ R.m₁ (k + 1))),
        ∃ hdom : ∀ Y ∈ 𝒴, IsDj R.m₀ (k + 1) Y,
        ∀ g : Fld d L N₁ R.m₁ (k + 1) N, g ∈ l1Ball d L N₁ R.m₁ (k + 1) N →
        ∃ BR : StepActivityBound (R.toStepTowerG.step k hk N₁ ν β p₁)
            (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g,
        ∃ BC : StepActivityBoundC (R.toStepTowerG.step k hk N₁ ν β p₁)
            (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g,
          BR.m₀ = R.m₀ ∧ BC.m₀ = R.m₀ ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧
          BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS ((R.toStepTowerG.step k hk N₁ ν β p₁).blockSplit R.m₀ hp0) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = R.κ0 ∧ BC.κ0 = R.κ0 ∧ BR.κ' = R.κ' ∧ BC.κ' = R.κ' ∧
          BR.κH = 2 * R.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 d L R.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
          BR.εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
              Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
            CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
              Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) ∧
      (∃ E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
          DetExpansionLocC (R.toStepTowerG.step k hk N₁ ν β p₁) 1 z R.t
            ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
            ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))),
        (∀ z D T', (E z).term D T' = ∑ y ∈ (R.toStepTowerG.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N R.BG R.κ) D y T') ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
              (K := k + 1) 1 (k + 1) Set.univ))).image (detCollarHullC q₀),
            (E z).detGroupedC q₀ D X =
            rootTrace (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a 1 ν
              (unitQ (R.toStepTowerG.step k hk N₁ ν β p₁).G') (unitP (R.toStepTowerG.step k hk N₁ ν β p₁).G')
              ((R.toStepTowerG.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
              (svec (R.toStepTowerG.step k hk N₁ ν β p₁).G' (bgFieldC (R.toStepTowerG.step k hk N₁ ν β p₁).G'
                (R.toStepTowerG.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D))
              (bgMultC (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D)) ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)),
            ‖(E z).detGroupedC q₀ D X‖ ≤
              hullConst d L
                  ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                  ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
                    (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
                Real.exp (-hullRate d L
                  ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  sizeJ 1 (k + 1) X)) ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)), (E z).detGroupedC q₀ D X ≠ 0 →
            IsPolyDom 1 (k + 1) X ∧
              box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide L 1 R.m₁ (k + 1)) ⊆ X) ∧
        (∀ z (D D₂ : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D₂ →
          ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)),
            (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGroupedC q₀ D X = (E z).detGroupedC q₀ D₂ X) ∧
        (∀ {σ : Equiv.Perm (CTorus d L N₁ R.m₁ (k + 1))},
          GenSymm L N₁ R.m₁ (k + 1) (k + 1) 1 σ →
          ∃ Sy : LatSymm (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).G' σ,
            (∀ D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N,
              XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
              XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t (Sy.sym D)) ∧
            ∀ z, (∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N) T',
                (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
              ∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N)
                (X : Set (CTorus d L N₁ R.m₁ (k + 1))),
                (E (rootAct σ z)).detGroupedC q₀ (Sy.sym D) (σ '' X) =
                  (E z).detGroupedC q₀ D X) ∧
        (∀ z (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ {Rm : Matrix (Fin N) (Fin N) ℂ}, Rmᵀ * Rm = 1 →
            (∀ T', (E z).term (D.rot Rm) T' = (E z).term D T') ∧
            ∀ X : Set (CTorus d L N₁ R.m₁ (k + 1)),
              (E z).detGroupedC q₀ (D.rot Rm) X = (E z).detGroupedC q₀ D X) ∧
        (∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ∀ {Q : Matrix (Fin N) (Fin N) ℝ}, Qᵀ * Q = 1 →
            XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t
              (D.rot (cmat Q)))) ∧
      (∃ Jr : (R.toStepTowerG.step k hk N₁ ν β p₁).JointRep R.t (2 * p₁),
      ∃ val : ((((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ) ×
            ((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ))) →
          (((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ) × ((R.toStepTowerG.step k hk N₁ ν β p₁).U × Fin N → ℂ)) →
            ℂ → (RawData d L (N₁ * L ^ R.m₁) (k + 1) N ×
              (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) → ℂ,
        (∀ x w σ Θ, val x w σ Θ =
          (-((R.toStepTowerG.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3
            (hatFun (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a₁
              (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t (R.toStepTowerG.step k hk N₁ ν β p₁).hG'
              (((R.toStepTowerG.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne (R.toStepTowerG.step k hk N₁ ν β p₁).hG (R.toStepTowerG.step k hk N₁ ν β p₁).hG'
                (le_refl (k + 1)) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t))
            taylorWeight x.1 w.1 σ Θ.1 +
          ((R.toStepTowerG.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus d L N₁ R.m₁ (k + 1) × Fin N,
            Θ.2 s.1 s.2 *
            dirTermSrc (hatFun (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a₁
              (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t (R.toStepTowerG.step k hk N₁ ν β p₁).hG'
              (((R.toStepTowerG.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a₁
                (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t
                (fun D' ψ' => svec (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
                  (flFieldOne (R.toStepTowerG.step k hk N₁ ν β p₁).G' (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
                    R.BG₂ R.κ (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν D' ψ')
                  s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        ∀ (g : Fld d L N₁ R.m₁ (k + 1) N) (x : (R.toStepTowerG.step k hk N₁ ν β p₁).EC),
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
          ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
            Jr.W2 (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g
                (rawOf (R.toStepTowerG.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
              val (x, x) (x, x) (τ : ℂ)
                  (rawOf (R.toStepTowerG.step k hk N₁ ν β p₁).D',
                    fun y i => g y i / ((R.toStepTowerG.step k hk N₁ ν β p₁).β : ℂ)) -
                val (x, x) (x, x) (τ : ℂ) (rawOf (R.toStepTowerG.step k hk N₁ ν β p₁).D', 0)) ∧
      (∀ q : ℝ, 0 < q → q ≤ 1 →
        ∀ S : StepSetting d L N₁ R.m₁ k N (rhoSepG d L R.m₁), S = R.toStepTowerG.step k hk N₁ ν β p₁ →
        ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
              ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
              (RawData d L (N₁ * L ^ R.m₁) (k + 1) N ×
                (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
            (𝒴 : Finset (Set (CTorus d L N₁ R.m₁ (k + 1))))
            (Tt : Set (CTorus d L N₁ R.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
              ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
              (RawData d L (N₁ * L ^ R.m₁) (k + 1) N ×
                (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
            (I : DirectTerms S R.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                  (S.β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ S.a₁ R.BG R.BG₂ R.κ R.t
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))
                  (2 * R.κdec - 1)
                  (rawOf S.D', (0 : CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ))
                  (physSΛEta S S.a₁ S.ν R.t (q / S.β))
                  (physXW S (lvCpsiG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val (physAgΘ S)
                  (AgFDirPair S)),
            I.𝒴 = 𝒴 ∧ I.T = Tt ∧
            ∃ hF : DirectTermsFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
                (physVq S 1 ν R.t q),
              (∀ g : Fld d L N₁ R.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
                ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν R.t q,
                  physInclScaled N S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                    (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                  (I.atThetaOn S R.m₀ _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S R.m₀ _ hF hg).T = Tt) ∧
              ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ S.a₁ R.BG R.BG₂ R.κ R.t
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β),
                4 * (S.β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ S.a₁ R.BG R.BG₂ R.κ R.t
                    (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) ≤
                  CE' * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
                      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
                    q * CF' * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
                      Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
                ∀ {Kc : ℝ} (hKc : K0 d L R.κ0 ≤ Kc),
                (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit R.m₀ hp).Ωb b),
                  AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
                    (labelActFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc r.1 r.2).H y Φ)
                    (physVq S 1 ν R.t q ×ˢ ball (0 : ℂ) 2)) ∧
                (∀ e (he : e ∈ physVq S 1 ν R.t q) (u : ℂ),
                  labelActFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc e u =
                    dtAct S R.m₀ (I.atThetaOn S R.m₀ _ hF he)
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc u) ∧
                (∀ e ∈ physVq S 1 ν R.t q, ∀ u : ℂ, ‖u‖ < 2 →
                  ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit R.m₀ hp).Ωb b),
                  (labelActFamilyOn S R.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                      hLN hp0 (by norm_num) hεU
                      R.κ0_ent hKc e u).H y Φ =
                    I.T y.1 (S.hatOf R.m₀ p₁ hp Φ, S.hatOf R.m₀ p₁ hp Φ)
                      (S.hatOf R.m₀ p₁ hp Φ, S.hatOf R.m₀ p₁ hp Φ) u
                      (physInclScaled N S (((1 / S.β : ℝ)) : ℂ) e)))
      ) ∧
      -- (ii)
      (∀ ε : ℝ, ε ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) →
        ε ≤ C.theta ∧
        ε ≤ stepTheta d L (2 * (K0 d L R.κ0 + 1) + rootUnionK d L R.m₀ R.m₁ R.κ0)
          (2 * R.κdec - 1) R.κ0 R.κ') ∧
      -- (iii)
      (
    ∃ (𝒴 : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ R.m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ R.m₁ (k + 1)) →
      RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ) → ℂ),
    (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t)) ∧
    (∀ zb, ∀ Θ ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (R.toStepTowerG.step k hk N₁ ν β p₁).a (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t,
      ∀ ψ' ∈ FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      blockEnergyOne (R.toStepTowerG.step k hk N₁ ν β p₁).G' (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.BG₂ R.κ R.t k zb
        (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ
        FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      ∀ u' ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ
        FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      agreeOn (thickSet (R.toStepTowerG.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
        (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
    (∀ zb Y, ∀ u ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t ×ˢ
        FlBall (stepG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.t,
      ‖Ev zb Y u‖ ≤ energyBdScaled d L N (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) k
        (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ) *
        Real.exp (-2 * R.κdec * treeLenCov (R.toStepTowerG.step k hk N₁ ν β p₁).G' 1 Y)) ∧
    (∀ x : (R.toStepTowerG.step k hk N₁ ν β p₁).E, ‖x‖ ≤ p₁ →
      ∃ Q : RawData d L (N₁ * L ^ R.m₁) (k + 1) N → (R.toStepTowerG.step k hk N₁ ν β p₁).EC,
        AnalyticOnNhd ℂ Q (XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t) ∧
        (∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N) (hDh : ∀ y i, D.h y i = ((R.toStepTowerG.step k hk N₁ ν β p₁).h₀ i : ℂ)),
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D →
          Q (rawOf D) = ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) ∧
        (∀ Θ ∈ XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) (R.toStepTowerG.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t, ∀ b : (R.toStepTowerG.step k hk N₁ ν β p₁).U,
          vn (fun i => Q Θ (b, i)) ≤
            markedRad d L N k (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ R.κ p₁ ((((R.toStepTowerG.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
        ∀ (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))))
          (zb : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) (Y : Set (CTorus d L N₁ R.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun w : (physParam N (R.toStepTowerG.step k hk N₁ ν β p₁) × ℂ) × ℂ =>
            markedBlockTerm (Ev zb Y) taylorWeight
              (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' (w.1.2 • Q (w.1.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)))
              (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' ((R.toStepTowerG.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N))))
              (w.1.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N) w.2)
          ((physV (R.toStepTowerG.step k hk N₁ ν β p₁) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ×ˢ Metric.ball (0 : ℂ) (1 / 16)) ∧
        AnalyticOnNhd ℂ (fun w : physParam N (R.toStepTowerG.step k hk N₁ ν β p₁) × ℂ => deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' (w.2 • Q (w.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)))
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' ((R.toStepTowerG.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N))))
            (w.1.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)) 0)
          (physV (R.toStepTowerG.step k hk N₁ ν β p₁) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ∧
        ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < 1 / 16 → ∀ e ∈ physV (R.toStepTowerG.step k hk N₁ ν β p₁) (R.toStepTowerG.step k hk N₁ ν β p₁).a₁ (R.toStepTowerG.step k hk N₁ ν β p₁).ν R.t, ∀ u : ℂ,
          ‖u‖ < 17 / 16 →
          ‖deriv (markedBlockTerm (Ev zb Y) taylorWeight
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' (u • Q (e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)))
            (liftC (R.toStepTowerG.step k hk N₁ ν β p₁).hG' ((R.toStepTowerG.step k hk N₁ ν β p₁).maskUC z (Q (e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N))))
            (e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N)) 0‖ ≤
            3 * (energyBdScaled d L N (compWeight L (R.toStepTowerG.step k hk N₁ ν β p₁).a₁) k
              (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ) *
              Real.exp (-2 * R.κdec * treeLenCov (R.toStepTowerG.step k hk N₁ ν β p₁).G' 1 Y)) /
              ((lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * t₀)) ∧
    ∀ (D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N)
    (hDh : ∀ y i, D.h y i = ((R.toStepTowerG.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (_hD : XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D)
    {x : ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).E} (_hx : ‖x‖ ≤ p₁)
    (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1),
    HasDerivAt (fun t : ℂ => ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁))
        (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).markedTangentC z (s : ℂ) t x))
      (-(((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) 0 ∧
    (fderiv ℂ (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)))
        ((s : ℂ) • ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)
      (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
        (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
      -(((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
        deriv (markedBlockTerm (Ev zb Y) taylorWeight
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            ((s : ℂ) • ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
          (liftC ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).hG'
            (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
              (((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
          (rawOf ((R.toStepTowerG.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0)
      ) ∧
      -- (iv)
      (∀ S : StepSetting d L N₁ R.m₁ k N (rhoSepG d L R.m₁),
        S = R.toStepTowerG.step k hk N₁ ν β p₁ →
      ∃ (Ev : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ R.m₁ (k + 1)) →
          RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ) → ℂ)
        (M : RawData d L (N₁ * L ^ R.m₁) (k + 1) N → Matrix (S.U × Fin N) (S.U × Fin N) ℂ),
        (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
          (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 R.t)) ∧
        (∀ (D' : BgData S.G' N) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' (compWeight L 1) ν (k + 1) 1 R.t D' → ∀ x : S.E,
          (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D') *ᵥ yhat x) =
            (S.withDatum D' hD').shiftUC x) ∧
        ∀ (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E), ‖x‖ ≤ p₁ →
          (∀ (D' : BgData S.G' N) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' (compWeight L 1) ν (k + 1) 1 R.t D' →
            (S.withDatum D' hD').MarkRealAt R.t 2 x) ∧
          S.MarkedRootFamily z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev 1 ν R.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (3 * ‖energyBdScaled d L N (compWeight L 1) k
                (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ)‖ /
                ((lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 d L * (((L : ℕ) : ℝ) ^ (1 + R.m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * R.κdec - 1) * cBr d L))) (2 * R.κdec - 1) ∧
          S.MarkedRootAssembly z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev R.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (|β| * (3 * ‖energyBdScaled d L N (compWeight L 1) k
                (cK2' d L N (famConst d L R.BG₂ R.κ) * R.t) R.t (rho4 d L N R.BG R.κ)‖ /
                ((lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 d L * (((L : ℕ) : ℝ) ^ (1 + R.m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * R.κdec - 1) * cBr d L)))) (2 * R.κdec - 1)
      ) ∧
      -- (v)
      (∀ S : StepSetting d L N₁ R.m₁ k N (rhoSepG d L R.m₁),
        S = R.toStepTowerG.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
    ∃ (Jr : S.JointRep R.t (2 * p₁)) (𝒴 : Finset (Set (CTorus d L N₁ R.m₁ (k + 1))))
      (hdom : ∀ Y ∈ 𝒴, IsDj R.m₀ (k + 1) Y) (εU : ℝ),
      εU = β * prop33EpsEtaScaled d L N R.m₁ k R.m₀ 1 R.BG R.BG₂ R.κ R.t
        (lvRG d L N R.κ R.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / β) ∧ 0 ≤ εU ∧
      ∃ Aseg : ∀ e : physParam N S, e ∈ physFibre S S.a₁ S.ν R.t → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit R.m₀ hp).Ωb
            (4 * εU) (2 * R.κdec - 1) R.κ0 (2 * (K0 d L R.κ0 + 1)),
        (∀ (e : physParam N S) (he : e ∈ physFibre S S.a₁ S.ν R.t), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁))
                ((e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) e.2
                ((e.1 : RawData d L (N₁ * L ^ R.m₁) (k + 1) N), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit R.m₀ hp).restr x)) ∧
        (∀ g : Fld d L N₁ R.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈
              physFibre S S.a₁ S.ν R.t,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) p.1 x +
                S.WtwoC (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit R.m₀ hp).restr x))
      ) ∧
      -- (vi)
      (
    ∃ E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTowerG.step k hk N₁ ν β p₁) 1 z R.t
          ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (R.toStepTowerG.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N R.BG R.κ) D y T') ∧
      ∀ z (X : Set (CTorus d L N₁ R.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun e : rawSub N (R.toStepTowerG.step k hk N₁ ν β p₁).G' =>
            (E z).detGroupedC q₀ (bgOfRaw e.1 e.2) X)
          (((↑) : rawSub N (R.toStepTowerG.step k hk N₁ ν β p₁).G' →
              RawData d L (N₁ * L ^ R.m₁) (k + 1) N) ⁻¹'
            XiCRaw (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t) ∧
        AnalyticOnNhd ℂ (fun e : physParam N (R.toStepTowerG.step k hk N₁ ν β p₁) =>
            (E z).detGroupedC q₀ (bgOfRaw e.1.1 e.1.2) X)
          (physV (R.toStepTowerG.step k hk N₁ ν β p₁) 1 ν R.t) ∧
        (∀ D : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N,
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          ‖(E z).detGroupedC q₀ D X‖ ≤
            hullConst d L
                ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
              Real.exp (-hullRate d L
                ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                sizeJ 1 (k + 1) X)) ∧
        (∀ D D₂ : BgData (R.toStepTowerG.step k hk N₁ ν β p₁).G' N,
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D →
          XiCData (R.toStepTowerG.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 R.t D₂ →
          (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGroupedC q₀ D X = (E z).detGroupedC q₀ D₂ X)
      ) ∧
      -- (vii) renormalization lane
      (
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      (∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec) 1
          (fun D _ => bgClass (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) ν
            (renCK d L N R.BG R.κ * R.t) D)
          (fun D φ ξ => renC1On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t
            (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
          (fun D _ => bgFieldC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν
            (bgC0 d L N) D)) ∧
      (∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        HasLocPrinciple (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec) 1
          (fun _ ξ => pertClass (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
            (renCK d L N R.BG R.κ * (cK2 d L N * (8 * R.t * ‖ξ‖)))
            (bgK1 d L N * (xiC1 d * R.t) + renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t) * R.r₀
              + 2) (renMassU ν ξ))
          (fun _ v ξ => renC2On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1)
            (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
          (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
            bgMultC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D +
              (F ((D.Ψ, D.h), ξ)).2))) ∧
      (∀ p : (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N,
        HasLocPrinciple (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
                (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k
              (fam R.m₀ (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec) 1
          (fun _ ξ => {v | SupBounds (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) v
            (renCK d L N R.BG R.κ * (cK2 d L N * (8 * R.t * ‖ξ‖)))})
          (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))
      ) ∧
      (∀ {εR : ℝ}, εR ≤ R.r₀ → ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
    ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) εR
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
        (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
        (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec)
      (1 * ((d + 6) * (renCK d L N R.BG R.κ * R.t) ^ 2 *
        blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (blockSites d L N₁ R.m₁ (k + 1) k z)) *
        εR ^ 1)
      (fun D ξ => renC1On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t
        (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h
        (bgFieldC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D) ξ) term
      ) ∧
      (∀ {εR : ℝ}, 0 ≤ εR → εR ≤ R.r₀ → ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν R.t) εR
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
        (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀
        (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀ k (fam R.m₀ (blockSite k z))))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) R.m₀) (3 / 2 * R.κdec)
      (1 * (17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * R.t) +
        renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t) * R.r₀ + 2)) *
        (renCK d L N R.BG R.κ * cK2 d L N * (8 * R.t)) ^ 2)) *
        blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (blockSites d L N₁ R.m₁ (k + 1) k z)) *
        εR ^ 2)
      (fun D ξ => renC2On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1)
        (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
        (bgMultC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D +
          (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term
      ) := by
  obtain ⟨hull, C, hk0, hkdec, hk', hkout, hkH, hkapp, hkdet, hBh, hlh, hKc, hKall, hKtot,
    CE, CF, CE', CF', hCE, hCF, hCE', hCF', H⟩ := R.stepPieces_fromTowerRenSolG_rho hm₀ hLq hhull hA p
  obtain ⟨β₀, h3, -, Hk⟩ := H 1 one_pos
  refine ⟨hull, C, hk0, hkdec, hk', hkout, hkH, hkapp, hkdet, hBh, hlh, hKc, hKall, hKtot,
    β₀, CE, CF, CE', CF', h3, hCE, hCF, hCE', hCF', ?_⟩
  intro k hk N₁ _ hLN hN ν hν0 hν β hβ p₁ hp0 hp₁
  obtain ⟨hne, Hd⟩ := Hk k hk N₁ hLN hN ν hν0 hν β hβ p₁ hp0 hp₁
  refine ⟨hne, fun D => ?_⟩
  obtain ⟨⟨⟨𝒴, hdom, h1⟩, h1b, h1c, h1d⟩, h2m, rest⟩ := Hd D
  exact ⟨⟨⟨𝒴, hdom, fun g hg => by simpa only [one_mul] using h1 g hg⟩, h1b, h1c, h1d⟩,
    fun ε hε => h2m ε (by simpa only [one_mul] using hε), rest⟩
end Balaban.Inhabited
