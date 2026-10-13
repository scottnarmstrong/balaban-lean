/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.StepTowerThetaG
public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.TowerCoreRatesTwoRadii
public import Balaban.Inhabited.DetOutputTermsWitness
public import Balaban.Inhabited.RenormThetaChartTower
public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.StepTowerThetaDetG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# One tower, two chart radii

## Main results

* `StepTowerTheta`, `StepTowerTheta.toG`: the fixed `3, 3, 2` record with the determinant data at
  the doubled radius and its bridge to `StepTowerThetaG`;
* `StepTowerTheta.detExpansion_scale`, `StepTowerTheta.detGrouped_ambient`: the two-radii
  determinant lemmas, corollaries of the general ones in `StepTowerThetaDetG`.

The chart monotonicity in the radius (`xiCData_mono_radius`) and the ambient extension lemmas
(`renE0_theta_domain_of_le`, `exists_renDetGrouped_ambient_of_le`) are in `StepTowerThetaDetG`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization



open Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

theorem xiK2_pos' : 0 < xiK2 3 3 2 := by
  have := cK2_pos 3 3 2
  unfold xiK2; positivity

/-- **The shared tower with the determinant data at the doubled radius.**  Besides
`StepTowerRenSol`, the step core `FlCore` and the two determinant margins at the radius `2 t`, and
a parameter radius `r₀` so small that `ξ₂ · (3/2) · r₀ ≤ 1`: the chart radius
`t + ξ₂ (3/2) t r₀` of the renormalized datum is then at most `2 t`. -/
structure StepTowerTheta (κmin : ℝ) extends StepTowerRenSol κmin where
  core2 : Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ (2 * t)
    (levelKc 3 3) (Cchi 3 3) c₂ BG₂ (2 * t))
  dom_margin2 : decDomMargin 3 3 2 BG κ (xiC1 3 * (2 * t)) < δc
  coer_margin2 : K4 3 3 2 BG κ * (xiC1 3 * (2 * t)) < coerciveConst 3 / 2
  r₀_xi : xiK2 3 3 2 * ((3 / 2 : ℝ) * r₀) ≤ 1

/-- **The chart radius of the renormalized datum is at most `2 t`.** -/
theorem StepTowerTheta.εs_le {κmin : ℝ} (R : StepTowerTheta κmin) :
    R.t + xiK2 3 3 2 * ((3 / 2 : ℝ) * R.t * R.r₀) ≤ 2 * R.t := by
  have h := mul_le_mul_of_nonneg_left R.r₀_xi R.t_pos.le
  nlinarith

/-- **The bridge**: the fixed `3, 3, 2` record with the determinant data at the doubled radius is
a general one. -/
noncomputable def StepTowerTheta.toG {κmin : ℝ} (T : StepTowerTheta κmin) :
    StepTowerThetaG 3 3 2 κmin :=
  { T.toStepTowerRenSol.toG with
    core2 := flCore_three_transport T.core2
    dom_margin2 := T.dom_margin2
    coer_margin2 := T.coer_margin2
    r₀_xi := T.r₀_xi }

namespace StepTowerTheta

variable {κmin : ℝ} (T : StepTowerTheta κmin)

@[simp] theorem toG_toStepTowerRenSolG :
    T.toG.toStepTowerRenSolG = T.toStepTowerRenSol.toG := rfl
@[simp] theorem toG_r₀ : T.toG.r₀ = T.r₀ := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl

end StepTowerTheta

/-- A general tower with the determinant data at the doubled radius at `3, 3, 2` with
`κ₀ = a_Ent + 2` and `m₀ = 1` gives a fixed one. -/
theorem StepTowerThetaG.nonempty_fixed_of_three {κmin : ℝ} (T : StepTowerThetaG 3 3 2 κmin)
    (h0 : T.κ0 = aEnt 3 3 + 2) (hm : T.m₀ = 1) : Nonempty (StepTowerTheta κmin) := by
  have hcore : Nonempty (FlCore 2 (Gp T.m₁ (rhoSep T.m₁)) (Hm T.m₁ (rhoSep T.m₁))
      1 nuW T.c T.BG T.κ (2 * T.t) (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ (2 * T.t)) := by
    have h := T.core2
    rw [νref_three] at h
    have e := rhoSepG_three (m₁ := T.m₁)
    have key : ∀ ϱ : ℝ, ϱ = rhoSepG 3 3 T.m₁ →
        Nonempty (FlCore 2 (Gp T.m₁ ϱ) (Hm T.m₁ ϱ) 1 nuW T.c T.BG T.κ (2 * T.t)
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ (2 * T.t)) := by
      intro ϱ hϱ; subst hϱ; exact h
    exact key _ e.symm
  exact ⟨StepTowerTheta.mk (StepTowerRenSol.mk (StepTowerRenEnd.mk
    (StepTowerRen.mk (T.toStepTowerG.ofThree h0 hm)
      T.ren_margin T.r₀ T.r₀_pos T.r₀_le T.D₀_le_one T.D₀_le_star T.D₁_le_star) T.end_margin)
    T.sol_margin T.sol_K T.sol_ζ) hcore T.dom_margin2 T.coer_margin2 T.r₀_xi⟩

/-- **The record is inhabited** for every `κmin`. -/
theorem exists_stepTowerTheta (κmin : ℝ) : Nonempty (StepTowerTheta κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerThetaG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerThetaG.nonempty_fixed_of_three T (h0 (by simp; linarith)) hm

/-- The tower with the renormalization margins, `K₁ ξ₁ t < δ_*`, and the core and determinant
margins at the radius `2 t`. -/
theorem exists_stepTowerRen_two (κmin : ℝ) :
    ∃ R : StepTowerRen κmin, bgK1 3 3 2 * (xiC1 3 * R.t) < deltaStar 3 3 2 ∧
      Nonempty (FlCore 2 (Gp R.m₁ (rhoSep R.m₁)) (Hm R.m₁ (rhoSep R.m₁)) 1 nuW R.c R.BG R.κ
        (2 * R.t) (levelKc 3 3) (Cchi 3 3) R.c₂ R.BG₂ (2 * R.t)) ∧
      decDomMargin 3 3 2 R.BG R.κ (xiC1 3 * (2 * R.t)) < R.δc ∧
      K4 3 3 2 R.BG R.κ * (xiC1 3 * (2 * R.t)) < coerciveConst 3 / 2 := by
  obtain ⟨T⟩ := exists_stepTowerTheta κmin
  exact ⟨T.toStepTowerRen, T.sol_margin, T.core2, T.dom_margin2, T.coer_margin2⟩



section TowerFamily

/-- **The determinant family at every scale, at chart radius `2 t`.**  For every scale
`k ≥ 1`, `3 ∣ N₁`, `5 < N₁`, `0 ≤ ν`, `ν 3^{2(k+1)} ≤ 1`: the datum of the step lies in the chart at
radius `2 t`, and for every root `z` the record has an element at radius `2 t` with the same
rate and constant as in `detExpansionLocC_scale_fromTower` and the same term formula. -/
theorem StepTowerTheta.detExpansion_scale {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 (2 * R.t)
        (R.toStepTower.step k hk N₁ ν β p₁).D' ∧
      ∀ z, ∃ E : DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
        ∀ D T', E.term D T' = ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 R.BG R.κ) D y T' := by
  have h := R.toG.detExpansion_scale k hk N₁ h3N hN hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTowerTheta.toG_m₁, StepTowerTheta.toG_κ, StepTowerTheta.toG_t,
    StepTowerTheta.toG_BG] at h
  have e1 : (R.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate R.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 R.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) = towerDetConst R.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  exact h


/-- **The determinant part of `E0θ` on the renormalization domain, at the tower.**  At every scale
there is a family `E z` of determinant records at chart radius `2 t` with the term formula, and

* the value at `ξ = 0`: `renE0θ_det R.t E z S.D' 0` is the determinant term
  `-(1/2) ∑_y ∑_i log A_C(y, i)(y, i)` of the step;
* for every root `z` and hull `X` an ambient function `F`, analytic on the renormalization domain
  `expDom (XiCOneReal … R.t) R.r₀`, equal there to the regrouped determinant term at the
  renormalized datum, bounded there by `C_hull e^{-λ_hull sizeJ X}`, and equal at `ξ = 0` to the
  regrouped term at the datum itself. -/
theorem StepTowerTheta.detGrouped_ambient {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 R.BG R.κ) D y T') ∧
      (∀ z, renE0θ_det R.t E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
            (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))))
        (X : Set (CTorus 3 3 N₁ R.m₁ (k + 1))),
        ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) → ℂ,
          AnalyticOnNhd ℂ F (expDom (R.toStepTower.step k hk N₁ ν β p₁).G'
            (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν R.t)
            R.r₀) ∧
          ∀ (D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2),
            XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν R.t D →
            (∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
              F ((D.Ψ, D.h), ξ) =
                (E z).detGrouped (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ) X ∧
              ‖F ((D.Ψ, D.h), ξ)‖ ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
                Real.exp (-hullRate 3 3 (towerDetRate R.κ) * sizeJ 1 (k + 1) X)) ∧
            F ((D.Ψ, D.h), 0) = (E z).detGrouped D X := by
  have h := R.toG.detGrouped_ambient k hk N₁ h3N hN hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTowerTheta.toG_m₁, StepTowerTheta.toG_κ, StepTowerTheta.toG_t,
    StepTowerTheta.toG_BG, StepTowerTheta.toG_r₀] at h
  have e1 : (R.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate R.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 R.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) = towerDetConst R.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  exact h

end TowerFamily

end Balaban.Inhabited
