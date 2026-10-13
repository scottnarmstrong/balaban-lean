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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# One tower, two chart radii

## Main results

* `xiCBounds_mono`, `xiC_mono_radius`, `xiCData_mono_radius`: the chart `Ξ^c(𝔹; σ, ε)` grows with
  the radius `ε`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization

section Mono

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {ν σ ε ε₂ : ℝ}

theorem xiCBounds_mono {Dr Dc : BgData G N} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hε0 : 0 < ε) (hε : ε ≤ ε₂)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ ε₂ Dr Dc Ψ'' h'' φr φc αr αc := by
  have h1 : σ * ε ≤ σ * ε₂ := mul_le_mul_of_nonneg_left hε hσ
  have h2 : σ ^ 2 * ε ≤ σ ^ 2 * ε₂ := mul_le_mul_of_nonneg_left hε (by positivity)
  have hε2 : 0 < ε₂ := hε0.trans_le hε
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  have e : ∀ e : ℝ, 0 < e → (σ * e) ^ 2 / e = σ ^ 2 * e := fun e he => by field_simp
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right h2 (by have := hp x; positivity))
  · exact (hb.mult x).trans_le h2
  · exact (hb.val x).trans_le hε
  · exact (hb.close x hx).trans_le h2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · have := hb.hAbs x hx
    rw [e ε hε0] at this
    rw [e ε₂ hε2]
    exact this.trans_le h2
  · exact (hb.hDot x).trans_le (pow_le_pow_left₀ (mul_nonneg hσ hε0.le) h1 2)

theorem xiC_mono_radius {n : ℕ} {a : ℕ → ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 0 ≤ σ) (hε : ε ≤ ε₂)
    (h : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n σ ε₂ Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hs, hε0, Dr, Dc, hXr, hC, hU, hb⟩ := h
  exact ⟨hs, hε0.trans_le hε, Dr, Dc, ⟨hXr.1, hXr.2.1, xiBounds_mono hσ hε0.le hε hXr.2.2⟩, hC, hU,
    xiCBounds_mono hσ hε0 hε hb⟩

end Mono

section MonoData

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν σ ε ε₂ : ℝ} {n : ℕ}

/-- **Radius monotonicity of the chart**: `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; σ, ε₂)` for `ε ≤ ε₂`. -/
theorem xiCData_mono_radius {D : BgData G N} (hσ : 0 ≤ σ) (hε : ε ≤ ε₂)
    (h : XiCData G a ν n σ ε D) : XiCData G a ν n σ ε₂ D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h
  exact ⟨Ψ₀, h₀, Ψ'', h'', xiC_mono_radius hσ hε hX, hR⟩

end MonoData

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

section Ambient

open Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}

/-- **The renormalized datum lies in the step chart at every radius `ε₂ ≥ εs`.**  This is
`renE0_theta_domain` followed by `xiCData_mono_radius`. -/
theorem renE0_theta_domain_of_le (S : StepSetting d L N₁ m₁ k N ϱ)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (εren εstep ε₂ r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀) (hle : εstep ≤ ε₂)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν εren D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k + 1) 1 ε₂ (renThetaDatum S εren D ξ) :=
  xiCData_mono_radius zero_le_one hle (renE0_theta_domain S H εren εstep r₀ hM D hD ξ hξ)

/-- **The ambient analytic extension, for a record at a chart radius `ε₂ ≥ εs`.**  As
`exists_renDetGrouped_ambient`, with the record `E` at any radius `ε₂ ≥ εstep`. -/
theorem exists_renDetGrouped_ambient_of_le {m₀ : ℕ}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {εstep ε₂ κ'' cdet : ℝ}
    (E : DetExpansionLocC S m₀ z ε₂ κ'' cdet)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (εren r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀) (hle : εstep ≤ ε₂) (hm : m₀ = 1)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
      AnalyticOnNhd ℂ F (expDom S.G' (XiCOneReal S.G' S.a S.ν εren) r₀) ∧
      ∀ (D : BgData S.G' N) (ξ : Fin 3 → ℂ), XiCOneReal S.G' S.a S.ν εren D → ‖ξ‖ < r₀ →
        F ((D.Ψ, D.h), ξ) = E.detGrouped (renThetaDatum S εren D ξ) X := by
  subst hm
  choose A hAan hAeq using E.analyticAt_raw
  refine ⟨fun q => ∑ T ∈ detCollarFibre 1 X,
    A T ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2), ?_, ?_⟩
  · rintro ⟨p, ξ'⟩ ⟨D, hD, hp, hξ⟩
    simp only at hp hξ
    subst hp
    have hθ := renE0_theta_domain_of_le S H εren εstep ε₂ r₀ hM hle D hD ξ' hξ
    refine Finset.analyticAt_fun_sum _ fun T _ => ?_
    have hTh := analyticOnNhd_renThetaRaw εren Set.univ ((D.Ψ, D.h), ξ') trivial
    have hA : AnalyticAt ℂ (A T) ((fun x i => (1 + renZeta εren ξ') * D.Ψ x i), D.h) :=
      hAan T _ hθ
    exact AnalyticAt.comp_of_eq hA hTh rfl
  · intro D ξ hD hξ
    have hθ := renE0_theta_domain_of_le S H εren εstep ε₂ r₀ hM hle D hD ξ hξ
    unfold DetExpansionLocC.detGrouped detCollarGrouped
    refine Finset.sum_congr rfl fun T _ => ?_
    exact hAeq T _ hθ

end Ambient

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
  have h := detExpansionLocC_scale_of_tower R.m₁_four (by have := R.t_pos; positivity)
    (Classical.choice R.core2) R.large_block R.dom_margin2 R.coer_margin2 R.δc_small R.det_z
    k hk N₁ h3N hN hν0 hν β p₁ R.δ
  refine ⟨h.1, fun z => ?_⟩
  have hz := h.2 z
  rw [StepTower.det_rate_den, StepTower.det_const_eq] at hz
  exact hz


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
  obtain ⟨hD0, hfam⟩ := R.detExpansion_scale k hk N₁ h3N hN hν0 hν β p₁
  choose E hE using hfam
  have hH := bgHyp_lv (k := k) R.m₁ hν0 hν
  have hM := thetaChartMargin_of_stepTowerRenSol R.toStepTowerRenSol
  have hN1 : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have hrate := towerDetRate_nonneg R.toStepTower
  have hconst := towerDetConst_nonneg R.toStepTower
  have hle := R.εs_le
  refine ⟨E, hE, fun z => renE0θ_det_zero R.t E z hD0, fun z X => ?_⟩
  obtain ⟨F, hFan, hFeq⟩ := exists_renDetGrouped_ambient_of_le (E z) hH R.t R.r₀ hM hle rfl X
  refine ⟨F, hFan, fun D hD => ⟨fun ξ hξ => ⟨hFeq D ξ hD hξ, ?_⟩, ?_⟩⟩
  · rw [hFeq D ξ hD hξ]
    exact (E z).detGrouped_bound (by norm_num) hN1 hconst hrate
      (renE0_theta_domain_of_le _ hH R.t _ (2 * R.t) R.r₀ hM hle D hD ξ hξ) X
  · have := hFeq D 0 hD (by simpa using R.r₀_pos)
    rwa [renThetaDatum_zero] at this

end TowerFamily

end Balaban.Inhabited
