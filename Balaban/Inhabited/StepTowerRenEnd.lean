/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRen
public import Balaban.Fluctuation.RenormEndpointSharp
public import Balaban.Fluctuation.RenormPertClass
public import Balaban.Fluctuation.RenormSharedClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower with the endpoint margin

`StepTowerRenEnd κmin` extends `StepTowerRen κmin` by the margin
`K₂'(B_fam) (b_* t r₀) ≤ c₆` (the sharp bound at radius `r₀` fits in the ball `c₆`).
`StepTowerRen.shrink` shows that all landed margins persist when `r₀` decreases, and
`exists_stepTowerRenEnd` shows that the record is inhabited for every `κmin`.

At every scale of such a tower, `renDec_one_unique_sharp_scale_of_tower` gives the endpoint
`s = 1` and `renDec_pertClass_scale_of_tower` the class bound at `c_K = renCK`, `B = 8 t`, with no
margin hypothesis.  The radius `r_F` of the renormalized solution is not a field of the record:
`exists_isRenSol` needs, besides the scale (`BgHyp`, `hsm`, `hc1`, all given by `FlCore` at each
scale), the numeric margins `K₁ ξ₁ t + 3 r_F ≤ δ_*` and `8 t r_F ≤ δ_*`, and the first is not
implied by the fields of `StepTower` (`bg1_cap` bounds `K₁ ξ₁ t` by `c₁`, not by `δ_*`).  So the
endpoint theorem takes `IsRenSol … r_F …` and `r₀ ≤ r_F` as scale hypotheses.

Not here: locality and the fields `locC2`, `locDφ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- The coefficient `b_* t` of the sharp bound is nonnegative at the tower constants. -/
theorem StepTowerRen.coef_nonneg {κmin : ℝ} (R : StepTowerRen κmin) :
    0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t := by
  obtain ⟨hC₀⟩ := R.core
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 (by norm_num : 0 < 3)
  have hK1 := bgK1_pos 3 3 2
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  have := R.t_pos
  positivity

/-- **The margins of the record persist when `r₀` decreases.** -/
def StepTowerRen.shrink {κmin : ℝ} (R : StepTowerRen κmin) (r : ℝ) (hr0 : 0 < r)
    (hr : r ≤ R.r₀) : StepTowerRen κmin :=
  { R with
    r₀ := r
    r₀_pos := hr0
    r₀_le := hr.trans R.r₀_le
    D₀_le_one := by have := R.D₀_le_one; linarith
    D₀_le_star := by have := R.D₀_le_star; linarith
    D₁_le_star := by
      have h := R.D₁_le_star
      have hb := R.coef_nonneg
      have : (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * r ≤
          (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * R.r₀ :=
        mul_le_mul_of_nonneg_left hr hb
      linarith }

/-- The shrunk record has the same constants. -/
@[simp] theorem StepTowerRen.shrink_r₀ {κmin : ℝ} (R : StepTowerRen κmin) (r : ℝ) (hr0 : 0 < r)
    (hr : r ≤ R.r₀) : (R.shrink r hr0 hr).r₀ = r := rfl

/-- The shared tower with the renormalization margins and the endpoint margin. -/
structure StepTowerRenEnd (κmin : ℝ) extends StepTowerRen κmin where
  end_margin : cK2' 3 3 2 (famConst 3 3 BG κ) *
    ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 BG κ + bgK1 3 3 2) * xiC1 3)) * t * r₀) ≤ c6 3 3 2

/-- **The record with the endpoint margin is inhabited** for every `κmin`. -/
theorem exists_stepTowerRenEnd (κmin : ℝ) : Nonempty (StepTowerRenEnd κmin) := by
  obtain ⟨R⟩ := exists_stepTowerRen κmin
  obtain ⟨hC₀⟩ := R.core
  have hd : 0 < 3 := by norm_num
  have hB1 := famConst_ge_one (L := 3) hC₀.hS.fam.2.1 R.κ hd
  have hK2 : 0 ≤ cK2' 3 3 2 (famConst 3 3 R.BG R.κ) :=
    cK2'_nonneg (d := 3) (L := 3) (N := 2) (B := famConst 3 3 R.BG R.κ) (by linarith)
  have hc6 : 0 < c6 3 3 2 := c6_pos (d := 3) (L := 3) (N := 2) hd
  have hA : 0 ≤ cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) :=
    mul_nonneg hK2 R.coef_nonneg
  obtain ⟨r, hr0, hr1, -, hr2, -⟩ := exists_radius_margins hA hc6 hc6 R.r₀_pos
    R.r₀_pos
  refine ⟨{ R.shrink r hr0 hr1 with end_margin := ?_ }⟩
  simp only [StepTowerRen.shrink]
  calc _ = cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) * r := by ring
    _ ≤ c6 3 3 2 := hr2

/-- The `FlCore` of the tower at a scale. -/
theorem StepTowerRen.flCore_scale {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    FlCore 2 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (lvLow N₁ R.m₁ k (rhoSep R.m₁)) 1 ν R.c
      R.BG R.κ R.t (levelKc 3 3) (Cchi 3 3) R.c₂ R.BG₂ R.t := by
  obtain ⟨hC₀⟩ := R.core
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) R.m₁_four hN hν0 hν
  have hHB := bgHyp_lv (k := k) R.m₁ hν0 hν
  exact flCore_level_transfer hC₀ hSD (opSetting_lv R.m₁_four hN hν0 hν) (isLevel_lvLow hk)
    isLevel_lvTop hHB

/-- **`renDec_one_unique_sharp` at every scale of the tower with the endpoint margin**: the cut
family at `s = 1` is the renormalized solution `F` (any `IsRenSol` solution map of radius
`rF ≥ r₀`), with no margin hypothesis. -/
theorem renDec_one_unique_sharp_scale_of_tower {κmin : ℝ} (R : StepTowerRenEnd κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) {rF B : ℝ}
    {F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)}
    (hF : IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t rF B F)
    (hrF : R.r₀ ≤ rF) :
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) :=
  renDec_one_unique_sharp (R.flCore_scale k hk N₁ hN hν0 hν) R.r₀_pos R.r₀_le X₁ hF hrF
    R.D₀_le_one R.D₀_le_star R.D₁_le_star R.end_margin

/-- **`renDec_pertClass` at every scale of the tower** at the shared constant `c_K = renCK` and
`B = 8 t`: the constant inequality (CB) is `renCK_mul_ge` times `t`. -/
theorem renDec_pertClass_scale_of_tower {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => F p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ →
        ∀ s ∈ polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ)
          (fun _ => Real.exp R.κ),
          SupBounds (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (F (rawOf D, ξ) s).1
            (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖))) ∧
          ((F (rawOf D, ξ) s).1,
            decBgMult (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (rho4 3 3 2 R.BG R.κ)
              (extParams (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁
                (s ∘ (renLabelEquiv (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁).symm)) D +
              (F (rawOf D, ξ) s).2) ∈
            pertClass (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (renCK 3 3 2 R.BG R.κ * (cK2 3 3 2 * (8 * R.t * ‖ξ‖)))
              (bgK1 3 3 2 * (xiC1 3 * R.t) + renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) * R.r₀ + 2)
              (renMassU ν ξ) := by
  obtain ⟨hC₀⟩ := R.core
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 (by norm_num : 0 < 3)
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  have hcK : 1 ≤ renCK 3 3 2 R.BG R.κ := by
    have := renCK_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    have := mul_nonneg hK4.le hX
    linarith
  have hCB : cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) ≤
      renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * R.t) := by
    have h := renCK_mul_ge (d := 3) (L := 3) (N := 2) (BG := R.BG) (κ := R.κ)
    have := mul_le_mul_of_nonneg_right h R.t_pos.le
    nlinarith
  have := renDec_pertClass (R.flCore_scale k hk N₁ hN hν0 hν) R.r₀_pos R.r₀_le X₁
    R.D₀_le_one R.D₀_le_star R.D₁_le_star (B := 8 * R.t) (cK := renCK 3 3 2 R.BG R.κ)
    (by have := R.t_pos; positivity) hcK hCB
  simpa [mul_assoc] using this

end Balaban.Inhabited
