/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormPot

/-!
# Real inequalities for the explicit bounds

`smallBnd_le`: `smallBnd ≤ C M P² t⁶ σ^{3-α₁} (ε/ρ)²` and `tailBnd_le` for large polymers.
-/

@[expose] public section

namespace Balaban.SmallField

/-- Facts on the power `σ^{3-α₁}` used throughout. -/
structure SigPow (σ α₁ Tσ Sσ : ℝ) : Prop where
  pos : 0 < σ
  le_one : σ ≤ 1
  cube : σ ^ 3 ≤ Tσ
  quart : σ ^ 4 ≤ Tσ
  prod : σ * Sσ = Tσ
  sq : Sσ * Sσ ≤ Tσ
  Snn : 0 ≤ Sσ

theorem sigPow (σ α₁ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    SigPow σ α₁ (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) := by
  refine ⟨hσ, hσ1, ?_, ?_, ?_, ?_, (Real.rpow_pos_of_pos hσ _).le⟩
  · have := Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (show 3 - α₁ ≤ 3 by linarith)
    simpa using this
  · have := Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (show 3 - α₁ ≤ 4 by linarith)
    simpa using this
  · rw [← Real.rpow_one_add' hσ.le (by linarith)]; congr 1; ring
  · rw [← Real.rpow_add hσ]
    exact Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)

theorem cube_term {c Λ M r σ t P Tσ : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hr : 0 < r) (hrΛ : r ≤ Λ)
    (hσ : 0 < σ) (hσ3 : σ ^ 3 ≤ Tσ) (ht : 1 ≤ t) (hP : 1 ≤ P) :
    2 * M * (c * r * σ * t) ^ 3 ≤ 2 * c ^ 3 * Λ * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have ht3 : t ^ 3 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
  have hc3 : 0 ≤ c ^ 3 := by positivity
  have hT0 : 0 ≤ Tσ := le_trans (by positivity) hσ3
  have hΛ0 : 0 ≤ Λ := hr.le.trans hrΛ
  calc 2 * M * (c * r * σ * t) ^ 3 = 2 * c ^ 3 * M * (r ^ 2 * r * σ ^ 3 * t ^ 3 * 1) := by ring
    _ ≤ 2 * c ^ 3 * M * (r ^ 2 * Λ * Tσ * t ^ 6 * P ^ 2) := by
        gcongr
    _ = _ := by ring

theorem zr_le {C1 κ1 σ t r : ℝ} (hC1 : 0 ≤ C1) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (ht : 1 ≤ t) (hr : 0 < r) :
    (C1 * σ ^ 2 + κ1 * t * σ) * r ≤ (C1 + κ1) * r * σ * t := by
  have h1 : σ ^ 2 ≤ σ * t := by nlinarith
  have h2 : C1 * σ ^ 2 ≤ C1 * (σ * t) := mul_le_mul_of_nonneg_left h1 hC1
  have : (C1 * σ ^ 2 + κ1 * t * σ) ≤ (C1 + κ1) * σ * t := by nlinarith
  calc (C1 * σ ^ 2 + κ1 * t * σ) * r ≤ ((C1 + κ1) * σ * t) * r := mul_le_mul_of_nonneg_right this hr.le
    _ = _ := by ring

theorem z0r_le {C1 κ1 σ t r : ℝ} (hC1 : 0 ≤ C1) (hκ : 0 ≤ κ1) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (ht : 1 ≤ t) (hr : 0 < r) : C1 * σ ^ 2 * r ≤ (C1 + κ1) * r * σ * t := by
  have := zr_le (κ1 := κ1) hC1 hσ hσ1 ht hr
  have h0 : 0 ≤ κ1 * t * σ * r := by positivity
  nlinarith

/-- The hypotheses of the real inequalities. -/
structure NumCtx (N : ℕ) (A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ) : Prop where
  hA : 0 ≤ A
  hΛ : 1 ≤ Λ
  hKc : 0 ≤ Kc
  hM : 0 ≤ M
  hρ : 0 < ρ
  hρ1 : ρ ≤ 1
  hr : 0 < r
  hrΛ : r ≤ Λ
  hν : 0 ≤ ν
  hνσ : ν ≤ σ ^ 2
  ht : 1 ≤ t
  hP : 1 ≤ P
  hK0 : 0 ≤ K₂
  hK : K₂ ≤ Kc * Sσ * (r * ρ)
  hS : SigPow σ α₁ Tσ Sσ

section Num

variable {N : ℕ} {A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ}

/-- The common size `Y = M P² t⁶ σ^{3-α₁} r²`. -/
def sizeY (M P t Tσ r : ℝ) : ℝ := M * P ^ 2 * t ^ 6 * Tσ * r ^ 2

theorem NumCtx.hT0 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) : 0 ≤ Tσ :=
  le_trans (by have := h.hS.pos; positivity) h.hS.cube

theorem NumCtx.hY (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) : 0 ≤ sizeY M P t Tσ r := by
  have := h.hT0; have := h.hM; have := h.hr; have := h.ht; unfold sizeY
  have : 0 < t := by linarith
  positivity

theorem NumCtx.t1 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    2 * M * ((sZ0 N σ (r * ρ) + sD N A σ (r * ρ) t) / ρ) ^ 3 ≤
      2 * (cC1 N + cK1 N A) ^ 3 * Λ * sizeY M P t Tσ r := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := h.hA; positivity
  have eq : (sZ0 N σ (r * ρ) + sD N A σ (r * ρ) t) / ρ =
      (cC1 N * σ ^ 2 + cK1 N A * t * σ) * r := by
    have := h.hρ
    unfold sZ0 sD; field_simp
  rw [eq]
  have h1 := zr_le (κ1 := cK1 N A) hC1 h.hS.pos h.hS.le_one h.ht h.hr
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hM := h.hM
  have h0 : 0 ≤ (cC1 N * σ ^ 2 + cK1 N A * t * σ) * r := by
    have := h.hS.pos; have := h.hr
    positivity
  calc 2 * M * ((cC1 N * σ ^ 2 + cK1 N A * t * σ) * r) ^ 3
      ≤ 2 * M * (((cC1 N + cK1 N A) * r * σ * t)) ^ 3 := by gcongr
    _ ≤ _ := by
        have := cube_term (c := cC1 N + cK1 N A) (Λ := Λ) (M := M) (r := r) (σ := σ) (t := t)
          (P := P) (Tσ := Tσ) (by positivity) h.hM h.hr h.hrΛ h.hS.pos h.hS.cube h.ht h.hP
        exact this

theorem NumCtx.t2 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    2 * M * (sZ0 N σ (r * ρ) / ρ) ^ 3 ≤
      2 * (cC1 N + cK1 N A) ^ 3 * Λ * sizeY M P t Tσ r := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := h.hA; positivity
  have eq : sZ0 N σ (r * ρ) / ρ = cC1 N * σ ^ 2 * r := by
    have := h.hρ
    unfold sZ0; field_simp
  rw [eq]
  have h1 := z0r_le (κ1 := cK1 N A) hC1 hK1 h.hS.pos h.hS.le_one h.ht h.hr
  have hM := h.hM
  have h0 : 0 ≤ cC1 N * σ ^ 2 * r := by
    have := h.hS.pos; have := h.hr; positivity
  calc 2 * M * (cC1 N * σ ^ 2 * r) ^ 3
      ≤ 2 * M * (((cC1 N + cK1 N A) * r * σ * t)) ^ 3 := by gcongr
    _ ≤ _ := by
        have := cube_term (c := cC1 N + cK1 N A) (Λ := Λ) (M := M) (r := r) (σ := σ) (t := t)
          (P := P) (Tσ := Tσ) (by positivity) h.hM h.hr h.hrΛ h.hS.pos h.hS.cube h.ht h.hP
        exact this

theorem NumCtx.t3 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    4 * M * sZ0 N σ (r * ρ) * sD N A σ (r * ρ) t / ρ ^ 2 ≤
      4 * cC1 N * cK1 N A * sizeY M P t Tσ r := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := h.hA; positivity
  have hρ := h.hρ
  have eq : 4 * M * sZ0 N σ (r * ρ) * sD N A σ (r * ρ) t / ρ ^ 2 =
      4 * cC1 N * cK1 N A * M * (t * σ ^ 3 * r ^ 2) := by
    unfold sZ0 sD; field_simp
  rw [eq]
  have hσ := h.hS.pos
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hM := h.hM
  have hcube := h.hS.cube
  have ht1 : t ≤ t ^ 6 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
  have hP2' : 1 ≤ P ^ 2 := by nlinarith [h.hP]
  have hT0 := h.hT0
  calc 4 * cC1 N * cK1 N A * M * (t * σ ^ 3 * r ^ 2)
      = 4 * cC1 N * cK1 N A * M * (t * σ ^ 3 * r ^ 2 * 1) := by ring
    _ ≤ 4 * cC1 N * cK1 N A * M * (t ^ 6 * Tσ * r ^ 2 * P ^ 2) := by
        gcongr
    _ = _ := by unfold sizeY; ring

/-- The constant `c₃ = 2 + N κ₁² Λ`. -/
def cC3 (N : ℕ) (A Λ : ℝ) : ℝ := 2 + N * cK1 N A ^ 2 * Λ

theorem NumCtx.F_le (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    sF N A σ (r * ρ) t ≤ cC3 N A Λ * t ^ 2 * σ ^ 2 * (r * ρ) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hρ := h.hρ
  have hr := h.hr
  have hσ := h.hS.pos
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hrρ : r * ρ ≤ Λ := by nlinarith [h.hrΛ, h.hρ1]
  have hrρ0 : 0 < r * ρ := by positivity
  have ht2 : 1 ≤ t ^ 2 := by nlinarith [h.ht]
  have e : sF N A σ (r * ρ) t =
      2 * (σ ^ 2 * (r * ρ)) + N * cK1 N A ^ 2 * t ^ 2 * σ ^ 2 * (r * ρ) ^ 2 := by
    unfold sF sD; ring
  rw [e]
  unfold cC3
  have h1 : 2 * (σ ^ 2 * (r * ρ)) ≤ 2 * t ^ 2 * σ ^ 2 * (r * ρ) := by
    have : 0 ≤ σ ^ 2 * (r * ρ) := by positivity
    nlinarith
  have h2 : (N : ℝ) * cK1 N A ^ 2 * t ^ 2 * σ ^ 2 * (r * ρ) ^ 2 ≤
      N * cK1 N A ^ 2 * Λ * t ^ 2 * σ ^ 2 * (r * ρ) := by
    have hq : (r * ρ) ^ 2 ≤ Λ * (r * ρ) := by nlinarith
    have hc : 0 ≤ (N : ℝ) * cK1 N A ^ 2 * t ^ 2 * σ ^ 2 := by positivity
    calc (N : ℝ) * cK1 N A ^ 2 * t ^ 2 * σ ^ 2 * (r * ρ) ^ 2
        ≤ N * cK1 N A ^ 2 * t ^ 2 * σ ^ 2 * (Λ * (r * ρ)) := mul_le_mul_of_nonneg_left hq hc
      _ = _ := by ring
  nlinarith

theorem NumCtx.t4 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    P * (M / ρ) * sEe N A σ (r * ρ) t ≤ cC3 N A Λ * (1 + cC3 N A Λ) * sizeY M P t Tσ r := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hρ := h.hρ
  have hr := h.hr
  have hσ := h.hS.pos
  have hM := h.hM
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hP0 : 0 < P := lt_of_lt_of_le one_pos h.hP
  have hc3 : 0 ≤ cC3 N A Λ := by unfold cC3 cK1; have := h.hA; have := h.hΛ; positivity
  have hF := h.F_le
  have hF0 : 0 ≤ sF N A σ (r * ρ) t := by unfold sF sD; positivity
  have hτ : 0 ≤ σ ^ 2 * (r * ρ) := by positivity
  have hE : sEe N A σ (r * ρ) t ≤ cC3 N A Λ * (1 + cC3 N A Λ) * t ^ 4 * σ ^ 4 * (r * ρ) ^ 2 := by
    unfold sEe
    set F := sF N A σ (r * ρ) t
    set c3 := cC3 N A Λ
    have ht2 : 1 ≤ t ^ 2 := by nlinarith [h.ht]
    have hb : F ≤ c3 * t ^ 2 * (σ ^ 2 * (r * ρ)) := by linarith
    have hb0 : 0 ≤ c3 * t ^ 2 * (σ ^ 2 * (r * ρ)) := by positivity
    calc F * (σ ^ 2 * (r * ρ)) + F ^ 2
        ≤ c3 * t ^ 2 * (σ ^ 2 * (r * ρ)) * (σ ^ 2 * (r * ρ)) +
          (c3 * t ^ 2 * (σ ^ 2 * (r * ρ))) ^ 2 := by
          gcongr
      _ = c3 * t ^ 2 * σ ^ 4 * (r * ρ) ^ 2 * (1 + c3 * t ^ 2) := by ring
      _ ≤ c3 * t ^ 2 * σ ^ 4 * (r * ρ) ^ 2 * ((1 + c3) * t ^ 2) := by
          gcongr
          nlinarith
      _ = _ := by ring
  have hPM : 0 ≤ P * (M / ρ) := by positivity
  calc P * (M / ρ) * sEe N A σ (r * ρ) t
      ≤ P * (M / ρ) * (cC3 N A Λ * (1 + cC3 N A Λ) * t ^ 4 * σ ^ 4 * (r * ρ) ^ 2) := by
        gcongr
    _ = cC3 N A Λ * (1 + cC3 N A Λ) * (M * P * t ^ 4 * σ ^ 4 * r ^ 2 * ρ) := by
        field_simp
    _ ≤ cC3 N A Λ * (1 + cC3 N A Λ) * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2 * 1) := by
        have hT := h.hS.quart
        have hT0 := h.hT0
        have ht4 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
        have hPP : P ≤ P ^ 2 := by nlinarith [h.hP]
        have hρ1 := h.hρ1
        have hc3' : 0 ≤ cC3 N A Λ * (1 + cC3 N A Λ) := by positivity
        gcongr
    _ = _ := by unfold sizeY; ring

theorem NumCtx.t5 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    2 * P ^ 2 * M * sF N A σ (r * ρ) t ^ 2 / ρ ^ 2 ≤ 2 * cC3 N A Λ ^ 2 * sizeY M P t Tσ r := by
  have hρ := h.hρ
  have hr := h.hr
  have hσ := h.hS.pos
  have hM := h.hM
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hP0 : 0 < P := lt_of_lt_of_le one_pos h.hP
  have hF := h.F_le
  have hF0 : 0 ≤ sF N A σ (r * ρ) t := by unfold sF sD; have := h.hA; positivity
  have hT := h.hS.quart
  have hT0 := h.hT0
  have ht4 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
  have hc3 : 0 ≤ cC3 N A Λ := by unfold cC3 cK1; have := h.hA; have := h.hΛ; positivity
  calc 2 * P ^ 2 * M * sF N A σ (r * ρ) t ^ 2 / ρ ^ 2
      ≤ 2 * P ^ 2 * M * (cC3 N A Λ * t ^ 2 * σ ^ 2 * (r * ρ)) ^ 2 / ρ ^ 2 := by gcongr
    _ = 2 * cC3 N A Λ ^ 2 * (M * P ^ 2 * t ^ 4 * σ ^ 4 * r ^ 2) := by field_simp
    _ ≤ 2 * cC3 N A Λ ^ 2 * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by gcongr
    _ = _ := by unfold sizeY; ring

theorem NumCtx.t6 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    ν / 2 * P * (4 * M / ρ ^ 2) * (N * sD N A σ (r * ρ) t ^ 2) ≤
      2 * N * cK1 N A ^ 2 * sizeY M P t Tσ r := by
  have hρ := h.hρ
  have hr := h.hr
  have hσ := h.hS.pos
  have hM := h.hM
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hP0 : 0 < P := lt_of_lt_of_le one_pos h.hP
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hT := h.hS.quart
  have hT0 := h.hT0
  have ht2 : t ^ 2 ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
  have hPP : P ≤ P ^ 2 := by nlinarith [h.hP]
  have hν := h.hν
  have hνσ := h.hνσ
  have hκ : 0 ≤ cK1 N A ^ 2 := sq_nonneg _
  calc ν / 2 * P * (4 * M / ρ ^ 2) * (N * sD N A σ (r * ρ) t ^ 2)
      = 2 * N * cK1 N A ^ 2 * (ν * (P * M * t ^ 2 * σ ^ 2 * r ^ 2)) := by
        unfold sD; field_simp; ring
    _ ≤ 2 * N * cK1 N A ^ 2 * (σ ^ 2 * (P * M * t ^ 2 * σ ^ 2 * r ^ 2)) := by gcongr
    _ = 2 * N * cK1 N A ^ 2 * (P * M * t ^ 2 * σ ^ 4 * r ^ 2) := by ring
    _ ≤ 2 * N * cK1 N A ^ 2 * (P ^ 2 * M * t ^ 6 * Tσ * r ^ 2) := by gcongr
    _ = _ := by unfold sizeY; ring

theorem NumCtx.t7 (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    P ^ 2 * (M / ρ ^ 2) * sEb N A σ (r * ρ) K₂ t ≤
      (38400 * N ^ 3 * A ^ 3 * Kc + 57600 * N ^ 3 * A ^ 4 * Kc ^ 2) * sizeY M P t Tσ r := by
  have hρ := h.hρ
  have hr := h.hr
  have hσ := h.hS.pos
  have hM := h.hM
  have hA := h.hA
  have hKc := h.hKc
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hP0 : 0 < P := lt_of_lt_of_le one_pos h.hP
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hS := h.hS
  have hK := h.hK
  have hK0 := h.hK0
  have ht3 : t ^ 3 ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
  have ht4 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
  have hT0 := h.hT0
  have hε : 0 ≤ r * ρ := by positivity
  have h1 : σ * (r * ρ) * K₂ ≤ Kc * Tσ * (r * ρ) ^ 2 := by
    calc σ * (r * ρ) * K₂ ≤ σ * (r * ρ) * (Kc * Sσ * (r * ρ)) := by gcongr
      _ = Kc * (σ * Sσ) * (r * ρ) ^ 2 := by ring
      _ = _ := by rw [hS.prod]
  have h2 : K₂ ^ 2 ≤ Kc ^ 2 * Tσ * (r * ρ) ^ 2 := by
    calc K₂ ^ 2 ≤ (Kc * Sσ * (r * ρ)) ^ 2 := by gcongr
      _ = Kc ^ 2 * (Sσ * Sσ) * (r * ρ) ^ 2 := by ring
      _ ≤ Kc ^ 2 * Tσ * (r * ρ) ^ 2 := by gcongr; exact hS.sq
  have e : sEb N A σ (r * ρ) K₂ t = 38400 * N ^ 3 * A ^ 3 * t ^ 3 * (σ * (r * ρ) * K₂) +
      57600 * N ^ 3 * A ^ 4 * t ^ 4 * K₂ ^ 2 := by
    unfold sEb; ring
  rw [e]
  have hc1 : 0 ≤ 38400 * (N : ℝ) ^ 3 * A ^ 3 * t ^ 3 := by positivity
  have hc2 : 0 ≤ 57600 * (N : ℝ) ^ 3 * A ^ 4 * t ^ 4 := by positivity
  have hPM : 0 ≤ P ^ 2 * (M / ρ ^ 2) := by positivity
  calc P ^ 2 * (M / ρ ^ 2) * (38400 * N ^ 3 * A ^ 3 * t ^ 3 * (σ * (r * ρ) * K₂) +
        57600 * N ^ 3 * A ^ 4 * t ^ 4 * K₂ ^ 2)
      ≤ P ^ 2 * (M / ρ ^ 2) * (38400 * N ^ 3 * A ^ 3 * t ^ 3 * (Kc * Tσ * (r * ρ) ^ 2) +
        57600 * N ^ 3 * A ^ 4 * t ^ 4 * (Kc ^ 2 * Tσ * (r * ρ) ^ 2)) := by gcongr
    _ = (38400 * N ^ 3 * A ^ 3 * Kc * t ^ 3 + 57600 * N ^ 3 * A ^ 4 * Kc ^ 2 * t ^ 4) *
          (M * P ^ 2 * Tσ * r ^ 2) := by field_simp
    _ ≤ (38400 * N ^ 3 * A ^ 3 * Kc * t ^ 6 + 57600 * N ^ 3 * A ^ 4 * Kc ^ 2 * t ^ 6) *
          (M * P ^ 2 * Tσ * r ^ 2) := by
        have : 0 ≤ M * P ^ 2 * Tσ * r ^ 2 := by positivity
        gcongr
    _ = _ := by unfold sizeY; ring

end Num

theorem smallBnd_le (N : ℕ) (A Λ Kc : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) (hKc : 0 ≤ Kc) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBnd N A M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hc3 : 0 ≤ cC3 N A Λ := by unfold cC3; positivity
  refine ⟨2 * (cC1 N + cK1 N A) ^ 3 * Λ + 2 * (cC1 N + cK1 N A) ^ 3 * Λ + 4 * cC1 N * cK1 N A +
    cC3 N A Λ * (1 + cC3 N A Λ) + 2 * cC3 N A Λ ^ 2 + 2 * N * cK1 N A ^ 2 +
    (38400 * N ^ 3 * A ^ 3 * Kc + 57600 * N ^ 3 * A ^ 4 * Kc ^ 2), by positivity, ?_⟩
  intro M ρ ν σ r K₂ t P Tσ Sσ α₁ hM hρ hρ1 hr hrΛ hν hνσ ht hP hK0 hK hS
  have h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁ :=
    ⟨hA, hΛ, hKc, hM, hρ, hρ1, hr, hrΛ, hν, hνσ, ht, hP, hK0, hK, hS⟩
  have e1 := h.t1
  have e2 := h.t2
  have e3 := h.t3
  have e4 := h.t4
  have e5 := h.t5
  have e6 := h.t6
  have e7 := h.t7
  unfold sizeY at e1 e2 e3 e4 e5 e6 e7
  unfold smallBnd
  linarith

theorem tailBnd_le (N : ℕ) (A Λ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cC1 N + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hΛ0 : 0 ≤ Λ := by linarith
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; positivity
  set c2 : ℝ := cC1 N + cK1 N A with hc2
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨(2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (16 * c2 ^ 4 * Λ ^ 2), by positivity, ?_⟩
  intro M ρ σ r t P Tσ Sσ α₁ hM hρ hr hrΛ ht hP htail hS
  have hσ := hS.pos
  have hσ1 := hS.le_one
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have hPP : P ≤ P ^ 2 := by nlinarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  -- first: tailBnd ≤ C M P² t²
  have h1 : tailBnd N A M ρ σ (r * ρ) t P ≤
      (2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (M * P ^ 2 * t ^ 2) := by
    unfold tailBnd
    have e : P * (σ ^ 2 * (r * ρ) / ρ) = P * σ ^ 2 * r := by field_simp
    have e2 : (σ * (r * ρ) / ρ) = σ * r := by field_simp
    rw [e, e2]
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
    have hr1 : r * σ ^ 2 ≤ Λ := by
      have := mul_le_mul_of_nonneg_left hσ2 hr.le
      linarith
    have hσr : (σ * r) ^ 2 ≤ Λ ^ 2 := by
      have : σ * r ≤ Λ := by nlinarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have a1 : P * σ ^ 2 * r ≤ Λ * (P ^ 2 * t ^ 2) := by
      have h1 : P * (σ ^ 2 * r) ≤ P * Λ := mul_le_mul_of_nonneg_left (by linarith) hP0.le
      have h2 : Λ * P ≤ Λ * P ^ 2 := mul_le_mul_of_nonneg_left hPP hΛ0
      have h3 : Λ * P ^ 2 ≤ Λ * (P ^ 2 * t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hΛ0
        nlinarith [sq_nonneg P]
      nlinarith
    have a2 : 6400 * (N : ℝ) ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * r) ^ 2 ≤
        6400 * N ^ 3 * A ^ 2 * Λ ^ 2 * (P ^ 2 * t ^ 2) := by
      have hc : 0 ≤ 6400 * (N : ℝ) ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 := by positivity
      calc 6400 * (N : ℝ) ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * r) ^ 2
          ≤ 6400 * N ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * Λ ^ 2 := mul_le_mul_of_nonneg_left hσr hc
        _ = _ := by ring
    have a3 : (2 : ℝ) ≤ 2 * (P ^ 2 * t ^ 2) := by nlinarith
    have : M * (2 + P * σ ^ 2 * r + 6400 * N ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * r) ^ 2) ≤
        M * ((2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (P ^ 2 * t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      linarith
    linarith [this]
  -- second: use the tail condition
  have h2 : 1 ≤ (2 * c2 * t * σ * r) ^ 4 := by
    have := htail
    exact one_le_pow₀ this.le
  have hT := hS.quart
  have hT0 : 0 ≤ Tσ := le_trans (by positivity) hS.cube
  have h3 : M * P ^ 2 * t ^ 2 ≤ 16 * c2 ^ 4 * Λ ^ 2 * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
    have hr4 : r ^ 4 ≤ Λ ^ 2 * r ^ 2 := by
      have : r ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hr.le hrΛ 2
      nlinarith [pow_pos hr 2]
    calc M * P ^ 2 * t ^ 2 = M * P ^ 2 * t ^ 2 * 1 := by ring
      _ ≤ M * P ^ 2 * t ^ 2 * (2 * c2 * t * σ * r) ^ 4 := by gcongr
      _ = 16 * c2 ^ 4 * (M * P ^ 2 * t ^ 6 * σ ^ 4 * r ^ 4) := by ring
      _ ≤ 16 * c2 ^ 4 * (M * P ^ 2 * t ^ 6 * Tσ * (Λ ^ 2 * r ^ 2)) := by gcongr
      _ = _ := by ring
  have hC : 0 ≤ 2 + Λ + 6400 * (N : ℝ) ^ 3 * A ^ 2 * Λ ^ 2 := by positivity
  calc _ ≤ (2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (M * P ^ 2 * t ^ 2) := h1
    _ ≤ (2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) *
        (16 * c2 ^ 4 * Λ ^ 2 * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hC
    _ = _ := by ring

end Balaban.SmallField
