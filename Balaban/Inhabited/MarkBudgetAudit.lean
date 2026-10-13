/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkedRootAssemblyFromTower
public import Balaban.Fluctuation.Thm31cde
public import Balaban.Inhabited.DAPhysicalCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Audit of the mark budget of Theorem 3.1 (c) at the shared tower

Numbers only.  The constants are those of `markedRootAssembly_zero_fromTower` (cubic rooted marks)
and `marked_count_scaled_dec_resummed` (decoupled marks) at `d = L = 3`, `N = 2`, `m₀ = 1`, with
`b = β 3^k = S.betaU`.
-/

@[expose] public section

namespace Balaban.Inhabited.MarkBudgetAudit

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

section Const

variable {κmin : ℝ} (T : StepTower κmin)

/-- The potential size `V = cK2' · t` of the block energy bound. -/
noncomputable abbrev Vstar : ℝ := cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t

/-- `E_*` of the landed bounds, at the scale `k`. -/
noncomputable abbrev Estar (k : ℕ) : ℝ :=
  ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Vstar T) T.t (rho4 3 3 2 T.BG T.κ)‖

/-- The scale-free part of `E_*`:  `27 (a (t+V)² + 3 V² + (1+ρ) V²/9)`. -/
noncomputable abbrev Ecst (a : ℝ) : ℝ :=
  27 * (a * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 + (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9)

/-- The bridge and fibre factor `c₁ M^d n_F e^{(2κ_dec-1) c_Br}` (`M = 3^{1+m₁}`). -/
noncomputable abbrev Kmark : ℝ :=
  (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
    ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3))

/-- The constant `F₀` of the cubic rooted marks `G_{z,Y'} = -β markedOut` (landed in
`markedRootAssembly_zero_fromTower`). -/
noncomputable def cubicF0 (k : ℕ) (β p₁ : ℝ) : ℝ :=
  |β| * (3 * Estar T k / ((lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
    (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
    ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)))

/-- The constant `F_dec(t₀) = (‖E_*‖/t₀) c₁ M^d n_F e^{a c_Br}` of the decoupled marks (landed in
`marked_count_scaled_dec_resummed`), `a = 2κ_dec - 1`. -/
noncomputable def decF (k : ℕ) (t₀ : ℝ) : ℝ :=
  (Estar T k / t₀) * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
    ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3))

theorem Vstar_nonneg : 0 ≤ Vstar T := by
  have h := cK2'_nonneg (d := 3) (L := 3) (N := 2) (B := famConst 3 3 T.BG₂ T.κ) T.fam_nonneg
  exact mul_nonneg h T.t_pos.le

theorem Kmark_pos : 0 < Kmark T := by
  have := one_le_c1 3 3
  have : (0 : ℝ) < nFibre 3 3 := by unfold nFibre; positivity
  unfold Kmark; positivity

theorem Kmark_eq : Kmark T = (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
    ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)) := rfl

theorem energyBdScaled_eq (k : ℕ) (a V δ ρ : ℝ) (ha : compWeight 3 1 k = a) :
    energyBdScaled 3 3 2 (compWeight 3 1) k V δ ρ =
      3 ^ k * (27 * (a * (δ + V) ^ 2 + 3 * V ^ 2 + (1 + ρ) * V ^ 2 / 9)) := by
  unfold energyBdScaled
  rw [ha]
  push_cast
  field_simp
  ring

theorem Ecst_lo {a : ℝ} (ha : 1 / 2 ≤ a) :
    27 * (1 / 2 * T.t ^ 2) ≤ Ecst T a := by
  have h1 := Vstar_nonneg T
  have h2 := T.rho_nonneg
  have h3 := T.t_pos
  unfold Ecst
  have : (1 / 2 : ℝ) * T.t ^ 2 ≤ a * (T.t + Vstar T) ^ 2 := by
    have : T.t ^ 2 ≤ (T.t + Vstar T) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (T.t + Vstar T)]
  nlinarith [sq_nonneg (Vstar T)]

theorem Ecst_hi {a : ℝ} (ha : a ≤ 2) :
    Ecst T a ≤ 27 * (2 * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 +
      (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9) := by
  unfold Ecst
  nlinarith [sq_nonneg (T.t + Vstar T)]

theorem Ecst_pos {a : ℝ} (ha : 1 / 2 ≤ a) : 0 < Ecst T a := by
  have := Ecst_lo T ha
  have := T.t_pos
  nlinarith

theorem Estar_eq {k : ℕ} (hk : 1 ≤ k) :
    Estar T k = 3 ^ k * Ecst T (compWeight 3 1 k) := by
  have ha := compWeight_three_mem hk
  have hpos := Ecst_pos T ha.1
  unfold Estar
  rw [energyBdScaled_eq k _ _ _ _ rfl]
  rw [Real.norm_of_nonneg (by positivity)]

end Const

section Cubic

variable {κmin : ℝ} (T : StepTower κmin)

/-- The lower constant of the cubic family. -/
noncomputable def cLow : ℝ :=
  96 * 512 * (27 * (1 / 2 * T.t ^ 2)) * Kmark T / lvKappa T.κ T.t ^ 3

/-- The upper constant of the cubic family. -/
noncomputable def cHigh : ℝ :=
  96 * 4096 * (27 * (2 * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 +
    (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9)) * Kmark T / lvKappa T.κ T.t ^ 3

theorem cLow_pos : 0 < cLow T := by
  have := Kmark_pos T
  have := T.t_pos
  have := lvKappa_pos T.κ T.t_pos
  unfold cLow; positivity

/-- **The landed constant `F₀` in terms of `b = β 3^k`**:
`F₀ = 96 b Ecst Kmark / r³`, `r = lvR/4`. -/
theorem cubicF0_eq_b {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) :
    cubicF0 T k β p₁ = 96 * (β * 3 ^ k) * Ecst T (compWeight 3 1 k) * Kmark T /
      (lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 := by
  unfold cubicF0
  rw [Estar_eq T hk, abs_of_pos hβ]
  unfold Kmark
  ring

private theorem alg_lo (s κ p E K : ℝ) (hs : s ≠ 0) (hκ : κ ≠ 0) (hp : p ≠ 0) :
    96 * 512 * E * K / κ ^ 3 * p ^ 3 / s = 96 * s ^ 2 * E * K / (κ * s / (8 * p)) ^ 3 := by
  field_simp
  ring

private theorem alg_hi (s κ p E K : ℝ) (hs : s ≠ 0) (hκ : κ ≠ 0) (hp : p ≠ 0) :
    96 * 4096 * E * K / κ ^ 3 * p ^ 3 / s = 96 * s ^ 2 * E * K / (κ * s / (16 * p)) ^ 3 := by
  field_simp
  ring

theorem lvR_div_four_le {b p₁ : ℝ} (hp : 0 < p₁) :
    lvR T.κ T.t b p₁ / 4 ≤ lvKappa T.κ T.t * Real.sqrt b / (8 * p₁) := by
  unfold lvR
  rw [lvCpsi_eq]
  have : 0 < lvKappa T.κ T.t * Real.sqrt b / (8 * p₁) ∨ lvKappa T.κ T.t * Real.sqrt b / (8 * p₁) ≤ 0 :=
    lt_or_ge 0 _ |>.imp id id
  have e : (lvKappa T.κ T.t * Real.sqrt b / (2 * p₁) - 4) / 4 =
      lvKappa T.κ T.t * Real.sqrt b / (8 * p₁) - 1 := by field_simp; ring
  rw [e]; linarith

theorem le_lvR_div_four {b p₁ : ℝ} (hp : 0 < p₁)
    (h16 : 16 * p₁ ≤ lvCpsi T.κ T.t b) :
    lvKappa T.κ T.t * Real.sqrt b / (16 * p₁) ≤ lvR T.κ T.t b p₁ / 4 := by
  unfold lvR
  rw [← lvCpsi_eq]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
  rw [lvCpsi_eq] at h16 ⊢
  have e : lvKappa T.κ T.t * Real.sqrt b / (16 * p₁) * 4 =
      lvKappa T.κ T.t * Real.sqrt b / (4 * p₁) := by field_simp; ring
  rw [e]
  have h : 4 ≤ lvKappa T.κ T.t * Real.sqrt b / (4 * p₁) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have e2 : lvKappa T.κ T.t * Real.sqrt b / (2 * p₁) =
      2 * (lvKappa T.κ T.t * Real.sqrt b / (4 * p₁)) := by field_simp; ring
  rw [e2]; linarith

/-- **Lower bound (the true exponent is `-1/2`)**: for `r > 0`,
`F₀ ≥ cLow · p₁³ / √b`. -/
theorem markedRoot_F0_ge {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁)
    (hr : 0 < lvR T.κ T.t (β * 3 ^ k) p₁) :
    cLow T * p₁ ^ 3 / Real.sqrt (β * 3 ^ k) ≤ cubicF0 T k β p₁ := by
  rw [cubicF0_eq_b T hk hβ]
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hk1 := lvKappa_pos T.κ T.t_pos
  have hEc := Ecst_lo T (compWeight_three_mem hk).1
  have hK := Kmark_pos T
  set r := lvR T.κ T.t b p₁ / 4 with hrdef
  have hr4 : 0 < r := by rw [hrdef]; positivity
  have hrA := lvR_div_four_le T (b := b) hp
  have hA : 0 < lvKappa T.κ T.t * Real.sqrt b / (8 * p₁) := by positivity
  have h3 : r ^ 3 ≤ (lvKappa T.κ T.t * Real.sqrt b / (8 * p₁)) ^ 3 :=
    pow_le_pow_left₀ hr4.le hrA 3
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have step : 96 * b * (27 * (1 / 2 * T.t ^ 2)) * Kmark T /
      (lvKappa T.κ T.t * Real.sqrt b / (8 * p₁)) ^ 3 ≤
      96 * b * Ecst T (compWeight 3 1 k) * Kmark T / r ^ 3 := by
    have hE0 := Ecst_pos T (compWeight_three_mem hk).1
    apply div_le_div₀ (by positivity) _ (by positivity) h3
    nlinarith [mul_pos hb0 hK]
  refine le_trans (le_of_eq ?_) step
  unfold cLow
  have := alg_lo (Real.sqrt b) (lvKappa T.κ T.t) p₁ (27 * (1 / 2 * T.t ^ 2)) (Kmark T) hs.ne'
    hk1.ne' hp.ne'
  rw [hsq] at this
  exact this

/-- **Upper bound**: for `16 p₁ ≤ c_ψ`, `F₀ ≤ cHigh · p₁³ / √b`. -/
theorem markedRoot_F0_le {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁)
    (h16 : 16 * p₁ ≤ lvCpsi T.κ T.t (β * 3 ^ k)) :
    cubicF0 T k β p₁ ≤ cHigh T * p₁ ^ 3 / Real.sqrt (β * 3 ^ k) := by
  rw [cubicF0_eq_b T hk hβ]
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hk1 := lvKappa_pos T.κ T.t_pos
  have hEc := Ecst_hi T (compWeight_three_mem hk).2
  have hK := Kmark_pos T
  have hE0 := Ecst_pos T (compWeight_three_mem hk).1
  have hrA := le_lvR_div_four T hp h16
  have hA : 0 < lvKappa T.κ T.t * Real.sqrt b / (16 * p₁) := by positivity
  set r := lvR T.κ T.t b p₁ / 4 with hrdef
  have h3 : (lvKappa T.κ T.t * Real.sqrt b / (16 * p₁)) ^ 3 ≤ r ^ 3 :=
    pow_le_pow_left₀ hA.le hrA 3
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have step : 96 * b * Ecst T (compWeight 3 1 k) * Kmark T / r ^ 3 ≤
      96 * b * (27 * (2 * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 +
        (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9)) * Kmark T /
      (lvKappa T.κ T.t * Real.sqrt b / (16 * p₁)) ^ 3 := by
    apply div_le_div₀ _ _ (by positivity) h3
    · have := mul_pos hb0 hK
      nlinarith
    · nlinarith [mul_pos hb0 hK]
  refine le_trans step (le_of_eq ?_)
  unfold cHigh
  have := alg_hi (Real.sqrt b) (lvKappa T.κ T.t) p₁ (27 * (2 * (T.t + Vstar T) ^ 2 +
    3 * Vstar T ^ 2 + (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9)) (Kmark T) hs.ne'
    hk1.ne' hp.ne'
  rw [hsq] at this
  exact this.symm

end Cubic

section Polylog

variable {κmin : ℝ} (T : StepTower κmin)

/-- **The cubic constant is `O(p₁³ b^{-1/2})`, with `p₁ ≤ A₁ (log b)^p`**: one threshold `b₀`
(of the tower and of `A₁`, `p`) after which `F₀ ≤ cHigh A₁³ (log b)^{3p} / √b`. -/
theorem markedRoot_F0_le_polylog {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) :
    ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ β p₁ : ℝ, 0 < β → 0 < p₁ → b₀ ≤ β * 3 ^ k →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      cubicF0 T k β p₁ ≤
        cHigh T * (A₁ ^ 3 * Real.log (β * 3 ^ k) ^ (3 * p)) / Real.sqrt (β * 3 ^ k) := by
  have hk1 := lvKappa_pos T.κ T.t_pos
  refine ⟨max 1 (pLogThreshold A₁ p (lvKappa T.κ T.t / 16)), le_max_left _ _,
    fun k hk β p₁ hβ hp hb hp₁ => ?_⟩
  have hb1 : 1 ≤ β * 3 ^ k := (le_max_left _ _).trans hb
  have hbt : pLogThreshold A₁ p (lvKappa T.κ T.t / 16) ≤ β * 3 ^ k := (le_max_right _ _).trans hb
  have hpl := pLog_le_mul_sqrt hA p (by positivity : 0 < lvKappa T.κ T.t / 16) hb1 hbt
  have h16 : 16 * p₁ ≤ lvCpsi T.κ T.t (β * 3 ^ k) := by
    rw [lvCpsi_eq]; linarith
  refine (markedRoot_F0_le T hk hβ hp h16).trans ?_
  have hc : 0 ≤ cHigh T := by
    have := Kmark_pos T
    have := T.rho_nonneg
    have := Vstar_nonneg T
    unfold cHigh; positivity
  have h3 : p₁ ^ 3 ≤ A₁ ^ 3 * Real.log (β * 3 ^ k) ^ (3 * p) := by
    have hpl0 : p₁ ^ 3 ≤ pLog A₁ p (β * 3 ^ k) ^ 3 := pow_le_pow_left₀ hp.le hp₁ 3
    refine hpl0.trans (le_of_eq ?_)
    unfold pLog
    rw [mul_pow, ← pow_mul, mul_comm p 3]
  gcongr

end Polylog

section Decoupled

variable {κmin : ℝ} (T : StepTower κmin)

/-- The lower bound of `covSupConstC` on weights in `[1/2, 2]`. -/
noncomputable def covMin : ℝ := ((2 : ℕ) : ℝ) * Green.ballConst 3 (xAgmonRate 3 3 / 3) * (2 / Real.sqrt 2)

theorem covMin_pos : 0 < covMin := by
  have := ballConst_pos (d := 3) (L := 3) (by norm_num) le_rfl
  unfold covMin; positivity

theorem covMin_le {a : ℝ} (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2) (κ : ℝ) :
    covMin ≤ covSupConstC 3 3 2 a κ := by
  obtain ⟨h1, h2⟩ := ha
  have ha0 : 0 < a := by linarith
  have hB := ballConst_pos (d := 3) (L := 3) (by norm_num) le_rfl
  have hε : 0 ≤ xAgmonRate 3 3 := (xAgmonRate_pos (L := 3) (by norm_num) le_rfl).le
  have hT := covTConst_nonneg 3 3 a (xAgmonRate 3 3) κ
  have e1 : (1 : ℝ) ≤ Real.exp (xAgmonRate 3 3 * (2 * 3)) := Real.one_le_exp (by positivity)
  have e2 : (1 : ℝ) ≤ Real.exp (xAgmonRate 3 3 * 3 / 3) := Real.one_le_exp (by positivity)
  have hs : Real.sqrt a ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h2
  have hs0 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  unfold covSupConstC covSqrtEntryConstC covC1Const covMin
  simp only [Nat.cast_ofNat] at hB ⊢
  have hC : 2 ≤ 2 * Real.exp (xAgmonRate 3 3 * (2 * 3)) + covTConst 3 3 a (xAgmonRate 3 3) κ / a := by
    have h0 : 0 ≤ covTConst 3 3 a (xAgmonRate 3 3) κ / a := by positivity
    exact le_add_of_le_of_nonneg (by simpa using mul_le_mul_of_nonneg_left e1 (by norm_num : (0:ℝ) ≤ 2)) h0
  have h4 : 2 / Real.sqrt 2 ≤ (2 * Real.exp (xAgmonRate 3 3 * (2 * 3)) +
      covTConst 3 3 a (xAgmonRate 3 3) κ / a) * Real.exp (xAgmonRate 3 3 * 3 / 3) /
        Real.sqrt a := by
    rw [le_div_iff₀ hs0]
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    calc 2 / Real.sqrt 2 * Real.sqrt a ≤ 2 / Real.sqrt 2 * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 := by field_simp
      _ ≤ _ := by nlinarith
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- The radius `markedRad` at `cc = b^{-1/2}`, `c_ψ = p₁`, as an explicit function. -/
noncomputable def decMR (k : ℕ) (b p₁ : ℝ) : ℝ :=
  Real.sqrt 2 * ((Real.sqrt b)⁻¹ * (covSupConstC 3 3 2 (compWeight 3 1 k) T.κ * p₁))

theorem markedRad_eq (k : ℕ) {b : ℝ} (hb : 0 ≤ b) (p₁ : ℝ) :
    markedRad 3 3 2 k 1 T.κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = decMR T k b p₁ := by
  unfold markedRad decMR
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hb _), Real.sqrt_eq_rpow b,
    Real.rpow_neg hb]
  norm_num

theorem decMR_ge {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 ≤ p₁) :
    Real.sqrt 2 * ((Real.sqrt b)⁻¹ * (covMin * p₁)) ≤ decMR T k b p₁ := by
  have := covMin_le (compWeight_three_mem hk) T.κ
  unfold decMR
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  gcongr

theorem decMR_le {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 ≤ p₁) :
    decMR T k b p₁ ≤ Real.sqrt 2 * ((Real.sqrt b)⁻¹ * (covSupMaxC 3 3 2 T.κ * p₁)) := by
  have := covSupConstC_le_covSupMaxC (N := 2) (d := 3) (L := 3) (by norm_num) le_rfl T.κ
    (compWeight_three_mem hk)
  unfold decMR
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  gcongr

theorem decMR_pos {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    0 < decMR T k b p₁ :=
  lt_of_lt_of_le (by have := covMin_pos; positivity) (decMR_ge T hk hb hp.le)

/-- **Any admissible `t₀` of the decoupled count obeys `t₀ · markedRad < δ₁`.**  (The count asks
`0 < t₀ ≤ b₀` and `(‖u‖ + b₀) markedRad < δ₁`.) -/
theorem t0_mul_lt {t₀ b₀ u mr δ₁ : ℝ} (hmr : 0 ≤ mr) (hu : 0 ≤ u) (h0 : t₀ ≤ b₀)
    (h : (u + b₀) * mr < δ₁) : t₀ * mr < δ₁ := by
  have : t₀ * mr ≤ (u + b₀) * mr := mul_le_mul_of_nonneg_right (by linarith) hmr
  linarith

theorem decF_eq (k : ℕ) (t₀ : ℝ) : decF T k t₀ = Estar T k / t₀ * Kmark T := by
  unfold decF Kmark; ring

/-- **Lower bound for the constant of the decoupled count at every admissible `t₀`.** -/
theorem decF_ge {k : ℕ} {t₀ mr : ℝ} (ht0 : 0 < t₀) (hadm : t₀ * mr < T.t) :
    Estar T k * mr / T.t * Kmark T ≤ decF T k t₀ := by
  have hE : 0 ≤ Estar T k := norm_nonneg _
  have hK := Kmark_pos T
  have ht := T.t_pos
  rw [decF_eq]
  refine mul_le_mul_of_nonneg_right ?_ hK.le
  rw [div_le_div_iff₀ ht ht0]
  nlinarith [mul_le_mul_of_nonneg_left hadm.le hE]

/-- The lower constant of the decoupled marks `G = -β markedOutDec`. -/
noncomputable def cDecLow : ℝ :=
  27 * (1 / 2 * T.t ^ 2) * (Real.sqrt 2 * covMin) * Kmark T / T.t

/-- The upper constant of the decoupled marks at the best `t₀`. -/
noncomputable def cDecHigh : ℝ :=
  2 * (27 * (2 * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 +
    (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9)) * (Real.sqrt 2 * covSupMaxC 3 3 2 T.κ) *
      Kmark T / T.t

theorem cDecLow_pos : 0 < cDecLow T := by
  have := Kmark_pos T
  have := T.t_pos
  have := covMin_pos
  unfold cDecLow; positivity

/-- **The decoupled constant grows like `√b`.**  For every admissible `t₀`, the constant
`β F_dec(t₀)` of the mark `G = -β markedOutDec` is at least `cDecLow · p₁ · √b`. -/
theorem dec_G_ge {k : ℕ} (hk : 1 ≤ k) {β p₁ t₀ : ℝ} (hβ : 0 < β) (hp : 0 < p₁) (ht0 : 0 < t₀)
    (hadm : t₀ * decMR T k (β * 3 ^ k) p₁ < T.t) :
    cDecLow T * p₁ * Real.sqrt (β * 3 ^ k) ≤ |β| * decF T k t₀ := by
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have h1 := decF_ge T (k := k) ht0 hadm
  have h2 := decMR_ge T hk hb0 hp.le
  have hEc := Ecst_lo T (compWeight_three_mem hk).1
  have hK := Kmark_pos T
  have ht := T.t_pos
  rw [abs_of_pos hβ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 hβ.le)
  rw [Estar_eq T hk]
  have hmr0 := covMin_pos
  have key : cDecLow T * p₁ * Real.sqrt b =
      β * (3 ^ k * (27 * (1 / 2 * T.t ^ 2)) * (Real.sqrt 2 * ((Real.sqrt b)⁻¹ * (covMin * p₁))) /
        T.t * Kmark T) := by
    unfold cDecLow
    generalize Kmark T = K
    generalize covMin = cm
    field_simp
    rw [hsq, hb]
    ring
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ hβ.le
  have e0 := Ecst_pos T (compWeight_three_mem hk).1
  gcongr

/-- **Attained: the best admissible `t₀` gives `β F_dec ≤ cDecHigh · p₁ · √b`.**  With
`t₀ = δ₁/(2 markedRad)` the landed hypothesis `(‖u‖ + t₀) markedRad < δ₁` holds for `‖u‖ ≤ 1`
(when `markedRad < δ₁/2`), and the constant is `2 E_* markedRad/δ₁ · c₁M^d n_F e^{a c_Br}`. -/
theorem dec_G_le_best {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁)
    (hsmall : decMR T k (β * 3 ^ k) p₁ < T.t / 2) :
    (∀ u : ℝ, |u| ≤ 1 →
      (u + T.t / (2 * decMR T k (β * 3 ^ k) p₁)) * decMR T k (β * 3 ^ k) p₁ < T.t) ∧
    |β| * decF T k (T.t / (2 * decMR T k (β * 3 ^ k) p₁)) ≤
      cDecHigh T * p₁ * Real.sqrt (β * 3 ^ k) := by
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hmr := decMR_pos T hk hb0 hp
  set mr := decMR T k b p₁ with hmrdef
  have ht := T.t_pos
  have hK := Kmark_pos T
  refine ⟨fun u hu => ?_, ?_⟩
  · have : (u + T.t / (2 * mr)) * mr = u * mr + T.t / 2 := by field_simp
    rw [this]
    have : u * mr ≤ mr := by
      calc u * mr ≤ |u| * mr := mul_le_mul_of_nonneg_right (le_abs_self u) hmr.le
        _ ≤ 1 * mr := mul_le_mul_of_nonneg_right hu hmr.le
        _ = mr := one_mul _
    linarith
  · have hE0 := Ecst_pos T (compWeight_three_mem hk).1
    have hEh := Ecst_hi T (compWeight_three_mem hk).2
    have hmrle := decMR_le T hk hb0 hp.le
    have e : decF T k (T.t / (2 * mr)) = 2 * (3 ^ k * Ecst T (compWeight 3 1 k)) * mr / T.t *
        Kmark T := by
      rw [decF_eq, Estar_eq T hk]
      generalize Kmark T = K
      field_simp
    rw [abs_of_pos hβ, e]
    have step : β * (2 * (3 ^ k * Ecst T (compWeight 3 1 k)) * mr / T.t * Kmark T) ≤
        β * (2 * (3 ^ k * (27 * (2 * (T.t + Vstar T) ^ 2 + 3 * Vstar T ^ 2 +
          (1 + rho4 3 3 2 T.BG T.κ) * Vstar T ^ 2 / 9))) *
          (Real.sqrt 2 * ((Real.sqrt b)⁻¹ * (covSupMaxC 3 3 2 T.κ * p₁))) / T.t * Kmark T) := by
      apply mul_le_mul_of_nonneg_left _ hβ.le
      have := T.rho_nonneg
      have := Vstar_nonneg T
      gcongr
    refine step.trans (le_of_eq ?_)
    unfold cDecHigh
    generalize Kmark T = K
    field_simp
    rw [hsq, hb]
    ring

end Decoupled

section Budget

/-- **Budget of Theorem 3.1 (c)**: `B = β_k⁻¹`, `β_k = b = β 3^k = S.betaU`
(`Thm31cde.thm31c_of_input`). -/
noncomputable def budgetC (b : ℝ) : ℝ := b⁻¹

/-- **Budget of Theorem 3.1 (d)**: `B = ½ β_{k+1}^{-m-1}`, `β_{k+1} = 3 b`
(`Thm31cde.thm31d_of_input`). -/
noncomputable def budgetD (b : ℝ) (m : ℕ) : ℝ := (1 / 2) * (3 * b) ^ (-(m : ℤ) - 1)

/-- **Budget of Theorem 3.1 (e)**: `B = ½ β_{k+1}^{-n}`, `β_{k+1} = 3 b`
(`Thm31cde.thm31e_of_input`). -/
noncomputable def budgetE (b : ℝ) (n : ℕ) : ℝ := (1 / 2) * (3 * b) ^ (-(n : ℤ))

theorem budgetD_le {b : ℝ} (hb : 1 ≤ 3 * b) (m : ℕ) : budgetD b m ≤ b⁻¹ := by
  have hb0 : 0 < b := by linarith
  unfold budgetD
  rw [show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have h1 : 3 * b ≤ (3 * b) ^ (m + 1) := by
    calc 3 * b = (3 * b) ^ 1 := (pow_one _).symm
      _ ≤ (3 * b) ^ (m + 1) := pow_le_pow_right₀ hb (by omega)
  have h2 : ((3 * b) ^ (m + 1))⁻¹ ≤ (3 * b)⁻¹ := inv_anti₀ (by positivity) h1
  have h3 : (3 * b)⁻¹ ≤ b⁻¹ := inv_anti₀ hb0 (by linarith)
  have : 0 ≤ ((3 * b) ^ (m + 1))⁻¹ := by positivity
  linarith

theorem budgetE_le {b : ℝ} (hb : 1 ≤ 3 * b) {n : ℕ} (hn : 1 ≤ n) : budgetE b n ≤ b⁻¹ := by
  have hb0 : 0 < b := by linarith
  unfold budgetE
  rw [zpow_neg, zpow_natCast]
  have h1 : 3 * b ≤ (3 * b) ^ n := by
    calc 3 * b = (3 * b) ^ 1 := (pow_one _).symm
      _ ≤ (3 * b) ^ n := pow_le_pow_right₀ hb hn
  have h2 : ((3 * b) ^ n)⁻¹ ≤ (3 * b)⁻¹ := inv_anti₀ (by positivity) h1
  have h3 : (3 * b)⁻¹ ≤ b⁻¹ := inv_anti₀ hb0 (by linarith)
  have : 0 ≤ ((3 * b) ^ n)⁻¹ := by positivity
  linarith

/-- The budgets of (d), (e) are at most that of (c): the exponent required by (c) (`-1`) is the
weakest of the three (those of (d), (e) are `-(m+1)`, `-n`). -/
theorem budget_all_le {b : ℝ} (hb : 1 ≤ 3 * b) :
    (∀ m : ℕ, budgetD b m ≤ budgetC b) ∧ (∀ n : ℕ, 1 ≤ n → budgetE b n ≤ budgetC b) :=
  ⟨fun m => budgetD_le hb m, fun _ hn => budgetE_le hb hn⟩

/-- The anchored sum is bounded below by any single term. -/
theorem marks_sum_ge {d L N₁ m₁ K m₀ : ℕ} [NeZero L] [NeZero N₁] {X : Type*}
    [MeasurableSpace X] {ν : MeasureTheory.Measure X}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W f : ℝ → X → ℂ} (I : InterpMarks ν BS W f)
    {F Dd : ℝ} (i0 : I.ι) (hdl : I.Lab.dl (I.y0 i0) ≤ Dd) (hF : ∀ i, F ≤ I.F0 i) :
    CPE d L I.Kc I.κH I.κ0 I.κ' * Real.exp (-I.κ0 * Dd) * F ≤
      CPE d L I.Kc I.κH I.κ0 I.κ' * (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) := by
  have hκ0 : 0 ≤ I.κ0 := by have := aEnt_nonneg d L; have := I.hκ0; linarith
  have hKc : 0 < I.Kc := by
    have := K0_pos d L I.κ0
    have := I.hKc
    linarith
  have hCPE : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' := by
    have := one_le_c1 d L
    unfold CPE
    positivity
  have he : Real.exp (-I.κ0 * Dd) ≤ Real.exp (-I.κ0 * I.Lab.dl (I.y0 i0)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h1 : F * Real.exp (-I.κ0 * Dd) ≤ I.F0 i0 * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i0)) :=
    calc F * Real.exp (-I.κ0 * Dd) ≤ I.F0 i0 * Real.exp (-I.κ0 * Dd) :=
          mul_le_mul_of_nonneg_right (hF i0) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left he (I.hF0 i0).le
  have h2 : I.F0 i0 * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i0)) ≤
      ∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i)) :=
    Finset.single_le_sum (f := fun i => I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i)))
      (fun i _ => (mul_pos (I.hF0 i) (Real.exp_pos _)).le) (Finset.mem_univ i0)
  calc CPE d L I.Kc I.κH I.κ0 I.κ' * Real.exp (-I.κ0 * Dd) * F
      = CPE d L I.Kc I.κH I.κ0 I.κ' * (F * Real.exp (-I.κ0 * Dd)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h2) hCPE

end Budget

section Verdict

variable {κmin : ℝ} (T : StepTower κmin)

/-- The constant of the landed bound of `markedRootAssembly_zero_fromTower` is `cubicF0`
(definitional unfolding, `|β|` times the displayed expression). -/
theorem cubicF0_landed (k : ℕ) (β p₁ : ℝ) :
    |β| * (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
              (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
              ((lvR T.κ T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
            (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
            ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3))) = cubicF0 T k β p₁ := rfl

/-- The constant of `marked_count_scaled_dec_resummed` (`d = L = 3`, `N = 2`, `m₀ = 1`,
`δ₁ = T.t`, `BG₂ = T.BG₂`, `BG = T.BG`) is `decF`. -/
theorem decF_landed (k : ℕ) (t₀ : ℝ) :
    (‖energyBdScaled 3 3 2 (compWeight 3 1) k
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ / t₀) *
      (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
      ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)) = decF T k t₀ := rfl

/-- **The cubic constant exceeds the budget of (c).**  For every positive constant `C` (standing
for `C_PE` times the entropy factor), `p₁ ≥ 1` and `b = β 3^k > 1/(C cLow)²`:
`β_k⁻¹ < C · F₀`. -/
theorem cubic_exceeds_budget {k : ℕ} (hk : 1 ≤ k) {β p₁ C : ℝ} (hβ : 0 < β) (hp1 : 1 ≤ p₁)
    (hr : 0 < lvR T.κ T.t (β * 3 ^ k) p₁) (hC : 0 < C)
    (hbig : 1 / (C * cLow T) ^ 2 < β * 3 ^ k) :
    budgetC (β * 3 ^ k) < C * cubicF0 T k β p₁ := by
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hcl := cLow_pos T
  have hCc : 0 < C * cLow T := by positivity
  have hF := markedRoot_F0_ge T hk hβ (by linarith) hr
  have hp3 : 1 ≤ p₁ ^ 3 := one_le_pow₀ hp1
  have h1 : 1 / (C * cLow T) < Real.sqrt b := by
    rw [Real.lt_sqrt (by positivity)]
    rw [div_pow, one_pow]
    exact hbig
  have h2 : C * cLow T / Real.sqrt b ≤ C * cubicF0 T k β p₁ := by
    have : cLow T / Real.sqrt b ≤ cLow T * p₁ ^ 3 / Real.sqrt b :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right hcl.le hp3) hs.le
    calc C * cLow T / Real.sqrt b = C * (cLow T / Real.sqrt b) := by ring
      _ ≤ C * (cLow T * p₁ ^ 3 / Real.sqrt b) := mul_le_mul_of_nonneg_left this hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [hb] using hF) hC.le
  refine lt_of_lt_of_le ?_ h2
  unfold budgetC
  rw [lt_div_iff₀ hs]
  have h3 : 1 < C * cLow T * Real.sqrt b := by
    rw [div_lt_iff₀ hCc] at h1; linarith
  have : b⁻¹ * Real.sqrt b = (Real.sqrt b)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul₀ hb0.ne']
    field_simp
    nlinarith [hsq]
  rw [this]
  rw [inv_lt_iff_one_lt_mul₀ hs]
  linarith

/-- **Necessary condition for the cubic budget:** if `C · F₀ ≤ β_k⁻¹` then
`C cLow p₁³ ≤ b^{-1/2}`, i.e. `p₁ ≲ b^{-1/6}`. -/
theorem cubic_budget_needs_small_p1 {k : ℕ} (hk : 1 ≤ k) {β p₁ C : ℝ} (hβ : 0 < β)
    (hp : 0 < p₁) (hr : 0 < lvR T.κ T.t (β * 3 ^ k) p₁) (hC : 0 < C)
    (h : C * cubicF0 T k β p₁ ≤ budgetC (β * 3 ^ k)) :
    C * cLow T * p₁ ^ 3 ≤ (Real.sqrt (β * 3 ^ k))⁻¹ := by
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hF := markedRoot_F0_ge T hk hβ hp hr
  have h1 : C * (cLow T * p₁ ^ 3 / Real.sqrt b) ≤ b⁻¹ :=
    (mul_le_mul_of_nonneg_left (by simpa [hb] using hF) hC.le).trans h
  have h2 : C * cLow T * p₁ ^ 3 / Real.sqrt b ≤ b⁻¹ := by
    calc _ = C * (cLow T * p₁ ^ 3 / Real.sqrt b) := by ring
      _ ≤ _ := h1
  rw [div_le_iff₀ hs] at h2
  have : b⁻¹ * Real.sqrt b = (Real.sqrt b)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul₀ hb0.ne']
    field_simp
    nlinarith [hsq]
  rwa [this] at h2

/-- **The decoupled constant exceeds the budget of (c)**, at every admissible `t₀`. -/
theorem dec_exceeds_budget {k : ℕ} (hk : 1 ≤ k) {β p₁ t₀ C : ℝ} (hβ : 0 < β) (hp1 : 1 ≤ p₁)
    (ht0 : 0 < t₀) (hadm : t₀ * decMR T k (β * 3 ^ k) p₁ < T.t) (hC : 0 < C)
    (hb1 : 1 ≤ β * 3 ^ k) (hbig : 1 / (C * cDecLow T) ^ 2 < β * 3 ^ k) :
    budgetC (β * 3 ^ k) < C * (|β| * decF T k t₀) := by
  set b := β * 3 ^ k with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hcl := cDecLow_pos T
  have hCc : 0 < C * cDecLow T := by positivity
  have hF := dec_G_ge T hk hβ (by linarith) ht0 hadm
  have h1 : 1 / (C * cDecLow T) < Real.sqrt b := by
    rw [Real.lt_sqrt (by positivity)]
    rw [div_pow, one_pow]
    exact hbig
  have h3 : 1 < C * cDecLow T * Real.sqrt b := by
    rw [div_lt_iff₀ hCc] at h1; linarith
  have h4 : C * cDecLow T * Real.sqrt b ≤ C * (|β| * decF T k t₀) := by
    have : cDecLow T * Real.sqrt b ≤ cDecLow T * p₁ * Real.sqrt b := by
      have := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hcl.le hp1) hs.le
      simpa using this
    calc C * cDecLow T * Real.sqrt b = C * (cDecLow T * Real.sqrt b) := by ring
      _ ≤ C * (cDecLow T * p₁ * Real.sqrt b) := mul_le_mul_of_nonneg_left this hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [hb] using hF) hC.le
  have h5 : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
  unfold budgetC
  linarith

/-- **Verdict for the consumer** (Theorem 3.1 (c), (d), (e)): a mark record whose constants
`F0 i` are at least a constant `F`, and with one anchor of distance at most `Dd`, has anchored
sum `CPE ∑ F0 e^{-κ0 dl} ≥ C F` with `C = CPE e^{-κ0 Dd} > 0`; if `C F` exceeds `β_k⁻¹`, the
hypothesis `hB` of `thm31c_of_input` fails, and so do those of `thm31d_of_input` (`m` any),
`thm31e_of_input` (`n ≥ 1`). -/
theorem budgets_fail_of_gt {d L N₁ m₁ K m₀ : ℕ} [NeZero L] [NeZero N₁] {X : Type*}
    [MeasurableSpace X] {ν : MeasureTheory.Measure X}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W f : ℝ → X → ℂ} (I : InterpMarks ν BS W f)
    {F Dd b : ℝ} (i0 : I.ι) (hdl : I.Lab.dl (I.y0 i0) ≤ Dd) (hF : ∀ i, F ≤ I.F0 i)
    (hb : 1 ≤ 3 * b)
    (hgt : budgetC b < CPE d L I.Kc I.κH I.κ0 I.κ' * Real.exp (-I.κ0 * Dd) * F) :
    ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetC b) ∧
    (∀ m : ℕ, ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetD b m)) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetE b n)) := by
  have h := lt_of_lt_of_le hgt (marks_sum_ge I i0 hdl hF)
  obtain ⟨hD, hE⟩ := budget_all_le hb
  refine ⟨not_le.2 h, fun m => not_le.2 ?_, fun n hn => not_le.2 ?_⟩
  · exact lt_of_le_of_lt (hD m) h
  · exact lt_of_le_of_lt (hE n hn) h

theorem cpe_exp_pos {d L N₁ m₁ K m₀ : ℕ} [NeZero L] [NeZero N₁] {X : Type*}
    [MeasurableSpace X] {ν : MeasureTheory.Measure X}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W f : ℝ → X → ℂ} (I : InterpMarks ν BS W f) (Dd : ℝ) :
    0 < CPE d L I.Kc I.κH I.κ0 I.κ' * Real.exp (-I.κ0 * Dd) := by
  have hKc : 0 < I.Kc := by
    have := K0_pos d L I.κ0
    have := I.hKc
    linarith
  have := one_le_c1 d L
  unfold CPE
  positivity

/-- **Verdict (T3), cubic rooted marks: the budget of (c), (d), (e) is NOT certified.**
Let `I` be any mark record whose constants `F0 i` are at least the landed constant `F₀` of the
cubic family (`cubicF0`), with an anchor of bounded distance `Dd`.  Then, for `p₁ ≥ 1`, `r > 0`,
and `b = β 3^k` with `1 ≤ 3b` and `b > 1/(C cLow)²` (`C = C_PE e^{-κ0 Dd}`), the hypothesis `hB`
of `thm31c_of_input` fails, and so do those of `thm31d_of_input` (all `m`) and
`thm31e_of_input` (all `n ≥ 1`).  The obtained size is `F₀ ≍ p₁³ b^{-1/2}`, the size required
is `b^{-1}`. -/
theorem markBudget_cubic_negative {d L N₁ m₁ K m₀ : ℕ} [NeZero L] [NeZero N₁] {X : Type*}
    [MeasurableSpace X] {ν : MeasureTheory.Measure X}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W f : ℝ → X → ℂ} (I : InterpMarks ν BS W f)
    {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {β p₁ Dd : ℝ} (hβ : 0 < β)
    (hp1 : 1 ≤ p₁) (hr : 0 < lvR T.κ T.t (β * 3 ^ k) p₁) (i0 : I.ι)
    (hdl : I.Lab.dl (I.y0 i0) ≤ Dd) (hF : ∀ i, cubicF0 T k β p₁ ≤ I.F0 i)
    (hb : 1 ≤ 3 * (β * 3 ^ k))
    (hbig : 1 / (CPE d L I.Kc I.κH I.κ0 I.κ' * Real.exp (-I.κ0 * Dd) * cLow T) ^ 2 <
      β * 3 ^ k) :
    ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetC (β * 3 ^ k)) ∧
    (∀ m : ℕ, ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetD (β * 3 ^ k) m)) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetE (β * 3 ^ k) n)) :=
  budgets_fail_of_gt I i0 hdl hF hb
    (cubic_exceeds_budget T hk hβ hp1 hr (cpe_exp_pos I Dd) hbig)

/-- **Verdict (T3′), decoupled marks: the budget of (c), (d), (e) is NOT certified**, at every
admissible `t₀` of the count; the constant even grows like `p₁ √b`. -/
theorem markBudget_dec_negative {d L N₁ m₁ K m₀ : ℕ} [NeZero L] [NeZero N₁] {X : Type*}
    [MeasurableSpace X] {ν : MeasureTheory.Measure X}
    {BS : ProdSplit ν d L N₁ m₁ K m₀} {W f : ℝ → X → ℂ} (I : InterpMarks ν BS W f)
    {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {β p₁ t₀ Dd : ℝ} (hβ : 0 < β)
    (hp1 : 1 ≤ p₁) (ht0 : 0 < t₀) (hadm : t₀ * decMR T k (β * 3 ^ k) p₁ < T.t) (i0 : I.ι)
    (hdl : I.Lab.dl (I.y0 i0) ≤ Dd) (hF : ∀ i, |β| * decF T k t₀ ≤ I.F0 i)
    (hb : 1 ≤ β * 3 ^ k)
    (hbig : 1 / (CPE d L I.Kc I.κH I.κ0 I.κ' * Real.exp (-I.κ0 * Dd) * cDecLow T) ^ 2 <
      β * 3 ^ k) :
    ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetC (β * 3 ^ k)) ∧
    (∀ m : ℕ, ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetD (β * 3 ^ k) m)) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ (CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ budgetE (β * 3 ^ k) n)) :=
  budgets_fail_of_gt I i0 hdl hF (by linarith)
    (dec_exceeds_budget T hk hβ hp1 ht0 hadm (cpe_exp_pos I Dd) hb hbig)

end Verdict

end Balaban.Inhabited.MarkBudgetAudit
