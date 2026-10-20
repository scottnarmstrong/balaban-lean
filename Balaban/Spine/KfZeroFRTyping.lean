/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KfZeroGoodParts
public import Balaban.LargeField.Base.KF0FRBeta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The typing condition of route FR

`notes/phase1/KF0-FR.md` (P). The parameters of route FR are functions of the block side
`s = M L` (and of `d, N, κ`): the whitening range `R = ⌊(s-3)/4⌋`, the multiplicity
`k = (1+d)(4R+3)^d`, the support size `s₁ = (4R+3)^d`, the target `b_*` of the weights, the heavy
smallness `η_*` and the cutoff `p` with `2^{N-1} e^{-p²/8} = η_*/4`. The typing condition
`KF0FRTyping d N L κ s` asks `s ≥ 6` and that the defect of the whitening be small:
`θ_*(d, L, R) ≤ min(1/4, b_*/(24 p²), 1/(2 p² k s₁))`. It holds for every large `s`
(`exists_KF0FRTyping`): `θ_*` decays exponentially in `s/L²` while the right side decays
polynomially in `s`. Hence the condition is a lower bound on `s` (`kf0FRs0`,
`kF0FRTyping_of_le`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban.LargeField.KF0FR Filter Topology

noncomputable section

/-- The whitening range. -/
def frRr (s : ℕ) : ℕ := (s - 3) / 4

/-- The multiplicity of the supports. -/
def frKk (d s : ℕ) : ℕ := (1 + d) * (4 * frRr s + 3) ^ d

/-- The size of the supports. -/
def frS1 (d s : ℕ) : ℕ := (4 * frRr s + 3) ^ d

/-- The exponent `(κ₀ + κ₁) 3^d` of the block gas. -/
def frD (d : ℕ) (κ : ℝ) : ℝ := (kf0K0 d + (κ + kf0K0 d + 5 / 2)) * 3 ^ d

/-- The target of the weights. -/
def frBs (d : ℕ) (κ : ℝ) (s : ℕ) : ℝ :=
  Real.exp (-frD d κ) / (16 * (1 + d) * 3 ^ d * (s : ℝ) ^ d)

/-- The spread heavy smallness. -/
def frTauB (d : ℕ) (κ : ℝ) (s : ℕ) : ℝ := frBs d κ s / (4 * frS1 d s)

/-- The heavy smallness of one site. -/
def frEta (d : ℕ) (κ : ℝ) (s : ℕ) : ℝ :=
  frTauB d κ s ^ (2 * frKk d s) / (8 ^ frKk d s * Real.exp 1)

/-- The cutoff of the Gaussian variables. -/
def frP (d N : ℕ) (κ : ℝ) (s : ℕ) : ℝ :=
  Real.sqrt (8 * Real.log (4 * 2 ^ (N - 1) / frEta d κ s))

/-- The admissible size of the defect. -/
def frThetaBd (d N : ℕ) (κ : ℝ) (s : ℕ) : ℝ :=
  min (1 / 4) (min (frBs d κ s / (24 * frP d N κ s ^ 2))
    (1 / (2 * frP d N κ s ^ 2 * frKk d s * frS1 d s)))

/-- **The typing condition of route FR** at the block side `s`. -/
def KF0FRTyping (d N L : ℕ) (κ : ℝ) (s : ℕ) : Prop :=
  6 ≤ s ∧ frThetaStar d L (frRr s) ≤ frThetaBd d N κ s

/-! ### Elementary bounds of the parameters -/

theorem frD_nonneg (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ frD d κ := by
  unfold frD
  have h1 := kf0K0_ge_log d
  have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ kf0K0 d := by linarith
  positivity

theorem one_le_frLd (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    (1 : ℝ) ≤ 64 * (1 + d) * 3 ^ d * Real.exp (frD d κ) := by
  have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have he : (1 : ℝ) ≤ Real.exp (frD d κ) := Real.one_le_exp (frD_nonneg d hκ)
  have h64 : (1 : ℝ) ≤ 64 * (1 + d) := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h64 h3) he

theorem frS1_le {d s : ℕ} (hs : 3 ≤ s) : frS1 d s ≤ s ^ d :=
  Nat.pow_le_pow_left (by unfold frRr; omega) d

theorem one_le_frS1 (d s : ℕ) : 1 ≤ frS1 d s := Nat.one_le_pow _ _ (by omega)

theorem frKk_le {d s : ℕ} (hs : 3 ≤ s) : frKk d s ≤ (1 + d) * s ^ d :=
  Nat.mul_le_mul_left _ (frS1_le hs)

theorem one_le_frKk (d s : ℕ) : 1 ≤ frKk d s := by
  unfold frKk; have := one_le_frS1 d s; unfold frS1 at this; nlinarith

theorem frBs_pos (d : ℕ) (κ : ℝ) {s : ℕ} (hs : 1 ≤ s) : 0 < frBs d κ s := by
  unfold frBs; have : (1 : ℝ) ≤ s := by exact_mod_cast hs
  positivity

theorem frBs_le_one (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) : frBs d κ s ≤ 1 := by
  unfold frBs
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 : Real.exp (-frD d κ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [frD_nonneg d hκ])
  have h2 : (1 : ℝ) ≤ 16 * (1 + d) * 3 ^ d * (s : ℝ) ^ d := by
    have hsd : (1 : ℝ) ≤ (s : ℝ) ^ d := one_le_pow₀ hs'
    have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have h16 : (1 : ℝ) ≤ 16 * (1 + d) := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h16 h3d) hsd
  rw [div_le_one (by linarith)]
  linarith

theorem frTauB_pos (d : ℕ) (κ : ℝ) {s : ℕ} (hs : 1 ≤ s) : 0 < frTauB d κ s := by
  unfold frTauB
  have := frBs_pos d κ hs
  have : (1 : ℝ) ≤ frS1 d s := by exact_mod_cast one_le_frS1 d s
  positivity

theorem frTauB_le_one (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) : frTauB d κ s ≤ 1 := by
  unfold frTauB
  have h1 := frBs_le_one d hκ hs
  have h2 : (1 : ℝ) ≤ frS1 d s := by exact_mod_cast one_le_frS1 d s
  rw [div_le_one (by positivity)]
  nlinarith [frBs_pos d κ hs]

theorem frEta_pos (d : ℕ) (κ : ℝ) {s : ℕ} (hs : 1 ≤ s) : 0 < frEta d κ s := by
  unfold frEta; have := frTauB_pos d κ hs; positivity

theorem frEta_le_one (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) : frEta d κ s ≤ 1 := by
  unfold frEta
  have h1 : frTauB d κ s ^ (2 * frKk d s) ≤ 1 :=
    pow_le_one₀ (frTauB_pos d κ hs).le (frTauB_le_one d hκ hs)
  have h2 : (1 : ℝ) ≤ 8 ^ frKk d s * Real.exp 1 := by
    have : (1 : ℝ) ≤ 8 ^ frKk d s := one_le_pow₀ (by norm_num)
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  rw [div_le_one (by linarith)]
  linarith

/-- The cutoff squared. -/
theorem frP_sq (d N : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) :
    frP d N κ s ^ 2 = 8 * Real.log (4 * 2 ^ (N - 1) / frEta d κ s) := by
  unfold frP
  rw [Real.sq_sqrt]
  have h1 := frEta_le_one d hκ hs
  have h2 := frEta_pos d κ hs
  have : 1 ≤ 4 * 2 ^ (N - 1) / frEta d κ s := by
    rw [le_div_iff₀ h2]
    have : (1 : ℝ) ≤ 2 ^ (N - 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have := Real.log_nonneg this
  positivity

/-- **The Gaussian tail at the cutoff is a quarter of the heavy smallness.** -/
theorem frP_tail (d N : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) :
    2 ^ (N - 1) * Real.exp (-frP d N κ s ^ 2 / 8) = frEta d κ s / 4 := by
  rw [frP_sq d N hκ hs]
  have h2 := frEta_pos d κ hs
  have hx : 0 < 4 * 2 ^ (N - 1) / frEta d κ s := by positivity
  rw [show -(8 * Real.log (4 * 2 ^ (N - 1) / frEta d κ s)) / 8 =
    -Real.log (4 * 2 ^ (N - 1) / frEta d κ s) by ring, Real.exp_neg, Real.exp_log hx]
  field_simp

/-! ### The typing condition holds for large blocks -/

/-- The cutoff squared is at most a power of the block side. -/
theorem frP_sq_le (d N : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 6 ≤ s) :
    frP d N κ s ^ 2 ≤ 8 * (Real.log (4 * 2 ^ (N - 1) * Real.exp 1) + (1 + d) *
      (3 + 2 * Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) + 4 * d)) *
        (s : ℝ) ^ (d + 1) := by
  have hs1 : 1 ≤ s := by omega
  have hs' : (6 : ℝ) ≤ s := by exact_mod_cast hs
  obtain ⟨cb, hcb⟩ : ∃ cb : ℝ, cb = Real.exp (-frD d κ) / (16 * (1 + d) * 3 ^ d) := ⟨_, rfl⟩
  have hcb0 : 0 < cb := by rw [hcb]; positivity
  have hbs : frBs d κ s = cb / (s : ℝ) ^ d := by
    unfold frBs; rw [hcb]; field_simp
  have hτ0 := frTauB_pos d κ hs1
  have hτlow : cb / (4 * (s : ℝ) ^ (2 * d)) ≤ frTauB d κ s := by
    unfold frTauB
    rw [hbs, div_div]
    have h1 : (frS1 d s : ℝ) ≤ (s : ℝ) ^ d := by exact_mod_cast frS1_le (by omega : 3 ≤ s)
    have h2 : (1 : ℝ) ≤ frS1 d s := by exact_mod_cast one_le_frS1 d s
    have hsd : (0 : ℝ) < (s : ℝ) ^ d := by positivity
    refine div_le_div_of_nonneg_left hcb0.le (mul_pos hsd (by linarith)) ?_
    rw [pow_mul']
    nlinarith [mul_le_mul_of_nonneg_left h1 hsd.le]
  have hlogτ : Real.log (frTauB d κ s)⁻¹ ≤
      Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) + 2 * d * s := by
    have h1 : (frTauB d κ s)⁻¹ ≤ 4 * (s : ℝ) ^ (2 * d) / cb := by
      rw [inv_le_comm₀ hτ0 (by positivity), inv_div]; exact hτlow
    have h2 : 4 * (s : ℝ) ^ (2 * d) / cb = 64 * (1 + d) * 3 ^ d * Real.exp (frD d κ) *
        (s : ℝ) ^ (2 * d) := by
      rw [hcb, Real.exp_neg]; field_simp; norm_num
    rw [h2] at h1
    refine (Real.log_le_log (by positivity) h1).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < s by positivity)
    push_cast
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  rw [frP_sq d N hκ hs1]
  unfold frEta
  have hk1 : (1 : ℝ) ≤ frKk d s := by exact_mod_cast one_le_frKk d s
  have hkle : (frKk d s : ℝ) ≤ (1 + d) * (s : ℝ) ^ d := by
    exact_mod_cast frKk_le (by omega : 3 ≤ s)
  have hsplit : Real.log (4 * 2 ^ (N - 1) / (frTauB d κ s ^ (2 * frKk d s) /
      (8 ^ frKk d s * Real.exp 1))) = Real.log (4 * 2 ^ (N - 1) * Real.exp 1) +
      frKk d s * Real.log 8 + 2 * frKk d s * Real.log (frTauB d κ s)⁻¹ := by
    have e1 : 4 * 2 ^ (N - 1) / (frTauB d κ s ^ (2 * frKk d s) / (8 ^ frKk d s * Real.exp 1)) =
        (4 * 2 ^ (N - 1) * Real.exp 1) *
          ((8 : ℝ) ^ frKk d s * ((frTauB d κ s)⁻¹) ^ (2 * frKk d s)) := by
      rw [inv_pow, div_div_eq_mul_div]; ring
    rw [e1, Real.log_mul (x := 4 * 2 ^ (N - 1) * Real.exp 1) (by positivity) (by positivity),
      Real.log_mul (x := (8 : ℝ) ^ frKk d s) (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    push_cast; ring
  rw [hsplit]
  have hl8 : Real.log 8 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith
    rw [h3]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
  have hC0 : 0 ≤ Real.log (4 * 2 ^ (N - 1) * Real.exp 1) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 ^ (N - 1) := one_le_pow₀ (by norm_num)
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hCl : 0 ≤ Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) :=
    Real.log_nonneg (one_le_frLd d hκ)
  have hsd : (s : ℝ) ^ d * s = (s : ℝ) ^ (d + 1) := by ring
  have hsd1 : (1 : ℝ) ≤ (s : ℝ) ^ (d + 1) := one_le_pow₀ (by linarith)
  have hsdd : (s : ℝ) ^ d ≤ (s : ℝ) ^ (d + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hlogτ0 : 0 ≤ Real.log (frTauB d κ s)⁻¹ :=
    Real.log_nonneg (one_le_inv₀ hτ0 |>.2 (frTauB_le_one d hκ hs1))
  set Ld := Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ))
  set C0 := Real.log (4 * 2 ^ (N - 1) * Real.exp 1)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  -- the bound term by term
  have hA : (frKk d s : ℝ) * Real.log 8 + 2 * frKk d s * Real.log (frTauB d κ s)⁻¹ ≤
      (1 + d) * (3 + 2 * Ld + 4 * d) * (s : ℝ) ^ (d + 1) := by
    have h1 : (frKk d s : ℝ) * Real.log 8 + 2 * frKk d s * Real.log (frTauB d κ s)⁻¹ ≤
        frKk d s * (3 + 2 * (Ld + 2 * d * s)) := by
      have := mul_le_mul_of_nonneg_left hlogτ (by positivity : (0 : ℝ) ≤ 2 * frKk d s)
      nlinarith
    refine h1.trans ?_
    calc (frKk d s : ℝ) * (3 + 2 * (Ld + 2 * d * s)) ≤
          (1 + d) * (s : ℝ) ^ d * (3 + 2 * (Ld + 2 * d * s)) :=
          mul_le_mul_of_nonneg_right hkle (by positivity)
      _ = (1 + d) * ((3 + 2 * Ld) * (s : ℝ) ^ d + 4 * d * ((s : ℝ) ^ d * s)) := by ring
      _ ≤ (1 + d) * ((3 + 2 * Ld) * (s : ℝ) ^ (d + 1) + 4 * d * (s : ℝ) ^ (d + 1)) := by
          rw [hsd]; gcongr
      _ = _ := by ring
  nlinarith

/-- `frThetaBd` is at least a negative power of the block side. -/
theorem frThetaBd_ge (d N : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 6 ≤ s) :
    min (1 / 4) (min (Real.exp (-frD d κ) / (16 * (1 + d) * 3 ^ d) / (24 *
      (8 * (Real.log (4 * 2 ^ (N - 1) * Real.exp 1) + (1 + d) *
        (3 + 2 * Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) + 4 * d)))))
      (1 / (2 * (8 * (Real.log (4 * 2 ^ (N - 1) * Real.exp 1) + (1 + d) *
        (3 + 2 * Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) + 4 * d))) * (1 + d)))) /
      (s : ℝ) ^ (3 * d + 1) ≤ frThetaBd d N κ s := by
  have hs1 : 1 ≤ s := by omega
  have hs' : (6 : ℝ) ≤ s := by exact_mod_cast hs
  set Cp := 8 * (Real.log (4 * 2 ^ (N - 1) * Real.exp 1) + (1 + d) *
    (3 + 2 * Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) + 4 * d)) with hCp
  have hp2 := frP_sq_le d N hκ hs
  rw [← hCp] at hp2
  have hp0 : 0 < frP d N κ s ^ 2 := by
    rw [frP_sq d N hκ hs1]
    have h1 := frEta_le_one d hκ hs1
    have h2 := frEta_pos d κ hs1
    have : 1 < 4 * 2 ^ (N - 1) / frEta d κ s := by
      rw [lt_div_iff₀ h2]
      have : (1 : ℝ) ≤ 2 ^ (N - 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have := Real.log_pos this
    positivity
  have hCp0 : 0 < Cp := by
    have hsd : (0 : ℝ) < (s : ℝ) ^ (d + 1) := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg hsd.le]
  obtain ⟨cb, hcb⟩ : ∃ cb : ℝ, cb = Real.exp (-frD d κ) / (16 * (1 + d) * 3 ^ d) := ⟨_, rfl⟩
  rw [← hcb]
  have hbs : frBs d κ s = cb / (s : ℝ) ^ d := by
    unfold frBs; rw [hcb]; field_simp
  have hsK : (1 : ℝ) ≤ (s : ℝ) ^ (3 * d + 1) := one_le_pow₀ (by linarith)
  have hspos : (0 : ℝ) < (s : ℝ) ^ (3 * d + 1) := by positivity
  set c1 := cb / (24 * Cp)
  set c2 := 1 / (2 * Cp * (1 + d))
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hcb0 : 0 < cb := by rw [hcb]; positivity
  unfold frThetaBd
  refine le_min ?_ (le_min ?_ ?_)
  · calc min (1 / 4) (min c1 c2) / (s : ℝ) ^ (3 * d + 1) ≤ 1 / 4 / 1 :=
          div_le_div₀ (by norm_num) (min_le_left _ _) (by norm_num) hsK
      _ = 1 / 4 := by norm_num
  · rw [hbs]
    have h1 : min (1 / 4) (min c1 c2) ≤ c1 := (min_le_right _ _).trans (min_le_left _ _)
    calc min (1 / 4) (min c1 c2) / (s : ℝ) ^ (3 * d + 1) ≤ c1 / (s : ℝ) ^ (3 * d + 1) :=
          div_le_div_of_nonneg_right h1 hspos.le
      _ ≤ cb / (s : ℝ) ^ d / (24 * frP d N κ s ^ 2) := by
          show cb / (24 * Cp) / (s : ℝ) ^ (3 * d + 1) ≤ _
          rw [div_div, div_div]
          have h3 : (s : ℝ) ^ d * (24 * frP d N κ s ^ 2) ≤ 24 * Cp * (s : ℝ) ^ (3 * d + 1) := by
            have : (s : ℝ) ^ d * (s : ℝ) ^ (d + 1) ≤ (s : ℝ) ^ (3 * d + 1) := by
              rw [← pow_add]; exact pow_le_pow_right₀ (by linarith) (by omega)
            nlinarith [mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ 24 * (s : ℝ) ^ d)]
          exact div_le_div_of_nonneg_left hcb0.le
            (mul_pos (pow_pos (by linarith) d) (mul_pos (by norm_num) hp0)) h3
  · have h1 : min (1 / 4) (min c1 c2) ≤ c2 := (min_le_right _ _).trans (min_le_right _ _)
    have hk : (frKk d s : ℝ) ≤ (1 + d) * (s : ℝ) ^ d := by
      exact_mod_cast frKk_le (by omega : 3 ≤ s)
    have hs1' : (frS1 d s : ℝ) ≤ (s : ℝ) ^ d := by exact_mod_cast frS1_le (by omega : 3 ≤ s)
    have hk0 : (1 : ℝ) ≤ frKk d s := by exact_mod_cast one_le_frKk d s
    have hs10 : (1 : ℝ) ≤ frS1 d s := by exact_mod_cast one_le_frS1 d s
    calc min (1 / 4) (min c1 c2) / (s : ℝ) ^ (3 * d + 1) ≤ c2 / (s : ℝ) ^ (3 * d + 1) :=
          div_le_div_of_nonneg_right h1 hspos.le
      _ ≤ 1 / (2 * frP d N κ s ^ 2 * frKk d s * frS1 d s) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
          have hprod : frP d N κ s ^ 2 * frKk d s * frS1 d s ≤
              Cp * (1 + d) * (s : ℝ) ^ (3 * d + 1) := by
            have e : (s : ℝ) ^ (d + 1) * (s : ℝ) ^ d * (s : ℝ) ^ d = (s : ℝ) ^ (3 * d + 1) := by
              rw [← pow_add, ← pow_add]; ring_nf
            calc frP d N κ s ^ 2 * frKk d s * frS1 d s ≤
                (Cp * (s : ℝ) ^ (d + 1)) * ((1 + d) * (s : ℝ) ^ d) * (s : ℝ) ^ d := by gcongr
              _ = Cp * (1 + d) * (s : ℝ) ^ (3 * d + 1) := by rw [← e]; ring
          have : c2 * (2 * frP d N κ s ^ 2 * frKk d s * frS1 d s) ≤ (s : ℝ) ^ (3 * d + 1) := by
            show 1 / (2 * Cp * (1 + d)) * (2 * frP d N κ s ^ 2 * frKk d s * frS1 d s) ≤ _
            rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
            nlinarith
          linarith

/-- **The typing condition holds for every large block side.** -/
theorem exists_KF0FRTyping {d N L : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → KF0FRTyping d N L κ s := by
  set ns := frNuStar L
  have hns := frNuStar_pos hL
  set q := 2 * (d : ℝ) / (2 * d + ns) with hq
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  set lam := -Real.log q / 8 with hlam
  have hlam0 : 0 < lam := by
    have := Real.log_neg hq0 hq1; rw [hlam]; linarith
  set A := 2 * (4 * d + 1) * (Real.sqrt ns)⁻¹ * ((2 * d + 1) / ns) with hA
  set Cp := 8 * (Real.log (4 * 2 ^ (N - 1) * Real.exp 1) + (1 + d) *
    (3 + 2 * Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) + 4 * d))
  set ct := min (1 / 4) (min (Real.exp (-frD d κ) / (16 * (1 + d) * 3 ^ d) / (24 * Cp))
    (1 / (2 * Cp * (1 + d))))
  have hct : 0 < ct := by
    have hC0 : 0 ≤ Real.log (4 * 2 ^ (N - 1) * Real.exp 1) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ 2 ^ (N - 1) := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith
    have hCl : 0 ≤ Real.log (64 * (1 + d) * 3 ^ d * Real.exp (frD d κ)) :=
      Real.log_nonneg (one_le_frLd d hκ)
    have hCp : 0 < Cp := by positivity
    positivity
  have hev := eventually_pow_mul_exp_le (c := lam) hlam0 (3 * d + 1) (A / ct) (ε := 1) one_pos
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max 6 ⌈S⌉₊, fun s hs => ⟨le_of_max_le_left hs, ?_⟩⟩
  have hs6 : 6 ≤ s := le_of_max_le_left hs
  have hsS : S ≤ (s : ℝ) := (Nat.le_ceil S).trans (by exact_mod_cast le_of_max_le_right hs)
  have hs' : (6 : ℝ) ≤ s := by exact_mod_cast hs6
  refine le_trans ?_ (frThetaBd_ge d N hκ hs6)
  -- the decay of the defect
  have hR : (s : ℝ) / 8 ≤ (frRr s + 1 : ℕ) := by
    unfold frRr
    have : s / 8 ≤ (s - 3) / 4 + 1 := by omega
    have h2 : ((s : ℝ) / 8) ≤ ((s / 8 : ℕ) : ℝ) + 1 := by
      have h8 : s < 8 * (s / 8 + 1) := by omega
      have : (s : ℝ) < 8 * (((s / 8 : ℕ) : ℝ) + 1) := by exact_mod_cast h8
      linarith
    have h3 : ((s / 8 : ℕ) : ℝ) + 1 ≤ ((s - 3) / 4 + 1 : ℕ) := by
      have : s / 8 + 1 ≤ (s - 3) / 4 + 1 := by omega
      exact_mod_cast this
    linarith
  have hqpow : q ^ (frRr s + 1) ≤ Real.exp (-(lam * s)) := by
    rw [← Real.rpow_natCast]
    calc q ^ ((frRr s + 1 : ℕ) : ℝ) ≤ q ^ ((s : ℝ) / 8) :=
          Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hR
      _ = Real.exp (-(lam * s)) := by
          rw [Real.rpow_def_of_pos hq0, hlam]; congr 1; ring
  have hmain := hS s hsS
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hsp : (0 : ℝ) < (s : ℝ) ^ (3 * d + 1) := by positivity
  unfold frThetaStar
  rw [← hA, ← hq]
  calc A * q ^ (frRr s + 1) ≤ A * Real.exp (-(lam * s)) := mul_le_mul_of_nonneg_left hqpow hA0
    _ ≤ ct / (s : ℝ) ^ (3 * d + 1) := by
        rw [le_div_iff₀ hsp]
        have := hmain
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hct] at this
        nlinarith [this]

open Classical in
/-- **The least block side of the typing**: every block side above it satisfies the typing
condition (`kF0FRTyping_of_le`); it is at least `6` (`six_le_kf0FRs0`). -/
def kf0FRs0 (d N L : ℕ) (κ : ℝ) : ℕ :=
  max 6 (if hex : ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → KF0FRTyping d N L κ s then Nat.find hex else 0)

theorem six_le_kf0FRs0 (d N L : ℕ) (κ : ℝ) : 6 ≤ kf0FRs0 d N L κ := le_max_left _ _

open Classical in
theorem kF0FRTyping_of_le {d N L : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ}
    (hs : kf0FRs0 d N L κ ≤ s) : KF0FRTyping d N L κ s := by
  have hex := exists_KF0FRTyping (N := N) hd hL hκ
  unfold kf0FRs0 at hs
  rw [dite_eq_left hex] at hs
  exact Nat.find_spec hex s (le_of_max_le_right hs)

/-- **The typing condition is compatible with block sides that are powers of `L`**: for `L ≥ 2`
every large power `L^n` satisfies `kf0FRs0 ≤ L^n · L`. -/
theorem kf0FRs0_le_pow (d N : ℕ) {L : ℕ} (hL : 2 ≤ L) (κ : ℝ) {n : ℕ}
    (hn : kf0FRs0 d N L κ ≤ n) : kf0FRs0 d N L κ ≤ L ^ n * L :=
  hn.trans ((Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_right _ (by omega)))

end

end Balaban.RootFSpine
