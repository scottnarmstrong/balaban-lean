module

public import Balaban.LargeField.Counter.Params
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Elementary facts on the constants of the step counter (§I.5.2, Lemma I.5.2 (F1))

Monotonicity of `λ` and of every derived sequence, lower bounds, and the characterizations of
`n_q` and `n_2`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

theorem le_r (j : ℕ) : S.Rb * S.lam j ^ 2 ≤ S.r j := Nat.le_ceil _

end Setting

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

theorem cast_L_ge : (2 : ℝ) ≤ S.L := by exact_mod_cast ok.two_le_L

theorem logL_pos : 0 < S.logL := by
  have : (1 : ℝ) < S.L := by linarith [ok.cast_L_ge]
  exact Real.log_pos this

theorem cStar_ge_one : 1 ≤ S.cStar := by
  have h1 := ok.logL_pos
  have h2 := ok.α_pos
  have h3 := ok.θm_pos
  have h4 := ok.θm_le_θp
  unfold Typing.cStar
  have : 0 ≤ S.θp / (S.α * S.logL) :=
    div_nonneg (by linarith) (mul_nonneg h2.le h1.le)
  linarith

theorem lam_add_le (j x : ℕ) : S.lam (j + x) ≤ S.lam j + x * S.θp := by
  induction x with
  | zero => simp
  | succ x ih =>
    have := (ok.lam_step (j + x)).2
    rw [← add_assoc]
    push_cast
    nlinarith

theorem lam_add_ge (j x : ℕ) : S.lam j + x * S.θm ≤ S.lam (j + x) := by
  induction x with
  | zero => simp
  | succ x ih =>
    have := (ok.lam_step (j + x)).1
    rw [← add_assoc]
    push_cast
    nlinarith

theorem lam_mono : Monotone S.lam := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hab
  have := ok.lam_add_ge a x
  have h := ok.θm_pos
  nlinarith [Nat.cast_nonneg (α := ℝ) x]

theorem lam_strictMono : StrictMono S.lam := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have := ok.lam_add_ge a (x + 1)
  have h := ok.θm_pos
  push_cast at this
  rw [← add_assoc] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) x]

theorem one_le_lam (j : ℕ) : 1 ≤ S.lam j := le_trans ok.one_le_lam0 (ok.lam_mono (Nat.zero_le j))

theorem θp_le_lam (j : ℕ) : S.θp ≤ S.lam j := le_trans ok.θp_le_lam0 (ok.lam_mono (Nat.zero_le j))

theorem lam_pos (j : ℕ) : 0 < S.lam j := lt_of_lt_of_le one_pos (ok.one_le_lam j)

theorem θp_pos : 0 < S.θp := lt_of_lt_of_le ok.θm_pos ok.θm_le_θp

theorem lam_succ_le_two (j : ℕ) : S.lam (j + 1) ≤ 2 * S.lam j := by
  have := (ok.lam_step j).2
  have := ok.θp_le_lam j
  linarith

theorem lam_le_mul (k n : ℕ) : S.lam (k + 1 + n) ≤ (n + 1) * S.lam (k + 1) := by
  have h1 := ok.lam_add_le (k + 1) n
  have h2 := ok.θp_le_lam (k + 1)
  have h3 : (n : ℝ) * S.θp ≤ n * S.lam (k + 1) :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
  linarith

/-! ### The radii -/

theorem one_le_Rb_lam_sq (j : ℕ) : 1 ≤ S.Rb * S.lam j ^ 2 := by
  have h1 := ok.one_le_lam j
  have h2 := ok.two_le_Rb
  nlinarith

theorem one_le_r (j : ℕ) : 1 ≤ S.r j := by
  unfold Setting.r
  exact Nat.one_le_iff_ne_zero.mpr (by
    have := ok.one_le_Rb_lam_sq j
    exact (Nat.ceil_pos.mpr (by linarith)).ne')

theorem r_le (j : ℕ) : (S.r j : ℝ) ≤ S.Rb * S.lam j ^ 2 + 1 := by
  unfold Setting.r
  exact (Nat.ceil_lt_add_one (by have := ok.one_le_Rb_lam_sq j; linarith)).le

theorem r_mono : Monotone S.r := by
  intro a b hab
  unfold Setting.r
  apply Nat.ceil_le_ceil
  have := ok.lam_mono hab
  have h1 := ok.one_le_lam a
  have h2 := ok.two_le_Rb
  gcongr

theorem one_le_c0 : 1 ≤ S.c0 := by
  have h := ok.c0_sS
  have hL := ok.cast_L_ge
  have hs : (0 : ℝ) ≤ S.sS := Nat.cast_nonneg _
  by_contra hc
  have : S.c0 = 0 := by omega
  rw [this] at h
  simp at h
  linarith

theorem one_le_rho (j : ℕ) : 1 ≤ S.rho j := by
  unfold Setting.rho
  exact Nat.mul_pos ok.one_le_c0 (ok.one_le_r j)

theorem rho_mono : Monotone S.rho := by
  intro a b hab
  unfold Setting.rho
  exact Nat.mul_le_mul_left _ (ok.r_mono hab)

theorem crit_mono : Monotone S.crit := by
  intro a b hab
  unfold Setting.crit
  have := ok.rho_mono hab
  omega

theorem omega_mono : Monotone S.omega := by
  intro a b hab
  unfold Setting.omega
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ha, hb]
    · simp [ha, hb]
  · have hb : b ≠ 0 := by omega
    simp only [ha, hb, ite_false]
    have h1 := ok.lam_mono (Nat.sub_le_sub_right hab 1)
    have h2 := ok.one_le_lam (a - 1)
    have h3 := ok.two_le_Rb
    have : ⌊S.Rb * S.lam (a - 1) ^ 2⌋₊ ≤ ⌊S.Rb * S.lam (b - 1) ^ 2⌋₊ := by
      apply Nat.floor_le_floor
      gcongr
    omega

theorem D_mono : Monotone S.D := by
  intro a b hab
  unfold Setting.D
  have h1 := ok.rho_mono hab
  have h2 := ok.omega_mono hab
  have h1' : (S.rho a : ℝ) ≤ S.rho b := by exact_mod_cast h1
  have h2' : (S.omega a : ℝ) ≤ S.omega b := by exact_mod_cast h2
  gcongr

theorem numax_mono : Monotone S.numax := by
  intro a b hab
  unfold Setting.numax
  apply Nat.ceil_le_ceil
  have := ok.lam_mono hab
  have h1 := ok.one_le_lam a
  have h2 := ok.Cν_pos
  gcongr

end Setting.Ok

end Balaban.LargeField
