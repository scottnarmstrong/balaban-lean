module

public import Balaban.LargeField.Counter.Costs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Comparison with the auxiliary functions (Part I, Lemma I.5.2 (F4), (F5))

Every derived quantity at scale `j` is at most the corresponding auxiliary function of `λ_j`;
the auxiliary functions are nondecreasing on `x ≥ 0`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

theorem sqrt_d_ge : (1 : ℝ) ≤ Real.sqrt S.d :=
  Real.one_le_sqrt.mpr (by exact_mod_cast ok.one_le_d)

theorem critBar_ge (x : ℝ) : 10 ≤ S.critBar x := by
  unfold Typing.critBar
  have := ok.Rb_pos
  have : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  have : 0 ≤ 2 * (S.c0 : ℝ) * (S.Rb * x ^ 2 + 1) := by positivity
  linarith

theorem omegaBar_ge (x : ℝ) : 13 ≤ S.omegaBar x := by
  unfold Typing.omegaBar
  have := ok.Rb_pos
  have := ok.cast_L_ge
  have : 0 ≤ 2 * S.Rb * x ^ 2 := by positivity
  linarith

theorem critBar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : S.critBar x ≤ S.critBar y := by
  unfold Typing.critBar
  have := ok.Rb_pos
  have : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  gcongr

theorem omegaBar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : S.omegaBar x ≤ S.omegaBar y := by
  unfold Typing.omegaBar
  have := ok.Rb_pos
  gcongr

theorem Dbar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : S.Dbar x ≤ S.Dbar y := by
  unfold Typing.Dbar
  have := ok.critBar_mono hx hxy
  have := ok.omegaBar_mono hx hxy
  gcongr

theorem nuBar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : S.nuBar x ≤ S.nuBar y := by
  unfold Typing.nuBar
  have := ok.Cν_pos
  gcongr

theorem n2Bar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : S.n2Bar x ≤ S.n2Bar y := by
  unfold Typing.n2Bar
  have h1 := ok.critBar_ge x
  have hL := ok.cast_L_ge
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
  have := ok.critBar_mono hx hxy
  have : 0 < (S.L : ℝ) * S.M * S.critBar x := by positivity
  have := Real.logb_le_logb_of_le (b := S.L) (by linarith) this
    (by gcongr : (S.L : ℝ) * S.M * S.critBar x ≤ S.L * S.M * S.critBar y)
  linarith

theorem Abar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : S.Abar x ≤ S.Abar y := by
  unfold Typing.Abar
  have := ok.A2_pos
  have := ok.θp_pos
  have := ok.Cw_nonneg
  gcongr

/-! ### the radii against their auxiliary functions -/

theorem one_le_nuBar {x : ℝ} (hx : 0 ≤ x) : 1 ≤ S.nuBar x := by
  unfold Typing.nuBar
  have := ok.Cν_pos
  have : 0 ≤ S.Cν * x ^ S.p2 := by positivity
  linarith

theorem one_le_Dbar (x : ℝ) : 1 ≤ S.Dbar x := by
  unfold Typing.Dbar
  have h1 := ok.sqrt_d_ge
  have h2 := ok.critBar_ge x
  have h3 := ok.omegaBar_ge x
  nlinarith

theorem nuBar_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S.nuBar x := by
  linarith [ok.one_le_nuBar hx]

theorem crit_le_bar (j : ℕ) : (S.crit j : ℝ) ≤ S.critBar (S.lam j) := by
  unfold Setting.crit Typing.critBar
  push_cast
  rw [S.rho_cast]
  have := ok.r_le j
  have : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  nlinarith

theorem omega_le_bar (j : ℕ) : (S.omega j : ℝ) ≤ S.omegaBar (S.lam j) := by
  unfold Setting.omega Typing.omegaBar
  have hRb := ok.Rb_pos
  by_cases hj : j = 0
  · simp only [hj, ite_true]
    push_cast
    have : 0 ≤ S.Rb * S.lam 0 ^ 2 := by have := ok.lam_pos 0; positivity
    linarith
  · simp only [hj, ite_false]
    push_cast
    have h1 : (⌊S.Rb * S.lam (j - 1) ^ 2⌋₊ : ℝ) ≤ S.Rb * S.lam (j - 1) ^ 2 :=
      Nat.floor_le (by have := ok.lam_pos (j - 1); positivity)
    have h2 := ok.lam_mono (Nat.sub_le j 1)
    have h3 : S.lam (j - 1) ^ 2 ≤ S.lam j ^ 2 := by
      have := ok.lam_pos (j - 1)
      gcongr
    nlinarith

theorem D_le_bar (j : ℕ) : S.D j ≤ S.Dbar (S.lam j) := by
  unfold Setting.D Typing.Dbar
  have h := ok.crit_le_bar j
  have h2 := ok.omega_le_bar j
  unfold Setting.crit at h
  push_cast at h
  have : (0 : ℝ) ≤ Real.sqrt S.d := Real.sqrt_nonneg _
  gcongr

theorem one_le_numax (j : ℕ) : 1 ≤ S.numax j := by
  unfold Setting.numax
  have := ok.Cν_pos
  have := ok.lam_pos j
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'

theorem numax_le_bar (j : ℕ) : (S.numax j : ℝ) ≤ S.nuBar (S.lam j) := by
  unfold Setting.numax Typing.nuBar
  have := ok.Cν_pos
  have := ok.lam_pos j
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem h_arg_ge (j : ℕ) :
    (1 : ℝ) ≤ 2 * Real.sqrt S.d * S.numax j * S.M * (S.crit j + S.omega j) := by
  have h1 := ok.sqrt_d_ge
  have h2 : (1 : ℝ) ≤ S.numax j := by exact_mod_cast ok.one_le_numax j
  have h3 : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
  have h4 : (1 : ℝ) ≤ S.crit j + S.omega j := by
    have : (1 : ℝ) ≤ S.crit j := by
      unfold Setting.crit; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (S.rho j)]
    have := (Nat.cast_nonneg (α := ℝ) (S.omega j))
    linarith
  calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ 2 * Real.sqrt S.d * S.numax j * S.M * (S.crit j + S.omega j) := by
      have : (0 : ℝ) ≤ 1 := by norm_num
      gcongr
      linarith

theorem h_le_bar (j : ℕ) : (S.h j : ℝ) ≤ S.hBar (S.lam j) := by
  unfold Setting.h Typing.hBar
  have hL := ok.cast_L_ge
  have harg := ok.h_arg_ge j
  have hY : 0 ≤ Real.logb S.L (2 * Real.sqrt S.d * S.numax j * S.M * (S.crit j + S.omega j)) :=
    Real.logb_nonneg (by linarith) harg
  have h1 := (Nat.ceil_lt_add_one hY).le
  have hmono : Real.logb S.L (2 * Real.sqrt S.d * S.numax j * S.M * (S.crit j + S.omega j)) ≤
      Real.logb S.L (2 * Real.sqrt S.d * S.nuBar (S.lam j) * S.M *
        (S.critBar (S.lam j) + S.omegaBar (S.lam j))) := by
    apply Real.logb_le_logb_of_le (by linarith) (by linarith)
    have h2 := ok.numax_le_bar j
    have h3 := ok.crit_le_bar j
    have h4 := ok.omega_le_bar j
    have : (0 : ℝ) ≤ Real.sqrt S.d := Real.sqrt_nonneg _
    have : (0 : ℝ) ≤ S.M := Nat.cast_nonneg _
    have hnb : 0 ≤ S.nuBar (S.lam j) := by
      unfold Typing.nuBar
      have := ok.Cν_pos
      have := ok.lam_pos j
      positivity
    gcongr
  push_cast
  linarith


theorem h_mono : Monotone S.h := by
  intro a b hab
  unfold Setting.h
  have hL := ok.cast_L_ge
  have h1 := ok.numax_mono hab
  have h2 := ok.crit_mono hab
  have h3 := ok.omega_mono hab
  have h1' : (S.numax a : ℝ) ≤ S.numax b := by exact_mod_cast h1
  have h2' : (S.crit a : ℝ) ≤ S.crit b := by exact_mod_cast h2
  have h3' : (S.omega a : ℝ) ≤ S.omega b := by exact_mod_cast h3
  have harg := ok.h_arg_ge a
  have : Real.logb S.L (2 * Real.sqrt S.d * S.numax a * S.M * (S.crit a + S.omega a)) ≤
      Real.logb S.L (2 * Real.sqrt S.d * S.numax b * S.M * (S.crit b + S.omega b)) := by
    apply Real.logb_le_logb_of_le (by linarith) (by linarith)
    have : (0 : ℝ) ≤ Real.sqrt S.d := Real.sqrt_nonneg _
    have : (0 : ℝ) ≤ S.M := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ S.numax a := Nat.cast_nonneg _
    gcongr
  have := Nat.ceil_le_ceil this
  omega

theorem CE_nonneg : 0 ≤ S.CE := by
  have h1 := ok.Csigma_nonneg
  have h2 := ok.one_le_cv
  have h3 := S.CV_ge
  have h4 : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  have h5 := ok.Rb_pos
  have h6 := ok.cast_L_ge
  unfold Typing.CE
  positivity

theorem n2_le_bar (j : ℕ) : (S.n2 j : ℝ) ≤ S.n2Bar (S.lam j) := by
  unfold Typing.n2Bar
  have hL := ok.cast_L_ge
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
  have hc : (10 : ℝ) ≤ S.crit j := by
    unfold Setting.crit; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (S.rho j)]
  have hpos : (0 : ℝ) < S.L * S.M * S.crit j := by positivity
  have hY : 0 ≤ Real.logb S.L ((S.L : ℝ) * S.M * S.crit j) :=
    Real.logb_nonneg (by linarith)
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hM)
        (by linarith))
  set n := ⌊Real.logb S.L ((S.L : ℝ) * S.M * S.crit j)⌋₊ + 1 with hn
  have hlt : S.L * S.M * S.crit j < S.L ^ n := by
    have h1 : Real.logb S.L ((S.L : ℝ) * S.M * S.crit j) < n := by
      rw [hn]; push_cast; exact Nat.lt_floor_add_one _
    have h2 := (Real.logb_lt_iff_lt_rpow (by linarith) hpos).mp h1
    rw [Real.rpow_natCast] at h2
    exact_mod_cast h2
  have h3 : (S.n2 j : ℝ) ≤ n := by exact_mod_cast S.n2_le_of hlt
  have h4 : (n : ℝ) ≤ Real.logb S.L ((S.L : ℝ) * S.M * S.crit j) + 1 := by
    rw [hn]; push_cast; linarith [Nat.floor_le hY]
  have h5 : Real.logb S.L ((S.L : ℝ) * S.M * S.crit j) ≤
      Real.logb S.L ((S.L : ℝ) * S.M * S.critBar (S.lam j)) := by
    apply Real.logb_le_logb_of_le (by linarith) hpos
    have := ok.crit_le_bar j
    gcongr
  linarith

theorem E_le (j : ℕ) : S.E j ≤ S.CE * S.lam j ^ (2 * S.d + 1) := by
  have hρ := ok.rho_le j
  have hρ1 := ok.one_le_rho_real j
  have hl := ok.lam_pos j
  have hl1 := ok.one_le_lam j
  have hcv := ok.one_le_cv
  have hCV := S.CV_ge
  have hd := ok.one_le_d
  have hRb := ok.Rb_pos
  have hc0 := ok.one_le_c0_real
  have hom : (S.omega j : ℝ) ≤ 2 * S.Rb * S.lam j ^ 2 + S.L + 11 := by
    have := ok.omega_le_bar j
    unfold Typing.omegaBar at this
    exact this
  have hsq : 1 ≤ S.lam j ^ 2 := ok.lam_sq_ge j
  have hL := ok.cast_L_ge
  -- bound on `D_j`
  have hD : S.D j ≤ Real.sqrt S.d * ((2 * S.c0 * (S.Rb + 1) + 2 * S.Rb + S.L + 21) * S.lam j ^ 2) := by
    unfold Setting.D
    have : (0 : ℝ) ≤ Real.sqrt S.d := Real.sqrt_nonneg _
    gcongr
    nlinarith
  -- bound on `v_j`
  have hv : S.v j ≤ S.cv * S.CV * S.lam j * (S.c0 * (S.Rb + 1) * S.lam j ^ 2) ^ (S.d - 1) := by
    unfold Setting.v
    have : 0 ≤ S.cv * S.CV := by positivity
    gcongr
  have hE0 : 0 ≤ 1 + 2 ^ (3 * S.d + 1) * S.Csigma := by
    have := ok.Csigma_nonneg
    positivity
  have hD0 := S.D_nonneg j
  have hv0 := ok.v_nonneg j
  unfold Setting.E Typing.CE
  have hc2 : (0 : ℝ) ≤ 2 * S.c0 * (S.Rb + 1) + 2 * S.Rb + S.L + 21 := by positivity
  calc (1 + 2 ^ (3 * S.d + 1) * S.Csigma) * S.v j * S.D j
      ≤ (1 + 2 ^ (3 * S.d + 1) * S.Csigma) *
        (S.cv * S.CV * S.lam j * (S.c0 * (S.Rb + 1) * S.lam j ^ 2) ^ (S.d - 1)) *
        (Real.sqrt S.d * ((2 * S.c0 * (S.Rb + 1) + 2 * S.Rb + S.L + 21) * S.lam j ^ 2)) := by
        gcongr
    _ = (1 + 2 ^ (3 * S.d + 1) * S.Csigma) * S.cv * S.CV * Real.sqrt S.d *
          ((S.c0 : ℝ) * (S.Rb + 1)) ^ (S.d - 1) *
          (2 * (S.c0 : ℝ) * (S.Rb + 1) + 2 * S.Rb + S.L + 21) * S.lam j ^ (2 * S.d + 1) := by
        have : S.lam j ^ (2 * S.d + 1) = S.lam j * (S.lam j ^ 2) ^ (S.d - 1) * S.lam j ^ 2 := by
          rw [← pow_mul, ← pow_succ', ← pow_add]; congr 1; omega
        rw [this, mul_pow]
        ring

theorem A_le (j : ℕ) :
    S.tau (j + 1) - S.tau j + S.w (j + 1) ≤ S.Abar (S.lam (j + 1)) := by
  have h1 := ok.tau_succ_sub_le j
  have h2 := ok.w_le (j + 1)
  unfold Typing.Abar
  linarith

end Setting.Ok

end Balaban.LargeField
