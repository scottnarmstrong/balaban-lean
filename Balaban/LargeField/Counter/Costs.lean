module

public import Balaban.LargeField.Counter.Growth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The cost sequences (Part I, Lemma I.5.2 (F2)–(F5))

`v, w, σ, τ, E` and the comparison with the auxiliary functions of `λ_j`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

theorem rho_cast (j : ℕ) : (S.rho j : ℝ) = S.c0 * S.r j := by
  unfold Setting.rho; push_cast; ring

theorem CV_ge : 1 ≤ S.CV := by
  unfold Typing.CV
  have : (1 : ℝ) ≤ 14 ^ S.d := one_le_pow₀ (by norm_num)
  linarith

theorem D_nonneg (j : ℕ) : 0 ≤ S.D j := by
  unfold Setting.D
  positivity

end Setting

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

theorem Rb_pos : 0 < S.Rb := by linarith [ok.two_le_Rb]

theorem one_le_d : 1 ≤ S.d := by have := ok.three_le_d; omega

theorem one_le_rho_real (j : ℕ) : (1 : ℝ) ≤ S.rho j := by exact_mod_cast ok.one_le_rho j

theorem one_le_c0_real : (1 : ℝ) ≤ S.c0 := by exact_mod_cast ok.one_le_c0

theorem lam_sq_ge (j : ℕ) : 1 ≤ S.lam j ^ 2 := by
  have := ok.one_le_lam j
  nlinarith

theorem rho_le (j : ℕ) : (S.rho j : ℝ) ≤ S.c0 * (S.Rb + 1) * S.lam j ^ 2 := by
  have h1 := ok.r_le j
  have h2 := ok.lam_sq_ge j
  rw [S.rho_cast]
  have h3 : (S.r j : ℝ) ≤ (S.Rb + 1) * S.lam j ^ 2 := by nlinarith
  have h4 := ok.one_le_c0_real
  calc (S.c0 : ℝ) * S.r j ≤ S.c0 * ((S.Rb + 1) * S.lam j ^ 2) := by gcongr
    _ = _ := by ring

theorem v_nonneg (j : ℕ) : 0 ≤ S.v j := by
  have := ok.one_le_cv
  have := S.CV_ge
  have := ok.lam_pos j
  have := ok.one_le_rho_real j
  unfold Setting.v
  positivity

theorem one_le_v (j : ℕ) : 1 ≤ S.v j := by
  have h1 := ok.one_le_cv
  have h2 := S.CV_ge
  have h3 := ok.one_le_lam j
  have h4 : (1 : ℝ) ≤ (S.rho j : ℝ) ^ (S.d - 1) := one_le_pow₀ (ok.one_le_rho_real j)
  unfold Setting.v
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

theorem w_nonneg (j : ℕ) : 0 ≤ S.w j := by
  have := ok.v_nonneg j
  unfold Setting.w
  positivity

theorem one_le_w (j : ℕ) : 1 ≤ S.w j := by
  have := ok.one_le_v j
  have := ok.one_le_rho_real j
  unfold Setting.w
  nlinarith

/-! ### (F2) -/

theorem v_le_mul (k n : ℕ) :
    S.v (k + 1 + n) ≤ 2 ^ (S.d - 1) * ((n + 1 : ℕ) : ℝ) ^ (2 * S.d - 1) * S.v (k + 1) := by
  have hl := ok.lam_le_mul k n
  have hr_a := ok.one_le_r (k + 1)
  have hr_a' : (1 : ℝ) ≤ S.r (k + 1) := by exact_mod_cast hr_a
  have hRb := S.le_r (k + 1)
  have hrle := ok.r_le (k + 1 + n)
  have hlam_sq : S.lam (k + 1 + n) ^ 2 ≤ ((n + 1) * S.lam (k + 1)) ^ 2 := by
    have := ok.lam_pos (k + 1 + n)
    gcongr
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hr : (S.r (k + 1 + n) : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 2 * S.r (k + 1) := by
    have h1 : S.Rb * S.lam (k + 1 + n) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * (S.Rb * S.lam (k + 1) ^ 2) := by
      have := ok.Rb_pos
      calc S.Rb * S.lam (k + 1 + n) ^ 2 ≤ S.Rb * (((n : ℝ) + 1) * S.lam (k + 1)) ^ 2 := by
            gcongr
        _ = _ := by ring
    have h2 : ((n : ℝ) + 1) ^ 2 * (S.Rb * S.lam (k + 1) ^ 2) ≤ ((n : ℝ) + 1) ^ 2 * S.r (k + 1) := by
      gcongr
    have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * S.r (k + 1) := by nlinarith
    nlinarith
  have hrho : (S.rho (k + 1 + n) : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 2 * S.rho (k + 1) := by
    rw [S.rho_cast, S.rho_cast]
    have := ok.one_le_c0_real
    calc (S.c0 : ℝ) * S.r (k + 1 + n) ≤ S.c0 * (2 * ((n : ℝ) + 1) ^ 2 * S.r (k + 1)) := by gcongr
      _ = _ := by ring
  have hpow : (S.rho (k + 1 + n) : ℝ) ^ (S.d - 1) ≤
      (2 * ((n : ℝ) + 1) ^ 2) ^ (S.d - 1) * (S.rho (k + 1) : ℝ) ^ (S.d - 1) := by
    rw [← mul_pow]
    gcongr
  have hcv := ok.one_le_cv
  have hCV := S.CV_ge
  have hd := ok.one_le_d
  have hexp : ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (2 * (S.d - 1)) = ((n : ℝ) + 1) ^ (2 * S.d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  unfold Setting.v
  calc S.cv * S.CV * S.lam (k + 1 + n) * (S.rho (k + 1 + n) : ℝ) ^ (S.d - 1)
      ≤ S.cv * S.CV * (((n : ℝ) + 1) * S.lam (k + 1)) *
        ((2 * ((n : ℝ) + 1) ^ 2) ^ (S.d - 1) * (S.rho (k + 1) : ℝ) ^ (S.d - 1)) := by
        have h0 : 0 ≤ S.cv * S.CV := by positivity
        have h1 : 0 ≤ S.lam (k + 1) := (ok.lam_pos _).le
        have h2 : 0 ≤ ((n : ℝ) + 1) := by positivity
        gcongr
    _ = 2 ^ (S.d - 1) * (((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (2 * (S.d - 1))) *
          (S.cv * S.CV * S.lam (k + 1) * (S.rho (k + 1) : ℝ) ^ (S.d - 1)) := by
        rw [mul_pow, ← pow_mul]
        ring
    _ = _ := by
        rw [hexp]
        push_cast
        ring

theorem summable_geom_poly :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (2 * S.d - 1) * ((S.L : ℝ) ^ (n + 1))⁻¹) := by
  have hL : ‖((S.L : ℝ))⁻¹‖ < 1 := by
    have := ok.cast_L_ge
    rw [norm_inv, Real.norm_of_nonneg (by linarith)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have h := summable_pow_mul_geometric_of_norm_lt_one (2 * S.d - 1) hL
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr (fun n => ?_)
  simp [inv_pow]

theorem summable_sigma_terms (k : ℕ) :
    Summable (fun n : ℕ => S.v (k + 1 + n) * ((S.L : ℝ) ^ (n + 1))⁻¹) := by
  have hs := (ok.summable_geom_poly).mul_left (2 ^ (S.d - 1) * S.v (k + 1))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · have := ok.v_nonneg (k + 1 + n)
    have : 0 ≤ ((S.L : ℝ) ^ (n + 1))⁻¹ := by
      have := ok.cast_L_ge
      positivity
    positivity
  · have h := ok.v_le_mul k n
    have : 0 ≤ ((S.L : ℝ) ^ (n + 1))⁻¹ := by
      have := ok.cast_L_ge
      positivity
    calc S.v (k + 1 + n) * ((S.L : ℝ) ^ (n + 1))⁻¹
        ≤ (2 ^ (S.d - 1) * ((n + 1 : ℕ) : ℝ) ^ (2 * S.d - 1) * S.v (k + 1)) *
            ((S.L : ℝ) ^ (n + 1))⁻¹ := by gcongr
      _ = _ := by ring

theorem sigma_nonneg (k : ℕ) : 0 ≤ S.sigma k := by
  unfold Setting.sigma
  refine tsum_nonneg (fun n => ?_)
  have := ok.v_nonneg (k + 1 + n)
  have : 0 ≤ ((S.L : ℝ) ^ (n + 1))⁻¹ := by
    have := ok.cast_L_ge
    positivity
  positivity

theorem sigma_rec (k : ℕ) : S.sigma k = (S.L : ℝ)⁻¹ * (S.v (k + 1) + S.sigma (k + 1)) := by
  have hL := ok.cast_L_ge
  have hL0 : (S.L : ℝ) ≠ 0 := by positivity
  unfold Setting.sigma
  rw [(ok.summable_sigma_terms k).tsum_eq_zero_add]
  have : ∀ n : ℕ, S.v (k + 1 + (n + 1)) * ((S.L : ℝ) ^ (n + 1 + 1))⁻¹ =
      (S.L : ℝ)⁻¹ * (S.v (k + 1 + 1 + n) * ((S.L : ℝ) ^ (n + 1))⁻¹) := by
    intro n
    rw [pow_succ _ (n + 1), mul_inv]
    have : k + 1 + (n + 1) = k + 1 + 1 + n := by omega
    rw [this]
    ring
  simp only [this]
  rw [tsum_mul_left]
  simp
  ring

theorem Csigma_nonneg : 0 ≤ S.Csigma := by
  unfold Typing.Csigma
  refine mul_nonneg (by positivity) (tsum_nonneg (fun n => ?_))
  have := ok.cast_L_ge
  positivity

theorem sigma_le (k : ℕ) : S.sigma k ≤ S.Csigma * S.v (k + 1) := by
  have hs := (ok.summable_geom_poly).mul_left (2 ^ (S.d - 1) * S.v (k + 1))
  unfold Setting.sigma
  calc ∑' n : ℕ, S.v (k + 1 + n) * ((S.L : ℝ) ^ (n + 1))⁻¹
      ≤ ∑' n : ℕ, (2 ^ (S.d - 1) * S.v (k + 1)) *
          (((n + 1 : ℕ) : ℝ) ^ (2 * S.d - 1) * ((S.L : ℝ) ^ (n + 1))⁻¹) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (ok.summable_sigma_terms k) hs
        have h := ok.v_le_mul k n
        have : 0 ≤ ((S.L : ℝ) ^ (n + 1))⁻¹ := by
          have := ok.cast_L_ge
          positivity
        calc S.v (k + 1 + n) * ((S.L : ℝ) ^ (n + 1))⁻¹
            ≤ (2 ^ (S.d - 1) * ((n + 1 : ℕ) : ℝ) ^ (2 * S.d - 1) * S.v (k + 1)) *
                ((S.L : ℝ) ^ (n + 1))⁻¹ := by gcongr
          _ = _ := by ring
    _ = S.Csigma * S.v (k + 1) := by
        rw [tsum_mul_left]
        unfold Typing.Csigma
        ring

theorem v_succ_le (k : ℕ) : S.v (k + 1) ≤ 2 ^ (3 * S.d) * S.v k := by
  have hl := ok.lam_succ_le_two k
  have hr_k := ok.one_le_r k
  have hr_k' : (1 : ℝ) ≤ S.r k := by exact_mod_cast hr_k
  have hRb := S.le_r k
  have hrle := ok.r_le (k + 1)
  have hlam_sq : S.lam (k + 1) ^ 2 ≤ (2 * S.lam k) ^ 2 := by
    have := ok.lam_pos (k + 1)
    gcongr
  have hr : (S.r (k + 1) : ℝ) ≤ 5 * S.r k := by
    have := ok.Rb_pos
    nlinarith
  have hrho : (S.rho (k + 1) : ℝ) ≤ 5 * S.rho k := by
    rw [S.rho_cast, S.rho_cast]
    have := ok.one_le_c0_real
    calc (S.c0 : ℝ) * S.r (k + 1) ≤ S.c0 * (5 * S.r k) := by gcongr
      _ = _ := by ring
  have hpow : (S.rho (k + 1) : ℝ) ^ (S.d - 1) ≤ 5 ^ (S.d - 1) * (S.rho k : ℝ) ^ (S.d - 1) := by
    rw [← mul_pow]
    gcongr
  have hd := ok.one_le_d
  have h5 : (2 : ℝ) * 5 ^ (S.d - 1) ≤ 2 ^ (3 * S.d) := by
    have h1 : (5 : ℝ) ^ (S.d - 1) ≤ 8 ^ (S.d - 1) := by gcongr; norm_num
    have h2 : (8 : ℝ) ^ (S.d - 1) = 2 ^ (3 * (S.d - 1)) := by
      rw [pow_mul]; norm_num
    have h3 : (2 : ℝ) ^ (3 * S.d) = 2 ^ (3 * (S.d - 1)) * 8 := by
      have : 3 * S.d = 3 * (S.d - 1) + 3 := by omega
      rw [this, pow_add]; norm_num
    have h4 : (0 : ℝ) < 2 ^ (3 * (S.d - 1)) := by positivity
    nlinarith
  have hv0 := ok.v_nonneg k
  unfold Setting.v at hv0 ⊢
  have hc : 0 ≤ S.cv * S.CV := by
    have := ok.one_le_cv
    have := S.CV_ge
    positivity
  have hk := ok.lam_pos k
  calc S.cv * S.CV * S.lam (k + 1) * (S.rho (k + 1) : ℝ) ^ (S.d - 1)
      ≤ S.cv * S.CV * (2 * S.lam k) * (5 ^ (S.d - 1) * (S.rho k : ℝ) ^ (S.d - 1)) := by
        have := ok.lam_pos (k + 1)
        gcongr
    _ = (2 * 5 ^ (S.d - 1)) * (S.cv * S.CV * S.lam k * (S.rho k : ℝ) ^ (S.d - 1)) := by ring
    _ ≤ 2 ^ (3 * S.d) * (S.cv * S.CV * S.lam k * (S.rho k : ℝ) ^ (S.d - 1)) := by
        gcongr

theorem E_nonneg (j : ℕ) : 0 ≤ S.E j := by
  have := ok.Csigma_nonneg
  have := ok.v_nonneg j
  have := S.D_nonneg j
  unfold Setting.E
  positivity

/-- (F2): `(v_k + 2σ_k) D_k ≤ E_k`. -/
theorem v_add_two_sigma_D_le (k : ℕ) : (S.v k + 2 * S.sigma k) * S.D k ≤ S.E k := by
  have h1 := ok.sigma_le k
  have h2 := ok.v_succ_le k
  have h3 := ok.Csigma_nonneg
  have h4 := S.D_nonneg k
  have h5 : S.sigma k ≤ S.Csigma * (2 ^ (3 * S.d) * S.v k) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 h3)
  unfold Setting.E
  have : S.v k + 2 * S.sigma k ≤ (1 + 2 ^ (3 * S.d + 1) * S.Csigma) * S.v k := by
    have : (2 : ℝ) ^ (3 * S.d + 1) = 2 * 2 ^ (3 * S.d) := by rw [pow_succ]; ring
    have e : (1 + 2 ^ (3 * S.d + 1) * S.Csigma) * S.v k =
        S.v k + 2 * (S.Csigma * (2 ^ (3 * S.d) * S.v k)) := by rw [this]; ring
    linarith [h5, e]
  exact mul_le_mul_of_nonneg_right this h4

/-! ### (F3) -/

theorem tau_succ_sub_le (j : ℕ) :
    S.tau (j + 1) - S.tau j ≤ 2 * S.A2 * S.p2 * S.θp * S.lam (j + 1) ^ (S.p2 - 1) := by
  have h := abs_pow_sub_pow_le (S.lam (j + 1)) (S.lam j) S.p2
  have h1 := ok.lam_pos j
  have h2 := ok.lam_pos (j + 1)
  have h3 := (ok.lam_step j).2
  have h4 := ok.lam_mono (Nat.le_succ j)
  have hmax : max |S.lam (j + 1)| |S.lam j| = S.lam (j + 1) := by
    rw [abs_of_pos h1, abs_of_pos h2]; exact max_eq_left h4
  rw [hmax, abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ h1.le h4 _)),
    abs_of_nonneg (sub_nonneg.mpr h4)] at h
  have h5 : S.lam (j + 1) ^ S.p2 - S.lam j ^ S.p2 ≤
      S.θp * S.p2 * S.lam (j + 1) ^ (S.p2 - 1) := by
    calc S.lam (j + 1) ^ S.p2 - S.lam j ^ S.p2
        ≤ (S.lam (j + 1) - S.lam j) * S.p2 * S.lam (j + 1) ^ (S.p2 - 1) := h
      _ ≤ S.θp * S.p2 * S.lam (j + 1) ^ (S.p2 - 1) := by gcongr
  have hA := ok.A2_pos
  unfold Setting.tau
  nlinarith

/-! ### (F4), (F5) -/

theorem w_le (j : ℕ) : S.w j ≤ S.Cw * S.lam j ^ (2 * S.d + 1) := by
  have hρ := ok.rho_le j
  have hρ1 := ok.one_le_rho_real j
  have hcv := ok.one_le_cv
  have hCV := S.CV_ge
  have hl := ok.lam_pos j
  have hd := ok.one_le_d
  unfold Setting.w Setting.v Typing.Cw
  have hc : 0 ≤ S.cv * S.CV := by positivity
  have hpow : (S.rho j : ℝ) ^ (S.d - 1) * S.rho j = (S.rho j : ℝ) ^ S.d := by
    rw [← pow_succ]; congr 1; omega
  calc S.cv * S.CV * S.lam j * (S.rho j : ℝ) ^ (S.d - 1) * S.rho j
      = S.cv * S.CV * S.lam j * (S.rho j : ℝ) ^ S.d := by rw [mul_assoc _ _ (S.rho j : ℝ), hpow]
    _ ≤ S.cv * S.CV * S.lam j * (S.c0 * (S.Rb + 1) * S.lam j ^ 2) ^ S.d := by gcongr
    _ = S.cv * S.CV * (S.c0 : ℝ) ^ S.d * (S.Rb + 1) ^ S.d * S.lam j ^ (2 * S.d + 1) := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

theorem Cw_nonneg : 0 ≤ S.Cw := by
  have := ok.one_le_cv
  have := S.CV_ge
  have := ok.Rb_pos
  unfold Typing.Cw
  positivity

end Setting.Ok

end Balaban.LargeField
