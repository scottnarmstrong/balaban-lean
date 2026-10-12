module

public import Balaban.LargeField.Counter.Bars
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The partial sums `W` and the ripeness time after a restart (Part I, Lemma I.5.3)
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

theorem W_split {a t : ℕ} (h : a ≤ t) : S.W a t = S.w a + S.W (a + 1) t := by
  unfold Setting.W
  rw [Finset.Icc_eq_cons_Ioc h, Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]

theorem W_eq_zero_of_lt {a t : ℕ} (h : t < a) : S.W a t = 0 := by
  unfold Setting.W
  rw [Finset.Icc_eq_empty_of_lt h]; simp

end Setting

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

theorem W_nonneg (a t : ℕ) : 0 ≤ S.W a t :=
  Finset.sum_nonneg (fun j _ => ok.w_nonneg j)

theorem W_mono_right (a : ℕ) : Monotone (S.W a) := by
  intro t t' h
  unfold Setting.W
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl h
  · intro j _ _; exact ok.w_nonneg j

theorem W_le (a t : ℕ) :
    S.W a t ≤ ((t + 1 - a : ℕ) : ℝ) * (S.Cw * S.lam t ^ (2 * S.d + 1)) := by
  unfold Setting.W
  have h := Finset.sum_le_card_nsmul (Finset.Icc a t) (fun j => S.w j)
    (S.Cw * S.lam t ^ (2 * S.d + 1)) (fun j hj => by
      have hjt : j ≤ t := (Finset.mem_Icc.mp hj).2
      calc S.w j ≤ S.Cw * S.lam j ^ (2 * S.d + 1) := ok.w_le j
        _ ≤ S.Cw * S.lam t ^ (2 * S.d + 1) := by
          have := ok.Cw_nonneg
          have := (ok.lam_pos j).le
          have := ok.lam_mono hjt
          gcongr)
  simpa [Nat.card_Icc] using h

theorem tau_mono : Monotone S.tau := by
  intro a b hab
  unfold Setting.tau
  have := ok.A2_pos
  have := (ok.lam_pos a).le
  have := ok.lam_mono hab
  gcongr

theorem tau_nonneg (t : ℕ) : 0 ≤ S.tau t := by
  have := ok.A2_pos
  have := (ok.lam_pos t).le
  unfold Setting.tau
  positivity

/-- Lemma I.5.3 in terms of the clock `s'` of the restarted component: for
`μ ≤ s' ≤ μ + 1 + Λ'` and `t = s' + n_q(s')`, with `X = max {λ_μ, Λ'}`. -/
theorem restart_bounds {μ s' : ℕ} {Λ' : ℝ} (hs1 : μ ≤ s')
    (hs2 : (s' : ℝ) ≤ μ + 1 + Λ') :
    S.lam (s' + S.nq s') ≤ S.cPrime * max (S.lam μ) Λ' ∧
    ((s' + S.nq s' : ℕ) : ℝ) - μ + 1 ≤ S.Ct * max (S.lam μ) Λ' ∧
    S.tau (s' + S.nq s') + S.W μ (s' + S.nq s') ≤ S.Phi (max (S.lam μ) Λ') := by
  set X := max (S.lam μ) Λ' with hX
  have hX1 : 1 ≤ X := le_trans (ok.one_le_lam μ) (le_max_left _ _)
  have hΛX : Λ' ≤ X := le_max_right _ _
  have hlamX : S.lam μ ≤ X := le_max_left _ _
  have hθ := ok.θp_pos
  have hcs := ok.cStar_ge_one
  have hαL := ok.αlogL_pos
  -- the clock
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hs1
  have hx : (x : ℝ) ≤ 1 + Λ' := by push_cast at hs2; linarith
  have h1 : S.lam (μ + x) ≤ (1 + 2 * S.θp) * X := by
    have := ok.lam_add_le μ x
    nlinarith
  have h2 : S.lam (μ + x + S.nq (μ + x)) ≤ S.cPrime * X := by
    have := ok.lam_add_nq (μ + x)
    unfold Typing.cPrime
    have h3 : S.θp ≤ S.cStar * S.θp * X := by
      have : 1 ≤ S.cStar * X := one_le_mul_of_one_le_of_one_le hcs hX1
      nlinarith
    nlinarith
  refine ⟨h2, ?_, ?_⟩
  · have := ok.nq_le (μ + x)
    have h4 : S.lam (μ + x) / (S.α * S.logL) ≤ (1 + 2 * S.θp) * X / (S.α * S.logL) :=
      div_le_div_of_nonneg_right h1 hαL.le
    have h5 : (1 + 2 * S.θp) * X / (S.α * S.logL) = ((1 + 2 * S.θp) / (S.α * S.logL)) * X := by
      ring
    unfold Typing.Ct
    push_cast
    nlinarith
  · have hcount := (ok.W_le μ (μ + x + S.nq (μ + x)))
    have hcnt : ((μ + x + S.nq (μ + x) + 1 - μ : ℕ) : ℝ) ≤ S.Ct * X := by
      have : ((μ + x + S.nq (μ + x) + 1 - μ : ℕ) : ℝ) =
          ((μ + x + S.nq (μ + x) : ℕ) : ℝ) - μ + 1 := by
        have : μ ≤ μ + x + S.nq (μ + x) := by omega
        rw [Nat.cast_sub (by omega)]
        push_cast; ring
      rw [this]
      have := ok.nq_le (μ + x)
      have h4 : S.lam (μ + x) / (S.α * S.logL) ≤ (1 + 2 * S.θp) * X / (S.α * S.logL) :=
        div_le_div_of_nonneg_right h1 hαL.le
      have h5 : (1 + 2 * S.θp) * X / (S.α * S.logL) = ((1 + 2 * S.θp) / (S.α * S.logL)) * X := by
        ring
      unfold Typing.Ct
      push_cast
      nlinarith
    have hpos : 0 ≤ S.Cw * S.lam (μ + x + S.nq (μ + x)) ^ (2 * S.d + 1) := by
      have := ok.Cw_nonneg
      have := (ok.lam_pos (μ + x + S.nq (μ + x))).le
      positivity
    have hlam_t := ok.lam_pos (μ + x + S.nq (μ + x))
    have hpow1 : S.lam (μ + x + S.nq (μ + x)) ^ (2 * S.d + 1) ≤ (S.cPrime * X) ^ (2 * S.d + 1) :=
      pow_le_pow_left₀ hlam_t.le h2 _
    have hpow2 : S.lam (μ + x + S.nq (μ + x)) ^ S.p2 ≤ (S.cPrime * X) ^ S.p2 :=
      pow_le_pow_left₀ hlam_t.le h2 _
    have hCw := ok.Cw_nonneg
    have hW : S.W μ (μ + x + S.nq (μ + x)) ≤
        S.Ct * X * (S.Cw * (S.cPrime * X) ^ (2 * S.d + 1)) := by
      calc S.W μ (μ + x + S.nq (μ + x))
          ≤ ((μ + x + S.nq (μ + x) + 1 - μ : ℕ) : ℝ) *
            (S.Cw * S.lam (μ + x + S.nq (μ + x)) ^ (2 * S.d + 1)) := hcount
        _ ≤ S.Ct * X * (S.Cw * (S.cPrime * X) ^ (2 * S.d + 1)) := by
          apply mul_le_mul hcnt _ hpos (by
            have : 0 ≤ S.Ct := by
              unfold Typing.Ct
              have := ok.αlogL_pos
              have := ok.θp_pos
              positivity
            positivity)
          exact mul_le_mul_of_nonneg_left hpow1 hCw
    have hτ : S.tau (μ + x + S.nq (μ + x)) ≤ 2 * S.A2 * (S.cPrime * X) ^ S.p2 := by
      unfold Setting.tau
      have := ok.A2_pos
      gcongr
    unfold Typing.Phi
    calc S.tau (μ + x + S.nq (μ + x)) + S.W μ (μ + x + S.nq (μ + x))
        ≤ 2 * S.A2 * (S.cPrime * X) ^ S.p2 +
          S.Ct * X * (S.Cw * (S.cPrime * X) ^ (2 * S.d + 1)) := by linarith
      _ = _ := by ring

end Setting.Ok

end Balaban.LargeField
