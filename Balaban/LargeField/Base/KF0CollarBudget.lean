/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0MeanShell
public import Balaban.LargeField.Base.KF0CollarClosure
public import Balaban.LargeField.Base.KF0BoundarySquare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The collar budget (KF0-LINK, L38.4)

Source: `notes/phase1/KF0-LINK.md` §1, paragraph "PROVED (new collar budget)" (L38.4), with the
corrected hypothesis: `β` is large (so `L = log(βa) ≥ 1`) and `a_Q ≥ A₀ log(βa)/√β`.

* `freezeRadius_le`, `freezeRadius_eq_zero_of_log_nonpos` (T1): with `t = √β a_Q`,
  `R ≤ (2/η) max(log(C_L t L), 0) + 1`, and `R = 0` when the logarithm is not positive.
* `kf0_log_poly_dominated`: the one-variable lemma, `Λ t (α (κ t²)^{1/(4d)} + 5)^d ≤ δ t²` for
  `t` large; its proof uses `log x ≤ x^ε/ε` (`Real.log_le_rpow_div`).
* `collar_budget_core`, `collar_budget` (T2), `collar_budget_uniform`, `collar_budget_gap` (T3):
  `(βν/4) a_Q² ≥ C_loss L (2⌈R/s⌉+1)^d + c L²` for `β ≥ β₁` and `a_Q ≥ A₀ L/√β`, where
  `c < A₀² ν/4`; the threshold `β₁` depends only on `d`, the bounds for `C_L`, `η`, and
  `A₀, c, C_loss, ν`, not on `a ≥ 1`.
* `sum_collar_budget` (T4): the summed form over the dressed components.
* `collar_budget_instance` (T5): `d = 3, ν = 1, a = 2, A₀ = 3, c = 1, s = 9, C_loss = 1`.

Arithmetic only.  The integrated collar potential, the linked expansion and the one-scale theorem
are NOT proved here.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Finset Balaban.KW

open scoped Classical

namespace Balaban.LargeField

/-! ### T1: the size of the frozen radius -/

theorem freezeRadius_le {d : ℕ} (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (β a aQ : ℝ) :
    (freezeRadius d ν β a aQ : ℝ) ≤
      2 / (-Real.log (kwQ d ν)) *
        max (Real.log (cL d ν * Real.sqrt β * aQ * Real.log (β * a))) 0 + 1 := by
  have heta : 0 < -Real.log (kwQ d ν) :=
    neg_pos.2 (Real.log_neg (kwQ_pos hd hν) (kwQ_lt_one hν))
  unfold freezeRadius
  have h0 : 0 ≤ 2 / (-Real.log (kwQ d ν)) *
      max (Real.log (cL d ν * Real.sqrt β * aQ * Real.log (β * a))) 0 := by positivity
  exact (Nat.ceil_lt_add_one h0).le

theorem freezeRadius_eq_zero_of_log_nonpos {d : ℕ} {ν β a aQ : ℝ}
    (h : Real.log (cL d ν * Real.sqrt β * aQ * Real.log (β * a)) ≤ 0) :
    freezeRadius d ν β a aQ = 0 := by
  unfold freezeRadius
  rw [max_eq_right h]
  simp

/-! ### The one-variable lemma -/

theorem kf0_log_poly_dominated {d : ℕ} (hd : 0 < d) {Λ α κ δ : ℝ} (hΛ : 0 ≤ Λ) (hα : 0 < α)
    (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      Λ * t * (α * (κ * t ^ 2) ^ ((1 : ℝ) / (4 * d)) + 5) ^ d ≤ δ * t ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = α * κ ^ ((1 : ℝ) / (4 * d)) + 5 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  refine ⟨max 1 ((Λ * B ^ d / δ) ^ 2), le_max_left _ _, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith
  have hu1 : 1 ≤ t ^ ((1 : ℝ) / (2 * d)) := Real.one_le_rpow ht1 (by positivity)
  have h1 : (κ * t ^ 2) ^ ((1 : ℝ) / (4 * d)) = κ ^ ((1 : ℝ) / (4 * d)) * t ^ ((1 : ℝ) / (2 * d)) := by
    rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0]
    congr 2
    push_cast
    field_simp
    ring
  have h2 : (t ^ ((1 : ℝ) / (2 * d))) ^ d = Real.sqrt t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0, Real.sqrt_eq_rpow]
    congr 1
    field_simp
  have h3 : α * (κ * t ^ 2) ^ ((1 : ℝ) / (4 * d)) + 5 ≤ B * t ^ ((1 : ℝ) / (2 * d)) := by
    rw [h1, hBdef]
    nlinarith [mul_nonneg hα.le (Real.rpow_nonneg hκ.le ((1 : ℝ) / (4 * d)))]
  have h4 : (α * (κ * t ^ 2) ^ ((1 : ℝ) / (4 * d)) + 5) ^ d ≤ B ^ d * Real.sqrt t := by
    calc _ ≤ (B * t ^ ((1 : ℝ) / (2 * d))) ^ d := pow_le_pow_left₀ (by positivity) h3 d
      _ = B ^ d * Real.sqrt t := by rw [mul_pow, h2]
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h5 : Λ * B ^ d / δ ≤ Real.sqrt t := by
    have : (Λ * B ^ d / δ) ^ 2 ≤ t := (le_max_right _ _).trans ht
    calc Λ * B ^ d / δ ≤ Real.sqrt ((Λ * B ^ d / δ) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt this
  have h6 : Λ * B ^ d ≤ δ * Real.sqrt t := by
    have := (div_le_iff₀ hδ).1 h5
    linarith [mul_comm (Real.sqrt t) δ]
  have ht2 : t ^ 2 = t * Real.sqrt t * Real.sqrt t := by
    rw [mul_assoc, Real.mul_self_sqrt ht0]; ring
  calc Λ * t * (α * (κ * t ^ 2) ^ ((1 : ℝ) / (4 * d)) + 5) ^ d
      ≤ Λ * t * (B ^ d * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = t * Real.sqrt t * (Λ * B ^ d) := by ring
    _ ≤ t * Real.sqrt t * (δ * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = δ * t ^ 2 := by rw [ht2]; ring

/-! ### T2: the budget -/

/-- The core of the budget, with the constants `C_L ≤ Cm`, `η ≥ ηm` and `ν ≥ ν₀` abstracted. -/
theorem collar_budget_core {d : ℕ} (hd : 0 < d) {ν₀ Cm ηm A₀ c Cl : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hν₀ : 0 < ν₀) (hCm : 0 < Cm) (hηm : 0 < ηm) (hA : 0 < A₀) (hCl : 0 ≤ Cl) (hc0 : 0 ≤ c)
    (hc : c < A₀ ^ 2 * ν₀ / 4) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ ν β a aQ : ℝ, ν₀ ≤ ν → cL d ν ≤ Cm →
      ηm ≤ -Real.log (kwQ d ν) → 1 ≤ a → β₁ ≤ β →
      A₀ * Real.log (β * a) / Real.sqrt β ≤ aQ →
      Cl * Real.log (β * a) *
          ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d +
        c * Real.log (β * a) ^ 2 ≤ β * ν / 4 * aQ ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (1 : ℝ) / (4 * d) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 4 / (ηm * ε) := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Cm / A₀ := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ν₀ / 4 - c / A₀ ^ 2 := ⟨_, rfl⟩
  have hA2 : 0 < A₀ ^ 2 := by positivity
  have hδ : 0 < δ := by
    have : c / A₀ ^ 2 < ν₀ / 4 := by rw [div_lt_iff₀ hA2]; linarith
    rw [hδdef]; linarith
  obtain ⟨t₀, ht₀1, ht₀⟩ := kf0_log_poly_dominated hd (Λ := Cl / A₀) (α := α) (κ := κ)
    (div_nonneg hCl hA.le) hα hκ hδ
  refine ⟨Real.exp (max 1 (t₀ / A₀)), Real.one_le_exp ((le_max_left _ _).trans' zero_le_one), ?_⟩
  intro ν β a aQ hν hC hη ha hβ haQ
  have hν0 : 0 < ν := hν₀.trans_le hν
  have hβ0 : 0 < β := (Real.exp_pos _).trans_le hβ
  have hsq : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hLge : max 1 (t₀ / A₀) ≤ Real.log (β * a) := by
    have h1 : max 1 (t₀ / A₀) ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hβ
    have h2 : Real.log β ≤ Real.log (β * a) :=
      Real.log_le_log hβ0 (by nlinarith)
    linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (β * a) := ⟨_, rfl⟩
  rw [← hLdef] at hLge haQ ⊢
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLge
  have hL0 : 0 < L := by linarith
  have hLt : t₀ ≤ A₀ * L := by
    have := (le_max_right _ _).trans hLge
    rw [div_le_iff₀ hA] at this
    linarith
  have htL : A₀ * L ≤ Real.sqrt β * aQ := by
    have := (div_le_iff₀ hsq).1 haQ
    linarith
  have haQ0 : 0 < aQ := by
    have : 0 < A₀ * L / Real.sqrt β := by positivity
    linarith
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.sqrt β * aQ := ⟨_, rfl⟩
  rw [← htdef] at htL
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htt : t ^ 2 = β * aQ ^ 2 := by
    rw [htdef, mul_pow, Real.sq_sqrt hβ0.le]
  have hLt' : L ≤ t / A₀ := by rw [le_div_iff₀ hA]; linarith
  have hCpos : 0 < cL d ν := cL_pos hd hν0
  -- the radius
  have hR := freezeRadius_le hd hν0 β a aQ
  rw [← hLdef] at hR
  have hCtL : cL d ν * Real.sqrt β * aQ * L = cL d ν * t * L := by rw [htdef]; ring
  rw [hCtL] at hR
  have hCtL' : cL d ν * t * L ≤ κ * t ^ 2 := by
    calc cL d ν * t * L ≤ Cm * t * (t / A₀) := by gcongr
      _ = κ * t ^ 2 := by rw [hκdef]; field_simp
  have hlog : Real.log (cL d ν * t * L) ≤ Real.log (κ * t ^ 2) :=
    Real.log_le_log (by positivity) hCtL'
  have hm : max (Real.log (cL d ν * t * L)) 0 ≤ (κ * t ^ 2) ^ ε / ε :=
    max_le (hlog.trans (Real.log_le_rpow_div (by positivity) hε0)) (by positivity)
  have hm0 : 0 ≤ max (Real.log (cL d ν * t * L)) 0 := le_max_right _ _
  have hη0 : 0 < -Real.log (kwQ d ν) := hηm.trans_le hη
  have h2η : 2 / (-Real.log (kwQ d ν)) ≤ 2 / ηm :=
    div_le_div_of_nonneg_left (by norm_num) hηm hη
  have hRb : (freezeRadius d ν β a aQ : ℝ) ≤ 2 / ηm * ((κ * t ^ 2) ^ ε / ε) + 1 := by
    refine hR.trans ?_
    have := mul_le_mul h2η hm hm0 (by positivity)
    linarith
  have hceil : (⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ : ℝ) < (freezeRadius d ν β a aQ : ℝ) / s + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hRs : (freezeRadius d ν β a aQ : ℝ) / s ≤ freezeRadius d ν β a aQ :=
    div_le_self (Nat.cast_nonneg _) hs1
  have hK : ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ≤
      α * (κ * t ^ 2) ^ ε + 5 := by
    have e : α * (κ * t ^ 2) ^ ε = 4 * (2 / ηm * ((κ * t ^ 2) ^ ε / ε)) / 2 := by
      rw [hαdef]; field_simp
    push_cast
    nlinarith
  have hKd : ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d ≤
      (α * (κ * t ^ 2) ^ ε + 5) ^ d := pow_le_pow_left₀ (by positivity) hK d
  have hloss : Cl * L * ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d ≤
      Cl / A₀ * t * (α * (κ * t ^ 2) ^ ε + 5) ^ d := by
    have : Cl * L ≤ Cl / A₀ * t := by
      calc Cl * L ≤ Cl * (t / A₀) := mul_le_mul_of_nonneg_left hLt' hCl
        _ = Cl / A₀ * t := by ring
    exact mul_le_mul this hKd (by positivity) (by positivity)
  have hdom := ht₀ t (hLt.trans htL)
  rw [← hεdef] at hdom
  have hcL : c * L ^ 2 ≤ c / A₀ ^ 2 * t ^ 2 := by
    calc c * L ^ 2 ≤ c * (t / A₀) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0.le hLt' 2) hc0
      _ = c / A₀ ^ 2 * t ^ 2 := by rw [div_pow]; ring
  have hfin : ν₀ / 4 * t ^ 2 ≤ ν / 4 * t ^ 2 := by
    gcongr
  calc _ ≤ δ * t ^ 2 + c / A₀ ^ 2 * t ^ 2 := add_le_add (hloss.trans hdom) hcL
    _ = ν₀ / 4 * t ^ 2 := by rw [hδdef]; ring
    _ ≤ ν / 4 * t ^ 2 := hfin
    _ = β * ν / 4 * aQ ^ 2 := by rw [htt]; ring

/-- **(L38.4), T2.**  Fix `d ≥ 1`, `0 < ν`, `s ≥ 1`, `C_loss ≥ 0`, `A₀ > 0` and `0 ≤ c < A₀²ν/4`.
There is `β₁ > 0` such that for all `a ≥ 1`, `β ≥ β₁` and `a_Q ≥ A₀ log(βa)/√β`:
`(βν/4) a_Q² ≥ C_loss log(βa) (2⌈R/s⌉+1)^d + c log²(βa)`, `R = freezeRadius d ν β a a_Q`.
(No upper bound on `a_Q` is needed.) -/
theorem collar_budget {d : ℕ} (hd : 0 < d) {ν A₀ c Cl : ℝ} {s : ℕ} (hs : 1 ≤ s) (hν : 0 < ν)
    (hA : 0 < A₀) (hCl : 0 ≤ Cl) (hc0 : 0 ≤ c) (hc : c < A₀ ^ 2 * ν / 4) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ β a aQ : ℝ, 1 ≤ a → β₁ ≤ β →
      A₀ * Real.log (β * a) / Real.sqrt β ≤ aQ →
      Cl * Real.log (β * a) *
          ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d +
        c * Real.log (β * a) ^ 2 ≤ β * ν / 4 * aQ ^ 2 := by
  have hη : 0 < -Real.log (kwQ d ν) :=
    neg_pos.2 (Real.log_neg (kwQ_pos hd hν) (kwQ_lt_one hν))
  obtain ⟨β₁, hβ₁, h⟩ := collar_budget_core hd hs hν (cL_pos hd hν) hη hA hCl hc0 hc
  exact ⟨β₁, hβ₁, fun β a aQ ha hβ haQ => h ν β a aQ le_rfl le_rfl le_rfl ha hβ haQ⟩

/-! ### T3: uniformity in `ν ∈ [ν₀, 1]` -/

theorem shellSum_mono {q q' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' < 1) (d : ℕ) :
    shellSum d q ≤ shellSum d q' := by
  unfold shellSum
  exact Summable.tsum_le_tsum (fun r => by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq hqq (by positivity)) (by positivity))
    (shell_summable hq (hqq.trans_lt hq')) (shell_summable (hq.trans hqq) hq')

theorem cL_le_of_gap {d : ℕ} (hd : 0 < d) {ν ν₀ : ℝ} (hν₀ : 0 < ν₀) (h : ν₀ ≤ ν) (h1 : ν ≤ 1) :
    cL d ν ≤ 4 * d * shellSum d (kwQ d ν₀) / (ν₀ * kwQ d 1) := by
  have hν : 0 < ν := hν₀.trans_le h
  have hq := kwQ_le_gap (d := d) hν₀ h
  have hq1 := kwQ_le_gap (d := d) hν h1
  have hq0 := kwQ_pos hd hν
  have hq10 := kwQ_pos hd (one_pos : (0 : ℝ) < 1)
  have hS := shellSum_mono (d := d) hq0.le hq.1 hq.2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold cL
  refine div_le_div₀ (by have := shellSum_pos (d := d) (kwQ_pos hd hν₀).le hq.2; positivity)
    (by gcongr) (by positivity) ?_
  exact mul_le_mul h hq1.1 hq10.le hν.le

theorem eta_ge_of_gap {d : ℕ} (hd : 0 < d) {ν ν₀ : ℝ} (hν₀ : 0 < ν₀) (h : ν₀ ≤ ν) :
    -Real.log (kwQ d ν₀) ≤ -Real.log (kwQ d ν) := by
  have hν : 0 < ν := hν₀.trans_le h
  have := Real.log_le_log (kwQ_pos hd hν) (kwQ_le_gap (d := d) hν₀ h).1
  linarith

theorem eta_pos {d : ℕ} (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) : 0 < -Real.log (kwQ d ν) :=
  neg_pos.2 (Real.log_neg (kwQ_pos hd hν) (kwQ_lt_one hν))

/-- **T3.**  The same budget, with one threshold `β₁` for all `ν ∈ [ν₀, 1]`, `c < A₀²ν₀/4`. -/
theorem collar_budget_uniform {d : ℕ} (hd : 0 < d) {ν₀ A₀ c Cl : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hν₀ : 0 < ν₀) (hA : 0 < A₀) (hCl : 0 ≤ Cl) (hc0 : 0 ≤ c) (hc : c < A₀ ^ 2 * ν₀ / 4) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ ν β a aQ : ℝ, ν₀ ≤ ν → ν ≤ 1 → 1 ≤ a → β₁ ≤ β →
      A₀ * Real.log (β * a) / Real.sqrt β ≤ aQ →
      Cl * Real.log (β * a) *
          ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d +
        c * Real.log (β * a) ^ 2 ≤ β * ν / 4 * aQ ^ 2 := by
  have hq0 := kwQ_pos hd hν₀
  have hCm : 0 < 4 * d * shellSum d (kwQ d ν₀) / (ν₀ * kwQ d 1) := by
    have := shellSum_pos (d := d) hq0.le (kwQ_lt_one hν₀)
    have := kwQ_pos hd (one_pos : (0 : ℝ) < 1)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  obtain ⟨β₁, hβ₁, h⟩ := collar_budget_core hd hs hν₀ hCm (eta_pos hd hν₀) hA hCl hc0 hc
  exact ⟨β₁, hβ₁, fun ν β a aQ h0 h1 ha hβ haQ =>
    h ν β a aQ h0 (cL_le_of_gap hd hν₀ h0 h1) (eta_ge_of_gap hd hν₀ h0) ha hβ haQ⟩

/-- **T3 at the reference gap.**  `ν_* = kf0Gap L₀`, `L₀ ≥ 1`, `c < A₀² ν_*/4`. -/
theorem collar_budget_gap {d : ℕ} (hd : 0 < d) {L₀ : ℕ} (hL₀ : 0 < L₀) {A₀ c Cl : ℝ} {s : ℕ}
    (hs : 1 ≤ s) (hA : 0 < A₀) (hCl : 0 ≤ Cl) (hc0 : 0 ≤ c)
    (hc : c < A₀ ^ 2 * Green.kf0Gap L₀ / 4) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ ν β a aQ : ℝ, Green.kf0Gap L₀ ≤ ν → ν ≤ 1 → 1 ≤ a → β₁ ≤ β →
      A₀ * Real.log (β * a) / Real.sqrt β ≤ aQ →
      Cl * Real.log (β * a) *
          ((2 * ⌈(freezeRadius d ν β a aQ : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d +
        c * Real.log (β * a) ^ 2 ≤ β * ν / 4 * aQ ^ 2 :=
  collar_budget_uniform hd hs (Green.kf0Gap_pos hL₀) hA hCl hc0 hc

/-! ### T4: the summed form over dressed components -/

section Sum

variable {d ℓ s m : ℕ} [NeZero ℓ] [NeZero m]

/-- **T4.**  For a bad set `B` with amplitudes `a_Q ≥ A₀ L/√β` and radii `R_Q = freezeRadius`,
`∑_{Q∈B} (βν/4) a_Q² ≥ C_loss L ∑_I |S_I| + c L² |B|` (`L = log(βa)`). -/
theorem sum_collar_budget (hd : 0 < d) {ν A₀ c Cl : ℝ} (hs : 1 ≤ s) (hν : 0 < ν)
    (hA : 0 < A₀) (hCl : 0 ≤ Cl) (hc0 : 0 ≤ c) (hc : c < A₀ ^ 2 * ν / 4) (hℓ : ℓ = s * m) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ β a : ℝ, 1 ≤ a → β₁ ≤ β → ∀ (B : Finset (Torus d m))
      (aQ : Torus d m → ℝ), (∀ Q ∈ B, A₀ * Real.log (β * a) / Real.sqrt β ≤ aQ Q) →
      Cl * Real.log (β * a) *
          ((∑ I ∈ kf0Components ℓ s m (fun Q => freezeRadius d ν β a (aQ Q)) B,
              (kf0Support ℓ s m (fun Q => freezeRadius d ν β a (aQ Q)) I).card : ℕ) : ℝ) +
        c * Real.log (β * a) ^ 2 * (B.card : ℝ) ≤
      ∑ Q ∈ B, β * ν / 4 * aQ Q ^ 2 := by
  obtain ⟨β₁, hβ₁, h⟩ := collar_budget hd hs hν hA hCl hc0 hc
  refine ⟨β₁, hβ₁, fun β a ha hβ B aQ haQ => ?_⟩
  set R : Torus d m → ℕ := fun Q => freezeRadius d ν β a (aQ Q) with hR
  have h1 := sum_card_support_le (ℓ := ℓ) (s := s) (m := m) (R := R) (B := B)
  have h2 : ∑ Q ∈ B, (kf0Collar ℓ s m R Q).card ≤
      ∑ Q ∈ B, (2 * ⌈(R Q : ℝ) / s⌉₊ + 1) ^ d :=
    Finset.sum_le_sum fun Q _ => card_kf0Collar_le hℓ R Q
  have h3 : ((∑ I ∈ kf0Components ℓ s m R B, (kf0Support ℓ s m R I).card : ℕ) : ℝ) ≤
      ∑ Q ∈ B, ((2 * ⌈(R Q : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d := by
    have := h1.trans h2
    exact_mod_cast this
  have hL : 0 ≤ Real.log (β * a) := by
    exact Real.log_nonneg (by nlinarith)
  calc _ ≤ Cl * Real.log (β * a) * ∑ Q ∈ B, ((2 * ⌈(R Q : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d +
        c * Real.log (β * a) ^ 2 * (B.card : ℝ) := by
          gcongr
    _ = ∑ Q ∈ B, (Cl * Real.log (β * a) * ((2 * ⌈(R Q : ℝ) / s⌉₊ + 1 : ℕ) : ℝ) ^ d +
          c * Real.log (β * a) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun Q hQ => h β a (aQ Q) ha hβ (haQ Q hQ)

end Sum

/-! ### T5: a non-vacuity instance -/

theorem log_two_mul_div_sqrt_le {β : ℝ} (hβ : 10368 ≤ β) :
    3 * Real.log (β * 2) / Real.sqrt β ≤ 2 := by
  have hβ0 : 0 < β := by linarith
  have hsq : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hx0 : 0 ≤ β * 2 := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt (Real.sqrt (β * 2)) := ⟨_, rfl⟩
  have hu12 : 12 ≤ u := by
    rw [hu]
    refine Real.le_sqrt_of_sq_le ?_
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hu2 : u ^ 2 = Real.sqrt (β * 2) := by
    rw [hu, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hu4 : u ^ 4 = β * 2 := by
    have : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [this, hu2, Real.sq_sqrt hx0]
  have hlog : Real.log (β * 2) ≤ 4 * (u - 1) := by
    have h1 : Real.log (β * 2) = 4 * Real.log u := by
      rw [← hu4, Real.log_pow]; norm_num
    have h2 := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
    rw [h1]; linarith
  have hsqrt : u ^ 2 ≤ 2 * Real.sqrt β := by
    rw [hu2, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hβ0.le]
  rw [div_le_iff₀ hsq]
  nlinarith

/-- **T5.**  For `d = 3`, `ν = 1`, `a = 2`, `A₀ = 3`, `c = 1 < 9/4`, `s = 9`, `C_loss = 1`: for all
large `β` the interval `[3 log(2β)/√β, 2]` is nonempty and the budget holds for each `a_Q` in it. -/
theorem collar_budget_instance :
    ∃ β₁ : ℝ, ∀ β : ℝ, β₁ ≤ β →
      (3 * Real.log (β * 2) / Real.sqrt β ≤ 2) ∧
      ∀ aQ : ℝ, 3 * Real.log (β * 2) / Real.sqrt β ≤ aQ → aQ ≤ 2 →
        1 * Real.log (β * 2) *
            ((2 * ⌈(freezeRadius 3 1 β 2 aQ : ℝ) / (9 : ℕ)⌉₊ + 1 : ℕ) : ℝ) ^ 3 +
          1 * Real.log (β * 2) ^ 2 ≤ β * 1 / 4 * aQ ^ 2 := by
  obtain ⟨β₁, hβ₁, h⟩ := collar_budget (d := 3) (ν := 1) (A₀ := 3) (c := 1) (Cl := 1) (s := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨max β₁ 10368, fun β hβ => ⟨log_two_mul_div_sqrt_le ((le_max_right _ _).trans hβ), ?_⟩⟩
  intro aQ haQ _
  exact h β 2 aQ (by norm_num) ((le_max_left _ _).trans hβ) haQ

end Balaban.LargeField
