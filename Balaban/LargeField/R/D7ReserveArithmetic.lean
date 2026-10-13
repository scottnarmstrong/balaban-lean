module

public import Balaban.LargeField.Counter.Bars
public import Balaban.LargeField.Analytic.Constants
public import Balaban.LargeField.Def7WitLF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Arithmetic of the reserve ledger for removed large-field components (VMOD-40, package 2)

A removed component `c` has at most `(crit_k)^d` cubes (`RegionHistory.removed_card_le`), and the
size increment of a label is at most `(d L + d + 3) |c|` (`d7Size_le_d7SizePre_add`).  The factor
`e^{-p₂,run(k)}` of the component must pay `κ (d L + d + 3) (crit_k)^d` together with three
entropy terms and `log⁺ (B_st / B₀)`.  This file proves the arithmetic of that ledger.

* `crit_le_critBar`, `crit_pow_le`: `crit_j ≤ crit̄(λ_j)` and
  `crit_j ^ d ≤ ccrit · (1 + λ_j ^ (2d))`, with `ccrit = 2^d ((2c₀+10)^d + (2c₀R_base)^d)`.
* `crit_pow_le_logBeta`: if `λ_j = λ̂_j` (the landed link, the hypothesis `hlam` of
  `Def7v2Basic`/`Def7Basic`, `Budget/LemmaB.lean`) and `RunningHyp` holds, then
  `crit_j ^ d ≤ ccrit · (1 + (log β_j + 3)^(2d))`.
* `mul_crit_pow_le_half_p2Run`: for `A₂ > 0`, `p₂ ≥ 2d+1`, `K ≥ 0` and
  `log β_j ≥ reserveX0 K` one has `K · crit_j^d ≤ ½ · p2Run`; the same holds for the logarithm
  of the rooted-entropy constant `Q · crit_j^d` (`log_mul_crit_pow_le_half_p2Run`).
* `RD7ChargeParams`: the ledger as a record of numbers; `rd7Charge_of_large_logBeta` produces it,
  `RD7ChargeParams.exp_p2Run_le` is its exponential form, `exists_scale_rd7ChargeParams` and
  `wit_exists_scale_rd7ChargeParams` show it is inhabited.

This is arithmetic only.  The three entropy terms, the gas estimate and everything analytic about
the large-field operation `R` are NOT proved here; the results are independent of the choice of the
generator of `R`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace D7Reserve

/-! ### Pure real arithmetic -/

theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (d : ℕ) :
    (a + b) ^ d ≤ 2 ^ d * (a ^ d + b ^ d) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have h2 : (a + b) ^ d ≤ (2 * max a b) ^ d := pow_le_pow_left₀ (by positivity) h1 d
  have h3 : max a b ^ d ≤ a ^ d + b ^ d := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; have := pow_nonneg ha d; linarith
    · rw [max_eq_left h]; have := pow_nonneg hb d; linarith
  calc (a + b) ^ d ≤ (2 * max a b) ^ d := h2
    _ = 2 ^ d * max a b ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (a ^ d + b ^ d) := by gcongr

/-- The threshold of the domination: `X₀ = max 3 (2^(2d+2) K C / A₂)`. -/
noncomputable def x0 (d : ℕ) (K C A2 : ℝ) : ℝ := max 3 (2 ^ (2 * d + 2) * K * C / A2)

theorem dominate_aux {d p2 : ℕ} {K C A2 X : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hA : 0 < A2)
    (hp : 2 * d + 1 ≤ p2) (hX : x0 d K C A2 ≤ X) :
    K * (C * (1 + (X + 3) ^ (2 * d))) ≤ 1 / 2 * (A2 * X ^ p2) := by
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXA : 2 ^ (2 * d + 2) * K * C ≤ A2 * X := by
    have := le_trans (le_max_right _ _) hX
    rwa [div_le_iff₀ hA, mul_comm X] at this
  have hX0 : 0 ≤ X := by linarith
  have hpow : (X + 3) ^ (2 * d) ≤ 2 ^ (2 * d) * X ^ (2 * d) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have h1 : 1 ≤ X ^ (2 * d) := one_le_pow₀ hX1
  have h2 : (1 : ℝ) ≤ 2 ^ (2 * d) := one_le_pow₀ (by norm_num)
  have hsum : 1 + (X + 3) ^ (2 * d) ≤ 2 ^ (2 * d + 1) * X ^ (2 * d) := by
    have : 1 ≤ 2 ^ (2 * d) * X ^ (2 * d) := by nlinarith
    calc 1 + (X + 3) ^ (2 * d) ≤ 2 ^ (2 * d) * X ^ (2 * d) + 2 ^ (2 * d) * X ^ (2 * d) := by
          linarith
      _ = 2 ^ (2 * d + 1) * X ^ (2 * d) := by ring
  have hXp : X ^ (2 * d + 1) ≤ X ^ p2 := pow_le_pow_right₀ hX1 hp
  have hKC : 0 ≤ K * C := mul_nonneg hK hC
  have hP : 0 ≤ X ^ (2 * d) := by positivity
  calc K * (C * (1 + (X + 3) ^ (2 * d))) = K * C * (1 + (X + 3) ^ (2 * d)) := by ring
    _ ≤ K * C * (2 ^ (2 * d + 1) * X ^ (2 * d)) := by gcongr
    _ = 1 / 2 * ((2 ^ (2 * d + 2) * K * C) * X ^ (2 * d)) := by ring
    _ ≤ 1 / 2 * ((A2 * X) * X ^ (2 * d)) := by gcongr
    _ = 1 / 2 * (A2 * X ^ (2 * d + 1)) := by ring
    _ ≤ 1 / 2 * (A2 * X ^ p2) := by gcongr

/-! ### Polynomial bound for `crit` (T1) -/

variable {S : Setting}

/-- The constant `ccrit = 2^d ((2c₀+10)^d + (2c₀R_base)^d)`. -/
noncomputable def ccrit (S : Setting) : ℝ :=
  2 ^ S.d * ((2 * (S.c0 : ℝ) + 10) ^ S.d + (2 * (S.c0 : ℝ) * S.Rb) ^ S.d)

theorem ccrit_nonneg (ok : S.Ok) : 0 ≤ ccrit S := by
  have := ok.Rb_pos
  unfold ccrit; positivity

/-- `crit_j ≤ crit̄(λ_j)` (`critBar` is landed; this comparison was not). -/
theorem crit_le_critBar (ok : S.Ok) (j : ℕ) : (S.crit j : ℝ) ≤ S.critBar (S.lam j) := by
  have hR := ok.Rb_pos
  have h0 : 0 ≤ S.Rb * S.lam j ^ 2 := by positivity
  have hc : (S.r j : ℝ) ≤ S.Rb * S.lam j ^ 2 + 1 := by
    unfold Setting.r
    exact (Nat.ceil_lt_add_one h0).le
  have hc0 : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  unfold Setting.crit Setting.rho Typing.critBar
  push_cast
  nlinarith

/-- (T1) `crit_j ^ d ≤ ccrit · (1 + λ_j ^ (2d))`. -/
theorem crit_pow_le (ok : S.Ok) (j : ℕ) :
    (S.crit j : ℝ) ^ S.d ≤ ccrit S * (1 + S.lam j ^ (2 * S.d)) := by
  have hR := ok.Rb_pos
  have hc0 : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  have hle : (S.crit j : ℝ) ≤ (2 * (S.c0 : ℝ) + 10) + (2 * (S.c0 : ℝ) * S.Rb) * S.lam j ^ 2 := by
    have := crit_le_critBar ok j
    unfold Typing.critBar at this
    linarith
  have h0 : (0 : ℝ) ≤ S.crit j := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ 2 * (S.c0 : ℝ) + 10 := by positivity
  have hB : (0 : ℝ) ≤ (2 * (S.c0 : ℝ) * S.Rb) * S.lam j ^ 2 := by positivity
  have h1 := pow_le_pow_left₀ h0 hle S.d
  have h2 := add_pow_le_two_pow_mul hA hB S.d
  have h3 : ((2 * (S.c0 : ℝ) * S.Rb) * S.lam j ^ 2) ^ S.d
      = (2 * (S.c0 : ℝ) * S.Rb) ^ S.d * S.lam j ^ (2 * S.d) := by
    rw [mul_pow, ← pow_mul]
  rw [h3] at h2
  have hAd : 0 ≤ (2 * (S.c0 : ℝ) + 10) ^ S.d := by positivity
  have hBd : 0 ≤ (2 * (S.c0 : ℝ) * S.Rb) ^ S.d := by positivity
  have hy : 0 ≤ S.lam j ^ (2 * S.d) := by
    rw [pow_mul]; positivity
  have h4 : (2 * (S.c0 : ℝ) + 10) ^ S.d + (2 * (S.c0 : ℝ) * S.Rb) ^ S.d * S.lam j ^ (2 * S.d)
      ≤ ((2 * (S.c0 : ℝ) + 10) ^ S.d + (2 * (S.c0 : ℝ) * S.Rb) ^ S.d)
        * (1 + S.lam j ^ (2 * S.d)) := by
    nlinarith [mul_nonneg hAd hy]
  unfold ccrit
  calc (S.crit j : ℝ) ^ S.d ≤ 2 ^ S.d * ((2 * (S.c0 : ℝ) + 10) ^ S.d
        + (2 * (S.c0 : ℝ) * S.Rb) ^ S.d * S.lam j ^ (2 * S.d)) := le_trans h1 h2
    _ ≤ 2 ^ S.d * (((2 * (S.c0 : ℝ) + 10) ^ S.d + (2 * (S.c0 : ℝ) * S.Rb) ^ S.d)
        * (1 + S.lam j ^ (2 * S.d))) := by gcongr
    _ = _ := by ring

/-! ### Relation with `log β` (T2) -/

variable {β ν a ε : ℝ} {b n : ℕ → ℝ}

/-- Under `λ_j = λ̂_j` and `RunningHyp`: `1 ≤ λ_j ≤ log β_j + 3`. -/
theorem lam_bounds (ok : S.Ok) (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j)
    (hrun : RunningHyp S.d S.L β ν a ε b n) (j : ℕ) :
    0 ≤ S.lam j ∧ S.lam j ≤ Real.log (b j) + 3 := by
  have h1 := hrun.lamHat_mono j
  have h2 := hrun.logBeta_ge j
  have h0 := ok.one_le_lam0
  have h5 := hlam 0
  rw [hlam j]
  constructor <;> linarith

/-- (T2) `crit_j ^ d ≤ ccrit · (1 + (log β_j + 3)^(2d))`. -/
theorem crit_pow_le_logBeta (ok : S.Ok) (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j)
    (hrun : RunningHyp S.d S.L β ν a ε b n) (j : ℕ) :
    (S.crit j : ℝ) ^ S.d ≤ ccrit S * (1 + (Real.log (b j) + 3) ^ (2 * S.d)) := by
  obtain ⟨h0, h1⟩ := lam_bounds ok hlam hrun j
  have := crit_pow_le ok j
  have h2 : S.lam j ^ (2 * S.d) ≤ (Real.log (b j) + 3) ^ (2 * S.d) :=
    pow_le_pow_left₀ h0 h1 _
  have := ccrit_nonneg ok
  calc (S.crit j : ℝ) ^ S.d ≤ ccrit S * (1 + S.lam j ^ (2 * S.d)) := crit_pow_le ok j
    _ ≤ _ := by gcongr

/-! ### Domination (T3) -/

/-- The explicit threshold `X₀(K) = max 3 (2^(2d+2) K ccrit / A₂)`. -/
noncomputable def reserveX0 (S : Setting) (K A2 : ℝ) : ℝ := x0 S.d K (ccrit S) A2

/-- (T3) For `K ≥ 0`, `A₂ > 0`, `p₂ ≥ 2d+1` and `log β_j ≥ X₀`:
`K · crit_j^d ≤ ½ · p2Run A₂ p₂ β j`. -/
theorem mul_crit_pow_le_half_p2Run (ok : S.Ok) (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j)
    (hrun : RunningHyp S.d S.L β ν a ε b n) {K A2 : ℝ} {p2 : ℕ} (hK : 0 ≤ K) (hA : 0 < A2)
    (hp : 2 * S.d + 1 ≤ p2) {j : ℕ} (hj : reserveX0 S K A2 ≤ Real.log (b j)) :
    K * (S.crit j : ℝ) ^ S.d ≤ 1 / 2 * p2Run A2 p2 b j := by
  have h1 := dominate_aux (d := S.d) (p2 := p2) hK (ccrit_nonneg ok) hA hp hj
  have h2 := crit_pow_le_logBeta ok hlam hrun j
  unfold p2Run
  calc K * (S.crit j : ℝ) ^ S.d ≤ K * (ccrit S * (1 + (Real.log (b j) + 3) ^ (2 * S.d))) := by
        gcongr
    _ ≤ _ := h1

/-- Under `Ok`, `p₂ ≥ 2d+3 ≥ 2d+1`, so the domination holds with `A₂, p₂` of the setting. -/
theorem mul_crit_pow_le_half_p2Run_of_ok (ok : S.Ok)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (hrun : RunningHyp S.d S.L β ν a ε b n)
    {K : ℝ} (hK : 0 ≤ K) {j : ℕ} (hj : reserveX0 S K S.A2 ≤ Real.log (b j)) :
    K * (S.crit j : ℝ) ^ S.d ≤ 1 / 2 * p2Run S.A2 S.p2 b j :=
  mul_crit_pow_le_half_p2Run ok hlam hrun hK ok.A2_pos (by have := ok.p2_ge; omega) hj

/-- The logarithm of a rooted-entropy constant `Q · crit_j^d` (for `D7GasRootEntropy`,
`Q = (2d+1) K₀`) is dominated a fortiori, since `log x ≤ x`. -/
theorem log_mul_crit_pow_le_half_p2Run (ok : S.Ok)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (hrun : RunningHyp S.d S.L β ν a ε b n)
    {Q : ℝ} (hQ : 0 ≤ Q) {j : ℕ} (hj : reserveX0 S Q S.A2 ≤ Real.log (b j)) :
    Real.log (Q * (S.crit j : ℝ) ^ S.d) ≤ 1 / 2 * p2Run S.A2 S.p2 b j :=
  le_trans (Real.log_le_self (by positivity)) (mul_crit_pow_le_half_p2Run_of_ok ok hlam hrun hQ hj)

/-! ### The ledger as a record (T4) -/

/-- The positive part of `log (Bst / B0)`. -/
noncomputable def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

/-- The reserve ledger of `notes/phase1/VMOD-40.md` §2 at scale `k`: nonnegative numbers
`Elabels, Emayer, Egas` with
`κ (d L + d + 3) crit_k^d + Elabels + Emayer + Egas + log⁺ (Bst/B0) ≤ p2Run`. -/
structure RD7ChargeParams (S : Setting) (κ : ℝ) (b : ℕ → ℝ) (Bst B0 : ℝ) (k : ℕ) where
  Elabels : ℝ
  Emayer : ℝ
  Egas : ℝ
  Elabels_nonneg : 0 ≤ Elabels
  Emayer_nonneg : 0 ≤ Emayer
  Egas_nonneg : 0 ≤ Egas
  ledger : κ * ((S.d : ℝ) * S.L + S.d + 3) * (S.crit k : ℝ) ^ S.d + Elabels + Emayer + Egas
    + logPlus (Bst / B0) ≤ p2Run S.A2 S.p2 b k

/-- The ledger holds once the entropy terms and `log⁺` fit in half of `p2Run` and
`log β_k ≥ X₀(κ (d L + d + 3))`. -/
theorem rd7Charge_of_large_logBeta (ok : S.Ok)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (hrun : RunningHyp S.d S.L β ν a ε b n)
    {κ Bst B0 : ℝ} (hκ : 0 ≤ κ) {k : ℕ} {Elabels Emayer Egas : ℝ}
    (h1 : 0 ≤ Elabels) (h2 : 0 ≤ Emayer) (h3 : 0 ≤ Egas)
    (hE : Elabels + Emayer + Egas + logPlus (Bst / B0) ≤ 1 / 2 * p2Run S.A2 S.p2 b k)
    (hk : reserveX0 S (κ * ((S.d : ℝ) * S.L + S.d + 3)) S.A2 ≤ Real.log (b k)) :
    Nonempty (RD7ChargeParams S κ b Bst B0 k) := by
  have hK : 0 ≤ κ * ((S.d : ℝ) * S.L + S.d + 3) := by positivity
  have := mul_crit_pow_le_half_p2Run_of_ok ok hlam hrun hK hk
  exact ⟨⟨Elabels, Emayer, Egas, h1, h2, h3, by linarith⟩⟩

namespace RD7ChargeParams

/-- Exponential form of the ledger (for `0 < B0`, `0 < Bst`):
`exp (-p2Run) ≤ exp (-κ (d L + d + 3) crit^d) · exp (-Elabels) · exp (-Emayer) · exp (-Egas)
· min 1 (B0 / Bst)`. -/
theorem exp_p2Run_le {κ : ℝ} {b : ℕ → ℝ} {Bst B0 : ℝ} {k : ℕ} (P : RD7ChargeParams S κ b Bst B0 k)
    (hB : 0 < Bst) (hB0 : 0 < B0) :
    Real.exp (-p2Run S.A2 S.p2 b k) ≤
      Real.exp (-(κ * ((S.d : ℝ) * S.L + S.d + 3) * (S.crit k : ℝ) ^ S.d)) *
        Real.exp (-P.Elabels) * Real.exp (-P.Emayer) * Real.exp (-P.Egas) * min 1 (B0 / Bst) := by
  have hmin : Real.exp (-logPlus (Bst / B0)) = min 1 (B0 / Bst) := by
    unfold logPlus
    rcases le_total 0 (Real.log (Bst / B0)) with h | h
    · rw [max_eq_right h, Real.exp_neg, Real.exp_log (by positivity)]
      have : B0 / Bst ≤ 1 := by
        have : 1 ≤ Bst / B0 := by
          by_contra hc
          push Not at hc
          have := Real.log_neg (by positivity) hc
          linarith
        rw [le_div_iff₀ hB0] at this
        rw [div_le_one hB]; linarith
      rw [min_eq_right this, inv_div]
    · rw [max_eq_left h, neg_zero, Real.exp_zero]
      have : 1 ≤ B0 / Bst := by
        have hx : Bst / B0 ≤ 1 := by
          by_contra hc
          push Not at hc
          have := Real.log_pos hc
          linarith
        rw [div_le_one hB0] at hx
        rw [le_div_iff₀ hB]; linarith
      rw [min_eq_left this]
  rw [← hmin, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := P.ledger
  linarith

end RD7ChargeParams

/-! ### Non-vacuity (T5) -/

/-- The scale-`k` growth: `log β_k → ∞` for admissible data. -/
theorem exists_large_logBeta (ok : S.Ok) (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j)
    (hrun : RunningHyp S.d S.L β ν a ε b n) (X : ℝ) : ∃ k, X ≤ Real.log (b k) := by
  have hm := ok.θm_pos
  obtain ⟨k, hk⟩ := exists_nat_ge ((X + 3) / S.θm)
  have key : ∀ m : ℕ, S.lam 0 + (m : ℝ) * S.θm ≤ S.lam m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := (ok.lam_step m).1
      push_cast; linarith
  refine ⟨k, ?_⟩
  have h1 := hrun.logBeta_ge k
  rw [← hlam k] at h1
  have h2 := key k
  have h0 := ok.one_le_lam0
  have h3 : X + 3 ≤ (k : ℝ) * S.θm := by
    rwa [div_le_iff₀ hm] at hk
  linarith

/-- (T5) For admissible data (`Ok`, `λ = λ̂`, `RunningHyp`), `0 ≤ κ` and `Bst ≤ B0`, `0 < B0`,
`0 < Bst`, the ledger record is inhabited at all large scales, with all three entropy terms zero. -/
theorem exists_scale_rd7ChargeParams (ok : S.Ok) (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j)
    (hrun : RunningHyp S.d S.L β ν a ε b n) {κ Bst B0 : ℝ} (hκ : 0 ≤ κ) (hB : 0 < Bst)
    (hB0 : 0 < B0) (hle : Bst ≤ B0) :
    ∃ K0 : ℕ, ∀ k, K0 ≤ k → Nonempty (RD7ChargeParams S κ b Bst B0 k) := by
  have hbig : ∀ X : ℝ, ∃ K0 : ℕ, ∀ k, K0 ≤ k → X ≤ Real.log (b k) := by
    intro X
    obtain ⟨m, hm⟩ := exists_nat_ge ((X + 3 + 1 - S.lam 0 + 0) / S.θm)
    refine ⟨m, fun k hk => ?_⟩
    have hmono : ∀ i j : ℕ, i ≤ j → S.lam i ≤ S.lam j := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ j _ ih =>
        have := (ok.lam_step j).1
        have := ok.θm_pos
        linarith
    have h1 := hrun.logBeta_ge k
    rw [← hlam k] at h1
    have key : ∀ m : ℕ, S.lam 0 + (m : ℝ) * S.θm ≤ S.lam m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => have := (ok.lam_step m).1; push_cast; linarith
    have h2 := key m
    have h3 := hmono m k hk
    have hθ := ok.θm_pos
    have h4 : X + 3 + 1 - S.lam 0 ≤ (m : ℝ) * S.θm := by
      have := hm
      rw [div_le_iff₀ hθ] at this
      linarith
    linarith
  obtain ⟨K0, hK0⟩ := hbig (max (reserveX0 S (κ * ((S.d : ℝ) * S.L + S.d + 3)) S.A2) 3)
  refine ⟨K0, fun k hk => ?_⟩
  have hX := hK0 k hk
  have hX1 := le_trans (le_max_left _ _) hX
  have hX3 : (3 : ℝ) ≤ Real.log (b k) := le_trans (le_max_right _ _) hX
  have hlog : logPlus (Bst / B0) = 0 := by
    unfold logPlus
    have : Real.log (Bst / B0) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one hB0).mpr hle)
    exact max_eq_left this
  have hp : 0 ≤ p2Run S.A2 S.p2 b k := by
    unfold p2Run
    have := ok.A2_pos
    positivity
  exact rd7Charge_of_large_logBeta ok hlam hrun hκ le_rfl le_rfl le_rfl
    (by rw [hlog]; linarith) hX1

end D7Reserve

/-! ### The landed witness -/

namespace Def7.Wit

/-- Running coefficients of the witness: `β_k = β 3^k`. -/
noncomputable def witBeta (β : ℝ) : ℕ → ℝ := fun k => β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))

/-- Running `ν_k = 3^(2k)`. -/
noncomputable def witNu : ℕ → ℝ := fun k => 1 * ((3 : ℕ) : ℝ) ^ (2 * k)

theorem wit_running (β : ℝ) (hβ : 0 < β) :
    RunningHyp wS.d wS.L β 1 (5 / 4) 0 (witBeta β) witNu where
  hd := by show 2 ≤ 3; norm_num
  hL := by show 2 ≤ 3; norm_num
  hβ := hβ
  hν := one_pos
  ha1 := by norm_num
  ha2 := by norm_num
  hε0 := le_rfl
  hε := by norm_num
  beta_eq := fun k => ⟨1, one_pos, by simp, by simp [witBeta, wS, setting, typing, typing0]⟩
  nu_eq := fun k => ⟨1, one_pos, by simp, by simp [witNu, wS, setting, typing, typing0]⟩

/-- (T5, witness) At the landed witness `wS` (`d = L = 3`, `A₂ = 1`, `p₂ = 9`, `β = wβ`) with
running coefficients `β_k = wβ 3^k` and `κ = 1`, `B_st = B₀ = 1`: the ledger record exists at all
sufficiently large scales, with `Elabels = Emayer = Egas = 0`.  (At small scales the landed
threshold is not claimed; `log β_k ≥ X₀` is needed.) -/
theorem wit_exists_scale_rd7ChargeParams :
    ∃ K0 : ℕ, ∀ k, K0 ≤ k →
      Nonempty (D7Reserve.RD7ChargeParams wS 1 (witBeta wβ) 1 1 k) :=
  D7Reserve.exists_scale_rd7ChargeParams wS_ok (fun j => setting_lam_eq wβ j)
    (wit_running wβ wβ_pos) zero_le_one one_pos one_pos le_rfl

end Def7.Wit

end Balaban.LargeField
