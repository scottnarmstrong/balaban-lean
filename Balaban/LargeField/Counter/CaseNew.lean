module

public import Balaban.LargeField.Counter.BudgetAux
public import Balaban.LargeField.Counter.Ineq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Case 1: new cubes ((T2), Part I §I.5.4)
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem Phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S.Phi x := by
  unfold Typing.Phi
  have h1 := G.ok.A2_pos
  have h2 := G.ok.cStar_ge_one
  have h3 := G.ok.θp_pos
  have hc : 0 ≤ S.cPrime := by
    unfold Typing.cPrime; positivity
  have hCt : 0 ≤ S.Ct := by
    unfold Typing.Ct
    have := G.ok.αlogL_pos
    positivity
  have := G.ok.Cw_nonneg
  positivity

/-- `(L : ℝ)^{Λ'} = max {ℓ', 1}` for `Λ' = log_L max {ℓ', 1}`. -/
theorem rpow_logb_max (len : ℝ) : (S.L : ℝ) ^ Real.logb S.L (max len 1) = max len 1 := by
  have hL := G.ok.cast_L_ge
  exact Real.rpow_logb (by linarith) (by linarith) (lt_of_lt_of_le one_pos (le_max_right _ _))

/-- The real-number core shared by Cases 1, 2b and 2c for a long restart. -/
theorem restart_big_pay {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {r : ℕ} {len' : ℝ}
    (hr : 1 ≤ P.card + r)
    (hlen : len' ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + r : ℕ) : ℝ) - 1) * S.D (k + 1))
    (hbig : S.lam (k + 1) < Real.logb S.L (max len' 1))
    (hpost : ∀ i ∈ P, 0 ≤ (f i).len) :
    (((P.card + r : ℕ) : ℝ) - 1) * S.E (k + 1) + S.Phi (Real.logb S.L (max len' 1)) + 1 ≤
      (P.card : ℝ) * S.tau (k + 1) + r * S.g k + S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len := by
  set Λ := Real.logb S.L (max len' 1) with hΛ
  have hL := G.ok.cast_L_ge
  have hl1 := G.ok.one_le_lam (k + 1)
  have hΛ1 : 1 < Λ := lt_of_le_of_lt hl1 hbig
  have hpow := G.rpow_logb_max len'
  rw [← hΛ] at hpow
  have hPw : 1 < (S.L : ℝ) ^ Λ := Real.one_lt_rpow (by linarith) (by linarith)
  have hlenP : (S.L : ℝ) ^ Λ ≤ ∑ i ∈ P, (f i).len / S.L +
      (((P.card + r : ℕ) : ℝ) - 1) * S.D (k + 1) := by
    rw [hpow]
    refine max_le hlen ?_
    have : (1 : ℝ) < max len' 1 := by rw [← hpow]; exact hPw
    rcases le_total len' 1 with h | h
    · rw [max_eq_right h] at this; exact absurd this (lt_irrefl _)
    · exact h.trans hlen
  have hx0 := G.lam_ge (k + 1)
  have hΛx : S.lam 0 ≤ Λ := hx0.trans hbig.le
  have h3 := G.lc.l3 Λ hΛx
  have h4 := G.lc.l4 Λ hΛx
  have hB : 0 < S.Dbar Λ := lt_of_lt_of_le one_pos (G.ok.one_le_Dbar Λ)
  have hDB : S.D (k + 1) ≤ S.Dbar Λ :=
    (G.ok.D_le_bar (k + 1)).trans (G.ok.Dbar_mono (G.ok.lam_pos _).le hbig.le)
  have hv := G.ok.one_le_v (k + 1)
  have hH : 0 ≤ ∑ i ∈ P, (f i).len / S.L := Finset.sum_nonneg (fun i hi => by
    exact div_nonneg (hpost i hi) (by linarith))
  have hsum : ∑ i ∈ P, (f i).len / S.L = (∑ i ∈ P, (f i).len) / S.L := by
    rw [Finset.sum_div]
  have hvH : S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len = S.v (k + 1) * ∑ i ∈ P, (f i).len / S.L := by
    rw [hsum]; ring
  rw [hvH]
  have := Ineq.big_pay (m := (P.card : ℝ)) (r := (r : ℝ)) (E := S.E (k + 1))
    (τ := S.tau (k + 1)) (g := S.g k) (v := S.v (k + 1)) (H := ∑ i ∈ P, (f i).len / S.L)
    (D := S.D (k + 1)) (B := S.Dbar Λ) (Pw := (S.L : ℝ) ^ Λ) (Φ := S.Phi Λ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hr) (G.E_nonneg _)
    (G.E_add_one_le_tau _) (G.E_add_one_le_g k) hv hH hDB hB
    (by push_cast at hlenP ⊢; exact hlenP) h3 h4
  push_cast at this ⊢
  linarith

/-- Case 1 (new cubes, (T2)): (B.7) holds. -/
theorem case_new {k : ℕ} {ι : Type*} {P : Finset ι} {f : ι → Book} {r : ℕ} {b' : Book}
    (hlenP : ∀ i ∈ P, 0 ≤ (f i).len) (hpost : ∀ i ∈ P, k < S.tStar (f i)) (hr : 1 ≤ r)
    (hf : RestartFacts S k b')
    (hlen : b'.len ≤ ∑ i ∈ P, (f i).len / S.L + (((P.card + r : ℕ) : ℝ) - 1) * S.D (k + 1)) :
    S.B7 k P f r b' := by
  have hΦ := (G.restart_Phi hf).2.2
  obtain ⟨-, -, -, hnu, hbank⟩ := hf
  have hsum := G.sum_lower (μ := k + 1) (P := P) (f := f) (fun i hi => hpost i hi)
  have hA : 0 ≤ S.v (k + 1) / S.L * ∑ i ∈ P, (f i).len := by
    have := G.ok.v_nonneg (k + 1)
    have : 0 ≤ ∑ i ∈ P, (f i).len := Finset.sum_nonneg hlenP
    have := G.ok.cast_L_ge
    positivity
  unfold Setting.B7
  rw [hnu, hbank]
  by_cases hΛ : Real.logb S.L (max b'.len 1) ≤ S.lam (k + 1)
  · rw [max_eq_left hΛ] at hΦ
    have := Ineq.small_pay (m := (P.card : ℝ)) (r := (r : ℝ)) (E := S.E (k + 1))
      (τ := S.tau (k + 1)) (g := S.g k) (Φ := S.Phi (S.lam (k + 1))) (Nat.cast_nonneg _)
      (by exact_mod_cast hr) (G.E_nonneg _) (G.Phi_nonneg (G.ok.lam_pos _).le)
      (G.E_add_one_le_tau _) (G.E_Phi_le_g k)
    push_cast at this ⊢
    linarith
  · have hbig := not_le.mp hΛ
    rw [max_eq_right hbig.le] at hΦ
    have := G.restart_big_pay (k := k) (P := P) (f := f) (r := r) (len' := b'.len)
      (by omega) hlen hbig hlenP
    push_cast at this ⊢
    linarith

end Setting.Good

end Balaban.LargeField
