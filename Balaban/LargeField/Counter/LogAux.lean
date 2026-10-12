module

public import Balaban.LargeField.Counter.CaseNew
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Logarithmic estimates for the lengths of spines (Part I, §I.5.4)
-/

@[expose] public section

namespace Balaban.LargeField

theorem logb_le_pred {L : ℝ} (hL : 2 ≤ L) {m : ℕ} (hm : 1 ≤ m) : Real.logb L m ≤ m - 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.logb_le_iff_le_rpow (by linarith) hm0]
  have h1 : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]; simp
  rw [h1, Real.rpow_natCast]
  have h2 : m ≤ 2 ^ (m - 1) := by
    have := Nat.lt_two_pow_self (n := m - 1)
    omega
  calc (m : ℝ) ≤ 2 ^ (m - 1) := by exact_mod_cast h2
    _ ≤ L ^ (m - 1) := by gcongr

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- `k + log_L max {ℓ, 1} ≤ t^*` for a post-`R` book. -/
theorem tStar_ge_len {k : ℕ} {b : Book} (hb : BookInv S k b) (hpost : k < S.tStar b) :
    (k : ℝ) + Real.logb S.L (max b.len 1) ≤ S.tStar b := by
  have hL := G.ok.cast_L_ge
  by_cases hp : b.pt
  · have := hb.pt_len hp
    rw [this]
    simp
    exact_mod_cast hpost.le
  · have hs := hb.np_clock hp
    have h1 := S.tStar_ge_right b
    have hΛ : 0 ≤ Real.logb S.L (max b.len 1) :=
      Real.logb_nonneg (by linarith) (le_max_right _ _)
    have h2 : Real.logb S.L (max b.len 1) ≤ ⌈Real.logb S.L (max b.len 1)⌉₊ := Nat.le_ceil _
    have h3 : ((⌈Real.logb S.L (max b.len 1)⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈Real.logb S.L (max b.len 1)⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h4 : (b.s : ℝ) = k + ((max 1 ⌈Real.logb S.L (max b.len 1)⌉₊ : ℕ) : ℝ) := by
      rw [hs]; push_cast; ring
    have h5 : (b.s : ℝ) ≤ S.tStar b := by exact_mod_cast (le_trans (Nat.le_add_right _ _) h1)
    linarith

/-- The logarithm of the length after a merge. -/
theorem len_log_bound {ι : Type*} {P : Finset ι} {f : ι → Book} {len' D : ℝ} {i1 : ι}
    (hi1 : i1 ∈ P) (hmax : ∀ j ∈ P, (f j).len ≤ (f i1).len) (hlen0 : ∀ j ∈ P, 0 ≤ (f j).len)
    (hD : 0 ≤ D)
    (hlen : len' ≤ ∑ i ∈ P, (f i).len / S.L + ((P.card : ℝ) - 1) * D) :
    Real.logb S.L (max len' 1) ≤ Real.logb S.L (max (f i1).len 1) +
      Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + D) := by
  have hL := G.ok.cast_L_ge
  have hc : (1 : ℝ) ≤ P.card := by exact_mod_cast Finset.card_pos.mpr ⟨i1, hi1⟩
  set M := max (f i1).len 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hℓM : (f i1).len ≤ M := le_max_left _ _
  have h1 : ∑ i ∈ P, (f i).len / S.L ≤ (P.card : ℝ) * (f i1).len := by
    have := Finset.sum_le_card_nsmul P (fun i => (f i).len / S.L) ((f i1).len) (fun j hj => by
      calc (f j).len / S.L ≤ (f j).len := div_le_self (hlen0 j hj) (by linarith)
        _ ≤ (f i1).len := hmax j hj)
    simpa using this
  have h2 : max len' 1 ≤ (P.card : ℝ) * (1 + D) * M := by
    refine max_le ?_ ?_
    · have : len' ≤ (P.card : ℝ) * M + (P.card : ℝ) * D := by
        have : (P.card : ℝ) * (f i1).len ≤ P.card * M := by gcongr
        nlinarith
      calc len' ≤ (P.card : ℝ) * M + (P.card : ℝ) * D := this
        _ ≤ (P.card : ℝ) * (1 + D) * M := by nlinarith [mul_nonneg (show (0:ℝ) ≤ P.card by linarith) (mul_nonneg hD (show 0 ≤ M - 1 by linarith))]
    · have : (1 : ℝ) ≤ (1 + D) * M := by nlinarith
      nlinarith
  have hpos : 0 < max len' 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc Real.logb S.L (max len' 1) ≤ Real.logb S.L ((P.card : ℝ) * (1 + D) * M) :=
        Real.logb_le_logb_of_le (by linarith) hpos h2
    _ = Real.logb S.L M + Real.logb S.L (P.card : ℝ) + Real.logb S.L (1 + D) := by
        rw [Real.logb_mul (by positivity) (by linarith), Real.logb_mul (by positivity) (by linarith)]
        ring

end Setting.Good

end Balaban.LargeField
