module

public import Balaban.LargeField.Counter.Bars
import Mathlib.Tactic.Linarith

/-!
# The core `k₁` of a window ending at `t` (Part I, Lemma I.4.9)

`k₁(t) = max {c ≤ t : c + n_q(c) ≤ t}`.  Since `c ↦ c + n_q(c)` is strictly increasing,
`k₁` is nondecreasing, increases by at most `1`, and `k₁ t = c ↔ c + n_q(c) ≤ t < c + 1 + n_q(c+1)`
for `t ≥ n_q(0)`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting

variable {S : Setting}

theorem k1_mono : Monotone S.k1 := by
  intro a b hab
  unfold Setting.k1
  exact Nat.findGreatest_mono (fun n h => le_trans h hab) hab

theorem k1_le (t : ℕ) : S.k1 t ≤ t := Nat.findGreatest_le t

theorem k1_spec_of_ne {t : ℕ} (h : S.k1 t ≠ 0) : S.k1 t + S.nq (S.k1 t) ≤ t := by
  unfold Setting.k1 at h ⊢
  exact ((Nat.findGreatest_eq_iff (P := fun c => c + S.nq c ≤ t)).mp rfl).2.1 h

theorem k1_spec {t : ℕ} (ht : S.nq 0 ≤ t) : S.k1 t + S.nq (S.k1 t) ≤ t := by
  unfold Setting.k1
  exact Nat.findGreatest_spec (P := fun c => c + S.nq c ≤ t) (m := 0) (Nat.zero_le t)
    (by simpa using ht)

theorem lt_k1_succ (t : ℕ) : t < (S.k1 t + 1) + S.nq (S.k1 t + 1) := by
  by_contra hcon
  have hcon := not_lt.mp hcon
  have hle : S.k1 t + 1 ≤ t := by
    have := S.one_le_nq (S.k1 t + 1)
    omega
  have hgt : S.k1 t < S.k1 t + 1 := Nat.lt_succ_self _
  exact Nat.findGreatest_is_greatest (P := fun c => c + S.nq c ≤ t) hgt hle hcon

theorem le_k1 {c t : ℕ} (h : c + S.nq c ≤ t) : c ≤ S.k1 t := by
  unfold Setting.k1
  exact Nat.le_findGreatest (by have := S.one_le_nq c; omega) h

end Setting

namespace Setting.Ok

variable {S : Setting} (ok : S.Ok)

include ok

theorem k1_add_nq (c : ℕ) : S.k1 (c + S.nq c) = c := by
  apply le_antisymm
  · by_contra hcon
    have hcon := not_le.mp hcon
    have h1 := S.k1_spec (t := c + S.nq c) (by have := ok.nq_mono (Nat.zero_le c); omega)
    have h2 := ok.add_nq_strictMono hcon
    simp only at h2
    omega
  · exact S.le_k1 le_rfl

theorem k1_eq_iff {t c : ℕ} (ht : S.nq 0 ≤ t) :
    S.k1 t = c ↔ c + S.nq c ≤ t ∧ t < (c + 1) + S.nq (c + 1) := by
  constructor
  · rintro rfl
    exact ⟨S.k1_spec ht, S.lt_k1_succ t⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · by_contra hcon
      have hcon := not_le.mp hcon
      have h3 := S.k1_spec ht
      have h4 := ok.add_nq_strictMono.monotone (show c + 1 ≤ S.k1 t by omega)
      omega
    · exact S.le_k1 h1

theorem k1_succ_le (t : ℕ) : S.k1 (t + 1) ≤ S.k1 t + 1 := by
  by_cases h0 : S.k1 (t + 1) = 0
  · omega
  · have h1 := S.k1_spec_of_ne h0
    set c := S.k1 (t + 1) with hc
    have h2 := ok.add_nq_strictMono (a := c - 1) (b := c) (by omega)
    simp only at h2
    have h3 : (c - 1) + S.nq (c - 1) ≤ t := by omega
    have := S.le_k1 h3
    omega

/-- For `v ≥ k₁(t₀)` there is `t ≥ t₀` with `k₁ t = v`. -/
theorem exists_k1_eq {t₀ v : ℕ} (hv : S.k1 t₀ ≤ v) :
    ∃ t, t₀ ≤ t ∧ S.k1 t = v := by
  rcases Nat.eq_or_lt_of_le hv with h | h
  · exact ⟨t₀, le_rfl, h⟩
  · refine ⟨v + S.nq v, ?_, ok.k1_add_nq v⟩
    have h1 := S.lt_k1_succ t₀
    have h2 := ok.add_nq_strictMono.monotone (show S.k1 t₀ + 1 ≤ v by omega)
    omega

/-- (c): if `t < μ + n_q(μ)` then `k₁ t ≤ μ - 1` (for `μ ≥ 1`). -/
theorem k1_le_pred {t μ : ℕ} (hμ : 1 ≤ μ) (ht : t < μ + S.nq μ) : S.k1 t ≤ μ - 1 := by
  by_cases h0 : S.k1 t = 0
  · omega
  · have h1 := S.k1_spec_of_ne h0
    by_contra hcon
    have hcon := not_le.mp hcon
    have h2 := ok.add_nq_strictMono.monotone (show μ ≤ S.k1 t by omega)
    omega

end Setting.Ok

end Balaban.LargeField
