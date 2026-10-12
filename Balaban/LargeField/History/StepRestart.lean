module

public import Balaban.LargeField.History.Scale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Restarts and pure shadows: the invariant `BookInv` after (T1)–(T3), (T5)
-/

@[expose] public section

namespace Balaban.LargeField

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- The invariant of the output of a restart ((T2), (T3), (T5)). -/
theorem restart_inv {μ : ℕ} {b' : Book}
    (hst : b'.st = WState.restart μ b'.pt)
    (hlen : 0 ≤ b'.len) (hptl : b'.pt → b'.len = 0)
    (hnp : ¬ b'.pt → b'.s = μ + max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊)
    (hpt : b'.pt → b'.s = μ) :
    BookInv S μ b' ∧ S.tStar b' = b'.s + S.nq b'.s ∧ μ ≤ b'.s ∧
      (b'.s : ℝ) ≤ μ + 1 + Real.logb S.L (max b'.len 1) ∧ b'.nu = 1 ∧ S.bank b' = 0 := by
  have hL := G.ok.cast_L_ge
  have hΛ : 0 ≤ Real.logb S.L (max b'.len 1) :=
    Real.logb_nonneg (by linarith) (le_max_right _ _)
  by_cases hp : b'.pt
  · have hst' : b'.st = .active μ 1 ∅ := by rw [hst, WState.restart_pt hp]
    have hs := hpt hp
    have hl0 := hptl hp
    have htS : S.tStar b' = μ + S.nq μ := by
      unfold Setting.tStar
      rw [Book.q_active hst', hs]
      have := G.n2_le_nq μ
      omega
    have hnu : b'.nu = 1 := Book.nu_active hst'
    have hadm : S.Admissible μ b' := by
      unfold Setting.Admissible; rw [hst']
      exact ⟨le_rfl, le_rfl, G.ok.one_le_numax μ, by simp⟩
    refine ⟨⟨hadm, hlen, hptl, fun _ => le_of_eq hs, fun h => absurd hp h, ?_, ?_, ?_⟩,
      ?_, ?_, ?_, hnu, ?_⟩
    · intro _; rw [hl0, hnu]; simp
    · intro _
      rw [htS, Book.q_active hst']
      have := G.ok.nq_mono (show μ ≤ μ + 1 by omega)
      omega
    · rw [htS]; omega
    · rw [htS, hs]
    · omega
    · rw [hs]; linarith
    · rw [S.bank_active hst']; simp
  · have hst' : b'.st = .pre := by rw [hst, WState.restart_npt hp]
    have hs := hnp hp
    have htS : S.tStar b' = b'.s + S.nq b'.s := G.tStar_pre hst'
    have hadm : S.Admissible μ b' := by
      unfold Setting.Admissible; rw [hst']; exact hp
    have hμs : μ ≤ b'.s := by omega
    refine ⟨⟨hadm, hlen, hptl, fun h => absurd h hp, hnp, ?_, ?_, ?_⟩, htS, hμs, ?_, ?_, ?_⟩
    · rintro (h | h)
      · exact absurd h (Book.not_active_of_pre hst')
      · exact absurd h (Book.not_pending_of_pre hst')
    · rintro (h | h)
      · exact absurd h (Book.not_active_of_pre hst')
      · exact absurd h (Book.not_pending_of_pre hst')
    · rw [htS]; omega
    · have h1 : (⌈Real.logb S.L (max b'.len 1)⌉₊ : ℝ) ≤ Real.logb S.L (max b'.len 1) + 1 :=
        (Nat.ceil_lt_add_one hΛ).le
      have hm : ((max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊ : ℕ) : ℝ) ≤
          1 + Real.logb S.L (max b'.len 1) := by
        rcases le_total 1 ⌈Real.logb S.L (max b'.len 1)⌉₊ with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; push_cast; linarith
      rw [hs, Nat.cast_add]
      linarith
    · exact Book.nu_pre hst'
    · exact S.bank_of_not_active (Book.not_active_of_pre hst')

end Setting.Good

end Balaban.LargeField
