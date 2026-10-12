module

public import Balaban.LargeField.History.RipeWindow
public import Balaban.LargeField.History.FlowBook

/-!
# Positivity of the gain clock and of the core scale of a ripe window

`RegionHistory.gain_pos`: every component of the history has gain clock `b(Z) ≥ 1` (K1 ruling,
`notes/phase1/K1-RULING.md`), and `RipeWindow.k1_pos`, `RipeWindow.q_pos`: `1 ≤ k₁(k)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

open Classical in
theorem gain_pos (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) :
    1 ≤ H.gain k Z := by
  induction k with
  | zero => exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    by_cases hnew : (Z.1 ∩ H.newCubes (k + 1)).Nonempty
    · rw [H.gain_of_new k Z hnew]; omega
    · have hs := H.seed_pos (k := k) (by omega) Z
      have hc0 : (Z.1 ∩ H.newCubes (k + 1)).card = 0 := by
        rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]; exact hnew
      have hp : 0 < (H.parts k Z).card := by omega
      obtain ⟨c, hc⟩ := Finset.card_pos.mp hp
      rw [H.gain_succ_of_not_new k Z hnew]
      refine le_trans ?_ (Finset.le_sup (f := fun c => if 1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k c)
        then k else H.gain k c) hc)
      split_ifs with h
      · exact h.1
      · exact ih (by omega) c

end RegionHistory

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

theorem RipeWindow.q_pos {k : ℕ} {Z : H.Comp k} (hkK : k ≤ K) (hW : H.RipeWindow k Z) :
    1 ≤ (H.bk k Z).q :=
  (H.gain_pos hkK Z).trans hW.gain_le

theorem RipeWindow.k1_pos {k : ℕ} {Z : H.Comp k} (hkK : k ≤ K) (hW : H.RipeWindow k Z) :
    1 ≤ S.k1 k := by
  rw [hW.core_k1]; exact hW.q_pos hkK

end RegionHistory

end Balaban.LargeField
