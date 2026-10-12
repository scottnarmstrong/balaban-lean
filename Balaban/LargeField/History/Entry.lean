module

public import Balaban.LargeField.History.Core

/-!
# Lemma I.4.13 (d): every branch ends at a certified entry

A *certified entry* at scale `e` is a component whose post-`R` state is `Active(e, 1, ∅)` and whose
spine is a point; it is one box of side `≤ crit_e` (Lemma I.4.8).  Entries are the outputs of a
restart with point spine, the pure shadows of a `Pre` part with point spine, and the kept ripe
components.  `exists_entry`: every `Active` or `Pending` component of scale `κ ≤ k₀` has an
ancestor that is an entry (following the branch backwards through (T1) and (T4)).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

variable (H) in
/-- A certified entry: post-`R` state `Active(e, 1, ∅)` and a point spine. -/
def IsEntry (e : ℕ) (Y : H.Comp e) : Prop :=
  (H.pb e Y).st = .active e 1 ∅ ∧ (H.bk e Y).len = 0

theorem pb_st_of_active {e : ℕ} {Y : H.Comp e} (h : (H.bk e Y).st = .active e 1 ∅) :
    (H.pb e Y).st = .active e 1 ∅ := by
  unfold pb Setting.postBook
  split_ifs
  · rfl
  · exact h

variable (G : S.Good)

include G

/-- **Lemma I.4.13 (d)**: each branch of the lineage of an `Active` or `Pending` component ends at
a certified entry, which is one box of side `≤ crit_e`. -/
theorem exists_entry (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) :
    ∀ κ (Y : H.Comp κ), κ ≤ k0 → κ ≤ K → ((H.bk κ Y).IsActive ∨ (H.bk κ Y).IsPending) →
    ∃ e, ∃ Y' : H.Comp e, H.Desc e κ Y' Y ∧ H.IsEntry e Y' ∧ CoveredBy S n e Y'.1 1 := by
  intro κ
  induction κ with
  | zero => intro Y; exact (H.F.isEmpty_comp_zero.false Y).elim
  | succ k ih =>
    intro Y hk0 hkK hact
    obtain ⟨hinv, hcase, hs1, hs2, hs3, hs4, hs5⟩ := H.step_facts G hk0 hkK Y
    have mk : (H.bk (k + 1) Y).st = .active (k + 1) 1 ∅ → (H.bk (k + 1) Y).pt →
        ∃ e, ∃ Y' : H.Comp e, H.Desc e (k + 1) Y' Y ∧ H.IsEntry e Y' ∧ CoveredBy S n e Y'.1 1 :=
      fun hst hp => ⟨k + 1, Y, Desc.refl Y, ⟨pb_st_of_active hst, hinv.pt_len hp⟩,
        cover_of_len hT (by omega) hk0 hkK Y (hinv.pt_len hp)⟩
    have hrestart : (H.bk (k + 1) Y).st = WState.restart (k + 1) (H.bk (k + 1) Y).pt →
        ∃ e, ∃ Y' : H.Comp e, H.Desc e (k + 1) Y' Y ∧ H.IsEntry e Y' ∧ CoveredBy S n e Y'.1 1 := by
      intro hst
      have hp : (H.bk (k + 1) Y).pt := by
        by_contra hnp
        rw [WState.restart_npt hnp] at hst
        rcases hact with h | h
        · exact Book.not_pre_of_active h hst
        · exact Book.not_pre_of_pending h hst
      exact mk (by rw [hst, WState.restart_pt hp]) hp
    have hact_of : ∀ c : H.Comp k, ((H.pb k c).IsActive ∨ (H.pb k c).IsPending) →
        (H.bk k c).IsActive ∨ (H.bk k c).IsPending := by
      intro c h
      by_cases hr : S.Ripe k (H.bk k c)
      · exact Or.inl hr.1
      · rwa [show H.pb k c = H.bk k c from S.postBook_of_not_ripe hr] at h
    have extend : ∀ c ∈ H.parts k Y, ((H.pb k c).IsActive ∨ (H.pb k c).IsPending) →
        ∃ e, ∃ Y' : H.Comp e, H.Desc e (k + 1) Y' Y ∧ H.IsEntry e Y' ∧ CoveredBy S n e Y'.1 1 := by
      intro c hc hc'
      obtain ⟨hrem, hsu⟩ := (H.mem_parts k c Y).mp hc
      obtain ⟨e, Y', hd, he, hcov⟩ := ih c (by omega) (by omega) (hact_of c hc')
      exact ⟨e, Y', hd.trans (Desc.single hrem hsu), he, hcov⟩
    cases hcase with
    | new hr hf => exact hrestart (hs1 hr)
    | mergePre hr hcard hpre hf => exact hrestart (hs3 hr hcard hpre)
    | overflow hr hcard hnpre hcap hf => exact hrestart (hs5 hr hcard hnpre hcap)
    | mergeCap hr hcard hnpre hcap hf =>
      obtain ⟨c, hc⟩ : (H.parts k Y).Nonempty := Finset.card_pos.mp (by omega)
      refine extend c hc ?_
      rcases Book.cases_st (H.pb k c) with h | h | h
      · exact absurd h (hnpre c hc)
      · exact Or.inr h
      · exact Or.inl h
    | shadow i hparts hr hle hge hnu hbank =>
      have hmem : i ∈ H.parts k Y := by rw [hparts]; exact Finset.mem_singleton_self i
      by_cases hact' : (H.pb k i).IsActive ∨ (H.pb k i).IsPending
      · exact extend i hmem hact'
      · have hpre : (H.pb k i).st = .pre := by
          rcases Book.cases_st (H.pb k i) with h | h | h
          · exact h
          · exact absurd (Or.inr h) hact'
          · exact absurd (Or.inl h) hact'
        have hst := hs2 hr i hparts
        have hp : (H.bk (k + 1) Y).pt := by
          by_contra hnp
          rw [WState.shadow_pre_npt hpre hnp] at hst
          rcases hact with h | h
          · exact Book.not_pre_of_active h hst
          · exact Book.not_pre_of_pending h hst
        exact mk (by rw [hst, WState.shadow_pre_pt hpre hp]) hp

end RegionHistory

end Balaban.LargeField
