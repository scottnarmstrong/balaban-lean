module

public import Balaban.LargeField.History.StepMerge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One step: classification and the invariant `BookInv` (Lemmas I.4.10, I.4.13)

`step_classify` shows that the bookkeeping of a component after the step `k → k+1` satisfies
`BookInv (k+1)` and falls under exactly one of the cases (T1) (pure shadow), (T2) (new cubes),
(T3) (merge with a `Pre` part), (T4) (merge within the cap), (T5) (overflow), together with
the facts the budget needs in that case.  `rstep_inv` is the same for `R^{(k)}`.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The facts about a restart output used by the budget. -/
def RestartFacts (S : Setting) (k : ℕ) (b' : Book) : Prop :=
  S.tStar b' = b'.s + S.nq b'.s ∧ k + 1 ≤ b'.s ∧
    (b'.s : ℝ) ≤ (k + 1 : ℕ) + 1 + Real.logb S.L (max b'.len 1) ∧ b'.nu = 1 ∧ S.bank b' = 0

/-- The five cases of a step with their facts. -/
inductive StepCase (S : Setting) (k : ℕ) {ι : Type*} (parts : Finset ι) (f : ι → Book) (r : ℕ)
    (b' : Book) : Prop
  | shadow (i : ι) (hparts : parts = {i}) (hr : r = 0) (hle : S.tStar b' ≤ S.tStar (f i))
      (hge : k + 1 ≤ S.tStar b') (hnu : b'.nu = (f i).nu) (hbank : S.bank b' = S.bank (f i)) :
      StepCase S k parts f r b'
  | new (hr : 1 ≤ r) (hf : RestartFacts S k b') : StepCase S k parts f r b'
  | mergePre (hr : r = 0) (hcard : 2 ≤ parts.card) (hpre : ∃ i ∈ parts, (f i).st = .pre)
      (hf : RestartFacts S k b') : StepCase S k parts f r b'
  | mergeCap (hr : r = 0) (hcard : 2 ≤ parts.card) (hnpre : ∀ i ∈ parts, (f i).st ≠ .pre)
      (hcap : ∑ i ∈ parts, (f i).nu ≤ S.numax (k + 1)) (hf : T4Facts S k parts f b') :
      StepCase S k parts f r b'
  | overflow (hr : r = 0) (hcard : 2 ≤ parts.card) (hnpre : ∀ i ∈ parts, (f i).st ≠ .pre)
      (hcap : S.numax (k + 1) < ∑ i ∈ parts, (f i).nu) (hf : RestartFacts S k b') :
      StepCase S k parts f r b'

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem step_classify {ι : Type*} {k : ℕ} {parts : Finset ι} {f : ι → Book} {r : ℕ} {b' : Book}
    (hinv : ∀ i ∈ parts, BookInv S k (f i)) (hpost : ∀ i ∈ parts, k < S.tStar (f i))
    (hseed : 1 ≤ parts.card + r) (hrule : S.BookRule (k + 1) True parts f r b') :
    BookInv S (k + 1) b' ∧ StepCase S k parts f r b' := by
  obtain ⟨hlen, hptl, hgen, hshadow, hnp, hcs, hco, hstate⟩ := hrule
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hstate trivial
  -- the restart facts, given the output is a restart
  have restart : (b'.st = WState.restart (k + 1) b'.pt) → (b'.pt → b'.s = k + 1) →
      BookInv S (k + 1) b' ∧ RestartFacts S k b' := by
    intro hst hpt
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := G.restart_inv hst hlen hptl hnp hpt
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  by_cases hr : 1 ≤ r
  · -- (T2)
    have hpt : b'.pt → b'.s = k + 1 := fun hp => hco hp (by
      rintro ⟨h, _⟩; omega)
    obtain ⟨hi, hf⟩ := restart (hs1 hr) hpt
    exact ⟨hi, StepCase.new hr hf⟩
  · have hr0 : r = 0 := by omega
    have hcard1 : 1 ≤ parts.card := by omega
    by_cases hc2 : 2 ≤ parts.card
    · have hpt : b'.pt → b'.s = k + 1 := fun hp => hco hp (by
        rintro ⟨_, i, hi, _⟩
        have : parts.card = 1 := by rw [hi]; simp
        omega)
      by_cases hpre : ∃ i ∈ parts, (f i).st = .pre
      · -- (T3)
        obtain ⟨hi, hf⟩ := restart (hs3 hr0 hc2 hpre) hpt
        exact ⟨hi, StepCase.mergePre hr0 hc2 hpre hf⟩
      · have hnpre : ∀ i ∈ parts, (f i).st ≠ .pre := fun i hi h => hpre ⟨i, hi, h⟩
        by_cases hcap : ∑ i ∈ parts, (f i).nu ≤ S.numax (k + 1)
        · -- (T4)
          have hact : ∀ i ∈ parts, (f i).IsActive ∨ (f i).IsPending := by
            intro i hi
            rcases Book.cases_st (f i) with h | h | h
            · exact absurd h (hnpre i hi)
            · exact Or.inr h
            · exact Or.inl h
          have hst := hs4 hr0 hc2 hnpre hcap
          subst hr0
          have hT := G.t4_inv hc2 hinv hact hcap hst hlen hptl hgen hnp hpt
          exact ⟨hT.inv, StepCase.mergeCap rfl hc2 hnpre hcap hT⟩
        · -- (T5)
          have hcap' : S.numax (k + 1) < ∑ i ∈ parts, (f i).nu := not_le.mp hcap
          obtain ⟨hi, hf⟩ := restart (hs5 hr0 hc2 hnpre hcap') hpt
          exact ⟨hi, StepCase.overflow hr0 hc2 hnpre hcap' hf⟩
    · -- (T1): a single part
      have hc1 : parts.card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc1
      have hmem : i ∈ parts := by rw [hi]; simp
      have hst := hs2 hr0 i hi
      have hlen' : b'.len ≤ (f i).len / S.L := by
        have := hgen
        rw [hi, hr0] at this
        simpa using this
      obtain ⟨hsh1, hsh2⟩ := hshadow hr0 i hi
      have hc1' : b'.pt → (f i).pt → b'.s = (f i).s := fun hp hq => hcs hp hr0 i hi hq
      have hc2' : b'.pt → ¬ (f i).pt → b'.s = k + 1 := fun hp hq => hco hp (by
        rintro ⟨_, j, hj, hjp⟩
        have : j = i := by
          have : j ∈ ({i} : Finset ι) := by rw [← hi, hj]; simp
          simpa using this
        subst this
        exact hq hjp)
      obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := G.shadow_inv (hinv i hmem) (hpost i hmem) hst hlen hptl
        hlen' hsh1 hsh2 hnp hc1' hc2'
      exact ⟨hi1, StepCase.shadow i hi hr0 hi2 hi3 hi4 hi5⟩

end Setting.Good

end Balaban.LargeField
