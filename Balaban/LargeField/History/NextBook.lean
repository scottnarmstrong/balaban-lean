module

public import Balaban.LargeField.History.Step
public import Balaban.LargeField.History.SpineOps
import Mathlib.Tactic.Linarith

/-!
# The bookkeeping of a component after a step (Definition I.4.7 item 5, (T1)-(T5))

`Setting.nextBook S μ parts f r Γ'` is the book of a component of `Z^pre_μ` with old parts `parts`
(post-`R` books `f`), `r` new cubes and final spine `Γ'`: its spine length is `ℓ(Γ')`, it is a
point iff `ℓ(Γ') = 0`, its clock `s` is given by item 5 and its window state by (T1)-(T5).
`BookRule` follows from the two spine properties of Lemma I.4.8 (the length bound (4.1) and the
pure-shadow rule).
-/

@[expose] public section

namespace Balaban.LargeField

open Classical in
/-- The smallness clock `s'` of Definition I.4.7 item 5. -/
noncomputable def Setting.nextClock (S : Setting) {ι : Type*} (μ : ℕ) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) (len : ℝ) : ℕ :=
  if len = 0 then
    (if r = 0 ∧ parts.card = 1 ∧ ∀ i ∈ parts, (f i).pt then parts.sup (fun i => (f i).s) else μ)
  else μ + max 1 ⌈Real.logb S.L (max len 1)⌉₊

open Classical in
/-- The window state after the step, (T1)-(T5). -/
noncomputable def Setting.nextState (S : Setting) {ι : Type*} (μ : ℕ) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) (pt' : Prop) (s' : ℕ) : WState :=
  if 1 ≤ r then WState.restart μ pt'
  else if h : parts.card = 1 then WState.shadow μ pt' (f (Finset.card_eq_one.mp h).choose)
  else if ∃ i ∈ parts, (f i).st = .pre then WState.restart μ pt'
  else if ∑ i ∈ parts, (f i).nu ≤ S.numax μ then S.t4State μ parts f s'
  else WState.restart μ pt'

/-- The book of a component of `Z^pre_μ`. -/
noncomputable def Setting.nextBook (S : Setting) {ι : Type*} (μ : ℕ) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) (Γ' : Spine S.d) : Book where
  st := S.nextState μ parts f r (Γ'.length = 0) (S.nextClock μ parts f r Γ'.length)
  s := S.nextClock μ parts f r Γ'.length
  len := Γ'.length
  pt := Γ'.length = 0

theorem Setting.nextClock_np (S : Setting) {ι : Type*} (μ : ℕ) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) {len : ℝ} (h : len ≠ 0) :
    S.nextClock μ parts f r len = μ + max 1 ⌈Real.logb S.L (max len 1)⌉₊ := by
  simp [Setting.nextClock, h]

theorem Setting.nextClock_pt_shadow (S : Setting) {ι : Type*} (μ : ℕ) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) {len : ℝ} (h : len = 0) (hr : r = 0) (i : ι) (hi : parts = {i})
    (hpi : (f i).pt) : S.nextClock μ parts f r len = (f i).s := by
  classical
  have hall : ∀ j ∈ parts, (f j).pt := by
    intro j hj; rw [hi, Finset.mem_singleton] at hj; rw [hj]; exact hpi
  have hc : parts.card = 1 := by rw [hi]; simp
  have hcond : r = 0 ∧ parts.card = 1 ∧ ∀ j ∈ parts, (f j).pt := ⟨hr, hc, hall⟩
  unfold Setting.nextClock
  rw [ite_eq_left h, ite_eq_left hcond, hi, Finset.sup_singleton]

theorem Setting.nextClock_pt_other (S : Setting) {ι : Type*} (μ : ℕ) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) {len : ℝ} (h : len = 0)
    (hnot : ¬ (r = 0 ∧ ∃ i, parts = {i} ∧ (f i).pt)) : S.nextClock μ parts f r len = μ := by
  classical
  have : ¬ (r = 0 ∧ parts.card = 1 ∧ ∀ i ∈ parts, (f i).pt) := by
    rintro ⟨hr, hc, hall⟩
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    exact hnot ⟨hr, i, hi, hall i (by rw [hi]; exact Finset.mem_singleton_self i)⟩
  simp only [Setting.nextClock, h, this, ↓reduceIte]

theorem Setting.nextBook_rule (S : Setting) {ι : Type*} (μ : ℕ) (win : Prop) (parts : Finset ι)
    (f : ι → Book) (r : ℕ) (Γ' : Spine S.d)
    (hlen : Γ'.length ≤ ∑ i ∈ parts, (f i).len / S.L +
      (((parts.card + r : ℕ) : ℝ) - 1) * S.D μ)
    (hshadow : r = 0 → ∀ i, parts = {i} → (f i).len ≤ S.L → Γ'.length = 0)
    (hpt : ∀ i ∈ parts, (f i).pt → (f i).len = 0) :
    S.BookRule μ win parts f r (S.nextBook μ parts f r Γ') := by
  classical
  have hL : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
  refine ⟨Γ'.length_nonneg, fun h => h, hlen, ?_, ?_, ?_, ?_, ?_⟩
  · intro hr i hi
    refine ⟨fun hn => ?_, fun hp => ?_⟩
    · by_contra hlt
      exact hn (hshadow hr i hi (not_lt.mp hlt))
    · have h0 := hpt i (by rw [hi]; exact Finset.mem_singleton_self i) hp
      exact hshadow hr i hi (by rw [h0]; exact hL)
  · intro hn
    exact S.nextClock_np μ parts f r (len := Γ'.length) hn
  · intro hp hr i hi hpi
    exact S.nextClock_pt_shadow μ parts f r (len := Γ'.length) hp hr i hi hpi
  · intro hp hnot
    exact S.nextClock_pt_other μ parts f r (len := Γ'.length) hp hnot
  · intro _
    have hs : (S.nextBook μ parts f r Γ').s = S.nextClock μ parts f r Γ'.length := rfl
    have hst : (S.nextBook μ parts f r Γ').st =
        S.nextState μ parts f r (Γ'.length = 0) (S.nextClock μ parts f r Γ'.length) := rfl
    have hpt' : (S.nextBook μ parts f r Γ').pt = (Γ'.length = 0) := rfl
    rw [hs, hst, hpt']
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hr
      simp only [Setting.nextState, hr, ↓reduceIte]
    · intro hr i hi
      have hcard : parts.card = 1 := by rw [hi]; simp
      have hc : (Finset.card_eq_one.mp hcard).choose = i :=
        Finset.singleton_injective ((Finset.card_eq_one.mp hcard).choose_spec.symm.trans hi)
      have hr' : ¬ 1 ≤ r := by omega
      simp only [Setting.nextState, hr', hcard, ↓reduceIte, ↓reduceDIte]
      rw [hc]
    · intro hr hc hpre
      have hr' : ¬ 1 ≤ r := by omega
      have hc' : parts.card ≠ 1 := by omega
      simp only [Setting.nextState, hr', hc', hpre, ↓reduceIte, ↓reduceDIte]
    · intro hr hc hnpre hcap
      have hr' : ¬ 1 ≤ r := by omega
      have hc' : parts.card ≠ 1 := by omega
      have hnp : ¬ ∃ i ∈ parts, (f i).st = .pre := by
        rintro ⟨i, hi, h⟩; exact hnpre i hi h
      simp only [Setting.nextState, hr', hc', hnp, hcap, ↓reduceIte, ↓reduceDIte]
    · intro hr hc hnpre hcap
      have hr' : ¬ 1 ≤ r := by omega
      have hc' : parts.card ≠ 1 := by omega
      have hnp : ¬ ∃ i ∈ parts, (f i).st = .pre := by
        rintro ⟨i, hi, h⟩; exact hnpre i hi h
      have hcap' : ¬ ∑ i ∈ parts, (f i).nu ≤ S.numax μ := by omega
      simp only [Setting.nextState, hr', hc', hnp, hcap', ↓reduceIte, ↓reduceDIte]

end Balaban.LargeField
