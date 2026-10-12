module

public import Balaban.LargeField.Counter.CapStrip
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The banks of a merge within the cap (Part I, (B.10))

`U' + ½ ∑_{ξ ∈ X} τ_ξ ≤ ∑_i U_i + ½ τ_μ`: the records released at the merge pay for the shift of the
ripeness time, and no bank is spent twice.
-/

@[expose] public section

namespace Balaban.LargeField

theorem sum_union_le_aux {A B : Finset ℕ} {g : ℕ → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ A ∪ B, g x ≤ ∑ x ∈ A, g x + ∑ x ∈ B, g x := by
  classical
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := g)
  have h2 : 0 ≤ ∑ x ∈ A ∩ B, g x := Finset.sum_nonneg (fun x _ => hg x)
  linarith

theorem sum_biUnion_le_aux {ι : Type*} (P : Finset ι) (M : ι → Finset ℕ) {g : ℕ → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ∑ x ∈ P.biUnion M, g x ≤ ∑ i ∈ P, ∑ x ∈ M i, g x := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    calc ∑ x ∈ M a ∪ s.biUnion M, g x ≤ ∑ x ∈ M a, g x + ∑ x ∈ s.biUnion M, g x :=
          sum_union_le_aux hg
      _ ≤ _ := by linarith

theorem sum_eq_erase_add (s : Finset ℕ) (μ : ℕ) (g : ℕ → ℝ) :
    ∑ x ∈ s, g x = ∑ x ∈ s.erase μ, g x + if μ ∈ s then g μ else 0 := by
  by_cases h : μ ∈ s
  · rw [if_pos h]; exact (Finset.sum_erase_add s g h).symm
  · rw [Finset.erase_eq_of_notMem h]; simp [h]

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

theorem bank_ineq {ι : Type*} {k : ℕ} {P : Finset ι} {f : ι → Book} {b' : Book}
    (hinv : ∀ i ∈ P, BookInv S k (f i)) (hT : T4Facts S k P f b') :
    S.bank b' + 1 / 2 * ∑ ξ ∈ S.stripSet (Setting.t4E (k + 1) P f) (S.t4t0 P f b'.s), S.tau ξ ≤
      ∑ i ∈ P, S.bank (f i) + 1 / 2 * S.tau (k + 1) := by
  classical
  set E := Setting.t4E (k + 1) P f with hEdef
  set t0 := S.t4t0 P f b'.s with ht0
  set q' := S.t4q (k + 1) P f b'.s with hq'
  set X := S.stripSet E t0 with hX
  have hqk : q' = S.k1 (S.Tmin E t0) := rfl
  have hτ0 : ∀ x, 0 ≤ S.tau x := G.ok.tau_nonneg
  set Ub := P.biUnion (fun i => (f i).M) with hUb
  have hEsub : ∀ ξ ∈ E, ξ ≠ k + 1 → ξ ∈ Ub := by
    intro ξ hξ hne
    unfold Setting.t4E at hEdef
    rw [hEdef] at hξ
    rcases Finset.mem_union.mp hξ with h | h
    · exact h
    · simp at h; exact absurd h hne
  have hbank_b : S.bank b' = 1 / 2 * ∑ ξ ∈ E.filter (fun ξ => q' < ξ), S.tau ξ := by
    unfold Setting.bank; rw [hT.M_eq]
  have hbank_sum : ∑ i ∈ P, S.bank (f i) = 1 / 2 * ∑ i ∈ P, ∑ ξ ∈ (f i).M, S.tau ξ := by
    unfold Setting.bank; rw [Finset.mul_sum]
  have hUb_le : ∑ ξ ∈ Ub, S.tau ξ ≤ ∑ i ∈ P, ∑ ξ ∈ (f i).M, S.tau ξ :=
    sum_biUnion_le_aux P (fun i => (f i).M) hτ0
  -- split off `μ`
  set M' := E.filter (fun ξ => q' < ξ) with hM'
  have e1 := sum_eq_erase_add M' (k + 1) S.tau
  have e2 := sum_eq_erase_add X (k + 1) S.tau
  have hdisj : Disjoint (M'.erase (k + 1)) (X.erase (k + 1)) := by
    rw [Finset.disjoint_left]
    intro ξ h1 h2
    have a1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase h1)).2
    have a2 := (G.mem_stripSet.mp (Finset.mem_of_mem_erase h2)).2.1
    omega
  have hsubU : M'.erase (k + 1) ∪ X.erase (k + 1) ⊆ Ub := by
    intro ξ hξ
    rcases Finset.mem_union.mp hξ with h | h
    · exact hEsub ξ (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1 (Finset.ne_of_mem_erase h)
    · exact hEsub ξ (G.mem_stripSet.mp (Finset.mem_of_mem_erase h)).1 (Finset.ne_of_mem_erase h)
  have hsum_le : ∑ ξ ∈ M'.erase (k + 1), S.tau ξ + ∑ ξ ∈ X.erase (k + 1), S.tau ξ ≤
      ∑ ξ ∈ Ub, S.tau ξ := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubU (fun x _ _ => hτ0 x)
  -- `μ` is in at most one of `M'`, `X`
  have hμ : (if k + 1 ∈ M' then S.tau (k + 1) else 0) + (if k + 1 ∈ X then S.tau (k + 1) else 0)
      ≤ S.tau (k + 1) := by
    have h0 := hτ0 (k + 1)
    by_cases h1 : k + 1 ∈ M'
    · have h2 : k + 1 ∉ X := by
        intro h2
        have := (G.mem_stripSet.mp h2).2.1
        have := (Finset.mem_filter.mp h1).2
        omega
      simp [h1, h2]
    · by_cases h2 : k + 1 ∈ X <;> simp [h1, h2, h0]
  rw [hbank_b, hbank_sum]
  have : ∑ ξ ∈ M', S.tau ξ + ∑ ξ ∈ X, S.tau ξ ≤ ∑ i ∈ P, ∑ ξ ∈ (f i).M, S.tau ξ + S.tau (k + 1) := by
    rw [e1, e2]; linarith
  linarith

end Setting.Good

end Balaban.LargeField
