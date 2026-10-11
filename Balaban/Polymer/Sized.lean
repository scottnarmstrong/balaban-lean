module

public import Balaban.Polymer.Local
public import Balaban.Polymer.PE

/-!
# The polymer expansion for polymers with a size

Polymers `x : P` carry a charged support `supp x ⊆ B` (the blocks outside a hole) and a size
`s x ≥ |supp x|`; two polymers are incompatible iff their charged supports meet.  If the activities
satisfy `‖K x‖ ≤ ε e^{-κ s x}` and the entropy sum `∑_{x ∋ b} ε e^{(κ' + α - κ) s x}` is at most `α`
for every block `b`, then the Kotecký–Preiss condition holds with `a x = α |supp x|`
(`sized_kp`) and the conclusions of `pe_lattice` hold (`pe_sized`).  This is the abstract form of
the lattice theorem with a hole (POLYMER.md §2.3 and §3.6).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable {P : Type*} [Fintype P] {B : Type*} [Fintype B] (supp : P → Finset B)

/-- Two polymers are incompatible iff their charged supports meet. -/
def shareBlock (x y : P) : Prop := ¬ Disjoint (supp x) (supp y)

omit [Fintype P] [Fintype B] in
theorem shareBlock_symm (x y : P) : shareBlock supp x y → shareBlock supp y x := fun h hd =>
  h hd.symm

omit [Fintype P] [Fintype B] in
theorem shareBlock_refl (hne : ∀ x, (supp x).Nonempty) (x : P) : shareBlock supp x x := by
  intro hd
  obtain ⟨b, hb⟩ := hne x
  exact Finset.disjoint_left.mp hd hb hb

omit [Fintype P] [Fintype B] in
theorem lnk_shareBlock (x y : P) : lnk (shareBlock supp) x y ↔ shareBlock supp x y :=
  ⟨fun h => h.elim id (shareBlock_symm supp _ _), Or.inl⟩

variable (s : P → ℝ) (g : Finset B → ℝ) {ε κ κ' α : ℝ}

/-- The weights `κ x = ε e^{-κ s x} e^{g(supp x)}`. -/
def sizedW (ε κ : ℝ) (x : P) : ℝ := ε * Real.exp (-κ * s x) * Real.exp (g (supp x) + 0)

section KP

variable (hε : 0 ≤ ε) (hα : 0 ≤ α) (hs : ∀ x, ((supp x).card : ℝ) ≤ s x)
  (hgs : ∀ x, g (supp x) ≤ κ' * s x)
  (hent : ∀ b, ∑ x, (if b ∈ supp x then ε * Real.exp ((κ' + α - κ) * s x) else 0) ≤ α)

include hε hα hs hgs in
omit [Fintype P] [Fintype B] in
theorem sizedW_mul_exp_le (x : P) :
    sizedW supp s g ε κ x * Real.exp (α * (supp x).card) ≤ ε * Real.exp ((κ' + α - κ) * s x) := by
  unfold sizedW
  have h1 : Real.exp (-κ * s x) * Real.exp (g (supp x) + 0) * Real.exp (α * (supp x).card) ≤
      Real.exp ((κ' + α - κ) * s x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := hgs x
    have h2 : α * ((supp x).card : ℝ) ≤ α * s x := mul_le_mul_of_nonneg_left (hs x) hα
    nlinarith
  calc ε * Real.exp (-κ * s x) * Real.exp (g (supp x) + 0) * Real.exp (α * (supp x).card)
      = ε * (Real.exp (-κ * s x) * Real.exp (g (supp x) + 0) * Real.exp (α * (supp x).card)) := by
        ring
    _ ≤ ε * Real.exp ((κ' + α - κ) * s x) := mul_le_mul_of_nonneg_left h1 hε

include hε hα hs hgs hent in
omit [Fintype B] in
theorem sized_kp :
    KPCond (shareBlock supp) (sizedW supp s g ε κ) (fun x => α * (supp x).card) := by
  constructor
  · intro x; unfold sizedW; positivity
  · intro Y
    calc ∑ Y', (if lnk (shareBlock supp) Y Y' then sizedW supp s g ε κ Y' *
          Real.exp (α * (supp Y').card) else 0)
        ≤ ∑ Y', ∑ b ∈ supp Y, (if b ∈ supp Y' then
          ε * Real.exp ((κ' + α - κ) * s Y') else 0) := by
          refine Finset.sum_le_sum (fun Y' _ => ?_)
          by_cases h : lnk (shareBlock supp) Y Y'
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
            obtain ⟨b, hbY, hbY'⟩ : ∃ b, b ∈ supp Y ∧ b ∈ supp Y' := by
              have h1 := (lnk_shareBlock supp Y Y').mp h
              by_contra hcon
              exact h1 (Finset.disjoint_left.mpr (fun b hb hb' => hcon ⟨b, hb, hb'⟩))
            calc _ ≤ ε * Real.exp ((κ' + α - κ) * s Y') :=
                  sizedW_mul_exp_le supp s g hε hα hs hgs Y'
              _ = (if b ∈ supp Y' then ε * Real.exp ((κ' + α - κ) * s Y') else 0) := by
                  rw [ite_eq_left_of_eq_true _ _ (eq_true hbY')]
              _ ≤ _ := Finset.single_le_sum (f := fun b => (if b ∈ supp Y' then
                  ε * Real.exp ((κ' + α - κ) * s Y') else 0))
                  (fun _ _ => by split_ifs <;> positivity) hbY
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
            exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
      _ = ∑ b ∈ supp Y, ∑ Y', (if b ∈ supp Y' then
          ε * Real.exp ((κ' + α - κ) * s Y') else 0) := Finset.sum_comm
      _ ≤ ∑ b ∈ supp Y, α := Finset.sum_le_sum (fun b _ => hent b)
      _ = α * (supp Y).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end KP

section Main

variable (hε : 0 ≤ ε) (hα : 0 ≤ α) (hne : ∀ x, (supp x).Nonempty)
  (hs : ∀ x, ((supp x).card : ℝ) ≤ s x) (hg0 : ∀ Y, 0 ≤ g Y)
  (hgs : ∀ x, g (supp x) ≤ κ' * s x)
  (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph (shareBlock supp) X).Connected →
      g (unionOf supp X) ≤ ∑ i, g (supp (X i)) + 0 * n)
  (hent : ∀ b, ∑ x, (if b ∈ supp x then ε * Real.exp ((κ' + α - κ) * s x) else 0) ≤ α)
  (T : Finset B) (hT : ∀ x, ∃ b ∈ T, b ∈ supp x)

include hε hα hne hs hg0 hgs hG3 hent hT in
/-- The polymer expansion for polymers with a size. -/
theorem pe_sized (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ ε * Real.exp (-κ * s x)) :
    Xi (shareBlock supp) K = Complex.exp (logSeries (shareBlock supp) K) ∧
    logSeries (shareBlock supp) K = ∑ Y : Finset B, PY (shareBlock supp) supp K Y ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock supp) supp K Y‖ * Real.exp (g Y) ≤ α) ∧
    ‖logSeries (shareBlock supp) K‖ ≤ T.card * α ∧
    Real.exp (-(T.card * α)) ≤ ‖Xi (shareBlock supp) K‖ ∧
    ‖Xi (shareBlock supp) K‖ ≤ Real.exp (T.card * α) := by
  have hKP := sized_kp supp s g hε hα hs hgs hent
  have hK' : ∀ x, ‖K x‖ ≤ sizedW supp s g ε κ x := fun x => by
    refine (hK x).trans ?_
    unfold sizedW
    calc ε * Real.exp (-κ * s x) = ε * Real.exp (-κ * s x) * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hg0 (supp x); linarith)) (by positivity)
  have hw : ∀ t : B, ∑ Y : P, (if t ∈ supp Y then
      sizedW supp s g ε κ Y * Real.exp (α * (supp Y).card) else 0) ≤ α := fun t =>
    le_trans (Finset.sum_le_sum (fun Y _ => by
      by_cases ht : t ∈ supp Y
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ht), ite_eq_left_of_eq_true _ _ (eq_true ht)]
        exact sizedW_mul_exp_le supp s g hε hα hs hgs Y
      · rw [ite_eq_right_of_eq_false _ _ (eq_false ht), ite_eq_right_of_eq_false _ _ (eq_false ht)]))
      (hent t)
  have hL : ‖logSeries (shareBlock supp) K‖ ≤ ∑ _b : T, α := by
    have := pe_logSeries_bound (shareBlock supp) (fun (b : T) (Y : P) => b.1 ∈ supp Y)
      (fun Y => by obtain ⟨b, hb, hY⟩ := hT Y; exact ⟨⟨b, hb⟩, hY⟩) hKP K hK'
      (fun _ => α) (fun b => by convert hw b.1 using 3)
    exact this
  have hnorm := pe_xi_norm_bounds (shareBlock supp) (fun (b : T) (Y : P) => b.1 ∈ supp Y)
    (fun Y => by obtain ⟨b, hb, hY⟩ := hT Y; exact ⟨⟨b, hb⟩, hY⟩) hKP
    (shareBlock_refl supp hne) K hK' (fun _ => α) (fun b => by convert hw b.1 using 3)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hL hnorm
  refine ⟨pe_xi_eq_exp (shareBlock supp) hKP (shareBlock_refl supp hne) K hK',
    logSeries_eq_sum_PY (shareBlock supp) supp hKP K hK', ?_, hL, hnorm.1, hnorm.2⟩
  intro b
  have := pe_PY_bound (shareBlock supp) supp g 0 le_rfl hg0 hG3 (κ0 := fun x => ε * Real.exp (-κ * s x))
    (fun x => rfl) hKP K hK b
  refine this.trans ?_
  refine le_trans (Finset.sum_le_sum (fun x _ => ?_)) (hent b)
  by_cases hb : b ∈ supp x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_left_of_eq_true _ _ (eq_true hb)]
    exact sizedW_mul_exp_le supp s g hε hα hs hgs x
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false hb)]

end Main

end Balaban.Polymer
