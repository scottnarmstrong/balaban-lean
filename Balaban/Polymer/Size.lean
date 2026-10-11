module

public import Balaban.Polymer.Sized

/-!
# The polymer expansion for a general size (PE-L)

POLYMER.md §2.3.  Polymers `x : P` carry nonempty charged supports `supp x ⊆ B` and a size
`d : Finset B → ℝ≥0`.  Assume (G1) `|supp x| ≤ c₁ (1 + d(supp x))`, (G2) `∑_{x ∋ b} e^{-κ₀ d(x)} ≤ K₀`
for every block `b`, (G3) `d(⋃ X_i) ≤ ∑ d(X_i) + c n` on clusters with connected incompatibility
graph, `|K x| ≤ ε e^{-κ d(x)}` with `κ ≥ κ' + κ₀ + c₁` and `α := ε K₀ e^{c₁ + κ' c} ≤ 1`.  Then
the Kotecký–Preiss condition holds with `a(x) = α |supp x|`, `b(x) = κ'(d(x) + c)`, and
`pe_size` gives `Ξ = exp L`, `L = ∑_Y P(Y)`, `∑_{Y ∋ □} |P(Y)| e^{κ' d(Y)} ≤ α e^{-κ' c}` and
`|L| ≤ α |T|`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section KP

variable {P : Type*} [Fintype P] {B : Type*} [Fintype B] (supp : P → Finset B)

omit [Fintype B] in
theorem kp_of_entropy {α : ℝ} (W : P → ℝ) (hW : ∀ x, 0 ≤ W x)
    (hent : ∀ b : B, ∑ x, (if b ∈ supp x then W x * Real.exp (α * (supp x).card) else 0) ≤ α) :
    KPCond (shareBlock supp) W (fun x => α * (supp x).card) := by
  constructor
  · exact hW
  · intro Y
    calc ∑ Y', (if lnk (shareBlock supp) Y Y' then W Y' * Real.exp (α * (supp Y').card) else 0)
        ≤ ∑ Y', ∑ b ∈ supp Y, (if b ∈ supp Y' then
          W Y' * Real.exp (α * (supp Y').card) else 0) := by
          refine Finset.sum_le_sum (fun Y' _ => ?_)
          by_cases h : lnk (shareBlock supp) Y Y'
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
            obtain ⟨b, hbY, hbY'⟩ : ∃ b, b ∈ supp Y ∧ b ∈ supp Y' := by
              have h1 := (lnk_shareBlock supp Y Y').mp h
              by_contra hcon
              exact h1 (Finset.disjoint_left.mpr (fun b hb hb' => hcon ⟨b, hb, hb'⟩))
            calc W Y' * Real.exp (α * (supp Y').card)
                = (if b ∈ supp Y' then W Y' * Real.exp (α * (supp Y').card) else 0) := by
                  rw [ite_eq_left_of_eq_true _ _ (eq_true hbY')]
              _ ≤ _ := Finset.single_le_sum (f := fun b => (if b ∈ supp Y' then
                  W Y' * Real.exp (α * (supp Y').card) else 0))
                  (fun _ _ => by split_ifs <;> [exact mul_nonneg (hW _) (Real.exp_pos _).le; exact le_rfl])
                  hbY
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
            exact Finset.sum_nonneg (fun _ _ => by
              split_ifs <;> [exact mul_nonneg (hW _) (Real.exp_pos _).le; exact le_rfl])
      _ = ∑ b ∈ supp Y, ∑ Y', (if b ∈ supp Y' then
          W Y' * Real.exp (α * (supp Y').card) else 0) := Finset.sum_comm
      _ ≤ ∑ b ∈ supp Y, α := Finset.sum_le_sum (fun b _ => hent b)
      _ = α * (supp Y).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end KP

section Main

variable {P : Type*} [Fintype P] {B : Type*} [Fintype B] (supp : P → Finset B)
  (d : Finset B → ℝ) {ε κ κ' κ0 K0 c c1 : ℝ}

/-- The weights `ε e^{-κ d(x)} e^{κ'(d(x) + c)}` of the polymer expansion with a size. -/
def sizeW (ε κ κ' c : ℝ) (x : P) : ℝ :=
  ε * Real.exp (-κ * d (supp x)) * Real.exp (κ' * (d (supp x) + c) + 0)

omit [Fintype P] [Fintype B] in
theorem sizeW_nonneg (hε : 0 ≤ ε) (x : P) : 0 ≤ sizeW supp d ε κ κ' c x := by
  unfold sizeW; positivity

omit [Fintype B] in
/-- The entropy condition of PE-L. -/
theorem size_entropy (hε : 0 ≤ ε)
    (hd : ∀ Y, 0 ≤ d Y)
    (hG1 : ∀ x, ((supp x).card : ℝ) ≤ c1 * (1 + d (supp x)))
    (hG2 : ∀ b : B, ∑ x, (if b ∈ supp x then Real.exp (-κ0 * d (supp x)) else 0) ≤ K0)
    (hκ : κ' + κ0 + c1 ≤ κ) (hα : ε * K0 * Real.exp (c1 + κ' * c) ≤ 1) (b : B) :
    ∑ x, (if b ∈ supp x then sizeW supp d ε κ κ' c x *
      Real.exp ((ε * K0 * Real.exp (c1 + κ' * c)) * (supp x).card) else 0) ≤
      ε * K0 * Real.exp (c1 + κ' * c) := by
  set α : ℝ := ε * K0 * Real.exp (c1 + κ' * c) with hαdef
  have hterm : ∀ x, sizeW supp d ε κ κ' c x * Real.exp (α * (supp x).card) ≤
      ε * Real.exp (c1 + κ' * c) * Real.exp (-κ0 * d (supp x)) := by
    intro x
    have h1 : α * ((supp x).card : ℝ) ≤ (supp x).card :=
      mul_le_of_le_one_left (Nat.cast_nonneg _) hα
    have h2 := hG1 x
    have h3 := hd (supp x)
    calc sizeW supp d ε κ κ' c x * Real.exp (α * (supp x).card)
        = ε * Real.exp (-κ * d (supp x) + (κ' * (d (supp x) + c) + 0) + α * (supp x).card) := by
          unfold sizeW
          have : Real.exp (-κ * d (supp x) + (κ' * (d (supp x) + c) + 0) + α * (supp x).card) =
              Real.exp (-κ * d (supp x)) * Real.exp (κ' * (d (supp x) + c) + 0) *
                Real.exp (α * (supp x).card) := by rw [Real.exp_add, Real.exp_add]
          rw [this]; ring
      _ ≤ ε * Real.exp ((c1 + κ' * c) + (-κ0 * d (supp x))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hε
          nlinarith
      _ = _ := by rw [Real.exp_add]; ring
  calc ∑ x, (if b ∈ supp x then sizeW supp d ε κ κ' c x * Real.exp (α * (supp x).card) else 0)
      ≤ ∑ x, ε * Real.exp (c1 + κ' * c) * (if b ∈ supp x then Real.exp (-κ0 * d (supp x)) else 0) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        by_cases hb : b ∈ supp x
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_left_of_eq_true _ _ (eq_true hb)]
          exact hterm x
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false hb)]
          simp
    _ = ε * Real.exp (c1 + κ' * c) * ∑ x, (if b ∈ supp x then Real.exp (-κ0 * d (supp x)) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ ε * Real.exp (c1 + κ' * c) * K0 :=
        mul_le_mul_of_nonneg_left (hG2 b) (by positivity)
    _ = α := by rw [hαdef]; ring


omit [Fintype P] [Fintype B] in
/-- The weight `g = κ'(d + c)` satisfies (G3) with constant `0`. -/
theorem size_g_G3 [Fintype P] {κ' c : ℝ} (hκ' : 0 ≤ κ')
    (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph (shareBlock supp) X).Connected →
      d (unionOf supp X) ≤ ∑ i, d (supp (X i)) + c * n) :
    ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph (shareBlock supp) X).Connected →
      (fun Y => κ' * (d Y + c)) (unionOf supp X) ≤
        ∑ i, (fun Y => κ' * (d Y + c)) (supp (X i)) + 0 * n := by
  intro n X hX
  have h1 := hG3 n X hX
  simp only [zero_mul, add_zero, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  nlinarith

/-- **PE-L for a general size** (POLYMER.md §2.3). -/
theorem pe_size (hε : 0 ≤ ε) (hK0 : 0 ≤ K0) (hκ' : 0 ≤ κ') (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y) (hne : ∀ x, (supp x).Nonempty)
    (hG1 : ∀ x, ((supp x).card : ℝ) ≤ c1 * (1 + d (supp x)))
    (hG2 : ∀ b : B, ∑ x, (if b ∈ supp x then Real.exp (-κ0 * d (supp x)) else 0) ≤ K0)
    (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph (shareBlock supp) X).Connected →
      d (unionOf supp X) ≤ ∑ i, d (supp (X i)) + c * n)
    (hκ : κ' + κ0 + c1 ≤ κ) (hα : ε * K0 * Real.exp (c1 + κ' * c) ≤ 1)
    (T : Finset B) (hT : ∀ x, ∃ b ∈ T, b ∈ supp x)
    (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ ε * Real.exp (-κ * d (supp x))) :
    Xi (shareBlock supp) K = Complex.exp (logSeries (shareBlock supp) K) ∧
    logSeries (shareBlock supp) K = ∑ Y : Finset B, PY (shareBlock supp) supp K Y ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock supp) supp K Y‖ * Real.exp (κ' * d Y) ≤
          ε * K0 * Real.exp (c1 + κ' * c) * Real.exp (-(κ' * c))) ∧
    ‖logSeries (shareBlock supp) K‖ ≤ T.card * (ε * K0 * Real.exp (c1 + κ' * c)) ∧
    Real.exp (-(T.card * (ε * K0 * Real.exp (c1 + κ' * c)))) ≤ ‖Xi (shareBlock supp) K‖ ∧
    ‖Xi (shareBlock supp) K‖ ≤ Real.exp (T.card * (ε * K0 * Real.exp (c1 + κ' * c))) := by
  set α : ℝ := ε * K0 * Real.exp (c1 + κ' * c) with hαdef
  have hα0 : 0 ≤ α := by positivity
  have hent := size_entropy supp d hε hd hG1 hG2 hκ hα
  have hW := sizeW_nonneg (κ := κ) (κ' := κ') (c := c) supp d hε
  have hKP := kp_of_entropy supp (sizeW supp d ε κ κ' c) hW hent
  have hK' : ∀ x, ‖K x‖ ≤ sizeW supp d ε κ κ' c x := fun x => by
    refine (hK x).trans ?_
    unfold sizeW
    calc ε * Real.exp (-κ * d (supp x)) = ε * Real.exp (-κ * d (supp x)) * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hd (supp x); positivity)) (by positivity)
  have hw : ∀ t : B, ∑ Y : P, (if t ∈ supp Y then
      sizeW supp d ε κ κ' c Y * Real.exp (α * (supp Y).card) else 0) ≤ α := hent
  have hL : ‖logSeries (shareBlock supp) K‖ ≤ ∑ _b : T, α := by
    exact pe_logSeries_bound (shareBlock supp) (fun (b : T) (Y : P) => b.1 ∈ supp Y)
      (fun Y => by obtain ⟨b, hb, hY⟩ := hT Y; exact ⟨⟨b, hb⟩, hY⟩) hKP K hK'
      (fun _ => α) (fun b => by convert hw b.1 using 3)
  have hnorm := pe_xi_norm_bounds (shareBlock supp) (fun (b : T) (Y : P) => b.1 ∈ supp Y)
    (fun Y => by obtain ⟨b, hb, hY⟩ := hT Y; exact ⟨⟨b, hb⟩, hY⟩) hKP
    (shareBlock_refl supp hne) K hK' (fun _ => α) (fun b => by convert hw b.1 using 3)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hL hnorm
  refine ⟨pe_xi_eq_exp (shareBlock supp) hKP (shareBlock_refl supp hne) K hK',
    logSeries_eq_sum_PY (shareBlock supp) supp hKP K hK', ?_, hL, hnorm.1, hnorm.2⟩
  intro b
  set g : Finset B → ℝ := fun Y => κ' * (d Y + c) with hg
  have hg0 : ∀ Y, 0 ≤ g Y := fun Y => by have := hd Y; positivity
  have hG3' := size_g_G3 supp d hκ' hG3
  have := pe_PY_bound (shareBlock supp) supp g 0 le_rfl hg0 hG3'
    (κ0 := fun x => ε * Real.exp (-κ * d (supp x))) (fun x => rfl) hKP K hK b
  have hle : ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
      ‖PY (shareBlock supp) supp K Y‖ * Real.exp (g Y) ≤ α := this.trans (hent b)
  have e : ∀ Y : Finset B, Real.exp (g Y) = Real.exp (κ' * d Y) * Real.exp (κ' * c) := fun Y => by
    rw [hg]; simp only []; rw [← Real.exp_add]; congr 1; ring
  have hc' : 0 < Real.exp (κ' * c) := Real.exp_pos _
  have : ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
      ‖PY (shareBlock supp) supp K Y‖ * Real.exp (g Y) =
      (∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock supp) supp K Y‖ * Real.exp (κ' * d Y)) * Real.exp (κ' * c) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun Y _ => by rw [e Y]; ring)
  rw [this] at hle
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hc']
  exact hle

end Main

end Balaban.Polymer
