module

public import Balaban.Polymer.Local
public import Balaban.Polymer.Animals

/-!
# The polymer expansion for polymers = connected block sets

`B` is a finite set of blocks with a nearest-neighbour graph `H` of degree at most `Δ`
(`Δ = 2d` for the block torus, see `blockGraph_degree_le`).  A polymer is a nonempty set of blocks
which is connected in `H`; its size is its number of blocks; two polymers are incompatible iff
they share a block.  By the animal bound (`card_animals_le`) the Kotecký–Preiss condition holds
with `a(Y) = α |Y|` as soon as `ε Σ_{n ≥ 1} Δ^{2(n-1)} e^{-(κ - κ' - α) n} ≤ α`, and then
`pe_lattice` gives `Ξ = exp L`, the local representation `L = Σ_Y P(Y)` and the bound
`Σ_{Y ∋ □} |P(Y)| e^{κ' |Y|} ≤ α`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Blocks

variable {B : Type*} [Fintype B] (H : SimpleGraph B)

/-- Nonempty connected block sets. -/
def IsAnimal (X : Finset B) : Prop := X.Nonempty ∧ (H.induce (X : Set B)).Connected

/-- The polymers: nonempty `H`-connected sets of blocks. -/
abbrev BlockPolymer := {X : Finset B // IsAnimal H X}

/-- Polymers are incompatible iff they share a block. -/
def overlap (X Y : BlockPolymer H) : Prop := ¬ Disjoint X.1 Y.1

omit [Fintype B] in
theorem overlap_symm (X Y : BlockPolymer H) : overlap H X Y → overlap H Y X := fun h =>
  fun hd => h hd.symm

omit [Fintype B] in
theorem overlap_refl (X : BlockPolymer H) : overlap H X X := by
  intro hd
  obtain ⟨b, hb⟩ := X.2.1
  exact Finset.disjoint_left.mp hd hb hb

omit [Fintype B] in
theorem lnk_overlap (X Y : BlockPolymer H) : lnk (overlap H) X Y ↔ overlap H X Y :=
  ⟨fun h => h.elim id (overlap_symm H _ _), Or.inl⟩

/-- Entropy: the number of polymers with `n` blocks through a given block. -/
theorem sum_animals_le {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) (b : B) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) :
    ∑ X : BlockPolymer H, (if b ∈ X.1 then f X.1.card else 0) ≤
      ∑ n ∈ range (Fintype.card B), (Δ : ℝ) ^ (2 * n) * f (n + 1) := by
  classical
  have h1 : ∑ X : BlockPolymer H, (if b ∈ X.1 then f X.1.card else 0) =
      ∑ X ∈ (Finset.univ : Finset (BlockPolymer H)).filter (fun X => b ∈ X.1), f X.1.card := by
    rw [Finset.sum_filter]
  rw [h1]
  have hmaps : ∀ X ∈ (Finset.univ : Finset (BlockPolymer H)).filter (fun X => b ∈ X.1),
      X.1.card - 1 ∈ range (Fintype.card B) := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have hpos : 0 < X.1.card := Finset.card_pos.mpr ⟨b, hX.2⟩
    have hle : X.1.card ≤ Fintype.card B := Finset.card_le_univ _
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hcard : (((Finset.univ : Finset (BlockPolymer H)).filter (fun X => b ∈ X.1)).filter
      (fun X => X.1.card - 1 = n)).card ≤ Δ ^ (2 * n) := by
    calc _ ≤ (animals H b (n + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun X => X.1) (fun X hX => ?_) (fun X _ Y _ h =>
            Subtype.ext h)
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hX
          rw [Finset.mem_coe, mem_animals]
          have hpos : 0 < X.1.card := Finset.card_pos.mpr ⟨b, hX.1⟩
          exact ⟨hX.1, by show X.1.card = n + 1; omega, X.2.2⟩
      _ ≤ Δ ^ (2 * (n + 1 - 1)) := card_animals_le H hdeg b (n + 1)
      _ = Δ ^ (2 * n) := by simp
  have hterm : ∀ X ∈ ((Finset.univ : Finset (BlockPolymer H)).filter (fun X => b ∈ X.1)).filter
      (fun X => X.1.card - 1 = n), f X.1.card = f (n + 1) := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    have hpos : 0 < X.1.card := Finset.card_pos.mpr ⟨b, hX.1⟩
    congr 1; omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  calc ((((Finset.univ : Finset (BlockPolymer H)).filter (fun X => b ∈ X.1)).filter
      (fun X => X.1.card - 1 = n)).card : ℝ) * f (n + 1) ≤ ((Δ ^ (2 * n) : ℕ) : ℝ) * f (n + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf _)
    _ = _ := by push_cast; ring

section Expansion

variable {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {ε κ κ' α : ℝ}

include hdeg in
/-- The entropy sum over polymers through a block. -/
theorem entropy_bound (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * Real.exp (-(κ - κ' - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α))) ≤ α)
    (b : B) :
    ∑ X : BlockPolymer H, (if b ∈ X.1 then ε * Real.exp ((κ' + α - κ) * X.1.card) else 0) ≤ α := by
  set q : ℝ := (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have h1 := sum_animals_le H hdeg b (fun n => ε * Real.exp ((κ' + α - κ) * n))
    (fun n => by positivity)
  refine h1.trans ?_
  have h2 : ∀ n ∈ range (Fintype.card B), (Δ : ℝ) ^ (2 * n) * (ε * Real.exp ((κ' + α - κ) * ((n + 1 : ℕ) : ℝ)))
      = ε * Real.exp (-(κ - κ' - α)) * q ^ n := by
    intro n _
    rw [hqdef, mul_pow, ← Real.exp_nat_mul, pow_mul]
    push_cast
    rw [show (κ' + α - κ) * ((n : ℝ) + 1) = -(κ - κ' - α) + (n : ℝ) * (-(κ - κ' - α)) by ring,
      Real.exp_add]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  have h3 : ∑ i ∈ range (Fintype.card B), q ^ i ≤ (1 - q)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hq0 hq)
  calc ε * Real.exp (-(κ - κ' - α)) * ∑ i ∈ range (Fintype.card B), q ^ i
      ≤ ε * Real.exp (-(κ - κ' - α)) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ε * Real.exp (-(κ - κ' - α)) / (1 - q) := by rw [div_eq_mul_inv]
    _ ≤ α := hcond


/-- The weights `κ(X) = ε e^{-κ |X|} e^{κ' |X|}` of the lattice expansion. -/
def latticeW (ε κ κ' : ℝ) (X : BlockPolymer H) : ℝ :=
  ε * Real.exp (-κ * X.1.card) * Real.exp (κ' * (X.1.card : ℝ) + 0)

omit [Fintype B] in
theorem latticeW_mul_exp (X : BlockPolymer H) :
    latticeW H ε κ κ' X * Real.exp (α * X.1.card) = ε * Real.exp ((κ' + α - κ) * X.1.card) := by
  unfold latticeW
  have e : Real.exp (-κ * (X.1.card : ℝ)) * Real.exp (κ' * (X.1.card : ℝ) + 0 + α * X.1.card) =
      Real.exp ((κ' + α - κ) * X.1.card) := by
    rw [← Real.exp_add]; congr 1; ring
  have e' : Real.exp (κ' * (X.1.card : ℝ) + 0 + α * X.1.card) =
      Real.exp (κ' * (X.1.card : ℝ) + 0) * Real.exp (α * X.1.card) := Real.exp_add _ _
  rw [← e, e']
  ring

include hdeg in
theorem lattice_kp (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * Real.exp (-(κ - κ' - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α))) ≤ α)
    :
    KPCond (overlap H) (latticeW H ε κ κ') (fun X => α * X.1.card) := by
  constructor
  · intro X; unfold latticeW; positivity
  · intro Y
    have hent := entropy_bound H hdeg hε hq hcond
    calc ∑ Y' : BlockPolymer H, (if lnk (overlap H) Y Y' then latticeW H ε κ κ' Y' *
          Real.exp (α * Y'.1.card) else 0)
        ≤ ∑ Y' : BlockPolymer H, ∑ b ∈ Y.1, (if b ∈ Y'.1 then
          ε * Real.exp ((κ' + α - κ) * Y'.1.card) else 0) := by
          refine Finset.sum_le_sum (fun Y' _ => ?_)
          rw [latticeW_mul_exp]
          by_cases h : lnk (overlap H) Y Y'
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
            obtain ⟨b, hbY, hbY'⟩ : ∃ b, b ∈ Y.1 ∧ b ∈ Y'.1 := by
              rcases (lnk_overlap H Y Y').mp h with h1
              by_contra hcon
              exact h1 (Finset.disjoint_left.mpr (fun b hb hb' => hcon ⟨b, hb, hb'⟩))
            calc ε * Real.exp ((κ' + α - κ) * Y'.1.card)
                = (if b ∈ Y'.1 then ε * Real.exp ((κ' + α - κ) * Y'.1.card) else 0) := by
                  rw [ite_eq_left_of_eq_true _ _ (eq_true hbY')]
              _ ≤ _ := Finset.single_le_sum (f := fun b => (if b ∈ Y'.1 then
                  ε * Real.exp ((κ' + α - κ) * Y'.1.card) else 0))
                  (fun _ _ => by split_ifs <;> positivity) hbY
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
            exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
      _ = ∑ b ∈ Y.1, ∑ Y' : BlockPolymer H, (if b ∈ Y'.1 then
          ε * Real.exp ((κ' + α - κ) * Y'.1.card) else 0) := Finset.sum_comm
      _ ≤ ∑ b ∈ Y.1, α := Finset.sum_le_sum (fun b _ => hent b)
      _ = α * Y.1.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring


include hdeg in
theorem lattice_entropy_W (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * Real.exp (-(κ - κ' - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α))) ≤ α)
    (b : B) :
    ∑ Y : BlockPolymer H, (if b ∈ Y.1 then latticeW H ε κ κ' Y * Real.exp (α * Y.1.card) else 0)
      ≤ α := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun Y _ => ?_))) (entropy_bound H hdeg hε hq hcond b)
  by_cases hb : b ∈ Y.1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_left_of_eq_true _ _ (eq_true hb),
      latticeW_mul_exp]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false hb)]

include hdeg in
/-- The polymer expansion for connected block sets: the abstract theorem for the lattice. -/
theorem pe_lattice (hε : 0 ≤ ε) (hκ' : 0 ≤ κ')
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * Real.exp (-(κ - κ' - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - κ' - α))) ≤ α)
    (K : BlockPolymer H → ℂ) (hK : ∀ X, ‖K X‖ ≤ ε * Real.exp (-κ * X.1.card)) :
    Xi (overlap H) K = Complex.exp (logSeries (overlap H) K) ∧
    logSeries (overlap H) K = ∑ Y : Finset B, PY (overlap H) (fun X => X.1) K Y ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (overlap H) (fun X => X.1) K Y‖ * Real.exp (κ' * (Y.card : ℝ)) ≤ α) ∧
    ‖logSeries (overlap H) K‖ ≤ Fintype.card B * α ∧
    Real.exp (-(Fintype.card B * α)) ≤ ‖Xi (overlap H) K‖ ∧
    ‖Xi (overlap H) K‖ ≤ Real.exp (Fintype.card B * α) := by
  have hKP := lattice_kp H hdeg hε hq hcond
  have hK' : ∀ X, ‖K X‖ ≤ latticeW H ε κ κ' X := fun X => by
    refine (hK X).trans ?_
    unfold latticeW
    calc ε * Real.exp (-κ * X.1.card) = ε * Real.exp (-κ * X.1.card) * 1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (by positivity)
  have hent := lattice_entropy_W H hdeg hε hq hcond
  have hw : ∀ b : B, ∑ Y : BlockPolymer H, (if b ∈ Y.1 then
      latticeW H ε κ κ' Y * Real.exp (α * Y.1.card) else 0) ≤ α := hent
  have hcover : ∀ Y : BlockPolymer H, ∃ b : B, b ∈ Y.1 := fun Y => Y.2.1
  have hL : ‖logSeries (overlap H) K‖ ≤ ∑ _b : B, α :=
    pe_logSeries_bound (overlap H) (fun (b : B) (Y : BlockPolymer H) => b ∈ Y.1) hcover hKP K hK'
      (fun _ => α) (fun b => by convert hw b using 3)
  have hnorm := pe_xi_norm_bounds (overlap H) (fun (b : B) (Y : BlockPolymer H) => b ∈ Y.1) hcover
    hKP (overlap_refl H) K hK' (fun _ => α) (fun b => by convert hw b using 3)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hL hnorm
  refine ⟨pe_xi_eq_exp (overlap H) hKP (overlap_refl H) K hK',
    logSeries_eq_sum_PY (overlap H) (fun X => X.1) hKP K hK', ?_, ?_, ?_, ?_⟩
  · intro b
    have := pe_PY_bound (overlap H) (fun X : BlockPolymer H => X.1) (fun Y : Finset B => κ' * (Y.card : ℝ)) 0
      le_rfl (fun Y => by positivity) ?_ (fun x => rfl) hKP K
      (fun x => hK x) b
    · exact this.trans (hw b |>.trans' (le_of_eq (Finset.sum_congr rfl (fun x _ => rfl))))
    · intro n X _
      have : (unionOf (fun X : BlockPolymer H => X.1) X).card ≤ ∑ i, (X i).1.card :=
        Finset.card_biUnion_le
      calc κ' * ((unionOf (fun X : BlockPolymer H => X.1) X).card : ℝ)
          ≤ κ' * ∑ i, ((X i).1.card : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ hκ'
            exact_mod_cast this
        _ = ∑ i, κ' * ((X i).1.card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ ∑ i, κ' * ((X i).1.card : ℝ) + 0 * n := by simp
  · exact hL
  · exact hnorm.1
  · exact hnorm.2

end Expansion

end Blocks

end Balaban.Polymer
