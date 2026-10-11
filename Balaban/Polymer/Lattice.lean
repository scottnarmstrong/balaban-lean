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

end Blocks

end Balaban.Polymer
