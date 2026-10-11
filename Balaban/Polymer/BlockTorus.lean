module

public import Balaban.Polymer.Lattice
public import Balaban.Frozen.Model.Torus

/-!
# The block torus

The nearest-neighbour graph on the torus of blocks `(ℤ/mℤ)^d` has degree at most `2 d`, also when
`m < 3` (where neighbours may coincide).  `pe_blockTorus` is the polymer expansion for polymers
= nearest-neighbour connected sets of blocks (`pe_lattice` with `Δ = 2 d`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable (d m : ℕ)

/-- The nearest-neighbour graph on the torus of blocks. -/
def blockGraph : SimpleGraph (Balaban.Torus d m) where
  Adj a b := a ≠ b ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨μ, hμ⟩ := h.2
    exact ⟨μ, hμ.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable [NeZero m]

theorem blockGraph_degree_le (a : Balaban.Torus d m) : (blockGraph d m).degree a ≤ 2 * d := by
  classical
  have hsub : (blockGraph d m).neighborFinset a ⊆
      (Finset.univ : Finset (Fin d × Bool)).image
        (fun p => a + (if p.2 then Pi.single p.1 1 else -Pi.single p.1 1)) := by
    intro b hb
    rw [SimpleGraph.mem_neighborFinset] at hb
    obtain ⟨_, μ, hμ | hμ⟩ := hb
    · exact Finset.mem_image.mpr ⟨(μ, true), Finset.mem_univ _, by simp [hμ]⟩
    · refine Finset.mem_image.mpr ⟨(μ, false), Finset.mem_univ _, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [hμ, add_neg_cancel_right]
  calc (blockGraph d m).degree a = ((blockGraph d m).neighborFinset a).card :=
        (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [mul_comm]

/-- The polymer expansion on the block torus: polymers are the nonempty nearest-neighbour
connected sets of blocks, of size `|X|` (number of blocks), incompatible iff they share a block. -/
theorem pe_blockTorus {ε κ κ' α : ℝ} (hε : 0 ≤ ε) (hκ' : 0 ≤ κ')
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * Real.exp (-(κ - κ' - α)) /
      (1 - ((2 * d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - κ' - α))) ≤ α)
    (K : BlockPolymer (blockGraph d m) → ℂ)
    (hK : ∀ X, ‖K X‖ ≤ ε * Real.exp (-κ * X.1.card)) :
    Xi (overlap (blockGraph d m)) K = Complex.exp (logSeries (overlap (blockGraph d m)) K) ∧
    logSeries (overlap (blockGraph d m)) K =
      ∑ Y : Finset (Balaban.Torus d m),
        PY (overlap (blockGraph d m)) (fun X => X.1) K Y ∧
    (∀ b : Balaban.Torus d m,
      ∑ Y ∈ (Finset.univ : Finset (Finset (Balaban.Torus d m))).filter (fun Y => b ∈ Y),
        ‖PY (overlap (blockGraph d m)) (fun X => X.1) K Y‖ * Real.exp (κ' * (Y.card : ℝ)) ≤ α) ∧
    ‖logSeries (overlap (blockGraph d m)) K‖ ≤ Fintype.card (Balaban.Torus d m) * α :=
  by
  have := pe_lattice (blockGraph d m) (Δ := 2 * d) (blockGraph_degree_le d m) hε hκ' hq hcond K hK
  refine ⟨this.1, this.2.1, fun b => ?_, this.2.2.2.1⟩
  convert this.2.2.1 b using 2
  ext Y
  simp

end Balaban.Polymer
