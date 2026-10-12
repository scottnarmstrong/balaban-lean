module

public import Balaban.LargeField.History.FlowBook
public import Balaban.LargeField.History.RegionLineage

/-!
# Volume counts of a step (Part II, Definition II.5.11, Lemma II.5.12)

For a component `Z'` of `Z^pre_{k+1}` the `π_k`-cubes over `Z'` split into the cubes of
`Z_k` (`oldCubes`, `n₁ = |Z_k ∩ Z'|_{#k}`) and the cubes outside `Z_k` (`outCubes`,
`n₂ = |Z^c_k ∩ Z'|_{#k}`).

* `card_preimage_blockMap`: the preimage of a set of `m` blocks has `N^d m` sites;
* `card_oldCubes_add_outCubes`: `n₁ + n₂ = L^d |Z'|_#`;
* `sum_parts_card`: `∑_Y |Y|_# = n₁` over the old parts `Y` of `Z'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Preimage

variable {d ℓ m N : ℕ} [NeZero ℓ] [NeZero m]

/-- The preimage of a set of `a` blocks under the block map has `N^d a` sites. -/
theorem card_preimage_blockMap (hℓ : ℓ = N * m) (A : Finset (Torus d m)) :
    (Finset.univ.filter fun x : Torus d ℓ => blockMap N m x ∈ A).card = N ^ d * A.card := by
  classical
  have h : (Finset.univ.filter fun x : Torus d ℓ => blockMap N m x ∈ A) =
      A.biUnion fun y => blockFibre N m y := by
    ext x
    simp [mem_blockFibre]
  rw [h, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun y _ => card_blockFibre hℓ y)]
    simp [mul_comm]
  · intro y _ y' _ hne
    show Disjoint (blockFibre N m y : Finset (Torus d ℓ)) (blockFibre N m y')
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_blockFibre] at hx hx'
    exact hne (hx.symm.trans hx')

end Preimage

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

open Classical in
/-- The `π_k`-cubes of `Z_k` over the component `Z'` of `Z^pre_{k+1}`:
`Z_k ∩ Z'`. -/
noncomputable def oldCubes (k : ℕ) (Z' : H.Comp (k + 1)) : Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun x => x ∈ (H.step k).Z ∧ blockMap S.L (n (k + 1)) x ∈ Z'.1

open Classical in
/-- The `π_k`-cubes outside `Z_k` over the component `Z'`: `Z^c_k ∩ Z'`. -/
noncomputable def outCubes (k : ℕ) (Z' : H.Comp (k + 1)) : Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun x => x ∉ (H.step k).Z ∧ blockMap S.L (n (k + 1)) x ∈ Z'.1

theorem card_oldCubes_add_outCubes (k : ℕ) (Z' : H.Comp (k + 1)) :
    (H.oldCubes k Z').card + (H.outCubes k Z').card = S.L ^ S.d * Z'.1.card := by
  classical
  have hℓ : n k = S.L * n (k + 1) := H.F.hnn k
  rw [← card_preimage_blockMap hℓ Z'.1, ← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [oldCubes, outCubes, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [oldCubes, outCubes, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hx'.1 hx.1

theorem oldCubes_eq (k : ℕ) (Z' : H.Comp (k + 1)) :
    H.oldCubes k Z' = (H.parts k Z').biUnion fun c => c.1 := by
  classical
  ext x
  simp only [oldCubes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · rintro ⟨hx, hy⟩
    have hzp : x ∈ H.F.Zpre k := H.Z_subset_Zpre k hx
    obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega k) (mem_finOf.mpr hzp)
    have hrem : Y ∉ H.rem k := (H.mem_Z_iff (Y := ⟨Y, hY⟩) hxY).mp hx
    have hs := H.succ_spec k (c := ⟨Y, hY⟩) hrem ⟨x, hxY, rfl⟩
    have heq : H.succ k ⟨Y, hY⟩ hrem = Z' :=
      Subtype.ext (comp_eq_of_mem (H.succ k ⟨Y, hY⟩ hrem).2 Z'.2 hs hy)
    exact ⟨⟨Y, hY⟩, (H.mem_parts k _ Z').mpr ⟨hrem, heq⟩, hxY⟩
  · rintro ⟨c, hc, hxc⟩
    obtain ⟨hrem, hs⟩ := (H.mem_parts k c Z').mp hc
    refine ⟨(H.mem_Z_iff hxc).mpr hrem, ?_⟩
    have := H.succ_spec k hrem ⟨x, hxc, rfl⟩
    rw [hs] at this
    exact this

theorem sum_parts_card (k : ℕ) (Z' : H.Comp (k + 1)) :
    ∑ c ∈ H.parts k Z', c.1.card = (H.oldCubes k Z').card := by
  rw [H.oldCubes_eq, Finset.card_biUnion]
  intro c hc c' hc' hne
  show Disjoint c.1 c'.1
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact hne (Subtype.ext (comp_eq_of_mem c.2 c'.2 hx hx'))

end RegionHistory

end Balaban.LargeField
