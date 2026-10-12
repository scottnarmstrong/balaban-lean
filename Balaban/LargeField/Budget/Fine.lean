module

public import Balaban.LargeField.Budget.Counts
public import Balaban.LargeField.History.LocalRegion

/-!
# Fine sets of cube sets: counts and extraction (for Lemma II.5.15)

The localized history records its sets as fine sets (preimages under `cubeMap`).  Here:

* `card_fineSet`: the fine set of `A ⊆ 𝕋_j` has `(L^j M)^d |A|` sites;
* `fineSet_injective`: `A` is recovered from its fine set (`cubeMap` is onto);
* `localHistory_Z`, `localHistory_P`: the records of the localized history of a component;
* `localHistory_congr`: the localized history only depends on the component and on the steps of
  its lineage localization.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Counts

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] [NeZero S.L] {M K : ℕ} [NeZero M]

/-- The number of sites of the fine torus over a set of `A` cubes of `𝕋_j` is `(L^j M)^d |A|`. -/
theorem card_fineSet (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K)
    (A : Finset (Torus S.d (n j))) :
    (RegionHistory.fineSet (S := S) (n := n) M K j (A : Set (Torus S.d (n j)))).ncard =
      (S.L ^ j * M) ^ S.d * A.card := by
  classical
  have hℓ : M * n K * S.L ^ K = S.L ^ j * M * n j := fine_eq hnn hjK
  have h := card_preimage_blockMap (d := S.d) (ℓ := M * n K * S.L ^ K) (N := S.L ^ j * M)
    (m := n j) hℓ A
  have e : RegionHistory.fineSet (S := S) (n := n) M K j (A : Set (Torus S.d (n j))) =
      ↑(Finset.univ.filter fun x : Torus S.d (M * n K * S.L ^ K) =>
        blockMap (S.L ^ j * M) (n j) x ∈ A) := by
    ext x
    simp [RegionHistory.fineSet, cubeMap]
  rw [e, Set.ncard_coe_finset, h]

/-- `cubeMap` is onto. -/
theorem cubeMap_surjective (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K)
    (x : Torus S.d (n j)) : ∃ y : Torus S.d (M * n K * S.L ^ K), cubeMap n S.L M K j y = x := by
  classical
  have hℓ : M * n K * S.L ^ K = S.L ^ j * M * n j := fine_eq hnn hjK
  have h := card_blockFibre (d := S.d) (ℓ := M * n K * S.L ^ K) (N := S.L ^ j * M) (m := n j) hℓ x
  have hpos : 0 < (S.L ^ j * M) ^ S.d := by
    have := NeZero.pos S.L
    have := NeZero.pos M
    positivity
  rw [← h] at hpos
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  exact ⟨y, mem_blockFibre.mp hy⟩

/-- A set of cubes is determined by its fine set. -/
theorem fineSet_injective (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j ≤ K)
    {A B : Set (Torus S.d (n j))}
    (h : RegionHistory.fineSet (S := S) (n := n) M K j A =
      RegionHistory.fineSet (S := S) (n := n) M K j B) : A = B := by
  ext x
  obtain ⟨y, rfl⟩ := cubeMap_surjective (S := S) (n := n) (M := M) (K := K) hnn hjK x
  have := Set.ext_iff.mp h y
  exact this

end Counts

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {M k : ℕ} [NeZero M]

theorem fine_lin_subset {j : ℕ} (hkK : k ≤ K) (Z : H.Comp k) :
    fineSet (S := S) (n := n) M K j ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) ⊆
      fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k))) := by
  have := H.neZero_L
  intro x hx
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  exact cubeMap_mem_of_desc H.F.hnn hkK hd hxY

/-- The `Z`-records of the localized history: the fine lineage. -/
theorem localHistory_Z (Z : H.Comp k) (hkK : k ≤ K) {j : ℕ} (hj : j ≤ k) :
    (localHistory H M K k Z).Z j =
      fineSet (S := S) (n := n) M K j ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) := by
  show fineSet M K j ((H.locRH k Z).step j).Z ∩ fineSet M K k Z.1 = _
  rw [locRH_Z Z hj (hj.trans hkK)]
  exact Set.inter_eq_left.mpr (fine_lin_subset hkK Z)

/-- The `P`-, `Q`-, `R`-, `S`-records of the localized history at a scale `j < k`: the fine
new cubes in the lineage. -/
theorem localHistory_new (Z : H.Comp k) (hkK : k ≤ K) {j : ℕ} (hj : j < k) :
    (localHistory H M K k Z).P j = fineSet (S := S) (n := n) M K (j + 1)
        ((H.step j).P ∩ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) ∧
    (localHistory H M K k Z).Q j = fineSet (S := S) (n := n) M K (j + 1)
        ((H.step j).Q ∩ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) ∧
    (localHistory H M K k Z).R j = fineSet (S := S) (n := n) M K (j + 1)
        ((H.step j).R ∩ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) ∧
    (localHistory H M K k Z).Sset j = fineSet (S := S) (n := n) M K (j + 1)
        ((H.step j).S ∩ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) := by
  obtain ⟨hP, hQ, hR, hS⟩ := locRH_new Z hj (by omega)
  have hsub : ∀ (X : Set (Torus S.d (n (j + 1)))),
      fineSet (S := S) (n := n) M K (j + 1)
        (X ∩ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) ∩
        fineSet M K k Z.1 =
      fineSet (S := S) (n := n) M K (j + 1)
        (X ∩ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _)) := by
    intro X
    refine Set.inter_eq_left.mpr (fun x hx => fine_lin_subset (j := j + 1) hkK Z ?_)
    exact hx.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show fineSet M K (j + 1) ((H.locRH k Z).step j).P ∩ fineSet M K k Z.1 = _
    rw [hP]; exact hsub _
  · show fineSet M K (j + 1) ((H.locRH k Z).step j).Q ∩ fineSet M K k Z.1 = _
    rw [hQ]; exact hsub _
  · show fineSet M K (j + 1) ((H.locRH k Z).step j).R ∩ fineSet M K k Z.1 = _
    rw [hR]; exact hsub _
  · show fineSet M K (j + 1) ((H.locRH k Z).step j).S ∩ fineSet M K k Z.1 = _
    rw [hS]; exact hsub _

/-- The number of sites of the `Z_j`-record of the localized history of `Z`. -/
theorem ncard_localHistory_Z (Z : H.Comp k) (hkK : k ≤ K) {j : ℕ} (hj : j ≤ k) :
    ((localHistory H M K k Z).Z j).ncard = (S.L ^ j * M) ^ S.d * (H.lin j k Z).card := by
  have := H.neZero_L
  rw [localHistory_Z Z hkK hj]
  exact card_fineSet H.F.hnn (hj.trans hkK) _

end RegionHistory

end Balaban.LargeField
