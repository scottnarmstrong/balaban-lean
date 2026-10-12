module

public import Balaban.LargeField.Budget.Injective

/-!
# From the localized history of a component to the data of its first level (Lemma II.5.15)

`Budget/Injective.lean` shows that the first-level data (the cubes of `Z_k` over `Z'`, the new
cubes in `Z'`, the localized histories of the old parts) determine the localized history of `Z'`.
Here we prove the converse, `record_forward`: the localized history of a component `Z'` of
`Z^pre_{k+1}` determines `Z'`, the cubes of `Z_k` over it, the new cubes in `Z'` and the localized
histories of its old parts.  This is what makes the bookkeeping of a component a function of its
localized history (`Budget/CanonicalBook.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {M K : ℕ} [NeZero M]

/-- The lineages at every scale `j ≤ k` are determined by the localized history. -/
theorem lin_eq_of_localHistory_eq {H1 H2 : RegionHistory S n R k0 K} {k : ℕ} (hkK : k ≤ K)
    (Z1 : H1.Comp k) (Z2 : H2.Comp k)
    (h : localHistory H1 M K k Z1 = localHistory H2 M K k Z2) {j : ℕ} (hj : j ≤ k) :
    H1.lin j k Z1 = H2.lin j k Z2 := by
  have := H1.neZero_L
  have h1 := congrFun (congrArg LocalHistory.Z h) j
  rw [localHistory_Z Z1 hkK hj, localHistory_Z Z2 hkK hj] at h1
  have h2 := fineSet_injective (S := S) (n := n) (M := M) (K := K) H1.F.hnn (hj.trans hkK) h1
  exact_mod_cast h2

/-- The new cubes of the lineage at a scale `j < k` are determined by the localized history. -/
theorem new_eq_of_localHistory_eq {H1 H2 : RegionHistory S n R k0 K} {k : ℕ} (hkK : k ≤ K)
    (Z1 : H1.Comp k) (Z2 : H2.Comp k)
    (h : localHistory H1 M K k Z1 = localHistory H2 M K k Z2) {j : ℕ} (hj : j < k) :
    (H1.step j).P ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).P ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _) ∧
    (H1.step j).Q ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).Q ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _) ∧
    (H1.step j).R ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).R ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _) ∧
    (H1.step j).S ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).S ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _) := by
  have := H1.neZero_L
  obtain ⟨a1, a2, a3, a4⟩ := localHistory_new (H := H1) (M := M) (K := K) Z1 hkK hj
  obtain ⟨b1, b2, b3, b4⟩ := localHistory_new (H := H2) (M := M) (K := K) Z2 hkK hj
  have hj1 : j + 1 ≤ K := by omega
  have hnn := H1.F.hnn
  have e1 := congrFun (congrArg LocalHistory.P h) j
  have e2 := congrFun (congrArg LocalHistory.Q h) j
  have e3 := congrFun (congrArg LocalHistory.R h) j
  have e4 := congrFun (congrArg LocalHistory.Sset h) j
  rw [a1, b1] at e1
  rw [a2, b2] at e2
  rw [a3, b3] at e3
  rw [a4, b4] at e4
  exact ⟨fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn hj1 e1,
    fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn hj1 e2,
    fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn hj1 e3,
    fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn hj1 e4⟩

/-- The lineage of an old part `c` of `Z'` is the part of the lineage of `Z'` lying over `c`
(on fine sites). -/
theorem mem_fine_lin_part {H : RegionHistory S n R k0 K} {k : ℕ} (hkK : k + 1 ≤ K)
    {Z' : H.Comp (k + 1)} {c : H.Comp k} (hc : c ∈ H.parts k Z') {j : ℕ} (hj : j ≤ k)
    (x : Torus S.d (M * n K * S.L ^ K)) :
    x ∈ fineSet (S := S) (n := n) M K j ((H.lin j k c : Finset (Torus S.d (n j))) : Set _) ↔
      x ∈ fineSet (S := S) (n := n) M K j ((H.lin j (k + 1) Z' : Finset (Torus S.d (n j))) :
        Set _) ∧
      x ∈ fineSet (S := S) (n := n) M K k (c.1 : Set (Torus S.d (n k))) := by
  have hkK' : k ≤ K := by omega
  have := H.neZero_L
  simp only [fineSet, Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · intro hx
    refine ⟨?_, fine_lin_subset hkK' c hx⟩
    rw [H.lin_succ_decomp k hj Z']
    exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
  · rintro ⟨hx1, hx2⟩
    rw [H.lin_succ_decomp k hj Z'] at hx1
    obtain ⟨c', hc', hx'⟩ := Finset.mem_biUnion.mp hx1
    have h1 := fine_lin_subset (M := M) hkK' c' (Finset.mem_coe.mpr hx')
    have hcc : c' = c := Subtype.ext (comp_eq_of_mem c'.2 c.2 h1 hx2)
    subst hcc
    exact hx'

/-- The steps of the lineage localizations of two components agree if the lineages and the new
cubes in the lineages agree. -/
theorem locRH_step_congr {H1 H2 : RegionHistory S n R k0 K} {k : ℕ} (hkK : k ≤ K) (Z1 : H1.Comp k)
    (Z2 : H2.Comp k) (hZ : Z1.1 = Z2.1)
    (hlin : ∀ j, j ≤ k → H1.lin j k Z1 = H2.lin j k Z2)
    (hP : ∀ j, j < k → (H1.step j).P ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).P ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _))
    (hQ : ∀ j, j < k → (H1.step j).Q ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).Q ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _))
    (hR : ∀ j, j < k → (H1.step j).R ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).R ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _))
    (hS : ∀ j, j < k → (H1.step j).S ∩ ((H1.lin (j + 1) k Z1 : Finset _) : Set _) =
        (H2.step j).S ∩ ((H2.lin (j + 1) k Z2 : Finset _) : Set _)) :
    ∀ j, (H1.locRH k Z1).step j = (H2.locRH k Z2).step j := by
  intro j
  have hZf : ∀ j, H1.tailZ k Z1 j = H2.tailZ k Z2 j := by
    intro j
    by_cases hj : j ≤ k
    · rw [tailZ_eq_lin Z1 hj (by omega), tailZ_eq_lin Z2 hj (by omega), hlin j hj]
    · exact tailZ_congr Z1 Z2 hZ hkK (by omega)
  by_cases hj : j < k
  · have hZj : ((H1.locRH k Z1).step j).Z = ((H2.locRH k Z2).step j).Z := by
      show (H1.locStep k Z1 j).Z = (H2.locStep k Z2 j).Z
      rw [locStep_Z, locStep_Z, hZf]
    obtain ⟨p1, q1, r1, s1⟩ := locRH_new Z1 hj (by omega)
    obtain ⟨p2, q2, r2, s2⟩ := locRH_new Z2 hj (by omega)
    refine RegionStep.eq_of_fields hZj ?_ ?_ ?_ ?_
    · rw [p1, p2]; exact hP j hj
    · rw [q1, q2]; exact hQ j hj
    · rw [r1, r2]; exact hR j hj
    · rw [s1, s2]; exact hS j hj
  · have e1 : (H1.locRH k Z1).step j = emptyStep S n R j (H1.tailZ k Z1 j) := by
      show H1.locStep k Z1 j = _
      unfold locStep; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h => hj h.1))
    have e2 : (H2.locRH k Z2).step j = emptyStep S n R j (H2.tailZ k Z2 j) := by
      show H2.locStep k Z2 j = _
      unfold locStep; exact ite_eq_right_of_eq_false _ _ (eq_false (fun h => hj h.1))
    rw [e1, e2, hZf j]

/-- The first-level data of a localized history (the converse of `localHistory_succ_eq`): the
localized history of a component `Z'` of `Z^pre_{k+1}` determines `Z'`, the cubes of `Z_k` over
`Z'`, the new cubes in `Z'`, and the localized histories of the old parts. -/
theorem record_forward {H1 H2 : RegionHistory S n R k0 K} {k : ℕ} (hkK : k + 1 ≤ K)
    (Z1 : H1.Comp (k + 1)) (Z2 : H2.Comp (k + 1))
    (h : localHistory H1 M K (k + 1) Z1 = localHistory H2 M K (k + 1) Z2) :
    Z1.1 = Z2.1 ∧ H1.oldCubes k Z1 = H2.oldCubes k Z2 ∧
    Z1.1 ∩ H1.newCubes (k + 1) = Z2.1 ∩ H2.newCubes (k + 1) ∧
    ∀ Y (h1 : Y ∈ comps (S.omega k) (H1.Zp k)) (h2 : Y ∈ comps (S.omega k) (H2.Zp k)),
      Y ∈ comps (S.omega k) (H1.oldCubes k Z1) →
        localHistory H1 M K k ⟨Y, h1⟩ = localHistory H2 M K k ⟨Y, h2⟩ := by
  classical
  have := H1.neZero_L
  have hkK' : k ≤ K := by omega
  have hnn := H1.F.hnn
  have hlin := fun j (hj : j ≤ k + 1) => lin_eq_of_localHistory_eq hkK Z1 Z2 h hj
  have hZ : Z1.1 = Z2.1 := by
    have := hlin (k + 1) le_rfl
    rwa [lin_self, lin_self] at this
  have hold : H1.oldCubes k Z1 = H2.oldCubes k Z2 := by
    have := hlin k (Nat.le_succ k)
    rwa [lin_succ_self (H := H1) (by omega), lin_succ_self (H := H2) (by omega)] at this
  refine ⟨hZ, hold, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := new_eq_of_localHistory_eq hkK Z1 Z2 h (j := k) (Nat.lt_succ_self k)
    rw [lin_self, lin_self] at a1 a2 a3 a4
    ext x
    simp only [Finset.mem_inter, RegionHistory.newCubes, mem_finOf]
    constructor
    · rintro ⟨hx, hn⟩
      refine ⟨hZ ▸ hx, ?_⟩
      have hx2 : x ∈ (Z2.1 : Set (Torus S.d (n (k + 1)))) := by rw [← hZ]; exact hx
      rcases hn with ((hn | hn) | hn) | hn
      · exact Or.inl (Or.inl (Or.inl ((Set.ext_iff.mp a1 x).mp ⟨hn, hx⟩).1))
      · exact Or.inl (Or.inl (Or.inr ((Set.ext_iff.mp a2 x).mp ⟨hn, hx⟩).1))
      · exact Or.inl (Or.inr ((Set.ext_iff.mp a3 x).mp ⟨hn, hx⟩).1)
      · exact Or.inr ((Set.ext_iff.mp a4 x).mp ⟨hn, hx⟩).1
    · rintro ⟨hx, hn⟩
      have hx1 : x ∈ (Z1.1 : Set (Torus S.d (n (k + 1)))) := by rw [hZ]; exact hx
      refine ⟨hx1, ?_⟩
      rcases hn with ((hn | hn) | hn) | hn
      · exact Or.inl (Or.inl (Or.inl ((Set.ext_iff.mp a1 x).mpr ⟨hn, hx⟩).1))
      · exact Or.inl (Or.inl (Or.inr ((Set.ext_iff.mp a2 x).mpr ⟨hn, hx⟩).1))
      · exact Or.inl (Or.inr ((Set.ext_iff.mp a3 x).mpr ⟨hn, hx⟩).1)
      · exact Or.inr ((Set.ext_iff.mp a4 x).mpr ⟨hn, hx⟩).1
  · intro Y h1 h2 hY
    have hY2 : Y ∈ comps (S.omega k) (H2.oldCubes k Z2) := hold ▸ hY
    have hc1 : (⟨Y, h1⟩ : H1.Comp k) ∈ H1.parts k Z1 := by
      rw [← H1.parts_image_eq_comps (by omega)] at hY
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hY
      exact hc
    have hc2 : (⟨Y, h2⟩ : H2.Comp k) ∈ H2.parts k Z2 := by
      rw [← H2.parts_image_eq_comps (by omega)] at hY2
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hY2
      exact hc
    refine localHistory_congr (M := M) (K := K) ⟨Y, h1⟩ ⟨Y, h2⟩ rfl ?_
    -- the lineages of the part agree
    have hlinY : ∀ j, j ≤ k → H1.lin j k ⟨Y, h1⟩ = H2.lin j k ⟨Y, h2⟩ := by
      intro j hj
      have hfs : fineSet (S := S) (n := n) M K j ((H1.lin j k ⟨Y, h1⟩ : Finset _) : Set _) =
          fineSet (S := S) (n := n) M K j ((H2.lin j k ⟨Y, h2⟩ : Finset _) : Set _) := by
        ext x
        rw [mem_fine_lin_part hkK hc1 hj, mem_fine_lin_part hkK hc2 hj, hlin j (by omega)]
      have := fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn (hj.trans hkK') hfs
      exact_mod_cast this
    have hnewY : ∀ j, j < k → ∀ (X1 X2 : Set (Torus S.d (n (j + 1)))),
        X1 ∩ ((H1.lin (j + 1) (k + 1) Z1 : Finset _) : Set _) =
          X2 ∩ ((H2.lin (j + 1) (k + 1) Z2 : Finset _) : Set _) →
        X1 ∩ ((H1.lin (j + 1) k ⟨Y, h1⟩ : Finset _) : Set _) =
          X2 ∩ ((H2.lin (j + 1) k ⟨Y, h2⟩ : Finset _) : Set _) := by
      intro j hj X1 X2 hX
      have hfs : fineSet (S := S) (n := n) M K (j + 1)
          (X1 ∩ ((H1.lin (j + 1) k ⟨Y, h1⟩ : Finset _) : Set _)) =
          fineSet (S := S) (n := n) M K (j + 1)
          (X2 ∩ ((H2.lin (j + 1) k ⟨Y, h2⟩ : Finset _) : Set _)) := by
        have hX' : fineSet (S := S) (n := n) M K (j + 1)
            (X1 ∩ ((H1.lin (j + 1) (k + 1) Z1 : Finset _) : Set _)) =
            fineSet (S := S) (n := n) M K (j + 1)
            (X2 ∩ ((H2.lin (j + 1) (k + 1) Z2 : Finset _) : Set _)) := by rw [hX]
        ext x
        have hx := Set.ext_iff.mp hX' x
        have l1 := mem_fine_lin_part hkK hc1 (show j + 1 ≤ k by omega) x
        have l2 := mem_fine_lin_part hkK hc2 (show j + 1 ≤ k by omega) x
        simp only [fineSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe] at hx l1 l2 ⊢
        constructor
        · rintro ⟨ha, hb⟩
          have hb' := (l1.mp hb)
          obtain ⟨hx1, hx2⟩ := hx.mp ⟨ha, hb'.1⟩
          exact ⟨hx1, l2.mpr ⟨hx2, hb'.2⟩⟩
        · rintro ⟨ha, hb⟩
          have hb' := (l2.mp hb)
          obtain ⟨hx1, hx2⟩ := hx.mpr ⟨ha, hb'.1⟩
          exact ⟨hx1, l1.mpr ⟨hx2, hb'.2⟩⟩
      exact fineSet_injective (S := S) (n := n) (M := M) (K := K) hnn (by omega) hfs
    have hnew := fun j (hj : j < k) =>
      new_eq_of_localHistory_eq hkK Z1 Z2 h (j := j) (by omega)
    exact locRH_step_congr hkK' (⟨Y, h1⟩ : H1.Comp k) ⟨Y, h2⟩ rfl hlinY
      (fun j hj => hnewY j hj _ _ (hnew j hj).1)
      (fun j hj => hnewY j hj _ _ (hnew j hj).2.1)
      (fun j hj => hnewY j hj _ _ (hnew j hj).2.2.1)
      (fun j hj => hnewY j hj _ _ (hnew j hj).2.2.2)

end RegionHistory

end Balaban.LargeField
