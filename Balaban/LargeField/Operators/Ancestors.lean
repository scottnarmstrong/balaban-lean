module

public import Balaban.LargeField.Operators.Variables

/-!
# Ancestors' variables inside the variables of a component (Part II, (II.3))

For a component `Z'` of `Z^pre_{k+1}` and an old part `Y ∈ Anc_k(Z')` (`RegionHistory.parts`) the
internal variables of `Y` (scales `j < k`) are internal variables of `Z'`:
`I(Y, 𝔞|_Y) ⊆ I(Z', 𝔞)` (the inclusion `ancInc`).  The proof compares the localized histories along
the lineage: the lineage of `Y` at scale `j + 1` is contained in that of `Z'`
(`lin_mono`), the localized records of `Y` and `Z'` at a cube of the lineage of `Y` are the
global ones (`mem_locOmega_iff`), and the fine set of `Y` lies in that of `Z'` (`fineSet_desc_sub`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- The lineage of an old part is contained in that of the component it joins. -/
theorem lin_mono {k : ℕ} {Y : H.Comp k} {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z') {a : ℕ} :
    ((H.lin a k Y : Finset (Torus S.d (n a))) : Set (Torus S.d (n a))) ⊆
      ((H.lin a (k + 1) Z' : Finset (Torus S.d (n a))) : Set (Torus S.d (n a))) := by
  intro x hx
  obtain ⟨Y', hd, hxY'⟩ := mem_lin.mp (Finset.mem_coe.mp hx)
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y', hd.trans (Desc.single hrem hs), hxY'⟩)

/-- The fine set of a descendant contains that of its ancestor. -/
theorem fineSet_desc_sub [NeZero S.L] {M a b : ℕ} [NeZero M] (hbK : b ≤ K) {Y : H.Comp a}
    {Z : H.Comp b} (h : H.Desc a b Y Z) :
    fineSet (S := S) (n := n) M K a Y.1 ⊆ fineSet (S := S) (n := n) M K b Z.1 := fun _ hx =>
  cubeMap_mem_of_desc H.F.hnn hbK h hx

/-- At a cube of the lineage of `Z`, the localized `Ω_{j+1}` is the global one (`j < k`). -/
theorem mem_locOmega_iff {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j < k) (hjK : j < K)
    {y : Torus S.d (n (j + 1))} (hy : y ∈ ((H.lin (j + 1) k Z : Finset _) : Set _)) :
    (y ∈ ((H.locRH k Z).step j).Omega ↔ y ∈ (H.step j).Omega) ∧
    (y ∈ ((H.locRH k Z).step j).OmegaDD ↔ y ∈ (H.step j).OmegaDD) := by
  obtain ⟨-, h2, h3, -⟩ := locRH_derived Z hj hjK
  constructor
  · have := congrArg (fun T : Set (Torus S.d (n (j + 1))) => y ∈ T) h2
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, hy, and_true, eq_iff_iff] at this
    exact (not_iff_not.mp this).symm
  · have := congrArg (fun T : Set (Torus S.d (n (j + 1))) => y ∈ T) h3
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, hy, and_true, eq_iff_iff] at this
    exact (not_iff_not.mp this).symm

/-- A cube outside the localized `Ω''_{j+1}` lies in the lineage. -/
theorem mem_lin_of_not_mem_locOmegaDD {k : ℕ} (Z : H.Comp k) {j : ℕ} (hj : j < k) (hjK : j < K)
    {y : Torus S.d (n (j + 1))} (hy : y ∉ ((H.locRH k Z).step j).OmegaDD) :
    y ∈ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) :
      Set (Torus S.d (n (j + 1)))) := by
  obtain ⟨-, -, h3, -⟩ := locRH_derived Z hj hjK
  have : y ∈ ((H.locRH k Z).step j).OmegaDDᶜ := hy
  rw [← h3] at this
  exact this.2

/-- The variable sets of an old part are contained in those of the component it joins
(`j < k`), for both kinds of variables. -/
theorem varSet_mono [NeZero S.L] {M : ℕ} [NeZero M] {k : ℕ} (hK : k + 1 ≤ K) {Y : H.Comp k}
    {Z' : H.Comp (k + 1)} (hY : Y ∈ H.parts k Z') {j : ℕ} (hj : j < k) (κ : VarKind) :
    varSet (H.localHistory M K k Y) j κ ⊆ varSet (H.localHistory M K (k + 1) Z') j κ := by
  obtain ⟨hrem, hs⟩ := (H.mem_parts k Y Z').mp hY
  have hdesc : H.Desc k (k + 1) Y Z' := Desc.single hrem hs
  have hfine : fineSet (S := S) (n := n) M K k Y.1 ⊆ fineSet (S := S) (n := n) M K (k + 1) Z'.1 :=
    fineSet_desc_sub hK hdesc
  have hlinY : ∀ x : Torus S.d (M * n K * S.L ^ K),
      cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k Y).step (j + 1)).Z ↔
        cubeMap n S.L M K (j + 1) x ∈ ((H.lin (j + 1) k Y : Finset (Torus S.d (n (j + 1)))) :
          Set (Torus S.d (n (j + 1)))) := fun x => by rw [locRH_Z Y (show j + 1 ≤ k by omega) (by omega)]
  have hlinZ : ∀ x : Torus S.d (M * n K * S.L ^ K),
      cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (k + 1) Z').step (j + 1)).Z ↔
        cubeMap n S.L M K (j + 1) x ∈ ((H.lin (j + 1) (k + 1) Z' : Finset (Torus S.d (n (j + 1)))) :
          Set (Torus S.d (n (j + 1)))) := fun x => by
    rw [locRH_Z Z' (show j + 1 ≤ k + 1 by omega) (by omega)]
  intro x hx
  cases κ with
  | large =>
    obtain ⟨⟨hx1, hxY⟩, hx2⟩ := hx
    have hx1' := (hlinY x).mp hx1
    have hx1'' := lin_mono hY hx1'
    have hxZ' := hfine hxY
    refine ⟨⟨(hlinZ x).mpr hx1'', hxZ'⟩, fun ⟨hΩ, _⟩ => hx2 ⟨?_, hxY⟩⟩
    have h1 := (mem_locOmega_iff Z' (show j < k + 1 by omega) (by omega) hx1'').1.mp hΩ
    exact (mem_locOmega_iff Y hj (by omega) hx1').1.mpr h1
  | fluct =>
    obtain ⟨⟨hx1, hxY⟩, hx2⟩ := hx
    have hnot : cubeMap n S.L M K (j + 1) x ∉ ((H.locRH k Y).step j).OmegaDD :=
      fun h => hx2 ⟨h, hxY⟩
    have hc := mem_lin_of_not_mem_locOmegaDD Y hj (by omega) hnot
    have hc' := lin_mono hY hc
    have hxZ' := hfine hxY
    refine ⟨⟨?_, hxZ'⟩, fun ⟨hΩ, _⟩ => hx2 ⟨?_, hxY⟩⟩
    · exact (mem_locOmega_iff Z' (show j < k + 1 by omega) (by omega) hc').1.mpr
        ((mem_locOmega_iff Y hj (by omega) hc).1.mp hx1)
    · exact (mem_locOmega_iff Y hj (by omega) hc).2.mpr
        ((mem_locOmega_iff Z' (show j < k + 1 by omega) (by omega) hc').2.mp hΩ)

end RegionHistory

end Balaban.LargeField
