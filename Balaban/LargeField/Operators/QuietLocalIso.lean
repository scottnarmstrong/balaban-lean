module

public import Balaban.LargeField.Operators.QuietEuclidHist
public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.Budget.Fine

/-!
# Local region isomorphism from the localized histories

A lattice symmetry `σ` that maps the localized history of a component `Z` of `H` to that of a
component `Z'` of `H'` (`HistImage`) maps the lineage localization `H.locRH k Z` to
`H'.locRH k Z'` (`regionIso_of_histImage`): the lineage regions and the new cubes of the
localization are recovered from the fine records by injectivity of `fineSet`.  This replaces the
global `RegionIso` in the covariance of the quiet kernel.  Also: quietness of a step is invariant
(`isQuiet_of_histImage`), and the step `0 → 1` is never quiet (`not_isQuiet_zero`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
  {k : ℕ} {Z : H.Comp k} {Z' : H'.Comp k}

theorem tailZ_image_of_lin
    (hlin : ∀ j, j ≤ k → ((H'.lin j k Z' : Finset (Torus S.d (n j))) : Set _) =
      σ.ec j '' ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _)) :
    ∀ j, j ≤ K → H'.tailZ k Z' j = σ.ec j '' H.tailZ k Z j := by
  intro j
  induction j with
  | zero => intro _; simp [tailZ]
  | succ j ih =>
    intro hj
    have hL : 0 < S.L := NeZero.pos S.L
    have hnn := H.F.hnn
    by_cases hc : j + 1 ≤ k ∧ j + 1 ≤ K
    · simp only [tailZ, hc, and_self, ↓reduceIte]
      exact hlin (j + 1) hc.1
    · simp only [tailZ, hc, ↓reduceIte]
      refine RegionStep.image_Zpre (σ.isAff_ec hnn (by omega)) (σ.isAff_ec hnn hj)
        (fun x => (σ.ec_blockMap hnn hj x).symm) hL (ih (by omega)) ?_ ?_ ?_ ?_ _ _ <;>
        simp [emptyStep]

/-- A record of the localization is determined by its fine set. -/
theorem record_image (hkK : k ≤ K) {j : ℕ} (hj : j + 1 ≤ K)
    {X X' : Set (Torus S.d (n (j + 1)))}
    (hX : X ⊆ ((H.lin (j + 1) k Z : Finset (Torus S.d (n (j + 1)))) : Set _))
    (hX' : X' ⊆ ((H'.lin (j + 1) k Z' : Finset (Torus S.d (n (j + 1)))) : Set _))
    (h : fineSet (S := S) (n := n) M K (j + 1) X' ∩ fineSet M K k Z'.1 =
      σ.ef '' (fineSet (S := S) (n := n) M K (j + 1) X ∩ fineSet M K k Z.1)) :
    X' = σ.ec (j + 1) '' X := by
  have h1 : fineSet (S := S) (n := n) M K (j + 1) X ⊆ fineSet M K k Z.1 := fun x hx =>
    fine_lin_subset (j := j + 1) hkK Z (hX hx)
  have h2 : fineSet (S := S) (n := n) M K (j + 1) X' ⊆ fineSet M K k Z'.1 := fun x hx =>
    fine_lin_subset (j := j + 1) hkK Z' (hX' hx)
  rw [Set.inter_eq_left.mpr h1, Set.inter_eq_left.mpr h2, σ.fineSet_image hj] at h
  exact fineSet_injective (M := M) H.F.hnn hj h

/-- **The localized histories determine the local region isomorphism**: a lattice symmetry
mapping the localized history of `Z` to that of `Z'` maps the lineage localization of `Z` to that
of `Z'`. -/
theorem regionIso_of_histImage (hkK : k ≤ K)
    (hI : HistImage σ.toTorusSym (H.localHistory M K k Z) (H'.localHistory M K k Z')) :
    RegionIso σ (H.locRH k Z) (H'.locRH k Z') := by
  have hlin := lin_image_of_histImage σ hkK hI
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · show (H'.locStep k Z' j).Z = _ '' (H.locStep k Z j).Z
    rw [locStep_Z, locStep_Z]
    exact tailZ_image_of_lin σ hlin j hj
  · by_cases hc : j < k ∧ j < K
    · exact record_image σ hkK hj
        (by rw [(locRH_new Z hc.1 hc.2).1]; exact Set.inter_subset_right)
        (by rw [(locRH_new Z' hc.1 hc.2).1]; exact Set.inter_subset_right) (hI.P j)
    · rw [locRH_step_empty Z hc, locRH_step_empty Z' hc]
      simp [emptyStep]
  · by_cases hc : j < k ∧ j < K
    · exact record_image σ hkK hj
        (by rw [(locRH_new Z hc.1 hc.2).2.1]; exact Set.inter_subset_right)
        (by rw [(locRH_new Z' hc.1 hc.2).2.1]; exact Set.inter_subset_right) (hI.Q j)
    · rw [locRH_step_empty Z hc, locRH_step_empty Z' hc]
      simp [emptyStep]
  · by_cases hc : j < k ∧ j < K
    · exact record_image σ hkK hj
        (by rw [(locRH_new Z hc.1 hc.2).2.2.1]; exact Set.inter_subset_right)
        (by rw [(locRH_new Z' hc.1 hc.2).2.2.1]; exact Set.inter_subset_right) (hI.R j)
    · rw [locRH_step_empty Z hc, locRH_step_empty Z' hc]
      simp [emptyStep]
  · by_cases hc : j < k ∧ j < K
    · exact record_image σ hkK hj
        (by rw [(locRH_new Z hc.1 hc.2).2.2.2]; exact Set.inter_subset_right)
        (by rw [(locRH_new Z' hc.1 hc.2).2.2.2]; exact Set.inter_subset_right) (hI.Sset j)
    · rw [locRH_step_empty Z hc, locRH_step_empty Z' hc]
      simp [emptyStep]

/-- Quietness is invariant under a region isomorphism that maps the component. -/
theorem isQuiet_of_regionIso {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl')
    {k : ℕ} (hk : k + 1 ≤ K) {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
    (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set _))
    (hq : IsQuiet Hl k Zc) : IsQuiet Hl' k Zc' := by
  unfold IsQuiet at *
  rw [Finset.eq_empty_iff_forall_notMem] at *
  intro y hy
  rw [Finset.mem_inter] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hy1' : y ∈ (Zc' : Set _) := hy1
  rw [hZ] at hy1'
  obtain ⟨y0, hy0, rfl⟩ := hy1'
  refine hq y0 (Finset.mem_inter.mpr ⟨hy0, ?_⟩)
  have h2 : σ.ec (k + 1) y0 ∈ (Hl'.step k).newCubes := by
    have := (mem_finOf (X := (Hl'.step k).newCubes)).mp hy2
    exact this
  have e : (Hl'.step k).newCubes = σ.ec (k + 1) '' (Hl.step k).newCubes := by
    show (Hl'.step k).P ∪ (Hl'.step k).Q ∪ (Hl'.step k).R ∪ (Hl'.step k).S = _
    rw [hiso.hP k hk, hiso.hQ k hk, hiso.hR k hk, hiso.hS k hk]
    show _ = σ.ec (k + 1) '' ((Hl.step k).P ∪ (Hl.step k).Q ∪ (Hl.step k).R ∪ (Hl.step k).S)
    simp only [Set.image_union]
  rw [e] at h2
  exact (mem_finOf (X := (Hl.step k).newCubes)).mpr ((σ.ec (k + 1)).injective.mem_set_image.mp h2)

/-- **The step `0 → 1` is never quiet**: every component of `Z^pre_1` contains a new cube
(Lemma II.7.2 (c)). -/
theorem not_isQuiet_zero (H : RegionHistory S n R k0 K) (hK : 1 ≤ K) (Z' : H.Comp 1) :
    ¬ IsQuiet (H.locRH 1 Z') 0 Z'.1 := by
  intro hq
  let Zl : (H.locRH 1 Z').Comp 1 := ⟨Z'.1, locComp_mem H hK Z'⟩
  have h := (H.locRH 1 Z').seed_pos (k := 0) (by omega) Zl
  have h0 : ((H.locRH 1 Z').parts 0 Zl).card = 0 := by
    rw [Finset.card_eq_zero]
    ext c
    exact (((H.locRH 1 Z').F.isEmpty_comp_zero).false c).elim
  have h1 : (Zl.1 ∩ (H.locRH 1 Z').newCubes (0 + 1)).card = 0 := by
    have : Zl.1 ∩ (H.locRH 1 Z').newCubes (0 + 1) = ∅ := hq
    rw [this]; rfl
  omega

end Balaban.LargeField
