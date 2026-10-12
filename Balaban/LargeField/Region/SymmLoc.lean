module

public import Balaban.LargeField.Region.SymmZpre
public import Balaban.LargeField.History.LocalRegion
public import Balaban.LargeField.Budget.Fine
public import Balaban.LargeField.Operators.QuietEuclidDom

/-!
# The lineage localization is covariant

If a lattice symmetry `σ` maps the region history `H` to `H'` (`RegionIso`) and the lineages of the
components `Z`, `Z'` correspond (`Lin_j(Z') = σ Lin_j(Z)`, `j ≤ k`), then it maps the lineage
localization `locRH k Z` of `H` to that of `H'` (`RegionIso.locRH`).  The lineage correspondence
follows from the correspondence of the localized histories (`lin_image_of_histImage`).  The steps
beyond the scale `k` of the localization are the steps without new cubes, whose regions are the
hull closures of thickened lineages: their covariance is the covariance of the hull closure
(`SymmHull.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
  (hglob : RegionIso σ H H') {k : ℕ} {Z : H.Comp k} {Z' : H'.Comp k}
  (hlin : ∀ j, j ≤ k → ((H'.lin j k Z' : Finset (Torus S.d (n j))) : Set _) =
    σ.ec j '' ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _))

include hglob hlin

theorem tailZ_image : ∀ j, j ≤ K → H'.tailZ k Z' j = σ.ec j '' H.tailZ k Z j := by
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
        (fun x => (σ.ec_blockMap hnn hj x).symm) hL (ih (by omega)) ?_ ?_ ?_ ?_ _ _ <;> simp [emptyStep]


omit hglob hlin in
theorem locRH_step_empty {H : RegionHistory S n R k0 K} {k : ℕ} (Z : H.Comp k) {j : ℕ}
    (hj : ¬ (j < k ∧ j < K)) :
    (H.locRH k Z).step j = emptyStep S n R j (H.tailZ k Z j) := by
  show H.locStep k Z j = _
  unfold locStep
  exact ite_eq_right_of_eq_false _ _ (eq_false hj)

/-- The lineage localization is covariant. -/
theorem RegionIso.locRH : RegionIso σ (H.locRH k Z) (H'.locRH k Z') := by
  have hnn := H.F.hnn
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · show (H'.locStep k Z' j).Z = _ '' (H.locStep k Z j).Z
    rw [locStep_Z, locStep_Z]
    exact tailZ_image σ hglob hlin j hj
  all_goals
    by_cases hc : j < k ∧ j < K
    · obtain ⟨hP, hQ, hR, hS⟩ := locRH_new Z hc.1 hc.2
      obtain ⟨hP', hQ', hR', hS'⟩ := locRH_new Z' hc.1 hc.2
      have hl := hlin (j + 1) (by omega)
      first
      | (rw [hP', hP, hl, hglob.hP j hj, Set.image_inter (σ.ec (j + 1)).injective])
      | (rw [hQ', hQ, hl, hglob.hQ j hj, Set.image_inter (σ.ec (j + 1)).injective])
      | (rw [hR', hR, hl, hglob.hR j hj, Set.image_inter (σ.ec (j + 1)).injective])
      | (rw [hS', hS, hl, hglob.hS j hj, Set.image_inter (σ.ec (j + 1)).injective])
    · rw [locRH_step_empty Z hc, locRH_step_empty Z' hc]
      simp [emptyStep]


omit hglob hlin in
/-- The lineages of corresponding components correspond, as soon as the localized histories do. -/
theorem lin_image_of_histImage {H H' : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k}
    {Z' : H'.Comp k} (hkK : k ≤ K)
    (hI : HistImage σ.toTorusSym (H.localHistory M K k Z) (H'.localHistory M K k Z')) :
    ∀ j, j ≤ k → ((H'.lin j k Z' : Finset (Torus S.d (n j))) : Set _) =
      σ.ec j '' ((H.lin j k Z : Finset (Torus S.d (n j))) : Set _) := by
  intro j hj
  have h := hI.Z j
  rw [localHistory_Z Z hkK hj, localHistory_Z Z' hkK hj, σ.toTorusSym.fineSet_image (hj.trans hkK)] at h
  exact fineSet_injective H.F.hnn (hj.trans hkK) h

end Balaban.LargeField
