/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.D7FineSizeWitness
public import Balaban.LargeField.History.InhabitedRipeRemoval
public import Balaban.LargeField.R.D7BoundTransport

/-!
# Non-vacuity of `R/D7AvoidGeometry` and `R/D7BoundTransport`

* The history `labBdry` of `D7FineSizeWitness` (a large-field region, `Rem_1 = ∅`): every label
  avoids the removed set, `labBdry_removedSet`, and the size equality of `R/D7AvoidGeometry`
  is instantiated, `labBdry_size_eq`.  The record `repBdry` (a nonzero boundary term) satisfies the
  pre-`R` record `D7Bdry2` (`repBdry_d7Pre`), and `d7Post_bound_degenerate` is the two-case bound
  theorem for `rout = rin = repBdry` with all three hypotheses (`hyp_avoid`, `hyp_gas`,
  `hyp_split`) discharged: the first by `rfl`, the others vacuously because nothing is removed.
  This is only the degenerate instance (rate and constant weakening); there is no landed pair of
  physical records `(rin, rout)` of the operation `R`.
* The history `ripeRemHistory` (a ripe component removed at scale `T`): the removed set is
  nonempty and a cube `y` lies in `Ω_T^post` but not in `Ω_T^pre`, so the label `{y}` meets the
  removed set and `X ∩ Ω^post ≠ X ∩ Ω^pre` for it (`ripeRem_label_meets_removal`): the
  disjointness hypothesis of `inter_omegaPost_of_disjoint` cannot be dropped.  Whether a nonempty
  label avoiding the removed set exists in this history (the removed component is all of
  `Z^pre_T`, and the torus is larger) is not proved here.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.LargeField Balaban.Localization Balaban.LargeField.Def7.Wit Balaban.Inhabited
  Balaban.LargeField.Def7v2 RegionHistory

/-- No component is removed in `labBdry`, so the removed set is empty. -/
theorem labBdry_removedSet : labBdry.H.removedSet 1 = ∅ := by
  have h : labBdry.H.rem 1 = ∅ := rfl
  simp [RegionHistory.removedSet, h]

/-- Every label avoids the removed set of `labBdry`; hence the sizes agree
(`d7Size_eq_d7SizePre_of_disjoint`). -/
theorem labBdry_size_eq (X : Finset (Torus wS.d (sides wS.L 1 nBdry 1))) :
    d7Size (wFrame nBdry) labBdry 1 X = d7SizePre (wFrame nBdry) labBdry 1 X :=
  d7Size_eq_d7SizePre_of_disjoint _ _ X (by rw [labBdry_removedSet]; exact Set.disjoint_empty _)

/-- **`repBdry` satisfies the pre-`R` record `D7Bdry2`**, for every pinned radius, with the region
`Z^pre_1`. -/
theorem repBdry_d7Pre (ν : ℝ) (aw μs ε ε1 νs : ℕ → ℝ) {fac : ℝ} (rate : ℝ) (hfac : 0 < fac)
    (rH : ℝ) :
    D7Bdry2 (wFrame nBdry) (sides_hnn wS.L 1 nBdry) le_rfl (repBdry ν fac rate)
      (fun A => A.H.F.Zpre 1) aw μs ε ε1 νs fac rate whv rH where
  loc_field := by intros; rfl
  loc_hist := by intros; rfl
  real := by
    intro A _ X _ ψ ψ' h g _ _ _
    rw [repBdry_B]
    split_ifs <;> simp
  analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
  bound := by
    intro A hA X hX h _ p _
    obtain rfl : A = labBdry := Finset.mem_singleton.1 hA
    rw [repBdry_B]
    split_ifs with hXu
    · subst hXu
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cBdry_pos rate hfac),
        ← d7Size_eq_d7SizePre_of_rem_empty (A := labBdry) (k := 1) (wFrame nBdry) Finset.univ rfl]
      exact cBdry_lt rate hfac
    · rw [norm_zero]; positivity
  rot := by intros; rfl
  euclid := by
    intro A _ A' _ σ _ _ X _ ψ ψ' h g
    rw [repBdry_B, repBdry_B]
    have hiff : X.map (σ.ec 1).toEmbedding = Finset.univ ↔ X = Finset.univ := by
      constructor
      · intro hm
        refine Finset.eq_univ_iff_forall.2 fun y => ?_
        have hy : (σ.ec 1) y ∈ X.map (σ.ec 1).toEmbedding := by rw [hm]; exact Finset.mem_univ _
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.1 hy
        exact (σ.ec 1).injective hxy ▸ hx
      · rintro rfl
        exact Finset.map_univ_equiv _
    simp only [hiff]
  support := by
    intro A _ X _ hnv ψ ψ' h g
    rw [repBdry_B]
    split_ifs with hXu
    · exact absurd (hXu ▸ fineValidPre_univ (wFrame nBdry) A 1) hnv
    · rfl

/-- **The two-case bound theorem, degenerate instance** (`rout = rin = repBdry`, no removed
component): all three hypotheses of `d7Post_bound_of_avoid_of_gas` hold, so the theorem applies
to a record with a nonzero boundary term.  The constant of the input record is `Bst`, that of the
conclusion `B0 ≥ Bst`, the rate `3κ/2` is weakened to `κ`. -/
theorem d7Post_bound_degenerate (ν : ℝ) (aw μs ε ε1 νs : ℕ → ℝ) {κ Bst B0 : ℝ} (hκ : 0 ≤ κ)
    (hBst : 0 < Bst) (hBB : Bst ≤ B0) (rH : ℝ) :
    D7PostBound (wFrame nBdry) (sides_hnn wS.L 1 nBdry) le_rfl (repBdry ν Bst ((3 / 2) * κ))
      (fun A => (A.H.step 1).Z) aw μs ε ε1 νs B0 κ whv rH := by
  refine d7Post_bound_of_avoid_of_gas (rin := repBdry ν Bst ((3 / 2) * κ))
    (rout := repBdry ν Bst ((3 / 2) * κ)) (repBdry_d7Pre ν aw μs ε ε1 νs _ hBst rH) hκ hBB
    (hBst.trans_le hBB) id (fun A hA => ⟨hA, rfl, rfl, rfl⟩) (fun _ _ _ _ _ _ => rfl) ?_ ?_
  · intro A hA Y _ hnd
    obtain rfl : A = labBdry := Finset.mem_singleton.1 hA
    exact absurd (by rw [labBdry_removedSet]; exact Set.disjoint_empty _) hnd
  · intro A hA Y hY _ hnc
    obtain rfl : A = labBdry := Finset.mem_singleton.1 hA
    exfalso
    rw [bdryDomsPost_eq_bdryDomsPre_of_rem_empty (A := labBdry) (k := 1) _ _ rfl] at hY
    exact hnc (by have := (mem_bdryDomsPre.1 hY).1; rwa [← labBdry_Zpre] at this)

end Balaban.LargeField.Def7

namespace Balaban.Inhabited.RipeRemoval

open Balaban Balaban.LargeField RadiiSet RadiiHist

/-- On `ripeRemHistory` the removed set is nonempty and there is a cube `y` of `Ω_T^post` that is
not in `Ω_T^pre`; for the label `{y}` the intersections with the two regions differ, so the
disjointness hypothesis of `inter_omegaPost_of_disjoint` is necessary. -/
theorem ripeRem_label_meets_removal :
    ∃ y, y ∈ ripeRemHistory.removedSet (Tstar wS) ∧
      y ∈ ripeRemHistory.omegaPost (Tstar wS) ∧ y ∉ Def7.OmegaCube ripeRemHistory (Tstar wS) ∧
      ({y} : Set _) ∩ ripeRemHistory.omegaPost (Tstar wS) ≠
        {y} ∩ Def7.OmegaCube ripeRemHistory (Tstar wS) := by
  have hne := ripeRemHistory_omegaPost_ne
  obtain ⟨y, hy⟩ : ∃ y, y ∈ ripeRemHistory.omegaPost (Tstar wS) ∧
      y ∉ Def7.OmegaCube ripeRemHistory (Tstar wS) := by
    by_contra hcon
    exact hne (Set.Subset.antisymm (fun y hy => by_contra fun hy' => hcon ⟨y, hy, hy'⟩)
      (ripeRemHistory.OmegaCube_subset_omegaPost _))
  refine ⟨y, hy.1.resolve_left hy.2, hy.1, hy.2, fun h => ?_⟩
  have : y ∈ ({y} : Set _) ∩ ripeRemHistory.omegaPost (Tstar wS) := ⟨rfl, hy.1⟩
  rw [h] at this
  exact hy.2 this.2

end Balaban.Inhabited.RipeRemoval
