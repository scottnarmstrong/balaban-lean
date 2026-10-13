module

public import Balaban.Inhabited.RRipeCardWitness
public import Balaban.LargeField.R.RRawHoleComponent
public import Balaban.LargeField.R.RHistoryLabels

/-!
# A non-empty raw hole in a removed component (non-vacuity of `RRawHoleComponent`)

On the landed admissible history `RipeRemoval.ripeRemHistory` the raw region `Ω_T^pre`
(`Def7.OmegaCube`, `T = Tstar wS`) misses a cube of the removed ripe component: the large-field
cube created at the step `0 → 1` keeps the previous region `Z_{T-1}` non-empty, so the step `T-1`
has `Ω ≠ 𝕋`, and `(Ω_T^pre)ᶜ ⊆ Z^pre_T = ⋃ Rem_T`.  Hence the raw hole of the removed component is
non-empty (`ripeRem_rawHole_meets`), `A_X` is non-empty for `X` the component, and the hypothesis
of `rawHole_nnConnected_subset_comp` is satisfiable.  The removed outcome is realized.

This file gives instances of geometric lemmas; nothing analytic about `R` is proved.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RadiiHist RipeRemoval RadiiSet

/-- **T1.**  A removed component of `ripeRemHistory` at the scale `T` contains a cube outside the
raw region `Ω_T^pre`. -/
theorem ripeRem_rawHole_meets :
    ∃ c ∈ ripeRemHistory.rem (Tstar wS), ∃ x ∈ c,
      x ∉ Def7.OmegaCube ripeRemHistory (Tstar wS) := by
  by_contra h
  push Not at h
  refine ripeRemHistory_omegaPost_ne (Set.Subset.antisymm ?_ ?_)
  · rintro x (hx | hx)
    · exact hx
    · obtain ⟨c, hc, hxc⟩ := (ripeRemHistory.mem_removedSet_iff).mp hx
      exact h c hc x hxc
  · exact ripeRemHistory.OmegaCube_subset_omegaPost _

/-- The labelled version of `ripeRemHistory` (all labels `0`). -/
noncomputable def ripeRemLab : LabHist wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS)
    (Tstar wS + 1) :=
  ⟨ripeRemHistory, ripeRemHistory_admissible, fun _ _ => 0⟩

/-- **T3.**  Instances on `ripeRemHistory` with `X = c` the removed component: non-empty newly
active set with its cardinality bounds, the raw-hole component theorem for a single raw-hole cube,
the partition, the box/cardinality/cover bounds, and the realized removed outcome. -/
theorem ripeRem_rawHole_instance :
    ∃ c : ripeRemHistory.Comp (Tstar wS), c.1 ∈ ripeRemHistory.rem (Tstar wS) ∧
      (ripeRemHistory.newlyActive c.1).Nonempty ∧
      (ripeRemHistory.newlyActive c.1).card ≤ (2 * wS.rho (Tstar wS) + 10) ^ wS.d ∧
      (∃ x ∈ c.1, ∃ Q : Set (Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))),
        Q = {x} ∧
        Q ⊆ (c.1 : Set _) ∩ (Def7.OmegaCube ripeRemHistory (Tstar wS))ᶜ ∧
        (Q ∩ (c.1 : Set _)).Nonempty ∧ Q ⊆ (c.1 : Set _)) ∧
      (∃ P : Finset (Finset (Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)))),
        (∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → Disjoint Q Q') ∧
        P.biUnion id = ripeRemHistory.newlyActive c.1 ∧
        ∑ Q ∈ P, Q.card = (ripeRemHistory.newlyActive c.1).card) ∧
      c.1.card ≤ (2 * wS.rho (Tstar wS) + 10) ^ wS.d ∧
      (∀ F : Def7.FineSizeFrame wS (side wS (bigN wS) (Tstar wS + 1)) 1 (Tstar wS + 1) 0 0,
        (coverBoxes F (Tstar wS) (c.1 : Set _)).ncard ≤
          (wS.crit (Tstar wS) + 2 * wS.L) ^ wS.d) ∧
      ripeRemLab.outcomeAt (Tstar wS) c.1 = some Outcome.rem ∧
      ripeRemLab.outcomeAt (Tstar wS) ∈ Realized (Tstar wS) ripeRemLab := by
  classical
  obtain ⟨c', hc', x, hx, hxO⟩ := ripeRem_rawHole_meets
  let c : ripeRemHistory.Comp (Tstar wS) := ⟨c', ripeRemHistory.rem_sub _ hc'⟩
  have G := wS_good
  have hkK : Tstar wS ≤ Tstar wS + 1 := Nat.le_succ _
  have hk1 : 1 ≤ Tstar wS := one_le_Tstar _
  have hxN : x ∈ ripeRemHistory.newlyActive c' :=
    ripeRemHistory.mem_newlyActive.mpr
      ⟨hx, (ripeRemHistory.mem_removedSet_iff).mpr ⟨c', hc', hx⟩, hxO⟩
  have hcard : c'.card ≤ (2 * wS.rho (Tstar wS) + 10) ^ wS.d :=
    RegionHistory.removed_card_le G ripeRem_thickness ripeRemHistory_admissible hkK
      (c := c) hc'
  have hsub : ripeRemHistory.newlyActive c' ⊆ c' := fun y hy =>
    (ripeRemHistory.mem_newlyActive.mp hy).1
  have hout : ripeRemLab.outcomeAt (Tstar wS) c' = some Outcome.rem :=
    (ripeRemLab.mem_rem_iff_outcomeAt _ _).mp hc'
  refine ⟨c, hc', ⟨x, hxN⟩, (Finset.card_le_card hsub).trans hcard, ⟨x, hx, {x}, rfl, ?_, ?_, ?_⟩,
    ?_, hcard, fun F => RegionHistory.removed_coverBoxes_ncard_le G ripeRem_thickness
      ripeRemHistory_admissible F hkK (c := c) hc', hout, ?_⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hx, hxO⟩
  · exact ⟨x, rfl, hx⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx
  · obtain ⟨P, -, hd, hU, hs⟩ := ripeRemHistory.newlyActive_partition hk1 c'
    exact ⟨P, hd, hU, hs⟩
  · exact ⟨ripeRemLab, LabHist.agree_refl _ _ _, rfl⟩

end Balaban.Inhabited
