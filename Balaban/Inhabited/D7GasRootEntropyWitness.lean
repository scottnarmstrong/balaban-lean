/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.D7GasRootEntropy
public import Balaban.Fluctuation.SizeModUnionTree
public import Balaban.Inhabited.RRawHoleWitness
public import Balaban.Inhabited.RExtraSizeWitness
public import Balaban.Fluctuation.Thm31Inhab

/-!
# Non-vacuity of `D7GasRootEntropy`

On the landed admissible history `RipeRemoval.ripeRemHistory` (genuine radii, `k₀ = T`, `K = T + 1`,
one removed component at scale `T`, non-empty raw hole) with a fine frame `m₀ = m₁ = 0`, `M = 1`
and the label `X` of all cubes of `𝕋_T` (its fine lift is the whole fine torus):

* `ripeRem_OmegaCube_nonempty`: the raw region `Ω_T^pre` contains a cube (the unique component of
  `Z^pre_T` has fewer than `n_T^d` cubes), so `X ∩ Ω_T^pre ≠ ∅`;
* the sums of `sum_exp_le_rawHole` (with `Q` the whole raw hole) and `sum_exp_le_removed` contain
  the term of `X`, hence are positive, and satisfy the bounds;
* `remMeeting_card_le` holds for `X`, with a removed component meeting it;
* `dcovMod_union_range_le` holds for the two-set family `X₀ = X₁ =` the fine torus with an active
  overlap (a cell of the fine lift of `Ω_T^pre`).

Counting lemmas only; nothing analytic about `R` is proved.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField RadiiHist RipeRemoval RadiiSet Def7

/-- The raw region `Ω_T^pre` of `ripeRemHistory` contains a cube. -/
theorem ripeRem_OmegaCube_nonempty :
    ∃ q, q ∈ OmegaCube ripeRemHistory (Tstar wS) := by
  classical
  by_contra h
  push Not at h
  have hk1 : 1 ≤ Tstar wS := one_le_Tstar _
  have hkK : Tstar wS ≤ Tstar wS + 1 := Nat.le_succ _
  obtain ⟨c, hc⟩ := RipeRemoval.comp_unique (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl
    wRH hk1 hkK (Tstar wS) hk1 le_rfl
  have hall : ∀ x, x ∈ c.1 := by
    intro x
    have hx : x ∈ ripeRemHistory.F.Zpre (Tstar wS) :=
      ripeRemHistory.OmegaCube_compl_subset_Zpre hk1 (h x)
    have hxZ : x ∈ ripeRemHistory.Zp (Tstar wS) := mem_finOf.mpr hx
    have hc' : linkClass (wS.omega (Tstar wS)) (ripeRemHistory.Zp (Tstar wS)) x ∈
        comps (wS.omega (Tstar wS)) (ripeRemHistory.Zp (Tstar wS)) :=
      mem_comps_iff.mpr ⟨x, hxZ, rfl⟩
    have hxc : x ∈ linkClass (wS.omega (Tstar wS)) (ripeRemHistory.Zp (Tstar wS)) x :=
      mem_linkClass.mpr ⟨hxZ, Linked.refl _⟩
    have := hc ⟨_, hc'⟩
    rw [← this] at *
    exact hxc
  have hrem : c.1 ∈ ripeRemHistory.rem (Tstar wS) :=
    RipeRemoval.mem_rem_T (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH hk1 c
  have hcard := RegionHistory.removed_card_le wS_good ripeRem_thickness ripeRemHistory_admissible
    hkK (c := c) hrem
  have hsub : (Finset.univ : Finset (Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)))) ⊆ c.1 :=
    fun x _ => hall x
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h1
  have h2 : Fintype.card (Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) =
      (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) ^ wS.d := by
    simp [Torus, ZMod.card]
  rw [h2] at h1
  have h3 := ripeRem_thickness (Tstar wS) hk1 le_rfl
  have h4 : (2 * wS.rho (Tstar wS) + 10) ^ wS.d <
      (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) ^ wS.d :=
    Nat.pow_lt_pow_left (by omega) (by have hd : wS.d = 3 := rfl; omega)
  omega

/-- The fine frame (`m₀ = m₁ = 0`, `M = 1`) used for the instances. -/
noncomputable def ripeFrame :
    FineSizeFrame wS (side wS (bigN wS) (Tstar wS + 1)) 1 (Tstar wS + 1) 0 0 :=
  Classical.choice (FineSizeFrame.nonempty (by simp))

/-- The label of all cubes is valid for the raw region. -/
theorem ripeFrame_validPre_univ :
    FineValidPre ripeFrame ripeRemLab (Tstar wS) Finset.univ := by
  have hX : Fluctuation.IsDj 0 (Tstar wS)
      (d7Pull ripeFrame (Tstar wS) ((Finset.univ : Finset (Torus wS.d
        (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)))) : Set _)) := by
    rw [Finset.coe_univ, d7Pull_univ]
    exact Fluctuation.isDj_univ _ _ _ _ _ _ _
  refine ⟨⟨hX, fun z _ => Or.inl (by rw [Finset.coe_univ, d7Pull_univ]; exact Set.subset_univ _)⟩,
    Fluctuation.dcovModE_ne_top_of_IsDj hX⟩

/-- **Instance of `remMeeting_card_le` (T5).** -/
theorem d7Gas_remMeeting_instance :
    1 ≤ (ripeRemLab.H.remMeeting (Finset.univ : Finset (Torus wS.d
        (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))))).card ∧
      (((ripeRemLab.H.remMeeting (Finset.univ : Finset (Torus wS.d
        (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))))).card : ℕ) : ℝ) ≤
        (2 * wS.d + 1) * Fluctuation.c1 wS.d wS.L *
          (1 + d7SizePre ripeFrame ripeRemLab (Tstar wS) Finset.univ) := by
  refine ⟨?_, remMeeting_card_le ripeFrame ripeRemLab (Nat.le_succ _) (one_le_Tstar _)
    ripeFrame_validPre_univ ?_⟩
  · obtain ⟨c, hc, x, hx, -⟩ := ripeRem_rawHole_meets
    exact Finset.card_pos.2 ⟨c, ripeRemLab.H.mem_remMeeting.2 ⟨hc, x, hx, Finset.mem_univ _⟩⟩
  · obtain ⟨q, hq⟩ := ripeRem_OmegaCube_nonempty
    exact ⟨q, Finset.mem_univ _, hq⟩

open Classical in
/-- **Instance of `sum_exp_le_rawHole` (T4, hole form).**  `Q` is the whole raw hole of
`ripeRemHistory` at scale `T` (a union of nearest-neighbour components of the hole, non-empty);
the label of all cubes contributes a positive term. -/
theorem d7Gas_rawHole_instance :
    ∃ Q : Finset (Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))), Q.Nonempty ∧
      0 < ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus wS.d
            (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) =>
          FineValidPre ripeFrame ripeRemLab (Tstar wS) X ∧ Q ⊆ X ∧
            ∃ q ∈ X, q ∈ OmegaCube ripeRemLab.H (Tstar wS)),
        Real.exp (-(Fluctuation.aEnt wS.d wS.L + 1) *
          d7SizePre ripeFrame ripeRemLab (Tstar wS) X) ∧
      ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus wS.d
            (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) =>
          FineValidPre ripeFrame ripeRemLab (Tstar wS) X ∧ Q ⊆ X ∧
            ∃ q ∈ X, q ∈ OmegaCube ripeRemLab.H (Tstar wS)),
        Real.exp (-(Fluctuation.aEnt wS.d wS.L + 1) *
          d7SizePre ripeFrame ripeRemLab (Tstar wS) X) ≤
        2 * wS.d * Q.card * Fluctuation.K0 wS.d wS.L (Fluctuation.aEnt wS.d wS.L + 1) := by
  obtain ⟨c, hc, x, hx, hxO⟩ := ripeRem_rawHole_meets
  obtain ⟨q0, hq0⟩ := ripeRem_OmegaCube_nonempty
  set Q := Finset.univ.filter (fun q : Torus wS.d (side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) =>
    q ∉ OmegaCube ripeRemLab.H (Tstar wS)) with hQ
  have hQne : Q.Nonempty := ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxO⟩⟩
  refine ⟨Q, hQne, ?_, sum_exp_le_rawHole ripeFrame ripeRemLab (Nat.le_succ _) Q hQne
    (fun q hq => (Finset.mem_filter.1 hq).2)
    (fun y _ z hz _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩) le_rfl⟩
  refine lt_of_lt_of_le (Real.exp_pos _) (Finset.single_le_sum (f := fun X =>
    Real.exp (-(Fluctuation.aEnt wS.d wS.L + 1) * d7SizePre ripeFrame ripeRemLab (Tstar wS) X))
    (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, ripeFrame_validPre_univ, Finset.subset_univ _,
      q0, Finset.mem_univ _, hq0⟩))

open Classical in
/-- **Instance of `sum_exp_le_removed` and `sum_exp_le_removed_explicit` (T4, removed form).** -/
theorem d7Gas_removed_instance :
    ∃ c ∈ ripeRemLab.H.rem (Tstar wS),
      0 < ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus wS.d
            (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) =>
          FineValidPre ripeFrame ripeRemLab (Tstar wS) X ∧ (∃ x ∈ X, x ∈ c) ∧
            ∃ q ∈ X, q ∈ OmegaCube ripeRemLab.H (Tstar wS)),
        Real.exp (-(Fluctuation.aEnt wS.d wS.L + 1) *
          d7SizePre ripeFrame ripeRemLab (Tstar wS) X) ∧
      ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus wS.d
            (side wS (bigN wS) (Tstar wS + 1) (Tstar wS))) =>
          FineValidPre ripeFrame ripeRemLab (Tstar wS) X ∧ (∃ x ∈ X, x ∈ c) ∧
            ∃ q ∈ X, q ∈ OmegaCube ripeRemLab.H (Tstar wS)),
        Real.exp (-(Fluctuation.aEnt wS.d wS.L + 1) *
          d7SizePre ripeFrame ripeRemLab (Tstar wS) X) ≤
        (2 * wS.d + 1) * (((2 * wS.rho (Tstar wS) + 10) ^ wS.d : ℕ) : ℝ) *
          Fluctuation.K0 wS.d wS.L (Fluctuation.aEnt wS.d wS.L + 1) := by
  obtain ⟨c, hc, x, hx, -⟩ := ripeRem_rawHole_meets
  obtain ⟨q0, hq0⟩ := ripeRem_OmegaCube_nonempty
  refine ⟨c, hc, ?_, sum_exp_le_removed_explicit ripeFrame ripeRemLab (Nat.le_succ _) wS_good
    ripeRem_thickness (one_le_Tstar _) hc le_rfl⟩
  refine lt_of_lt_of_le (Real.exp_pos _) (Finset.single_le_sum (f := fun X =>
    Real.exp (-(Fluctuation.aEnt wS.d wS.L + 1) * d7SizePre ripeFrame ripeRemLab (Tstar wS) X))
    (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, ripeFrame_validPre_univ, ⟨x, Finset.mem_univ _, hx⟩,
      q0, Finset.mem_univ _, hq0⟩))

/-- **Instance of `dcovMod_union_range_le` (T1).**  Two copies of the fine torus (valid labels for
the fine raw region) have an active overlap (a cell of the fine raw region), so the union bound
holds. -/
theorem d7Gas_unionTree_instance :
    ∃ Ω : Set (Localization.CTorus wS.d wS.L ripeFrame.N₁ 0 (Tstar wS + 1)),
      Fluctuation.DjMod 0 (Tstar wS) Ω (⋃ i ∈ Finset.range 2, (Set.univ : Set _)) ∧
      Fluctuation.dcovMod 0 (Tstar wS) Ω (⋃ i ∈ Finset.range 2, (Set.univ : Set _)) ≤
        ∑ _i ∈ Finset.range 2, Fluctuation.dcovMod 0 (Tstar wS) Ω (Set.univ : Set _) +
          Fluctuation.cG wS.d wS.L * (1 : ℕ) := by
  obtain ⟨q0, hq0⟩ := ripeRem_OmegaCube_nonempty
  have hnn := RegionHistory.tower ripeRemLab.H
  have hkK : Tstar wS ≤ Tstar wS + 1 := Nat.le_succ _
  refine ⟨d7Pull ripeFrame (Tstar wS) (OmegaCube ripeRemLab.H (Tstar wS)), ?_⟩
  have hdj : Fluctuation.DjMod 0 (Tstar wS) (d7Pull ripeFrame (Tstar wS)
      (OmegaCube ripeRemLab.H (Tstar wS))) (Set.univ : Set _) :=
    ⟨Fluctuation.isDj_univ _ _ _ _ _ _ _, fun z _ => Or.inl (Set.subset_univ _)⟩
  have hcell := Fluctuation.mem_cellsIn.1
    ((cellsIn_d7Pull_mem ripeFrame hnn hkK (OmegaCube ripeRemLab.H (Tstar wS))
      (cubeBase ripeFrame (Tstar wS) q0)).2
      ⟨aligned_cubeBase ripeFrame hnn hkK q0, by
        rw [cubeIdx_cubeBase ripeFrame hnn hkK]; exact hq0⟩)
  exact Fluctuation.dcovMod_union_range_le (fun _ => (Set.univ : Set _)) (fun _ => hdj) 1
    (fun _ _ _ => ⟨0, by omega, cubeBase ripeFrame (Tstar wS) q0, hcell.1,
      fun z hz => ⟨⟨Set.mem_univ _, Set.mem_univ _⟩, hcell.2 hz⟩⟩)

end Balaban.Inhabited
