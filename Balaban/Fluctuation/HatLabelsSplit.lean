/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31a
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block structure of `ν_{p₁}` (FLUCTUATION.md §3.4, Theorem 3.4)

The fluctuation measure `ν_{p₁} = ⨂_{u ∈ T^{(k)}_1} ν₁` of a step is the product, over the
`π_{k+1}`-cubes `b` of `𝕋`, of the block measures `ν_b = ⨂_{u ∈ b} ν₁` (the unit points lying in
the cube `b`).  This is the actual instance of the typing datum `BlockSplit`:

* `Balaban.Fluctuation.piSplitEquiv`, `map_piSplit`: a product measure over `U` is the product,
  over the fibres of a map `c : U → B`, of the fibre product measures;
* `StepSetting.cellOf`: the `π_{k+1}`-cube of a unit point;
* `StepSetting.blockSplit`: the `BlockSplit` of the step measure for `0 < p₁`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale

section Generic

variable {U B E : Type} [Fintype U] [Fintype B] [DecidableEq B] [MeasurableSpace E]

omit [Fintype U] [Fintype B] [DecidableEq B] in
theorem measurable_piSplit_fwd (c : U → B) :
    Measurable (fun (Φ : ∀ b, {u : U // c u = b} → E) (u : U) => Φ (c u) ⟨u, rfl⟩) := by
  refine Measurable.of_eval fun u => ?_
  exact (measurable_pi_apply (⟨u, rfl⟩ : {v : U // c v = c u})).comp (measurable_pi_apply (c u))

omit [Fintype U] [Fintype B] [DecidableEq B] in
theorem measurable_piSplit_bwd (c : U → B) :
    Measurable (fun (x : U → E) (b : B) (u : {u : U // c u = b}) => x u.1) := by
  refine Measurable.of_eval fun b => Measurable.of_eval fun u => ?_
  exact measurable_pi_apply (u.1 : U)

/-- The measurable equivalence between families on the fibres of `c : U → B` and families on
`U`. -/
def piSplitEquiv (c : U → B) : (∀ b, {u : U // c u = b} → E) ≃ᵐ (U → E) where
  toFun Φ u := Φ (c u) ⟨u, rfl⟩
  invFun x b u := x u.1
  left_inv Φ := by
    funext b u
    obtain ⟨u, rfl⟩ := u
    rfl
  right_inv x := rfl
  measurable_toFun := measurable_piSplit_fwd c
  measurable_invFun := measurable_piSplit_bwd c

/-- **A product measure is the product of the products over the fibres.** -/
theorem map_piSplit (c : U → B) (ν : Measure E) [IsProbabilityMeasure ν] :
    Measure.map (fun (x : U → E) (b : B) (u : {u : U // c u = b}) => x u.1)
      (Measure.pi fun _ : U => ν) =
      Measure.pi fun b : B => Measure.pi fun _ : {u : U // c u = b} => ν := by
  classical
  have hsymm : (fun (x : U → E) (b : B) (u : {u : U // c u = b}) => x u.1) =
      ⇑(piSplitEquiv (E := E) c).symm := by
    rfl
  rw [hsymm]
  set e := piSplitEquiv (E := E) c with he
  have h1 : Measure.map e (Measure.pi fun b : B => Measure.pi fun _ : {u : U // c u = b} => ν) =
      Measure.pi fun _ : U => ν := by
    refine (Measure.pi_eq (fun s hs => ?_)).symm
    rw [MeasurableEquiv.map_apply]
    have hpre : e ⁻¹' (Set.pi Set.univ s) =
        Set.pi Set.univ (fun b : B => Set.pi Set.univ (fun u : {u : U // c u = b} => s u.1)) := by
      ext Φ
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, he, piSplitEquiv]
      constructor
      · intro h b u
        obtain ⟨u, rfl⟩ := u
        exact h u
      · intro h u
        exact h (c u) ⟨u, rfl⟩
    rw [hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [← Fintype.prod_sigma (fun p : (Σ b, {u : U // c u = b}) => ν (s p.2.1))]
    exact Fintype.prod_equiv (Equiv.sigmaFiberEquiv c) _ _ (fun p => rfl)
  rw [← h1, Measure.map_map e.symm.measurable e.measurable]
  simp

end Generic

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- The `π_{k+1}`-cube (of `𝕋`) containing a site of the fine torus. -/
def cubeOfSite (m₀ : ℕ) (x : CTorus d L N₁ m₁ (k + 1)) :
    CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ :=
  ⟨cbase (cellSide L m₀ m₁ (k + 1)) x, aligned_cbase x, Set.subset_univ _⟩

theorem cubeOfSite_eq_of_unitBlock_eq {x x' : CTorus d L N₁ m₁ (k + 1)}
    (h : unitBlock x = unitBlock x') : cubeOfSite m₀ x = cubeOfSite m₀ x' := by
  refine Subtype.ext (funext fun i => ?_)
  have h1 := (unitBlock_eq_iff x x').1 h i
  have hcs : cellSide L m₀ m₁ (k + 1) = L ^ k * L ^ (1 + m₀ + m₁) := by
    unfold cellSide; rw [← pow_add]; congr 1; ring
  have h2 : (x i).val / cellSide L m₀ m₁ (k + 1) = (x' i).val / cellSide L m₀ m₁ (k + 1) := by
    rw [hcs, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1]
  simp only [cubeOfSite, cbase]
  rw [h2]

/-- The `π_{k+1}`-cube containing a unit point. -/
noncomputable def StepSetting.cellOf (u : S.U) :
    CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ :=
  cubeOfSite m₀ (Classical.choose ((mem_unitPts S.G').1 u.2))

theorem StepSetting.cellOf_unitPt (x : CTorus d L N₁ m₁ (k + 1)) :
    S.cellOf m₀ (unitPt S.hG' x) = cubeOfSite m₀ x := by
  have h := (Classical.choose_spec ((mem_unitPts S.G').1 (unitPt S.hG' x).2)).2
  exact cubeOfSite_eq_of_unitBlock_eq m₀ h

open Classical in
/-- **The block structure of `ν_{p₁}`**: the actual instance of `BlockSplit` for a step.  The
variable of the block `b` is the family of the fluctuation variables at the unit points lying in
the cube `b`, and `ν_b` is the product of the one-site measures over these points. -/
noncomputable def StepSetting.blockSplit (hp : 0 < S.p₁) : BlockSplit S m₀ where
  Ωb b := {u : S.U // S.cellOf m₀ u = b} → Rn N
  ms := fun _ => inferInstance
  μ b := Measure.pi fun _ => fluctMeasure1 N S.p₁
  prob := fun _ => by
    have := isProbabilityMeasure_fluctMeasure1 N hp
    infer_instance
  restr x b u := x u.1
  meas := measurable_piSplit_bwd (S.cellOf m₀)
  map_eq := by
    have := isProbabilityMeasure_fluctMeasure1 N hp
    exact map_piSplit (S.cellOf m₀) (fluctMeasure1 N S.p₁)

theorem StepSetting.blockSplit_restr (hp : 0 < S.p₁) (x : S.E)
    (b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    (u : {u : S.U // S.cellOf m₀ u = b}) : (S.blockSplit m₀ hp).restr x b u = x u.1 := rfl

end Step

end Balaban.Fluctuation
