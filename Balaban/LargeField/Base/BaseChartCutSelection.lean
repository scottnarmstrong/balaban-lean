/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutFamily

/-!
# Pointwise selection of first-block cuts by the P5 sector

The failed P5 cube tests select a set of bad first blocks. The complementary
union and its crossing-bond parameters are the elementary cut geometry of
P5 (2.5)–(2.6) and P4 (2.51)–(2.54).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.LargeField.Base Classical

variable {d N L n : ℕ} [NeZero L] [NeZero n]

theorem baseSector_coarse_side (L n : ℕ) : 1 * n * L ^ (1 - 1) = n := by
  simp

/-- The pointwise P5 sector selected by the failed cube tests has weight one.
Every other sector in the P5 decomposition has weight zero. -/
theorem baseSector_selected_sector_weight
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let f : Torus d n → ℝ := fun c =>
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ)
    let P : Finset (Torus d n) := Finset.univ.filter (fun c => f c = 0)
    (∏ c ∈ P, (1 - f c)) *
      (∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P, f c) = 1 := by
  dsimp only
  let f : Torus d n → ℝ := fun c =>
    chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ)
  let P : Finset (Torus d n) := Finset.univ.filter (fun c => f c = 0)
  have hbad : ∀ c ∈ P, f c = 0 := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hgood : ∀ c ∈ (Finset.univ : Finset (Torus d n)) \ P, f c = 1 := by
    intro c hc
    have hne : f c ≠ 0 := by
      intro hz
      have : c ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ c, hz⟩
      exact (Finset.mem_sdiff.mp hc).2 this
    rcases chiPrimeZero_eq_zero_or_one (baseSectorN L n) L 1 1
      regimeB ν δ₀ (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)
      with hz | ho
    · exact False.elim (hne hz)
    · exact ho
  rw [Finset.prod_eq_one (fun c hc => by
    change 1 - f c = 1
    rw [hbad c hc]
    ring)]
  rw [Finset.prod_eq_one hgood]
  ring

/-- The good first blocks form a complete-block union, and setting precisely
its crossing parameters to zero gives `CrossZero` for the landed cut operator. -/
theorem baseSector_selected_cut
    (ϱ : ℝ) (P : Finset (Torus d (1 * n * L ^ (1 - 1)))) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let U : Set (Torus d (1 * n * L ^ 1)) :=
      {x | jBlock d L (1 * n) 1 1 x ∉ P}
    let s : FineBond d L (1 * n) → ℂ := fun b =>
      if b.1 ∈ U ↔ bondTip b ∉ U then 0 else 1
    IsFirstBlockUnion G U ∧ CrossZero G U s ∧
      s ∈ baseParamNbhd G 0 := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let U : Set (Torus d (1 * n * L ^ 1)) :=
    {x | jBlock d L (1 * n) 1 1 x ∉ P}
  let s : FineBond d L (1 * n) → ℂ := fun b =>
    if b.1 ∈ U ↔ bondTip b ∉ U then 0 else 1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact (show jBlock d L (1 * n) 1 1 x ∉ P ↔
      jBlock d L (1 * n) 1 1 y ∉ P by rw [hxy])
  · intro b hb hcross
    change (if b.1 ∈ U ↔ bondTip b ∉ U then (0 : ℂ) else 1) = 0
    exact ite_eq_left hcross
  · intro b hb
    by_cases hcross : b.1 ∈ U ↔ bondTip b ∉ U
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      change ‖s b - (0 : ℂ)‖ ≤ 0
      simp [s, hcross]
    · refine ⟨1, zero_le_one, le_rfl, ?_⟩
      change ‖s b - (1 : ℂ)‖ ≤ 0
      simp [s, hcross]

/-- The physical P5 cube tests select their good first-block union and its
crossing-bond cut. On nonzero all-good support the selected union is the
whole fine torus, so a proper component needs a sector with both good and
bad first blocks. -/
theorem baseSector_physical_cut_selection
    (ϱ : ℝ) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let P : Finset (Torus d (1 * n * L ^ (1 - 1))) :=
      Finset.univ.filter fun c =>
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i)
          (baseSector_coarse_side L n ▸ c)
          (baseSectorSpin φ, baseSectorTheta θ) = 0
    let U : Set (Torus d (1 * n * L ^ 1)) :=
      {x | jBlock d L (1 * n) 1 1 x ∉ P}
    let s : FineBond d L (1 * n) → ℂ := fun b =>
      if b.1 ∈ U ↔ bondTip b ∉ U then 0 else 1
    IsFirstBlockUnion G U ∧ CrossZero G U s ∧
      s ∈ baseParamNbhd G 0 ∧
      (baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0 →
        P = ∅ ∧ U = Set.univ) := by
  dsimp only
  let P : Finset (Torus d (1 * n * L ^ (1 - 1))) :=
    Finset.univ.filter fun c =>
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i)
        (baseSector_coarse_side L n ▸ c)
        (baseSectorSpin φ, baseSectorTheta θ) = 0
  let U : Set (Torus d (1 * n * L ^ 1)) :=
    {x | jBlock d L (1 * n) 1 1 x ∉ P}
  let s : FineBond d L (1 * n) → ℂ := fun b =>
    if b.1 ∈ U ↔ bondTip b ∉ U then 0 else 1
  have hcut := baseSector_selected_cut (d := d) (L := L) (n := n) ϱ P
  dsimp only at hcut
  refine ⟨hcut.1, hcut.2.1, hcut.2.2, ?_⟩
  intro hp
  have hP : P = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro c hc
    have hz : chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) (baseSector_coarse_side L n ▸ c)
        (baseSectorSpin φ, baseSectorTheta θ) = 0 :=
      (Finset.mem_filter.mp hc).2
    have ho := baseSectorCube_eq_one_of_product_ne_zero
      regimeB ν δ₀ h θ φ hp (baseSector_coarse_side L n ▸ c)
    exact one_ne_zero (ho.symm.trans hz)
  refine ⟨hP, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  change jBlock d L (1 * n) 1 1 x ∉ P
  exact (Finset.eq_empty_iff_forall_notMem.mp hP) _

end Balaban.LargeField
