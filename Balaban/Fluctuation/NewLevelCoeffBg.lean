/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffA
public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Fluctuation.ParamActivitySubspace

/-!
# The coefficient of the new level as a formula on a background generating set (`NewLevelCoeffBg`)

P3 (4.41)-(4.47), P4 (2.56): the coefficient of a polymer `T` of the new level is the term of the
determinant of the step plus the interpolation coefficient of the marked cluster expansion of the
fluctuation integral (Theorem 3.4).  P3 pp. 78-79 recomputes the term of the polymer `Y` with the
generating set `𝔹_{k+1}(Y)`; the expansion (cubes, labels, block variables and their measure) stays
that of the step.  This file writes the coefficient as an explicit function of the parameter of a
background generating set `Gb` (`Gb = S.G'` for the step, a local set for the recomputation):

* `newLevelDetBg Gb a aT ν ρ Zb θ T`: the determinant part, `∑_{y ∈ Zb} detActivityBg y T` at the
  datum of `Gb` with raw data `θ.1` (no chart condition: the activity is a formula of the datum);
* `newLevelCoeffBg … H y0 G θ T`: `newLevelDetBg … θ T` plus `∫₀¹ ∑ᵢ G*(Y₀ᵢ, T)(s) ds` for the
  activities `H θ s` and the marks `G θ i s` given as functions (not bundled with their bounds), so
  that the formula has a value at every parameter.  At the parameters where the activities are a
  `LabelAct` the interpolation part is `gsumCoeff` (`gsumCoeff_eq_integral`);
* `gsumCoeff_eq_integral_of_agree`: the interpolation coefficient at `T` of a bundled system equals
  the formula of a system given by functions when the activities agree on the labels whose cubes lie
  in `T` and the marks agree when the cubes of their label lie in `T` (the reduction of the
  replacement identity of P3 p. 79 to the activities and the marks, `Gst_congr`);
* `newLevelCoeffBg_eq_of_agree`: the same for the whole coefficient, with the determinant parts.

The chain's family of the new level is this formula at `Gb = S.G'` on the step chart
(`StepTowerG.e0CoeffFamily_class_agree_rot_formula`); the recomputed family of a label polymer is
the formula at its local generating set, at the datum read from the field pair.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  MeasureTheory

section Formula

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱb : ℝ}
  (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)

/-- **The determinant part of the coefficient of the new level on `Gb`** (P3 (4.41), P4 (2.56)):
`∑_{y ∈ Zb} detActivityBg y T` at the datum of `Gb` whose raw data are `θ.1`, for a mask `Zb` of
unit points of `Gb` (the unit points of the block of the root). -/
noncomputable def newLevelDetBg (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (θ : physParamBg N Gb)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    ℂ :=
  ∑ y ∈ Zb, detActivityBg 1 a aT ν ρ
    (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2) y T

/-- The determinant part at the parameter of a datum `D` of `Gb` (any source). -/
theorem newLevelDetBg_rawOf (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb)) (D : BgData Gb N)
    (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    newLevelDetBg Gb a aT ν ρ Zb (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T =
      ∑ y ∈ Zb, detActivityBg 1 a aT ν ρ D y T := rfl

/-- The determinant part at a parameter whose raw data are those of a datum `D` of `Gb`. -/
theorem newLevelDetBg_of_eq (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    {θ : physParamBg N Gb} {D : BgData Gb N}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    newLevelDetBg Gb a aT ν ρ Zb θ T = ∑ y ∈ Zb, detActivityBg 1 a aT ν ρ D y T := by
  have hD : bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2 = D :=
    BgData.eq_of_raw (by rw [rawOf_bgOfRaw, hθ])
  unfold newLevelDetBg
  rw [hD]

variable {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ →
    Type*} [∀ b, MeasurableSpace (Ωb b)]
  (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
  {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

/-- **The coefficient of the new level on `Gb` as a formula** (P3 (4.41)-(4.47), P4 (2.56)): the
determinant part `newLevelDetBg` plus the interpolation coefficient `∫₀¹ ∑ᵢ G*(Y₀ᵢ, T)(s) ds` of
the marked cluster expansion with the label system `Lab`, the anchors `y0`, the activities
`H θ s` and the marks `G θ i s` of the parameter `θ` of `Gb`. -/
noncomputable def newLevelCoeffBg (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb)
    (G : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ : physParamBg N Gb)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    ℂ :=
  newLevelDetBg Gb a aT ν ρ Zb θ T +
    ∫ s in (0 : ℝ)..1, Gsum μ Lab (H θ (s : ℂ)) y0 (fun i => G θ i (s : ℂ)) T

/-- **The interpolation coefficient is the formula of its activities and marks**: `gsumCoeff` reads
the activities only through the functions `(A s).H`. -/
theorem gsumCoeff_eq_integral
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    gsumCoeff μ Lab A y0 G T =
      ∫ s in (0 : ℝ)..1, Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) T := rfl

/-- **The replacement identity reduced to the activities and the marks** (P3 p. 79): the
interpolation coefficient at `T` of a system with bundled activities `A` and marks `G` equals the
interpolation formula of activities `H'` and marks `G'` given as functions, when the activities
agree (for `s ∈ [0,1]`) on every label whose cubes lie in `T` and the marks agree (for
`s ∈ [0,1]`) whenever the cubes of their label lie in `T`.  Applied with the system of the step
and that recomputed on a local generating set at the datum read from the step's datum. -/
theorem gsumCoeff_eq_integral_of_agree
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (H' : ℂ → Lb → (∀ b, Ωb b) → ℂ)
    (G' : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hGdep : ∀ i s, DepOn (blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i))) (G i s))
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf 1 (k + 1) Set.univ (Lab.ysite y) ⊆ T → (A (s : ℂ)).H y = H' (s : ℂ) y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i)) ⊆ T → G i (s : ℂ) = G' i (s : ℂ)) :
    gsumCoeff μ Lab A y0 G T =
      ∫ s in (0 : ℝ)..1, Gsum μ Lab (H' (s : ℂ)) y0 (fun i => G' i (s : ℂ)) T := by
  rw [gsumCoeff_eq_integral]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold Gsum
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Gst_congr μ μ (A (s : ℂ)) (H' (s : ℂ)) _ T (hGdep i _) (fun _ _ => rfl)
    (hA s hs) (hG s hs i)

/-- **The replacement identity for the whole coefficient, reduced to its parts** (P3 p. 79): the
coefficient of a system with bundled activities on `Gp` (determinant part plus `gsumCoeff`) at the
parameter `θp` equals the formula `newLevelCoeffBg` on `Gb` at the parameter `θ`, when the
determinant parts agree at `T`, the activities agree on the labels inside `T` and the marks agree
on the anchors inside `T`. -/
theorem newLevelCoeffBg_eq_of_agree {ϱp : ℝ} (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp)
    (a : ℕ → ℝ) (aT ν ρ : ℝ) (Zp : Finset (unitPts Gp)) (Zb : Finset (unitPts Gb))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (θp : physParamBg N Gp)
    (H : physParamBg N Gb → ℂ → Lb → (∀ b, Ωb b) → ℂ)
    (G' : physParamBg N Gb → ι → ℂ → (∀ b, Ωb b) → ℂ) (θ : physParamBg N Gb)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hdet : newLevelDetBg Gp a aT ν ρ Zp θp T = newLevelDetBg Gb a aT ν ρ Zb θ T)
    (hGdep : ∀ i s, DepOn (blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i))) (G i s))
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
      blocksOf 1 (k + 1) Set.univ (Lab.ysite y) ⊆ T → (A (s : ℂ)).H y = H θ (s : ℂ) y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ (Lab.ysite (y0 i)) ⊆ T → G i (s : ℂ) = G' θ i (s : ℂ)) :
    newLevelDetBg Gp a aT ν ρ Zp θp T + gsumCoeff μ Lab A y0 G T =
      newLevelCoeffBg Gb μ a aT ν ρ Zb Lab H y0 G' θ T := by
  unfold newLevelCoeffBg
  rw [hdet, gsumCoeff_eq_integral_of_agree μ Lab A y0 G (H θ) (G' θ) T hGdep hA hG]

end Formula

end Balaban.Fluctuation
