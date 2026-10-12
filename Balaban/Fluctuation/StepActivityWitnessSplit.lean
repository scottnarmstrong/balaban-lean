/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepNonvanishInhab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `StepActivityBound` for the one-label activity on a torus with any number of blocks

`stepActivityBound_of_small` (`StepNonvanishInhab`) is stated for `N₁ = 1`, where the unique block
carries the whole fluctuation variable.  Here the same construction is carried out for every `N₁`:
the block structure `BlockSplit` has the variable `ψ̂` in one fixed block `b₀` (with law `ν_{p₁}`)
and the point mass at `0` in all other blocks; `ν_{p₁}` is the image of the resulting product
(`map_oneBlockMap`).  The single label is the whole torus `𝕋` and its activity is the truncated
exponent `W₁(s) + W₂(t)`; the smallness is the same hypothesis `hsmall`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField.Def6
  Balaban.Background Balaban.SmallField MeasureTheory

section Split

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The measure `ν` placed in the coordinate `b₀` and the point mass at `0` elsewhere. -/
noncomputable def oneBlockMeasure (ν : Measure X) [Zero X] (b₀ : ι) (b : ι) : Measure X :=
  open Classical in if b = b₀ then ν else Measure.dirac 0

instance oneBlockMeasure_prob (ν : Measure X) [Zero X] [IsProbabilityMeasure ν] (b₀ : ι) (b : ι) :
    IsProbabilityMeasure (oneBlockMeasure ν b₀ b) := by
  unfold oneBlockMeasure
  split_ifs <;> infer_instance

/-- The map placing `x` in the coordinate `b₀` and `0` elsewhere. -/
noncomputable def oneBlockMap [Zero X] (b₀ : ι) (x : X) : ι → X :=
  fun b => open Classical in if b = b₀ then x else 0

omit [Fintype ι] in
theorem measurable_oneBlockMap [Zero X] (b₀ : ι) : Measurable (oneBlockMap (X := X) b₀) := by
  refine measurable_pi_iff.2 fun b => ?_
  unfold oneBlockMap
  split_ifs
  · exact measurable_id
  · exact measurable_const

/-- **The image of `ν` under `x ↦ (x at b₀, 0 elsewhere)` is the product measure.** -/
theorem map_oneBlockMap (ν : Measure X) [Zero X] [MeasurableSingletonClass X]
    [IsProbabilityMeasure ν] (b₀ : ι) :
    Measure.map (oneBlockMap b₀) ν = Measure.pi (oneBlockMeasure ν b₀) := by
  classical
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (measurable_oneBlockMap b₀) (MeasurableSet.univ_pi hs)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b₀)]
  have h0 : oneBlockMeasure ν b₀ b₀ = ν := by simp [oneBlockMeasure]
  rw [h0]
  by_cases hall : ∀ b ∈ Finset.univ.erase b₀, (0 : X) ∈ s b
  · have : ∀ b ∈ Finset.univ.erase b₀, oneBlockMeasure ν b₀ b (s b) = 1 := by
      intro b hb
      have hne : b ≠ b₀ := Finset.ne_of_mem_erase hb
      simp [oneBlockMeasure, hne, hall b hb]
    rw [Finset.prod_congr rfl this, Finset.prod_const_one, mul_one]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, oneBlockMap]
    constructor
    · intro h; simpa using h b₀
    · intro h b
      by_cases hb : b = b₀
      · subst hb; simpa using h
      · simpa [hb] using hall b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩)
  · push Not at hall
    obtain ⟨b, hb, hb0⟩ := hall
    have hne : b ≠ b₀ := Finset.ne_of_mem_erase hb
    have hz : oneBlockMeasure ν b₀ b (s b) = 0 := by
      simp [oneBlockMeasure, hne, hb0]
    rw [Finset.prod_eq_zero hb hz, mul_zero]
    have : oneBlockMap b₀ ⁻¹' Set.pi Set.univ s = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, oneBlockMap,
        Set.mem_empty_iff_false, iff_false]
      intro h
      have := h b
      simp [hne] at this
      exact hb0 this
    rw [this, measure_empty]

end Split

section Inhab

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  (g : Fld d L N₁ m₁ (k + 1) N)

open Classical in
/-- **`StepActivityBound` for any `N₁`**: the single label `𝕋` carrying the truncated exponents
`W₁(s) + W₂(t)`, uniformly below the cluster threshold `stepActivityThreshold` on the segments. -/
theorem stepActivityBound_of_small_gen (hp₁ : 0 < S.p₁)
    (hmeas : ∀ p ∈ stepSegments, Measurable (fun x => S.WoneT C p.1 x + S.WtwoT C g p.2 x))
    (hsmall : ∀ p ∈ stepSegments, ∀ x,
      ‖S.WoneT C p.1 x + S.WtwoT C g p.2 x‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1)) :
    Nonempty (StepActivityBound S C g) := by
  have hprob : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hne : Nonempty (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
      Set.univ) := ⟨⟨cbase (cellSide L 0 m₁ (k + 1)) 0, aligned_cbase 0, Set.subset_univ _⟩⟩
  set b₀ := Classical.arbitrary (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0
    (k + 1) Set.univ) with hb₀
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hc1 := one_le_c1 d L
  set κ0 := aEnt d L + 1 with hκ0
  set Kc := K0 d L κ0 + 1 with hKc
  have hKc1 : 1 ≤ Kc := by linarith
  set κH := 3 * κ0 + c1 d L + 3 / 2 with hκH
  set εH := 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + 0 * cG d L)) with hεH
  have hεpos : 0 < εH := by positivity
  let Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1) Set.univ
      Unit :=
    { ysite := fun _ => Set.univ
      dl := fun _ => treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
        Set.univ
      isDj := fun _ => isDj_univ d L N₁ m₁ (k + 1) 0 (k + 1)
      meets := fun _ => by simp
      size := fun _ => Or.inl rfl }
  let BS : BlockSplit S 0 :=
    { Ωb := fun _ => S.E
      μ := oneBlockMeasure S.nuFl b₀
      restr := oneBlockMap b₀
      meas := measurable_oneBlockMap b₀
      map_eq := map_oneBlockMap S.nuFl b₀ }
  let A : ℝ × ℝ → LabelAct Lab BS.Ωb εH κH κ0 Kc := fun p =>
    { H := fun _ Φ => if p ∈ stepSegments then
        S.WoneT C p.1 (Φ b₀) + S.WtwoT C g p.2 (Φ b₀) else 0
      meas := fun _ => by
        by_cases hp : p ∈ stepSegments
        · simp only [hp, ite_true]
          exact (hmeas p hp).comp (measurable_pi_apply _)
        · simp only [hp, ite_false]; exact measurable_const
      dep := fun _ Φ Φ' h => by
        have hb : b₀ ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
            Set.univ (Lab.ysite ()) := by
          rw [mem_blocksOf]; exact Set.subset_univ _
        simp only [h b₀ hb]
      bound := fun _ Φ => by
        by_cases hp : p ∈ stepSegments
        · simp only [hp, ite_true]
          refine (hsmall p hp _).trans (le_of_eq ?_)
          simp [stepActivityThreshold, εH, κH, κ0, Kc, Lab]
        · simp only [hp, ite_false, norm_zero]; positivity
      entropy := fun b => by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        split_ifs
        · have h0 : 0 ≤ treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0
              (k + 1) Set.univ := treeLenCovOne_nonneg _ _ _
          have : Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (K := k + 1) 0 (k + 1) Set.univ) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [aEnt_nonneg d L])
          linarith
        · linarith }
  refine ⟨{
    m₀ := 0
    hN := by simp
    BS := BS
    Lb := Unit
    Lab := Lab
    εH := εH
    κH := κH
    κ0 := κ0
    κ' := 0
    Kc := Kc
    A := A
    hκ0 := le_rfl
    hKc := le_rfl
    hεpos := hεpos
    hκ' := le_rfl
    hκ := by rw [hκH]; linarith
    hε := le_rfl
    hW := fun p hp => ?_ }⟩
  filter_upwards [S.ae_ball hp₁] with x hx
  simp only [A, hp, ite_true, Finset.univ_unique, Finset.sum_singleton, BS, oneBlockMap]
  rw [S.WoneT_of_chi C p.1 x hx, S.WtwoT_of_chi C g p.2 x hx]

end Inhab

end Balaban.Fluctuation
