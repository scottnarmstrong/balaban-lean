/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.Thm31CoeffAnalytic
public import Balaban.Fluctuation.RootPavingMap
public import Balaban.Inhabited.Thm31bPolymer
import Mathlib.Tactic.Positivity

/-!
# Connected support and root anchoring of the parameterized remainder coefficients

For activities `A` and marks `G` (at one value of the parameter, so the statements hold for every
parameter) the coefficient `gsumCoeff μ Lab A y0 G T` of the polymer expansion, at `Ω = univ` and
level `K`, is non-zero only when

* the blocks of some mark label lie in `T` (`exists_blocksOf_subset_of_gsumCoeff_ne_zero`);
* `T` is non-empty, `sitesOf T` is a polymer and `dExt T = sizeJ (sitesOf T)`
  (`gsumCoeff_ne_zero_active`);
* if every mark label has the cube `bx` among its blocks, then `bx ∈ T`
  (`mem_of_gsumCoeff_ne_zero_of_labels`).

These are the statements of `RootActiveSize.lean` and `RootMarkedBound.lean` for `interpCoeff`,
stated directly for `gsumCoeff` without an `InterpMarks` record.  The last theorem feeds a
parameter-dependent family into `rooted_regroup_of_supp`, giving the regrouped family on domains
of `𝒟_K` containing the root box, with total sum equal to the sum of the coefficients (no
remainder) and the bound in `sizeJ`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited
  MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

section Param

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι] {E : Type*}

/-- **Support.**  If `gsumCoeff μ Lab A y0 G T ≠ 0` then the blocks of some mark label lie in `T`. -/
theorem exists_blocksOf_subset_of_gsumCoeff_ne_zero (hN : L ^ m₀ ∣ N₁)
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lab : CubeLabels m₀ K Set.univ Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ i u, Measurable (G i u))
    (hGdep : ∀ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i u))
    (hG : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {T : Finset 𝔅} (h : gsumCoeff μ Lab A y0 G T ≠ 0) :
    ∃ i, blocksOf m₀ K Set.univ (Lab.ysite (y0 i)) ⊆ T := by
  classical
  by_contra hno
  push Not at hno
  apply h
  unfold gsumCoeff Gsum
  have : (fun s : ℝ => ∑ i, Gst μ Lab (A (s : ℂ)).H
      (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i (s : ℂ)) T) = fun _ => 0 :=
    funext fun s => Finset.sum_eq_zero fun i _ =>
      (marked_cubes_explicit μ hN le_rfl isPiUnion_univ_K (A (s : ℂ)) (y0 i)
        (G i (s : ℂ)) (hGm i _) (hGdep i _) (hG i _) hκ0 hKc hεpos (hF0 i)
        hκ' hκG hκ hε).2.2.2.1 T (hno i)
  simp only [this]
  simp

/-- **Active sets.**  A non-zero coefficient has `T` non-empty, `sitesOf T` a polymer and
`dExt T = sizeJ`. -/
theorem gsumCoeff_ne_zero_active (hN : L ^ m₀ ∣ N₁)
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lab : CubeLabels m₀ K Set.univ Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ i u, Measurable (G i u))
    (hGdep : ∀ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i u))
    (hG : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {T : Finset 𝔅} (h : gsumCoeff μ Lab A y0 G T ≠ 0) :
    T.Nonempty ∧ IsPolyDom m₀ K (sitesOf T) ∧ dExt T = sizeJ m₀ K (sitesOf T) := by
  classical
  obtain ⟨i, hi⟩ := exists_blocksOf_subset_of_gsumCoeff_ne_zero hN μ A y0 G hGm hGdep hG hκ0
    hKc hεpos hF0 hκ' hκG hκ hε h
  have hne : T.Nonempty :=
    (Lab.blocksOf_nonempty hN le_rfl isPiUnion_univ_K (y0 i)).mono hi
  have htop : dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤ := fun ht =>
    h (gsumCoeff_eq_zero_of_dOmega_top hN μ Lab A y0 G ht)
  exact ⟨hne, (isPolyDom_and_dExt_eq_sizeJ hne htop).1, (isPolyDom_and_dExt_eq_sizeJ hne htop).2⟩

/-- **The anchor from the labels.**  If every mark label has the cube `bx` among its blocks (for
the energy marks, `bx = rootCube z`), a non-zero coefficient has `bx ∈ T`. -/
theorem mem_of_gsumCoeff_ne_zero_of_labels (hN : L ^ m₀ ∣ N₁)
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lab : CubeLabels m₀ K Set.univ Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ i u, Measurable (G i u))
    (hGdep : ∀ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i u))
    (hG : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {bx : 𝔅} (hlab : ∀ i, bx ∈ blocksOf m₀ K Set.univ (Lab.ysite (y0 i)))
    {T : Finset 𝔅} (h : gsumCoeff μ Lab A y0 G T ≠ 0) : bx ∈ T := by
  obtain ⟨i, hi⟩ := exists_blocksOf_subset_of_gsumCoeff_ne_zero hN μ A y0 G hGm hGdep hG hκ0
    hKc hεpos hF0 hκ' hκG hκ hε h
  exact hi (hlab i)

/-- **The regrouping for a parameter family.**  For activities `A θ` and marks `G θ` depending on a
parameter `θ`, with the root cube `bx` in every mark label, and for every `θ`, the coefficient
family `e θ T = gsumCoeff μ Lab (A θ) y0 (G θ) T` has the same total sum as its regrouping
`detCollarGrouped (e θ)`, which is non-zero only on domains of `𝒟_K` containing the box of `bx`,
and is bounded in `sizeJ`. -/
theorem gsumCoeff_rooted_regroup (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁)
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lab : CubeLabels m₀ K Set.univ Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : E → ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ θ i u, Measurable (G θ i u))
    (hGdep : ∀ θ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G θ i u))
    (hG : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {bx : 𝔅} (hlab : ∀ i, bx ∈ blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (θ : E) :
    ∑ X ∈ (Finset.univ : Finset (Finset 𝔅)).image detCollarHull,
        detCollarGrouped (fun T => gsumCoeff μ Lab (A θ) y0 (G θ) T) X =
        ∑ T, gsumCoeff μ Lab (A θ) y0 (G θ) T ∧
      (∀ X : Set (CTorus d L N₁ m₁ K),
        detCollarGrouped (fun T => gsumCoeff μ Lab (A θ) y0 (G θ) T) X ≠ 0 →
        IsDj m₀ K X ∧ box bx.1 (cellSide L m₀ m₁ K) ⊆ X) ∧
      ∀ X : Set (CTorus d L N₁ m₁ K),
        ‖detCollarGrouped (fun T => gsumCoeff μ Lab (A θ) y0 (G θ) T) X‖ ≤
          hullConst d L κ' (CPE d L Kc κH κ0 κ' * (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i)))) *
            Real.exp (-hullRate d L κ' * sizeJ m₀ K X) := by
  have hc : 0 ≤ CPE d L Kc κH κ0 κ' * (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) := by
    have h1 : 0 ≤ CPE d L Kc κH κ0 κ' := by unfold CPE c1; positivity
    have h2 : 0 ≤ ∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hF0 i).le (Real.exp_pos _).le
    positivity
  refine rooted_regroup_of_supp hL hN hc hκ' bx _
    (fun T hT => ?_) (fun T hT => ?_) (fun T => ?_)
  · by_contra hne
    exact hT (mem_of_gsumCoeff_ne_zero_of_labels hN μ (A θ) y0 (G θ) (hGm θ) (hGdep θ) (hG θ)
      hκ0 hKc hεpos hF0 hκ' hκG hκ hε hlab hne)
  · exact (gsumCoeff_ne_zero_active hN μ (A θ) y0 (G θ) (hGm θ) (hGdep θ) (hG θ)
      hκ0 hKc hεpos hF0 hκ' hκG hκ hε hT).2.1
  · simpa using norm_gsumCoeff_le (E := E) μ hN le_rfl isPiUnion_univ_K A y0 G Set.univ
      hGm hGdep hG hκ0 hKc hεpos hι hF0 hκ' hκG hκ hε T θ (Set.mem_univ θ)

end Param

end Balaban.Fluctuation
