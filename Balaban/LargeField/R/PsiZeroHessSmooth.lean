/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroInput
public import Balaban.LargeField.R.PsiZeroHessCalc

/-!
# Smoothness of the variational function on the tube and derivatives along lines (row 3)

The set of perturbations `u` for which the merged block field lies in the tube `Ψ̃(𝔹_k; η)` is open
(`isOpen_tube_merge`), on it `effOn` is smooth (`contDiffAt_effOn`, from `contDiffOn_effAction`), and along a line
`x₀ + t v` its first derivative is `fderiv` and its second derivative is `fderiv (fderiv)` (`effOn_line_derivs`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Filter Topology

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivatives of a `C²` function along a line. -/
theorem line_derivs {F : E → ℝ} {x0 : E} (hF : ContDiffAt ℝ 2 F x0) (v : E) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => F (x0 + s • v)) (fderiv ℝ F (x0 + t • v) v) t) ∧
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x0 + t • v) v) (fderiv ℝ (fderiv ℝ F) x0 v v) 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x0 + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x0
  have hcont : ContinuousAt (fun s : ℝ => x0 + s • v) 0 := (hline 0).continuousAt
  have hev : ∀ᶠ y in 𝓝 x0, ContDiffAt ℝ 2 F y := hF.eventually (by simp)
  refine ⟨?_, ?_⟩
  · have h0 : (fun s : ℝ => x0 + s • v) 0 = x0 := by simp
    have := hcont.eventually (h0 ▸ hev)
    filter_upwards [this] with t ht
    have hd : DifferentiableAt ℝ F (x0 + t • v) := ht.differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt t (hline t)
  · have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) x0 := hF.fderiv_right (by norm_num)
    have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x0) x0 :=
      (h1.differentiableAt (by norm_num)).hasFDerivAt
    have h2' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x0) (x0 + (0 : ℝ) • v) := by simpa using h2
    have h3 := h2'.comp_hasDerivAt (0 : ℝ) (hline 0)
    have h4 := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h3
    exact h4

end Gen

section Tube

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
  (Z : Finset (Torus d (N₀ * L ^ (k - k))))

theorem isOpen_imp {E : Type*} [TopologicalSpace E] {P : Prop} {S : Set E} (h : P → IsOpen S) :
    IsOpen {u : E | P → u ∈ S} := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simp [hP]

theorem continuous_merge_apply (ψ : BlockField d L N₀ k N) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) :
    Continuous fun u : SuppSpace Z N => mergeField Z ψ u z i :=
  (continuous_apply i).comp ((continuous_apply z).comp (contDiff_mergeField (n := 0) ψ).continuous)

theorem continuous_rn_merge (ψ : BlockField d L N₀ k N) (x x' : Torus d (N₀ * L ^ k)) :
    Continuous fun u : SuppSpace Z N =>
      rn (fun i => liftR (mergeField Z ψ u) x i - liftR (mergeField Z ψ u) x' i) := by
  unfold rn
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_merge_apply Z ψ _ i).sub (continuous_merge_apply Z ψ _ i)).pow 2

/-- The perturbations whose merged block field lies in the tube form an open set. -/
theorem isOpen_tube_merge (ψ : BlockField d L N₀ k N) (η : ℝ) :
    IsOpen {u : SuppSpace Z N | TubeOn G Set.univ η (mergeField Z ψ u)} := by
  unfold TubeOn
  rw [Set.ofPred_and]
  refine IsOpen.inter ?_ ?_
  · have : {u : SuppSpace Z N | ∀ x x', IsInterfacePair G x x' → jBlock d L N₀ k k x ∈ (Set.univ : Set _) →
        jBlock d L N₀ k k x' ∈ (Set.univ : Set _) →
          rn (fun i => liftR (mergeField Z ψ u) x i - liftR (mergeField Z ψ u) x' i) < η} =
        ⋂ x, ⋂ x', {u | IsInterfacePair G x x' →
          rn (fun i => liftR (mergeField Z ψ u) x i - liftR (mergeField Z ψ u) x' i) < η} := by
      ext u; simp
    rw [this]
    refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun x' => isOpen_imp fun _ => ?_
    exact isOpen_lt (continuous_rn_merge Z ψ x x') continuous_const
  · have : {u : SuppSpace Z N | ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ (Set.univ : Set _) →
        |∑ i, mergeField Z ψ u (jBlock d L N₀ k k x) i ^ 2 - 1| < η} =
        ⋂ x, {u | x ∈ dataSites G → |∑ i, mergeField Z ψ u (jBlock d L N₀ k k x) i ^ 2 - 1| < η} := by
      ext u; simp
    rw [this]
    refine isOpen_iInter_of_finite fun x => isOpen_imp fun _ => ?_
    have hc : Continuous fun u : SuppSpace Z N =>
        |∑ i, mergeField Z ψ u (jBlock d L N₀ k k x) i ^ 2 - 1| :=
      ((continuous_finsetSum _ fun i _ => (continuous_merge_apply Z ψ _ i).pow 2).sub
        continuous_const).abs
    exact isOpen_lt hc continuous_const

/-- `effOn` is smooth at every point of the open tube set. -/
theorem contDiffAt_effOn {a : ℕ → ℝ} (H : BgHyp d L k ϱ a 0) {η : ℝ} (hη : 0 < η)
    (hη0 : η ≤ bgC0 d L N) (hη1 : η ≤ bgC1 d L N) (ψ : BlockField d L N₀ k N) {x0 : SuppSpace Z N}
    (hx0 : TubeOn G Set.univ η (mergeField Z ψ x0)) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (effOn G a Z ψ) x0 := by
  have hU := isOpen_tube_merge G Z ψ η
  have hsm : ContDiffOn ℝ n (effAction G a) {ψ' | TubeOn G Set.univ η ψ'} :=
    contDiffOn_effAction G H hη hη0 hη1 (fun ψ' hψ' => hψ')
  have hc : ContDiffOn ℝ n (fun u : SuppSpace Z N => effAction G a (mergeField Z ψ u))
      {u | TubeOn G Set.univ η (mergeField Z ψ u)} :=
    hsm.comp (contDiff_mergeField (Zf := Z) (n := n) ψ).contDiffOn (fun u hu => hu)
  exact (hc.contDiffAt (hU.mem_nhds hx0))

end Tube

end Balaban.LargeField
