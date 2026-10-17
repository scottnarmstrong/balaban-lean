/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainIntegral

/-!
# The Gaussian integral over the free nodes of a forest (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (4).  In a finite forest with `m` children at every
node, the nodes in a set `Fx` of roots keep prescribed values `u`; integrating the other nodes in the
product of the Gaussian factors gives, for each tree, the composed Gaussian density at the value of its root
(`lintegral_forest_nodes`): at most `(c_{s-1} z_s² / 2π)^{N/2}` for a root of scale `s` in `Fx`, and `1` for
a root outside `Fx`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section ForestInt

variable {m k1 top N : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι)

/-- A node that is fixed (hence a root) of the tree of a root `r` is `r`. -/
theorem eq_root_of_fixed {r : ι}
    {i : ι} (hi : pa^[Fintype.card ι] i = r) (hfix : pa i = i) : i = r := by
  rw [iter_fixed pa hfix] at hi
  exact hi

end ForestInt

section Meas

variable {m k1 k N : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (B : BlockTree m k1 k) (e : ι ≃ Fin (B.n + 1)) (el : Lf ≃ Fin B.nLeaf)

/-- The windowed integrand is a measurable function of the node values. -/
theorem measurable_window_comp {X : Type*} [MeasurableSpace X] (c z : ℕ → ℝ)
    (ψG : Fin B.nLeaf → EuclideanSpace ℝ (Fin N)) (φ' : X → ι → EuclideanSpace ℝ (Fin N))
    (hφ : Measurable φ') :
    Measurable fun x => ENNReal.ofReal (B.windowIntegrand c z ψG
      (fun i => if h : i < B.n + 1 then φ' x (e.symm ⟨i, h⟩) else 0)) := by
  have hc : Continuous fun ψ : ℕ → EuclideanSpace ℝ (Fin N) => B.windowIntegrand c z ψG ψ := by
    simp_rw [BlockTree.windowIntegrand_eq]
    exact GaussTree.continuous_Psi _ B.n
  refine ENNReal.measurable_ofReal.comp (hc.measurable.comp (measurable_pi_iff.mpr fun i => ?_))
  by_cases h : i < B.n + 1
  · simp only [h, dite_true]
    exact (measurable_pi_apply _).comp hφ
  · simp only [h, dite_false]
    exact measurable_const

end Meas

section Fibre

variable {m k1 N : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι)

/-- **The integral over the free nodes of the tree of a fixed root**: with the root value `u r` fixed
(`Fx r`), integrating the free nodes of the tree gives the composed Gaussian density at `u r`. -/
theorem lintegral_fibre_fixed (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1)
    (Fx : ι → Prop) [DecidablePred Fx] (hFx : ∀ i, Fx i → pa i = i)
    (col : {i : ι // ¬ Fx i} → {r : ι // pa r = r}) (hcol : ∀ i, (col i).1 = pa^[Fintype.card ι] i.1)
    (r : {r : ι // pa r = r}) (hr : Fx r.1) (hm : 0 < m)
    (B : BlockTree m k1 (sc r.1))
    (e : {i : ι // pa^[Fintype.card ι] i = r.1} ≃ Fin (B.n + 1))
    (el : {l : Lf // pa^[Fintype.card ι] (lp l) = r.1} ≃ Fin B.nLeaf)
    (he0 : (e ⟨r.1, iter_fixed pa r.2 _⟩ : ℕ) = 0) (hsc : ∀ i, B.scale (e i) = sc i.1)
    (hpar : ∀ i, i.1 ≠ r.1 →
      B.par (e i) = e ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩)
    (hleaf : ∀ l, B.leafPar (el l) = e ⟨lp l.1, l.2⟩) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < sc r.1 → 0 < c j) (hz : ∀ s, k1 < s → s ≤ sc r.1 → 0 < z s)
    (u : ι → EuclideanSpace ℝ (Fin N)) (Ψl : Lf → EuclideanSpace ℝ (Fin N))
    (φ : ({i : {i : ι // ¬ Fx i} // col i = r} → EuclideanSpace ℝ (Fin N)) →
      {i : ι // pa^[Fintype.card ι] i = r.1} → EuclideanSpace ℝ (Fin N))
    (hφ : ∀ y j, φ y j = if h : Fx j.1 then u j.1 else
      y ⟨⟨j.1, h⟩, Subtype.ext ((hcol _).trans j.2)⟩)
    (G : ({i : {i : ι // ¬ Fx i} // col i = r} →
      EuclideanSpace ℝ (Fin N)) → ENNReal)
    (hG : ∀ y, G y = ENNReal.ofReal (B.windowIntegrand c z (fun x => Ψl (el.symm x).1)
      (fun i => if h : i < B.n + 1 then φ y (e.symm ⟨i, h⟩) else 0))) :
    ∫⁻ y, G y ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ENNReal.ofReal (gaussDens (B.composedPrecision c z) (u r.1 -
        B.composedMean z (fun x => Ψl (el.symm x).1))) := by
  classical
  let r' : {i : ι // pa^[Fintype.card ι] i = r.1} := ⟨r.1, iter_fixed pa r.2 _⟩
  let E : {i : {i : ι // pa^[Fintype.card ι] i = r.1} // i ≠ r'} ≃
      {i : {i : ι // ¬ Fx i} // col i = r} :=
    { toFun := fun i => ⟨⟨i.1.1, fun h => i.2 (Subtype.ext (eq_root_of_fixed pa i.1.2 (hFx _ h)))⟩,
        Subtype.ext ((hcol _).trans i.1.2)⟩
      invFun := fun j => ⟨⟨j.1.1, (hcol _).symm.trans (congrArg Subtype.val j.2)⟩,
        fun h => j.1.2 (by rw [congrArg Subtype.val h]; exact hr)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmp := PiTools.measurePreserving_reindex E
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) (fun _ v => v)
    (fun _ => MeasurePreserving.id _)
  let g : ({i : {i : ι // pa^[Fintype.card ι] i = r.1} // i ≠ r'} → EuclideanSpace ℝ (Fin N)) →
      ENNReal := fun Ψ => ENNReal.ofReal (B.windowIntegrand c z (fun x => Ψl (el.symm x).1)
        (fun i => if h : i < B.n + 1 then
          (fun j : {i : ι // pa^[Fintype.card ι] i = r.1} =>
            if h' : j = r' then u r.1 else Ψ ⟨j, h'⟩) (e.symm ⟨i, h⟩) else 0))
  have hφ' : Measurable fun (Ψ : {i : {i : ι // pa^[Fintype.card ι] i = r.1} // i ≠ r'} →
      EuclideanSpace ℝ (Fin N)) (j : {i : ι // pa^[Fintype.card ι] i = r.1}) =>
        if h' : j = r' then u r.1 else Ψ ⟨j, h'⟩ := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases h' : j = r'
    · simp only [h', dite_true]
      exact measurable_const
    · simp only [h', dite_false]
      exact measurable_pi_apply _
  have hg : Measurable g := measurable_window_comp B e c z (fun x => Ψl (el.symm x).1)
    (fun (Ψ : {i : {i : ι // pa^[Fintype.card ι] i = r.1} // i ≠ r'} →
      EuclideanSpace ℝ (Fin N)) (j : {i : ι // pa^[Fintype.card ι] i = r.1}) =>
        if h' : j = r' then u r.1 else Ψ ⟨j, h'⟩) hφ'
  have hφeq : ∀ y j, φ y j = if h' : j = r' then u r.1 else y (E ⟨j, h'⟩) := by
    intro y j
    rw [hφ]
    by_cases h' : j = r'
    · have h1 : Fx j.1 := by rw [congrArg Subtype.val h']; exact hr
      simp only [h1, dite_true]
      simp only [h', dite_true]
      rfl
    · have h1 : ¬ Fx j.1 := fun hf => h' (Subtype.ext (eq_root_of_fixed pa j.2 (hFx _ hf)))
      simp only [h1, dite_false]
      simp only [h', dite_false]
      rfl
  have hGg : ∀ y, G y = g (fun j => y (E j)) := by
    intro y
    rw [hG]
    refine congrArg ENNReal.ofReal (congrArg _ ?_)
    funext i
    by_cases hi : i < B.n + 1
    · simp only [hi, dite_true]
      exact hφeq y _
    · simp [hi]
  calc ∫⁻ y, G y ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
      = ∫⁻ y, g (fun j => y (E j)) ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
        lintegral_congr hGg
    _ = ∫⁻ Ψ, g Ψ ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
        hmp.lintegral_comp hg
    _ = _ := lintegral_window_nonroot (fun i : {i : ι // pa^[Fintype.card ι] i = r.1} => sc i.1)
        (fun i => ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩) (fun l => ⟨lp l.1, l.2⟩) r'
        B e el hm he0 hsc (fun i hi => hpar i (fun h => hi (Subtype.ext h))) hleaf c z hc hz (u r.1)
        (fun l => Ψl l.1)

/-- **The integral over the free nodes of the tree of a root outside `Fx`**: all nodes of the tree are
free, and integrating them gives `1`. -/
theorem lintegral_fibre_free (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1)
    (Fx : ι → Prop) [DecidablePred Fx] (hFx : ∀ i, Fx i → pa i = i)
    (col : {i : ι // ¬ Fx i} → {r : ι // pa r = r}) (hcol : ∀ i, (col i).1 = pa^[Fintype.card ι] i.1)
    (r : {r : ι // pa r = r}) (hr : ¬ Fx r.1) (hm : 0 < m)
    (B : BlockTree m k1 (sc r.1))
    (e : {i : ι // pa^[Fintype.card ι] i = r.1} ≃ Fin (B.n + 1))
    (el : {l : Lf // pa^[Fintype.card ι] (lp l) = r.1} ≃ Fin B.nLeaf)
    (he0 : (e ⟨r.1, iter_fixed pa r.2 _⟩ : ℕ) = 0) (hsc : ∀ i, B.scale (e i) = sc i.1)
    (hpar : ∀ i, i.1 ≠ r.1 →
      B.par (e i) = e ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩)
    (hleaf : ∀ l, B.leafPar (el l) = e ⟨lp l.1, l.2⟩) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < sc r.1 → 0 < c j) (hz : ∀ s, k1 < s → s ≤ sc r.1 → 0 < z s)
    (u : ι → EuclideanSpace ℝ (Fin N)) (Ψl : Lf → EuclideanSpace ℝ (Fin N))
    (φ : ({i : {i : ι // ¬ Fx i} // col i = r} → EuclideanSpace ℝ (Fin N)) →
      {i : ι // pa^[Fintype.card ι] i = r.1} → EuclideanSpace ℝ (Fin N))
    (hφ : ∀ y j, φ y j = if h : Fx j.1 then u j.1 else
      y ⟨⟨j.1, h⟩, Subtype.ext ((hcol _).trans j.2)⟩)
    (G : ({i : {i : ι // ¬ Fx i} // col i = r} →
      EuclideanSpace ℝ (Fin N)) → ENNReal)
    (hG : ∀ y, G y = ENNReal.ofReal (B.windowIntegrand c z (fun x => Ψl (el.symm x).1)
      (fun i => if h : i < B.n + 1 then φ y (e.symm ⟨i, h⟩) else 0))) :
    ∫⁻ y, G y ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) = 1 := by
  classical
  have hfree : ∀ j : {i : ι // pa^[Fintype.card ι] i = r.1}, ¬ Fx j.1 := fun j h => by
    have := eq_root_of_fixed pa j.2 (hFx _ h)
    rw [this] at h
    exact hr h
  let E : {i : ι // pa^[Fintype.card ι] i = r.1} ≃
      {i : {i : ι // ¬ Fx i} // col i = r} :=
    { toFun := fun i => ⟨⟨i.1, hfree i⟩, Subtype.ext ((hcol _).trans i.2)⟩
      invFun := fun j => ⟨j.1.1, (hcol _).symm.trans (congrArg Subtype.val j.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmp := PiTools.measurePreserving_reindex E
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) (fun _ v => v)
    (fun _ => MeasurePreserving.id _)
  let g : ({i : ι // pa^[Fintype.card ι] i = r.1} → EuclideanSpace ℝ (Fin N)) → ENNReal :=
    fun Ψ => ENNReal.ofReal (B.windowIntegrand c z (fun x => Ψl (el.symm x).1)
      (fun i => if h : i < B.n + 1 then Ψ (e.symm ⟨i, h⟩) else 0))
  have hg : Measurable g := measurable_window_comp B e c z (fun x => Ψl (el.symm x).1)
    (fun (Ψ : {i : ι // pa^[Fintype.card ι] i = r.1} → EuclideanSpace ℝ (Fin N)) => Ψ)
    measurable_id
  have hGg : ∀ y, G y = g (fun j => y (E j)) := by
    intro y
    rw [hG]
    refine congrArg ENNReal.ofReal (congrArg _ ?_)
    funext i
    by_cases hi : i < B.n + 1
    · simp only [hi, dite_true]
      rw [hφ]
      simp only [hfree, dite_false]
      rfl
    · simp [hi]
  calc ∫⁻ y, G y ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
      = ∫⁻ y, g (fun j => y (E j)) ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
        lintegral_congr hGg
    _ = ∫⁻ Ψ, g Ψ ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
        hmp.lintegral_comp hg
    _ = 1 := lintegral_window_all (fun i : {i : ι // pa^[Fintype.card ι] i = r.1} => sc i.1)
        (fun i => ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩) (fun l => ⟨lp l.1, l.2⟩)
        ⟨r.1, iter_fixed pa r.2 _⟩ B e el hm he0 hsc
        (fun i hi => hpar i (fun h => hi (Subtype.ext h))) hleaf c z hc hz (fun l => Ψl l.1)

end Fibre

end Balaban.LargeField
