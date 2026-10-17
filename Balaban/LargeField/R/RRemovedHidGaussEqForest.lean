/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainForestInt

/-!
# The exact Gaussian integral over the free nodes of a forest (W938)

`notes/phase1/LF4R-PLAN.md` §8.5.  `lintegral_forest_nodes_eq`: in a finite forest with `m` children at every
node, with the nodes of a set `Fx` of roots fixed at `u`, the integral over the other nodes of the product of
the Gaussian factors is, for the block trees `B r` of the forest, the product over the roots of the composed
Gaussian densities `g_{P_r}(u_r - 𝒬^♮_r ψ^G)` at the fixed roots (`integral_window_comp`) and `1` at the free
roots.  `lintegral_forest_nodes` (the sup bound) is its application.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section ForestEq

variable {m k1 top N : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι)

/-- The sup bound of the exact forest integral: the product over the roots of the composed Gaussian densities
at the fixed roots is at most the product of the suprema `(c_{s_r-1} z_{s_r}² / 2π)^{N/2}`. -/
theorem prod_forest_eq_le (hm : 0 < m) (htop : ∀ i, sc i ≤ top) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < top → 0 < c j) (hz : ∀ s, k1 < s → s ≤ top → 0 < z s)
    (Fx : ι → Prop) [DecidablePred Fx] (B : ∀ r : {r : ι // pa r = r}, BlockTree m k1 (sc r.1))
    (val : {r : ι // pa r = r} → EuclideanSpace ℝ (Fin N)) :
    ∏ r : {r : ι // pa r = r}, (if Fx r.1 then ENNReal.ofReal
        (gaussDens ((B r).composedPrecision c z) (val r)) else 1) ≤
      ∏ r ∈ Finset.univ.filter (fun r : ι => pa r = r ∧ Fx r),
        ENNReal.ofReal ((c (sc r - 1) * z (sc r) ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) := by
  classical
  calc _ ≤ ∏ r : {r : ι // pa r = r}, (if Fx r.1 then ENNReal.ofReal ((c (sc r.1 - 1) *
        z (sc r.1) ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) else 1) := by
        refine Finset.prod_le_prod (fun r _ => ?_)
        by_cases hr : Fx r.1
        · simp only [hr, ite_true]
          have hcr : ∀ j, k1 ≤ j → j < sc r.1 → 0 < c j :=
            fun j hj hlt => hc j hj (lt_of_lt_of_le hlt (htop _))
          have hzr : ∀ s, k1 < s → s ≤ sc r.1 → 0 < z s :=
            fun s hs hle => hz s hs (hle.trans (htop _))
          refine ENNReal.ofReal_le_ofReal ?_
          have hP := (B r).composedPrecision_pos hm c z hzr hcr
          have hP2 := composedPrecision_le (B r) c z hcr hzr
          refine (gaussDens_le hP _).trans ?_
          rw [finrank_euclideanSpace_fin]
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          gcongr
        · simp only [hr, ite_false, le_refl]
    _ = _ := by
        rw [← Finset.prod_subtype (Finset.univ.filter (fun r : ι => pa r = r))
          (fun r => by simp) (fun r => if Fx r then ENNReal.ofReal ((c (sc r - 1) *
            z (sc r) ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) else 1)]
        rw [Finset.prod_filter, Finset.prod_filter]
        refine Finset.prod_congr rfl fun r _ => ?_
        by_cases h1 : pa r = r <;> by_cases h2 : Fx r <;> simp [h1, h2]

/-- **The Gaussian integral over the free nodes of a forest, exactly.** -/
theorem lintegral_forest_nodes_eq (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1)
    (hge : ∀ i, k1 + 1 ≤ sc i)
    (hfull : ∀ i, (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l => lp l = i).card = m)
    (hm : 0 < m) (htop : ∀ i, sc i ≤ top) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < top → 0 < c j) (hz : ∀ s, k1 < s → s ≤ top → 0 < z s)
    (Fx : ι → Prop) [DecidablePred Fx] (hFx : ∀ i, Fx i → pa i = i)
    (u : ι → EuclideanSpace ℝ (Fin N)) (Ψl : Lf → EuclideanSpace ℝ (Fin N))
    (ext : ({i // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) → ι → EuclideanSpace ℝ (Fin N))
    (hext : ∀ Ψ i, ext Ψ i = if h : Fx i then u i else Ψ ⟨i, h⟩) :
    ∃ (B : ∀ r : {r : ι // pa r = r}, BlockTree m k1 (sc r.1))
      (e : ∀ r : {r : ι // pa r = r}, {i // pa^[Fintype.card ι] i = r.1} ≃ Fin ((B r).n + 1))
      (el : ∀ r : {r : ι // pa r = r},
        {l : Lf // pa^[Fintype.card ι] (lp l) = r.1} ≃ Fin (B r).nLeaf),
      (∀ r, (e r ⟨r.1, iter_fixed pa r.2 _⟩ : ℕ) = 0) ∧
      (∀ r i, (B r).scale (e r i) = sc i.1) ∧
      (∀ r i, i.1 ≠ r.1 →
        (B r).par (e r i) = e r ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩) ∧
      (∀ r l, (B r).leafPar (el r l) = e r ⟨lp l.1, l.2⟩) ∧
      ∫⁻ Ψ : {i // ¬ Fx i} → EuclideanSpace ℝ (Fin N), ENNReal.ofReal
        (∏ i : ι, z (sc i) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
          gaussDens (c (sc i - 1)) (z (sc i) • ext Ψ i - (m : ℝ)⁻¹ •
            ((∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i), ext Ψ j) +
              ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i), Ψl l)))
      ∂(Measure.pi fun _ : {i // ¬ Fx i} => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ∏ r : {r : ι // pa r = r}, (if Fx r.1 then ENNReal.ofReal
        (gaussDens ((B r).composedPrecision c z) (u r.1 -
          (B r).composedMean z (fun x => Ψl ((el r).symm x).1))) else 1) := by
  classical
  obtain ⟨B, e, el, he0, hsc, hpar, hleaf, hprod⟩ := forest_trees (m := m) (k1 := k1)
    (V := EuclideanSpace ℝ (Fin N)) sc pa lp hpa hge hfull
  let col : {i // ¬ Fx i} → {r : ι // pa r = r} :=
    fun i => ⟨pa^[Fintype.card ι] i.1, pa_iter_card_fixed sc pa hpa i.1⟩
  have hcol : ∀ i, (col i).1 = pa^[Fintype.card ι] i.1 := fun _ => rfl
  let φ : ∀ r : {r : ι // pa r = r}, ({i : {i : ι // ¬ Fx i} // col i = r} →
      EuclideanSpace ℝ (Fin N)) → {i : ι // pa^[Fintype.card ι] i = r.1} →
      EuclideanSpace ℝ (Fin N) :=
    fun r y j => if h : Fx j.1 then u j.1 else y ⟨⟨j.1, h⟩, Subtype.ext ((hcol _).trans j.2)⟩
  let G : ∀ r : {r : ι // pa r = r}, ({i : {i : ι // ¬ Fx i} // col i = r} →
      EuclideanSpace ℝ (Fin N)) → ENNReal := fun r y => ENNReal.ofReal
    ((B r).windowIntegrand c z (fun x => Ψl ((el r).symm x).1)
      (fun i => if h : i < (B r).n + 1 then φ r y ((e r).symm ⟨i, h⟩) else 0))
  have hGm : ∀ r, Measurable (G r) := by
    intro r
    refine measurable_window_comp (B r) (e r) c z (fun x => Ψl ((el r).symm x).1) (φ r) ?_
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases h : Fx j.1
    · simp only [φ, h, dite_true]
      exact measurable_const
    · simp only [φ, h, dite_false]
      exact measurable_pi_apply _
  have hA : ∀ Ψ : {i // ¬ Fx i} → EuclideanSpace ℝ (Fin N), ENNReal.ofReal
      (∏ i : ι, z (sc i) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
        gaussDens (c (sc i - 1)) (z (sc i) • ext Ψ i - (m : ℝ)⁻¹ •
          ((∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i), ext Ψ j) +
            ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i), Ψl l))) =
      ∏ r : {r : ι // pa r = r}, G r (PiTools.fibreMap (α := fun _ => EuclideanSpace ℝ (Fin N))
        col Ψ r) := by
    intro Ψ
    rw [hprod c z (ext Ψ) Ψl, ENNReal.ofReal_prod_of_nonneg]
    · refine Finset.prod_congr rfl fun r _ => ?_
      refine congrArg ENNReal.ofReal (congrArg _ ?_)
      funext i
      by_cases hi : i < (B r).n + 1
      · simp only [hi, dite_true]
        rw [hext]
        rfl
      · simp [hi]
    · intro r _
      exact windowIntegrand_nonneg (B r) c z
        (fun j hj hlt => hc j hj (lt_of_lt_of_le hlt (htop _)))
        (fun s hs hle => hz s hs (hle.trans (htop _))) _ _
  have hB := PiTools.lintegral_prod_fibres (α := fun _ : {i // ¬ Fx i} => EuclideanSpace ℝ (Fin N))
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) col G hGm
  have hexact : ∀ r : {r : ι // pa r = r}, ∫⁻ y, G r y ∂(Measure.pi fun _ : {i // col i = r} =>
      (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      if Fx r.1 then ENNReal.ofReal (gaussDens ((B r).composedPrecision c z) (u r.1 -
        (B r).composedMean z (fun x => Ψl ((el r).symm x).1))) else 1 := by
    intro r
    have hcr : ∀ j, k1 ≤ j → j < sc r.1 → 0 < c j :=
      fun j hj hlt => hc j hj (lt_of_lt_of_le hlt (htop _))
    have hzr : ∀ s, k1 < s → s ≤ sc r.1 → 0 < z s :=
      fun s hs hle => hz s hs (hle.trans (htop _))
    by_cases hr : Fx r.1
    · simp only [hr, ite_true]
      exact lintegral_fibre_fixed sc pa lp hpa Fx hFx col hcol r hr hm (B r) (e r) (el r) (he0 r)
        (hsc r) (hpar r) (hleaf r) c z hcr hzr u Ψl (φ r) (fun y j => rfl) (G r) (fun y => rfl)
    · simp only [hr, ite_false]
      exact lintegral_fibre_free sc pa lp hpa Fx hFx col hcol r hr hm (B r) (e r) (el r) (he0 r)
        (hsc r) (hpar r) (hleaf r) c z hcr hzr u Ψl (φ r) (fun y j => rfl) (G r) (fun y => rfl)
  refine ⟨B, e, el, he0, hsc, hpar, hleaf, ?_⟩
  calc _ = ∫⁻ Ψ : {i // ¬ Fx i} → EuclideanSpace ℝ (Fin N), ∏ r : {r : ι // pa r = r},
        G r (PiTools.fibreMap (α := fun _ => EuclideanSpace ℝ (Fin N)) col Ψ r) :=
        lintegral_congr hA
    _ = ∏ r : {r : ι // pa r = r}, ∫⁻ y, G r y ∂(Measure.pi fun _ : {i // col i = r} =>
        (volume : Measure (EuclideanSpace ℝ (Fin N)))) := hB
    _ = _ := Finset.prod_congr rfl fun r _ => hexact r

end ForestEq

end Balaban.LargeField
