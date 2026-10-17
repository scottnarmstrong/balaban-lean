/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainTree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian factors of a block tree as a product over its nodes (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (b), (c) (generic part): for the numbering of
`exists_blockTree_of_tree`, `windowIntegrand_eq_prod` (the integrand of (III.1.4) is the product over the
nodes of the Gaussian factors) and `lintegral_nodes_comp` (integrating the non-root nodes gives the
composed Gaussian density of the root value).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section Prod

variable {m k1 k : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι) (r : ι) (B : BlockTree m k1 k)
  (e : ι ≃ Fin (B.n + 1)) (el : Lf ≃ Fin B.nLeaf)

/-- The values `Ψ` on the nodes as a function on `ℕ` through the numbering `e` (zero outside). -/
theorem sum_child_nodes (he0 : (e r : ℕ) = 0) (hpar : ∀ i, i ≠ r → B.par (e i) = e (pa i))
    (Ψ : ι → V) (i : ι) :
    ∑ c ∈ (Finset.range (B.n + 1)).filter (fun c => c ≠ 0 ∧ B.par c = e i),
        (if h : c < B.n + 1 then Ψ (e.symm ⟨c, h⟩) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ r ∧ pa j = i), Ψ j := by
  classical
  refine Finset.sum_bij (fun c hc => e.symm ⟨c, Finset.mem_range.mp (Finset.mem_filter.mp hc).1⟩)
    ?_ ?_ ?_ ?_
  · intro c hc
    have hcf := Finset.mem_filter.mp hc
    have hcn := Finset.mem_range.mp hcf.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h
      apply hcf.2.1
      have := congrArg (fun j => (e j : ℕ)) h
      simpa [he0] using this
    · have hne : e.symm ⟨c, hcn⟩ ≠ r := by
        intro h
        apply hcf.2.1
        have := congrArg (fun j => (e j : ℕ)) h
        simpa [he0] using this
      have h1 := hpar _ hne
      simp only [Equiv.apply_symm_apply] at h1
      have h2 : e (pa (e.symm ⟨c, hcn⟩)) = e i := Fin.ext (h1 ▸ hcf.2.2)
      exact e.injective h2
  · intro c c' hc hc' h
    have := e.symm.injective h
    simpa using congrArg Fin.val this
  · intro j hj
    have hjf := Finset.mem_filter.mp hj
    refine ⟨(e j : ℕ), ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (e j).2, ?_, ?_⟩
    · intro h
      apply hjf.2.1
      have : e j = e r := Fin.ext (h.trans he0.symm)
      exact e.injective this
    · rw [hpar j hjf.2.1, hjf.2.2]
  · intro c hc
    have hcn := Finset.mem_range.mp (Finset.mem_filter.mp hc).1
    simp [hcn]

theorem sum_child_leaves (hleaf : ∀ l, B.leafPar (el l) = e (lp l)) (Ψl : Lf → V) (i : ι) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafPar x = e i), Ψl (el.symm x) =
      ∑ l ∈ Finset.univ.filter (fun l => lp l = i), Ψl l := by
  classical
  refine Finset.sum_bij (fun x _ => el.symm x) ?_ ?_ ?_ ?_
  · intro x hx
    have h1 := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h2 := hleaf (el.symm x)
    rw [Equiv.apply_symm_apply] at h2
    exact e.injective (Fin.ext (h2.symm.trans h1))
  · intro x x' _ _ h
    exact el.symm.injective h
  · intro l hl
    refine ⟨el l, ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hleaf l, (Finset.mem_filter.mp hl).2]
  · intro x _
    rfl

/-- **(b) generic: the integrand of (III.1.4) is the product over the nodes of the Gaussian
factors.**  For values `Ψ` on the nodes and `Ψl` on the leaves, the windowed integrand of the block tree
`B` (numbering `e`, `el`) is the product over the nodes `i` of
`z_{s_i}^{dim V} g_{c_{s_i - 1}}(z_{s_i} Ψ_i - m⁻¹ (∑_{children nodes} Ψ + ∑_{children leaves} Ψl))`. -/
theorem windowIntegrand_eq_prod (he0 : (e r : ℕ) = 0)
    (hsc : ∀ i, B.scale (e i) = sc i) (hpar : ∀ i, i ≠ r → B.par (e i) = e (pa i))
    (hleaf : ∀ l, B.leafPar (el l) = e (lp l)) (c z : ℕ → ℝ) (Ψ : ι → V) (Ψl : Lf → V) :
    B.windowIntegrand c z (fun x => Ψl (el.symm x))
        (fun i => if h : i < B.n + 1 then Ψ (e.symm ⟨i, h⟩) else 0) =
      ∏ i : ι, z (sc i) ^ Module.finrank ℝ V *
        gaussDens (c (sc i - 1)) (z (sc i) • Ψ i - (m : ℝ)⁻¹ •
          ((∑ j ∈ Finset.univ.filter (fun j => j ≠ r ∧ pa j = i), Ψ j) +
            ∑ l ∈ Finset.univ.filter (fun l => lp l = i), Ψl l)) := by
  classical
  unfold BlockTree.windowIntegrand
  rw [← Fin.prod_univ_eq_prod_range (fun i => z (B.scale i) ^ Module.finrank ℝ V *
    gaussDens (c (B.scale i - 1)) (z (B.scale i) • (fun i => if h : i < B.n + 1 then Ψ (e.symm ⟨i, h⟩)
      else 0) i - B.childAvg (fun x => Ψl (el.symm x)) (fun i => if h : i < B.n + 1 then
        Ψ (e.symm ⟨i, h⟩) else 0) i)) (B.n + 1)]
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hlt := (e i).2
  simp only [hsc i, hlt, dite_true, Equiv.symm_apply_apply, Fin.eta]
  unfold BlockTree.childAvg
  rw [sum_child_nodes (pa := pa) (r := r) (B := B) (e := e) he0 hpar Ψ i,
    sum_child_leaves (lp := lp) (B := B) (e := e) (el := el) hleaf Ψl i]

/-- The non-root nodes numbered `0, …, n - 1`. -/
noncomputable def nodeEquiv (he0 : (e r : ℕ) = 0) : {i // i ≠ r} ≃ Fin B.n where
  toFun i := ⟨(e i.1 : ℕ) - 1, by
    have h1 := (e i.1).2
    have h2 : (e i.1 : ℕ) ≠ 0 := fun h => i.2 (e.injective (Fin.ext (h.trans he0.symm)))
    omega⟩
  invFun a := ⟨e.symm ⟨a.1 + 1, by omega⟩, fun h => by
    have := congrArg (fun j => (e j : ℕ)) h
    simp [he0] at this⟩
  left_inv i := by
    have h2 : (e i.1 : ℕ) ≠ 0 := fun h => i.2 (e.injective (Fin.ext (h.trans he0.symm)))
    apply Subtype.ext
    apply e.injective
    apply Fin.ext
    simp
    omega
  right_inv a := by
    apply Fin.ext
    simp

theorem extVec_nodes (he0 : (e r : ℕ) = 0) (u : V) (Ψ : {i // i ≠ r} → V) :
    (fun i => if h : i < B.n + 1 then
        (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) (e.symm ⟨i, h⟩) else 0) =
      extVec u (fun a : Fin B.n => Ψ ((nodeEquiv r B e he0).symm a)) := by
  funext i
  unfold extVec
  by_cases h0 : i = 0
  · subst h0
    have h1 : (0 : ℕ) < B.n + 1 := Nat.succ_pos _
    have : e.symm ⟨0, h1⟩ = r := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext he0.symm
    simp only [h1, dite_true, this, ite_true]
  · by_cases h1 : i < B.n + 1
    · have h2 : i - 1 < B.n := by omega
      have hne : e.symm ⟨i, h1⟩ ≠ r := by
        intro h
        rw [Equiv.symm_apply_eq] at h
        have := congrArg Fin.val h
        simp [he0] at this
        exact h0 this
      simp only [h1, hne, h0, h2, dite_true, dite_false, ite_false]
      congr 1
      apply Subtype.ext
      show e.symm ⟨i, h1⟩ = e.symm ⟨i - 1 + 1, _⟩
      congr 1
      apply Fin.ext
      show i = i - 1 + 1
      omega
    · have h2 : ¬ i - 1 < B.n := by omega
      simp [h0, h1, h2]

/-- **(c) generic: integrating the non-root nodes** of the product of the Gaussian factors gives the
Gaussian density of the root value `u` (III.1.4), for the node numbering `e` of the block tree
`B`.  The integral is over all values of the non-root nodes. -/
theorem lintegral_nodes_comp (hm : 0 < m) (he0 : (e r : ℕ) = 0)
    (hsc : ∀ i, B.scale (e i) = sc i) (hpar : ∀ i, i ≠ r → B.par (e i) = e (pa i))
    (hleaf : ∀ l, B.leafPar (el l) = e (lp l)) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < k → 0 < c j) (hz : ∀ s, k1 < s → s ≤ k → 0 < z s) (u : V) (Ψl : Lf → V) :
    ∫⁻ Ψ : {i // i ≠ r} → V, ENNReal.ofReal (∏ i : ι, z (sc i) ^ Module.finrank ℝ V *
        gaussDens (c (sc i - 1)) (z (sc i) • (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) i -
          (m : ℝ)⁻¹ • ((∑ j ∈ Finset.univ.filter (fun j => j ≠ r ∧ pa j = i),
              (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) j) +
            ∑ l ∈ Finset.univ.filter (fun l => lp l = i), Ψl l)))
      ∂(MeasureTheory.Measure.pi fun _ : {i // i ≠ r} => (volume : Measure V)) =
    ENNReal.ofReal (gaussDens (B.composedPrecision c z)
      (u - B.composedMean z (fun x => Ψl (el.symm x)))) := by
  classical
  have hmp := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin B.n => V)
    (nodeEquiv r B e he0)
  have hvol : ∀ (ι' : Type) [Fintype ι'], (MeasureTheory.Measure.pi fun _ : ι' => (volume : Measure V)) =
      (volume : Measure (ι' → V)) := fun ι' _ => (MeasureTheory.volume_pi).symm
  rw [hvol]
  set g : (Fin B.n → V) → ENNReal := fun x => ENNReal.ofReal
    (B.windowIntegrand c z (fun x' => Ψl (el.symm x')) (extVec u x)) with hg
  have h1 : ∀ Ψ : {i // i ≠ r} → V, ENNReal.ofReal (∏ i : ι, z (sc i) ^ Module.finrank ℝ V *
        gaussDens (c (sc i - 1)) (z (sc i) • (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) i -
          (m : ℝ)⁻¹ • ((∑ j ∈ Finset.univ.filter (fun j => j ≠ r ∧ pa j = i),
              (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) j) +
            ∑ l ∈ Finset.univ.filter (fun l => lp l = i), Ψl l))) =
      g (MeasurableEquiv.piCongrLeft (fun _ : Fin B.n => V) (nodeEquiv r B e he0) Ψ) := by
    intro Ψ
    rw [hg]
    simp only
    rw [← windowIntegrand_eq_prod (sc := sc) (pa := pa) (lp := lp) (r := r) (B := B) (e := e)
      (el := el) he0 hsc hpar hleaf c z (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) Ψl,
      extVec_nodes r B e he0 u Ψ]
    congr 3
    funext a
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  simp_rw [h1]
  rw [hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) g]
  have hint : MeasureTheory.Integrable (fun x : Fin B.n → V =>
      B.windowIntegrand c z (fun x' => Ψl (el.symm x')) (extVec u x)) := by
    by_contra hni
    have h0 := B.integral_window_comp hm c z (fun x' => Ψl (el.symm x')) (fun s h1 h2 => hz s h1 h2) hc u
    rw [MeasureTheory.integral_undef hni] at h0
    have := gaussDens_pos (V := V) (B.composedPrecision_pos hm c z hz hc) (u - B.composedMean z (fun x' => Ψl (el.symm x')))
    linarith
  rw [hg]
  simp only
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall ?_)]
  · rw [B.integral_window_comp hm c z (fun x' => Ψl (el.symm x')) (fun s h1 h2 => hz s h1 h2) hc u]
  · intro x
    show 0 ≤ B.windowIntegrand c z (fun x' => Ψl (el.symm x')) (extVec u x)
    rw [BlockTree.windowIntegrand_eq]
    exact GaussTree.Psi_nonneg _ B.n
      (fun i hi => hz _ (B.scale_ge i hi) (B.scale_le i hi))
      (fun i hi => hc _ (by have := B.scale_ge i hi; omega)
        (by have := B.scale_ge i hi; have := B.scale_le i hi; omega)) _

end Prod

end Balaban.LargeField

