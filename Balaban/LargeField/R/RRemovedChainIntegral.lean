/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainForest
public import Balaban.LargeField.Operators.PiTools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian integral over the node variables of a forest (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (4).  Per block tree: the composed precision is at
most `c_{k-1} z_k²` (`composedPrecision_le`), and a Gaussian density of precision `P` is at most
`(P / 2π)^{dim/2}` (`gaussDens_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section Sup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A Gaussian density of precision `P` is at most `(P / 2π)^{dim V / 2}`. -/
theorem gaussDens_le {P : ℝ} (hP : 0 < P) (v : V) :
    gaussDens P v ≤ (P / (2 * Real.pi)) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  unfold gaussDens
  have h1 : Real.exp (-(P / 2) * ‖v‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ‖v‖ ^ 2 := by positivity
    nlinarith
  have h2 : 0 ≤ (P / (2 * Real.pi)) ^ ((Module.finrank ℝ V : ℝ) / 2) := by positivity
  nlinarith

end Sup

section Prec

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- The composed precision of a block tree is at most `c_{k-1} z_k²`: the top block alone contributes
`(c_{k-1} z_k²)⁻¹` to the sum of which it is the inverse. -/
theorem composedPrecision_le (c z : ℕ → ℝ) (hc : ∀ j, k1 ≤ j → j < k → 0 < c j)
    (hz : ∀ s, k1 < s → s ≤ k → 0 < z s) :
    B.composedPrecision c z ≤ c (k - 1) * z k ^ 2 := by
  have hk1 : k1 + 1 ≤ k := by
    have := B.scale_ge 0 (Nat.zero_le _)
    rw [B.root_scale] at this
    exact this
  have hzk := hz k (by omega) le_rfl
  have hck := hc (k - 1) (by omega) (by omega)
  have hterm : varpi k z (B.scale 0 - 1) ^ 2 * blockFrac m k (B.scale 0) ^ 2 / c (B.scale 0 - 1) =
      (c (k - 1) * z k ^ 2)⁻¹ := by
    rw [B.root_scale]
    have hv : varpi k z (k - 1) = (z k)⁻¹ := by
      unfold varpi
      have : k - (k - 1) = 1 := by omega
      simp [this]
    have hb : blockFrac m k k = 1 := by simp [blockFrac]
    rw [hv, hb]
    field_simp
  have hnn : ∀ i ∈ Finset.range (B.n + 1), 0 ≤ varpi k z (B.scale i - 1) ^ 2 *
      blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hge := B.scale_ge i (by omega)
    have hle := B.scale_le i (by omega)
    have := hc (B.scale i - 1) (by omega) (by omega)
    positivity
  have hsum : (c (k - 1) * z k ^ 2)⁻¹ ≤ ∑ i ∈ Finset.range (B.n + 1),
      varpi k z (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1) := by
    rw [← hterm]
    exact Finset.single_le_sum (f := fun i => varpi k z (B.scale i - 1) ^ 2 *
      blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1)) hnn
      (Finset.mem_range.mpr (Nat.succ_pos _))
  unfold BlockTree.composedPrecision
  have hpos : 0 < (c (k - 1) * z k ^ 2)⁻¹ := by positivity
  calc (∑ i ∈ Finset.range (B.n + 1), varpi k z (B.scale i - 1) ^ 2 *
        blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1))⁻¹
      ≤ ((c (k - 1) * z k ^ 2)⁻¹)⁻¹ := inv_anti₀ hpos hsum
    _ = c (k - 1) * z k ^ 2 := inv_inv _

end Prec

section Tree

variable {m k1 k N : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι) (r : ι) (B : BlockTree m k1 k)
  (e : ι ≃ Fin (B.n + 1)) (el : Lf ≃ Fin B.nLeaf)

/-- **The tree integral, root value fixed**: integrating the non-root nodes of a block tree in the
windowed integrand with root value `u` and leaf values `Ψl` gives the composed Gaussian density at `u`. -/
theorem lintegral_window_nonroot (hm : 0 < m) (he0 : (e r : ℕ) = 0)
    (hsc : ∀ i, B.scale (e i) = sc i) (hpar : ∀ i, i ≠ r → B.par (e i) = e (pa i))
    (hleaf : ∀ l, B.leafPar (el l) = e (lp l)) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < k → 0 < c j) (hz : ∀ s, k1 < s → s ≤ k → 0 < z s)
    (u : EuclideanSpace ℝ (Fin N)) (Ψl : Lf → EuclideanSpace ℝ (Fin N)) :
    ∫⁻ Ψ : {i // i ≠ r} → EuclideanSpace ℝ (Fin N), ENNReal.ofReal
        (B.windowIntegrand c z (fun x => Ψl (el.symm x)) (fun i => if h : i < B.n + 1 then
          (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) (e.symm ⟨i, h⟩) else 0))
      ∂(Measure.pi fun _ : {i // i ≠ r} => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
    ENNReal.ofReal (gaussDens (B.composedPrecision c z) (u - B.composedMean z
      (fun x => Ψl (el.symm x)))) := by
  rw [← lintegral_nodes_comp sc pa lp r B e el hm he0 hsc hpar hleaf c z hc hz u Ψl]
  refine lintegral_congr fun Ψ => ?_
  rw [windowIntegrand_eq_prod sc pa lp r B e el he0 hsc hpar hleaf c z
    (fun j : ι => if h : j = r then u else Ψ ⟨j, h⟩) Ψl]

/-- The windowed integrand is non-negative. -/
theorem windowIntegrand_nonneg (c z : ℕ → ℝ) (hc : ∀ j, k1 ≤ j → j < k → 0 < c j)
    (hz : ∀ s, k1 < s → s ≤ k → 0 < z s) (ψG : Fin B.nLeaf → EuclideanSpace ℝ (Fin N))
    (ψ : ℕ → EuclideanSpace ℝ (Fin N)) : 0 ≤ B.windowIntegrand c z ψG ψ := by
  rw [BlockTree.windowIntegrand_eq]
  exact GaussTree.Psi_nonneg _ B.n
    (fun i hi => hz _ (B.scale_ge i hi) (B.scale_le i hi))
    (fun i hi => hc _ (by have := B.scale_ge i hi; omega)
      (by have := B.scale_ge i hi; have := B.scale_le i hi; omega)) _

/-- The translated Gaussian density has integral `1` (as a lower integral). -/
theorem lintegral_gaussDens_shift {P : ℝ} (hP : 0 < P) (μ0 : EuclideanSpace ℝ (Fin N)) :
    ∫⁻ v : EuclideanSpace ℝ (Fin N), ENNReal.ofReal (gaussDens P (v - μ0)) = 1 := by
  have h1 : ∫ v : EuclideanSpace ℝ (Fin N), gaussDens P (v - μ0) = 1 := by
    rw [integral_sub_right_eq_self (fun v : EuclideanSpace ℝ (Fin N) => gaussDens P v) μ0]
    exact integral_gaussDens hP
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin N) => gaussDens P (v - μ0)) :=
    Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun v => (gaussDens_pos hP _).le), h1]
  simp

/-- **The tree integral, root value free**: integrating all nodes (the root included) of the windowed
integrand of a block tree gives `1`. -/
theorem lintegral_window_all (hm : 0 < m) (he0 : (e r : ℕ) = 0)
    (hsc : ∀ i, B.scale (e i) = sc i) (hpar : ∀ i, i ≠ r → B.par (e i) = e (pa i))
    (hleaf : ∀ l, B.leafPar (el l) = e (lp l)) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < k → 0 < c j) (hz : ∀ s, k1 < s → s ≤ k → 0 < z s)
    (Ψl : Lf → EuclideanSpace ℝ (Fin N)) :
    ∫⁻ Ψ : ι → EuclideanSpace ℝ (Fin N), ENNReal.ofReal
        (B.windowIntegrand c z (fun x => Ψl (el.symm x)) (fun i => if h : i < B.n + 1 then
          Ψ (e.symm ⟨i, h⟩) else 0))
      ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N)))) = 1 := by
  classical
  have hcont : Continuous fun Ψ : ι → EuclideanSpace ℝ (Fin N) => B.windowIntegrand c z
      (fun x => Ψl (el.symm x)) (fun i => if h : i < B.n + 1 then Ψ (e.symm ⟨i, h⟩) else 0) := by
    simp_rw [BlockTree.windowIntegrand_eq]
    refine (GaussTree.continuous_Psi _ B.n).comp (continuous_pi fun i => ?_)
    by_cases h : i < B.n + 1
    · simp only [h, dite_true]
      exact continuous_apply _
    · simp only [h, dite_false]
      exact continuous_const
  have hF : Measurable fun Ψ : ι → EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (B.windowIntegrand c z
      (fun x => Ψl (el.symm x)) (fun i => if h : i < B.n + 1 then Ψ (e.symm ⟨i, h⟩) else 0)) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  rw [PiTools.lintegral_split (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun i => i = r) _ hF]
  have hin : ∀ zz : {i // i = r} → EuclideanSpace ℝ (Fin N),
      ∫⁻ w : {i // ¬ i = r} → EuclideanSpace ℝ (Fin N), ENNReal.ofReal
        (B.windowIntegrand c z (fun x => Ψl (el.symm x)) (fun i => if h : i < B.n + 1 then
          ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => EuclideanSpace ℝ (Fin N))
            (fun i => i = r)).symm (zz, w)) (e.symm ⟨i, h⟩) else 0))
        ∂(Measure.pi fun _ : {i // ¬ i = r} => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ENNReal.ofReal (gaussDens (B.composedPrecision c z) (zz ⟨r, rfl⟩ - B.composedMean z
        (fun x => Ψl (el.symm x)))) := by
    intro zz
    rw [← lintegral_window_nonroot sc pa lp r B e el hm he0 hsc hpar hleaf c z hc hz (zz ⟨r, rfl⟩) Ψl]
    refine lintegral_congr fun w => ?_
    congr 3
    funext i
    by_cases hi : i < B.n + 1
    · simp only [hi, dite_true]
      by_cases h : (e.symm ⟨i, hi⟩) = r
      · simp [MeasurableEquiv.piEquivPiSubtypeProd, h]
      · simp [MeasurableEquiv.piEquivPiSubtypeProd, h]
    · simp [hi]
  simp_rw [hin]
  let _ : Unique {i // i = r} := ⟨⟨⟨r, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  have hmp := measurePreserving_funUnique (volume : Measure (EuclideanSpace ℝ (Fin N))) {i // i = r}
  have hpos := B.composedPrecision_pos hm c z hz hc
  have hmeas : Measurable fun v : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal
      (gaussDens (B.composedPrecision c z) (v - B.composedMean z (fun x => Ψl (el.symm x)))) :=
    ENNReal.measurable_ofReal.comp ((GaussTree.continuous_gaussDens _).comp
      (continuous_id.sub continuous_const)).measurable
  have := hmp.lintegral_comp (f := fun v : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal
      (gaussDens (B.composedPrecision c z) (v - B.composedMean z (fun x => Ψl (el.symm x))))) hmeas
  simp only [MeasurableEquiv.funUnique_apply] at this
  have h2 := this.trans (lintegral_gaussDens_shift hpos (B.composedMean z
    (fun x => Ψl (el.symm x))))
  convert h2 using 2
  congr
  exact Subsingleton.elim _ _

end Tree

end Balaban.LargeField
