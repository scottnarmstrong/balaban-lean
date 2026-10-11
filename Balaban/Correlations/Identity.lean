/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Clauses
public import Balaban.Model.Derivatives
public import Balaban.Model.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Constructions

/-!
# One- and two-point functions from the clauses of Root-F (CORRELATIONS.md, Proposition 1.4)

Conditional on the clauses of Root-F; consumed by the Root-C provider.  From
`RootFTorusClauses` (the identity for `log (Z(g)/Z(0))` on `∑ ∑ ‖g‖ < 1` and the analyticity of the
terms `T`) and the derivative identities `fderiv_logPartition_zero`,
`fderiv_fderiv_logPartition_zero` of `Balaban/Model/Derivatives.lean`:

* `onePoint_eq_of_clauses`: `⟨φ_i(x)⟩ = h_i + ∑_j ∑_X T_j(x, X; 0)_i`;
* `twoPointTruncated_eq_of_clauses`:
  `G_{ik}(x, y) = ∑_j ∑_X [D_{y,k} T_j(x, X; 0)_i + D_{x,i} T_j(y, X; 0)_k]`.
-/

@[expose] public section

namespace Balaban.Correlations

open Balaban Filter Topology

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_clm_mul_zero (A : E →L[ℂ] ℂ) {S : E → ℂ} (hS : DifferentiableAt ℂ S 0) (u : E) :
    fderiv ℂ (fun g => A g * S g) 0 u = A u * S 0 := by
  have h : HasFDerivAt (fun g => A g * S g) _ 0 :=
    (A.hasFDerivAt (x := (0 : E))).mul hS.hasFDerivAt
  rw [h.fderiv]
  simp [mul_comm]

theorem fderiv_fderiv_clm_mul_zero {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U)
    (A : E →L[ℂ] ℂ) {S : E → ℂ} (hS : AnalyticOnNhd ℂ S U) (u v : E) :
    fderiv ℂ (fun g => fderiv ℂ (fun g' => A g' * S g') g u) 0 v =
      A u * fderiv ℂ S 0 v + A v * fderiv ℂ S 0 u := by
  have hev : (fun g => fderiv ℂ (fun g' => A g' * S g') g u) =ᶠ[𝓝 0]
      fun g => A g * fderiv ℂ S g u + S g * A u := by
    filter_upwards [hU.mem_nhds h0] with g hg
    have hd := (hS g hg).differentiableAt
    have : HasFDerivAt (fun g' => A g' * S g') _ g :=
      (A.hasFDerivAt (x := g)).mul hd.hasFDerivAt
    rw [this.fderiv]
    simp
  rw [hev.fderiv_eq]
  have hW : DifferentiableAt ℂ (fun g => fderiv ℂ S g u) 0 :=
    ((hS 0 h0).fderiv.differentiableAt).clm_apply (differentiableAt_const u)
  have h1 : HasFDerivAt (fun g => A g * fderiv ℂ S g u) _ 0 :=
    (A.hasFDerivAt (x := (0 : E))).mul hW.hasFDerivAt
  have h2 := ((hS 0 h0).differentiableAt.hasFDerivAt).mul_const (A u)
  have h3 : HasFDerivAt (fun g => A g * fderiv ℂ S g u + S g * A u) _ 0 := h1.add h2
  rw [h3.fderiv]
  simp
  ring

theorem fderiv_sum_zero {ι : Type*} (s : Finset ι) {f : ι → E → ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) 0) (u : E) :
    fderiv ℂ (fun g => ∑ i ∈ s, f i g) 0 u = ∑ i ∈ s, fderiv ℂ (f i) 0 u := by
  rw [fderiv_fun_sum hf]
  simp

theorem fderiv_fderiv_sum_zero {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U) {ι : Type*}
    (s : Finset ι) {f : ι → E → ℂ} (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U) (u v : E) :
    fderiv ℂ (fun g => fderiv ℂ (fun g' => ∑ i ∈ s, f i g') g u) 0 v =
      ∑ i ∈ s, fderiv ℂ (fun g => fderiv ℂ (f i) g u) 0 v := by
  have hev : (fun g => fderiv ℂ (fun g' => ∑ i ∈ s, f i g') g u) =ᶠ[𝓝 0]
      fun g => ∑ i ∈ s, fderiv ℂ (f i) g u := by
    filter_upwards [hU.mem_nhds h0] with g hg
    rw [fderiv_fun_sum fun i hi => (hf i hi g hg).differentiableAt]
    simp
  rw [hev.fderiv_eq]
  have hW : ∀ i ∈ s, DifferentiableAt ℂ (fun g => fderiv ℂ (f i) g u) 0 := fun i hi =>
    ((hf i hi 0 h0).fderiv.differentiableAt).clm_apply (differentiableAt_const u)
  rw [fderiv_fun_sum hW]
  simp

end Calculus

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- The coordinate functional `g ↦ g x i`. -/
noncomputable def coordCLM (x : Torus d ℓ) (i : Fin N) : (Torus d ℓ → Fin N → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d ℓ => Fin N → ℂ) x)

omit [NeZero ℓ] in
@[simp] theorem coordCLM_apply (x : Torus d ℓ) (i : Fin N) (g : Torus d ℓ → Fin N → ℂ) :
    coordCLM x i g = g x i := rfl

theorem sum_sourceDelta (x₀ : Torus d ℓ) (i₀ : Fin N)
    (a : Torus d ℓ → Fin N → ℂ) :
    ∑ x, ∑ i, sourceDelta x₀ i₀ x i * a x i = a x₀ i₀ := by
  rw [Finset.sum_eq_single x₀ (fun x _ hx => by simp [sourceDelta, hx]) (by simp)]
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [sourceDelta, hi]) (by simp)]
  simp [sourceDelta]

theorem analyticOnNhd_component {U : Set (Torus d ℓ → Fin N → ℂ)}
    {f : (Torus d ℓ → Fin N → ℂ) → Fin N → ℂ} (hf : AnalyticOnNhd ℂ f U) (i : Fin N) :
    AnalyticOnNhd ℂ (fun g => f g i) U :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp_analyticOnNhd hf

/-- The right-hand side of the identity of Root-F. -/
noncomputable def idRhs (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) (T : RootFFamily d N)
    (ℓ : ℕ) [NeZero ℓ] (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  ∑ x, ∑ i, g x i * (h i : ℂ)
    + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
        g x i * T ℓ j x X g i

section Rhs

variable {L M : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf : ℕ} {κ c₉ δ : ℝ}
  {T : RootFFamily d N}

/-- The `i`th component of `T_j(x, X; ·)` as a function of the source. -/
def termComp (T : RootFFamily d N) (ℓ : ℕ) [NeZero ℓ] (j : ℕ) (x : Torus d ℓ)
    (X : Finset (Torus d ℓ)) (i : Fin N) (g : Torus d ℓ → Fin N → ℂ) : ℂ := T ℓ j x X g i

theorem termComp_analytic (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) (j : ℕ)
    (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (i : Fin N) :
    AnalyticOnNhd ℂ (termComp T ℓ j x X i) (sourceBall d N ℓ) :=
  analyticOnNhd_component (hcl.2.2.1 j x X) i

theorem logPartition_eventuallyEq (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) :
    logPartition d N ℓ β ν h =ᶠ[𝓝 0] idRhs h kf T ℓ :=
  Filter.eventually_of_mem (isOpen_sourceBall.mem_nhds zero_mem_sourceBall)
    fun g hg => hcl.2.2.2.2 g hg

theorem hasFDerivAt_idRhs (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) :
    HasFDerivAt (idRhs h kf T ℓ)
      (∑ x, ∑ i, (h i : ℂ) • coordCLM x i
        + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
            (g x i • fderiv ℂ (termComp T ℓ j x X i) g
              + termComp T ℓ j x X i g • coordCLM x i)) g := by
  refine HasFDerivAt.add ?_ ?_
  · refine HasFDerivAt.fun_sum fun x _ => HasFDerivAt.fun_sum fun i _ => ?_
    exact (coordCLM x i).hasFDerivAt.mul_const (h i : ℂ)
  · refine HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun x _ =>
      HasFDerivAt.fun_sum fun X _ => HasFDerivAt.fun_sum fun i _ => ?_
    exact (coordCLM x i).hasFDerivAt.mul ((termComp_analytic hcl j x X i g hg).differentiableAt.hasFDerivAt)

theorem fderiv_idRhs_apply (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) (u : Torus d ℓ → Fin N → ℂ) :
    fderiv ℂ (idRhs h kf T ℓ) g u =
      ∑ x, ∑ i, (h i : ℂ) * u x i
        + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
            (g x i * fderiv ℂ (termComp T ℓ j x X i) g u + termComp T ℓ j x X i g * u x i) := by
  rw [(hasFDerivAt_idRhs hcl hg).fderiv]
  simp

/-- Proposition 1.4 (one point): `⟨φ_i(x)⟩ = h_i + ∑_j ∑_X T_j(x, X; 0)_i`. -/
theorem onePoint_eq_of_clauses [NeZero N] (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ)
    (x : Torus d ℓ) (i : Fin N) :
    (onePoint d N ℓ β ν h x i : ℂ) =
      (h i : ℂ) + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ), T ℓ j x X 0 i := by
  rw [← fderiv_logPartition_zero β ν h x i, (logPartition_eventuallyEq hcl).fderiv_eq,
    fderiv_idRhs_apply hcl zero_mem_sourceBall]
  have h1 : ∑ x', ∑ i', (h i' : ℂ) * sourceDelta x i x' i' = h i := by
    simp_rw [mul_comm (h _ : ℂ)]
    exact sum_sourceDelta x i (fun _ i' => (h i' : ℂ))
  have h2 : ∀ j, ∑ x', ∑ X : Finset (Torus d ℓ), ∑ i',
      ((0 : Torus d ℓ → Fin N → ℂ) x' i' * fderiv ℂ (termComp T ℓ j x' X i') 0 (sourceDelta x i)
        + termComp T ℓ j x' X i' 0 * sourceDelta x i x' i') =
      ∑ X : Finset (Torus d ℓ), T ℓ j x X 0 i := by
    intro j
    rw [Finset.sum_comm]
    simp_rw [Pi.zero_apply, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun X _ => ?_
    simp_rw [mul_comm (termComp T ℓ j _ X _ 0)]
    exact sum_sourceDelta x i (fun x' i' => termComp T ℓ j x' X i' 0)
  rw [h1]
  simp_rw [h2]

/-- Proposition 1.4 (two points): `G_{ik}(x, y) = ∑_j ∑_X [D_{y,k} T_j(x, X; 0)_i +
D_{x,i} T_j(y, X; 0)_k]`. -/
theorem twoPointTruncated_eq_of_clauses [NeZero N]
    (hcl : RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) (x y : Torus d ℓ) (i k : Fin N) :
    (twoPointTruncated d N ℓ β ν h x y i k : ℂ) =
      ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ),
        (fderiv ℂ (termComp T ℓ j x X i) 0 (sourceDelta y k)
          + fderiv ℂ (termComp T ℓ j y X k) 0 (sourceDelta x i)) := by
  set u : Torus d ℓ → Fin N → ℂ := sourceDelta x i with hu
  set v : Torus d ℓ → Fin N → ℂ := sourceDelta y k with hv
  rw [← fderiv_fderiv_logPartition_zero β ν h x y i k]
  set E : (Torus d ℓ → Fin N → ℂ) → ℂ := fun g =>
    ∑ x', ∑ i', (h i' : ℂ) * u x' i'
      + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x', ∑ X : Finset (Torus d ℓ), ∑ i',
          (g x' i' * fderiv ℂ (termComp T ℓ j x' X i') g u + termComp T ℓ j x' X i' g * u x' i')
    with hE
  have e1 : (fun g => fderiv ℂ (logPartition d N ℓ β ν h) g u) =ᶠ[𝓝 0] E := by
    filter_upwards [(logPartition_eventuallyEq hcl).fderiv (𝕜 := ℂ),
      isOpen_sourceBall.mem_nhds zero_mem_sourceBall] with g hg hgb
    rw [hg]
    exact fderiv_idRhs_apply hcl hgb u
  rw [e1.fderiv_eq]
  have hW : ∀ j x' X i', DifferentiableAt ℂ (fun g => fderiv ℂ (termComp T ℓ j x' X i') g u) 0 :=
    fun j x' X i' =>
      ((termComp_analytic hcl j x' X i' 0 zero_mem_sourceBall).fderiv.differentiableAt).clm_apply
        (differentiableAt_const u)
  have hd : HasFDerivAt E
      (0 + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x', ∑ X : Finset (Torus d ℓ), ∑ i',
        (coordCLM x' i' 0 • fderiv ℂ (fun g => fderiv ℂ (termComp T ℓ j x' X i') g u) 0
          + fderiv ℂ (termComp T ℓ j x' X i') 0 u • coordCLM x' i'
          + (u x' i') • fderiv ℂ (termComp T ℓ j x' X i') 0)) 0 := by
    refine HasFDerivAt.add (hasFDerivAt_const _ _) ?_
    refine HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun x' _ =>
      HasFDerivAt.fun_sum fun X _ => HasFDerivAt.fun_sum fun i' _ => ?_
    refine HasFDerivAt.add ?_ ?_
    · exact (coordCLM x' i').hasFDerivAt.mul (hW j x' X i' |>.hasFDerivAt)
    · exact ((termComp_analytic hcl j x' X i' 0 zero_mem_sourceBall).differentiableAt.hasFDerivAt).mul_const
        (u x' i')
  rw [hd.fderiv]
  simp
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  have hA := sum_sourceDelta y k (fun x' i' => fderiv ℂ (termComp T ℓ j x' X i') 0 u)
  have hB := sum_sourceDelta x i (fun x' i' => fderiv ℂ (termComp T ℓ j x' X i') 0 v)
  simp only [Finset.sum_add_distrib]
  have hS1 : ∑ x', ∑ i', (fderiv ℂ (termComp T ℓ j x' X i') 0) u * v x' i' =
      fderiv ℂ (termComp T ℓ j y X k) 0 u := by
    rw [← hA]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hS1, hB, add_comm]

end Rhs

end Balaban.Correlations
