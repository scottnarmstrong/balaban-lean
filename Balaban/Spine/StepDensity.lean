/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.ClassStep
public import Balaban.LargeField.R.RRemovedChainRead
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The density of one renormalization step and its integral

The output density of the small-field step LF-3 (LFR Theorem IV.1.1) is the image of the input
under one renormalization step `S^{(k)} T^{(k)}` (P1 (1.10)–(1.11), P4 (4.1)):
`ρ'(ψ_{k+1}) = z^{N|T^{(k+1)}|} (T^{(k)} ρ)(z ψ_{k+1})`,
`(T^{(k)} ρ)(θ) = ∫ ∏_{y ∈ T^{(k+1)}} t_k(θ(y), (Qψ_k)(y)) ρ(ψ_k) dψ_k`, with the block average `Q`
(`stepAvg`) and the normalized Gaussian `t_k = gaussT` of constant `c = β_k a L^{d-2}`. The kernel is
the one of the quiet step data (`gaussProd`, `qCoarseK`), on the whole torus.

* `stepAvg`, `stepKernel`, `stepDensity`: the block average, the kernel and the density on the
  class carriers `𝒟[d, N, T, β, a, K, k]`;
* `integral_prod_gaussT_smul`: `z^{N|ι|} ∫ ∏_y t(z θ_y, w_y) dθ = 1` for every finite set of blocks;
* `integral_stepKernel_mul`: Fubini against the normalized kernel;
* `integralStep_stepDensity`: **`∫ ρ' = e^{-s |T^{(k+1)}_1|} ∫ ρ`** (LFR Theorem IV.1.1 (a), P1 (1.11))
  for every density whose sections are integrable; `s` is the vacuum normalization of the step.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7

namespace Balaban.RootFSpine

section Kernel

variable {N : ℕ}

/-- `∫ t_k(u, w) du = 1`. -/
theorem integral_gaussT_left {c : ℝ} (hc : 0 < c) (w : EuclideanSpace ℝ (Fin N)) :
    ∫ u, gaussT N c u w = 1 := by
  simp_rw [gaussT_eq_gaussDens N c _ w]
  rw [integral_sub_right_eq_self (fun u : EuclideanSpace ℝ (Fin N) => gaussDens c u) w,
    integral_gaussDens hc]

/-- `t_k(·, w)` is integrable. -/
theorem integrable_gaussT_left {c : ℝ} (hc : 0 < c) (w : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u w) := by
  by_contra hni
  have := integral_gaussT_left (N := N) hc w
  rw [integral_undef hni] at this
  exact zero_ne_one this

variable {ι : Type*} [Fintype ι]

/-- The product kernel over a finite set of blocks is normalized. -/
theorem integral_prod_gaussT {c : ℝ} (hc : 0 < c) (w : ι → EuclideanSpace ℝ (Fin N)) :
    ∫ θ : ι → EuclideanSpace ℝ (Fin N), ∏ y, gaussT N c (θ y) (w y)
      ∂(Measure.pi fun _ => volume) = 1 := by
  rw [integral_fintype_prod_eq_prod (f := fun y u => gaussT N c u (w y))]
  exact Finset.prod_eq_one fun y _ => integral_gaussT_left hc _

theorem integrable_prod_gaussT {c : ℝ} (hc : 0 < c) (w : ι → EuclideanSpace ℝ (Fin N)) :
    Integrable (fun θ : ι → EuclideanSpace ℝ (Fin N) => ∏ y, gaussT N c (θ y) (w y))
      (Measure.pi fun _ => volume) :=
  Integrable.fintype_prod (f := fun y u => gaussT N c u (w y))
    fun _ => integrable_gaussT_left hc _

theorem finrank_blockField :
    Module.finrank ℝ (ι → EuclideanSpace ℝ (Fin N)) = N * Fintype.card ι := by
  simp [Module.finrank_pi_fintype, mul_comm]

/-- With the field renormalization `z`: `z^{N|ι|} ∫ ∏_y t(z θ_y, w_y) dθ = 1`. -/
theorem integral_prod_gaussT_smul {c z : ℝ} (hc : 0 < c) (hz : 0 < z)
    (w : ι → EuclideanSpace ℝ (Fin N)) :
    z ^ (N * Fintype.card ι) * ∫ θ : ι → EuclideanSpace ℝ (Fin N),
      ∏ y, gaussT N c (z • θ y) (w y) ∂(Measure.pi fun _ => volume) = 1 := by
  have h := Measure.integral_comp_smul (μ := (Measure.pi fun _ : ι =>
    (volume : Measure (EuclideanSpace ℝ (Fin N)))))
    (fun θ : ι → EuclideanSpace ℝ (Fin N) => ∏ y, gaussT N c (θ y) (w y)) z
  simp only [Pi.smul_apply] at h
  rw [h, integral_prod_gaussT hc w, finrank_blockField, smul_eq_mul, mul_one,
    abs_of_pos (by positivity)]
  exact mul_inv_cancel₀ (by positivity)

theorem integrable_prod_gaussT_smul {c z : ℝ} (hc : 0 < c) (hz : 0 < z)
    (w : ι → EuclideanSpace ℝ (Fin N)) :
    Integrable (fun θ : ι → EuclideanSpace ℝ (Fin N) => ∏ y, gaussT N c (z • θ y) (w y))
      (Measure.pi fun _ => volume) := by
  have := (integrable_prod_gaussT (N := N) hc w).comp_smul hz.ne'
  simpa only [Pi.smul_apply] using this

end Kernel

section Fubini

variable {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Integrating a density against the normalized step kernel.** For an integrable `f` of the
old field `ψ`, a continuous linear coarse map `Q` and `c, z > 0`:
`∫ z^{N|ι|} (∫ ∏_y t(z θ_y, (Qψ)_y) f(ψ) dψ) dθ = ∫ f(ψ) dψ`. -/
theorem integral_stepKernel_mul {c z : ℝ} (hc : 0 < c) (hz : 0 < z)
    (Q : (κ → EuclideanSpace ℝ (Fin N)) → ι → EuclideanSpace ℝ (Fin N)) (hQ : Continuous Q)
    {f : (κ → EuclideanSpace ℝ (Fin N)) → ℂ} (hf : Integrable f (Measure.pi fun _ => volume)) :
    ∫ θ : ι → EuclideanSpace ℝ (Fin N), ((z ^ (N * Fintype.card ι) : ℝ) : ℂ) *
        ∫ ψ : κ → EuclideanSpace ℝ (Fin N), ((∏ y, gaussT N c (z • θ y) (Q ψ y) : ℝ) : ℂ) * f ψ
          ∂(Measure.pi fun _ => volume) ∂(Measure.pi fun _ => volume) =
      ∫ ψ, f ψ ∂(Measure.pi fun _ => volume) := by
  set μθ : Measure (ι → EuclideanSpace ℝ (Fin N)) := Measure.pi fun _ => volume
  set μψ : Measure (κ → EuclideanSpace ℝ (Fin N)) := Measure.pi fun _ => volume
  set D : ℝ := z ^ (N * Fintype.card ι)
  have hD : 0 < D := by positivity
  let F : (ι → EuclideanSpace ℝ (Fin N)) × (κ → EuclideanSpace ℝ (Fin N)) → ℂ := fun p =>
    ((D : ℝ) : ℂ) * (((∏ y, gaussT N c (z • p.1 y) (Q p.2 y) : ℝ) : ℂ) * f p.2)
  have hK : Continuous fun p : (ι → EuclideanSpace ℝ (Fin N)) × (κ → EuclideanSpace ℝ (Fin N)) =>
      ∏ y, gaussT N c (z • p.1 y) (Q p.2 y) := by
    refine continuous_finsetProd _ fun y _ => ?_
    unfold gaussT
    have h1 : Continuous fun p : (ι → EuclideanSpace ℝ (Fin N)) × (κ → EuclideanSpace ℝ (Fin N)) =>
        z • p.1 y := ((continuous_apply y).comp continuous_fst).const_smul z
    have h2 : Continuous fun p : (ι → EuclideanSpace ℝ (Fin N)) × (κ → EuclideanSpace ℝ (Fin N)) =>
        Q p.2 y := (continuous_apply y).comp (hQ.comp continuous_snd)
    fun_prop
  have hFm : AEStronglyMeasurable F (μθ.prod μψ) := by
    refine aestronglyMeasurable_const.mul ?_
    exact (Complex.continuous_ofReal.comp hK).aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_snd (μ := μθ))
  have hnorm : ∀ ψ, ∫ θ, ‖F (θ, ψ)‖ ∂μθ = ‖f ψ‖ := by
    intro ψ
    have hpt : ∀ θ : ι → EuclideanSpace ℝ (Fin N), ‖F (θ, ψ)‖ =
        (D * ∏ y, gaussT N c (z • θ y) (Q ψ y)) * ‖f ψ‖ := by
      intro θ
      simp only [F, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le]
      rw [Real.norm_of_nonneg (Finset.prod_nonneg fun y _ => gaussT_nonneg N c hc.le _ _)]
      ring
    simp_rw [hpt]
    rw [integral_mul_const, integral_const_mul, integral_prod_gaussT_smul hc hz, one_mul]
  have hFi : Integrable F (μθ.prod μψ) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Filter.Eventually.of_forall fun ψ => ?_, ?_⟩
    · exact ((integrable_prod_gaussT_smul hc hz (Q ψ)).ofReal.mul_const (f ψ)).const_mul _
    · simp_rw [hnorm]
      exact hf.norm
  have hinner : ∀ θ, ((D : ℝ) : ℂ) * ∫ ψ, ((∏ y, gaussT N c (z • θ y) (Q ψ y) : ℝ) : ℂ) * f ψ ∂μψ =
      ∫ ψ, F (θ, ψ) ∂μψ := fun θ => (integral_const_mul _ _).symm
  simp_rw [hinner]
  rw [integral_integral_swap (f := fun θ ψ => F (θ, ψ)) hFi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  have hc1 : ∫ θ, F (θ, ψ) ∂μθ =
      ((D * ∫ θ, ∏ y, gaussT N c (z • θ y) (Q ψ y) ∂μθ : ℝ) : ℂ) * f ψ := by
    simp only [F]
    rw [integral_const_mul, integral_mul_const, integral_complex_ofReal]
    push_cast
    ring
  simp only
  rw [hc1, integral_prod_gaussT_smul hc hz, Complex.ofReal_one, one_mul]

end Fubini

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ j, NeZero (n j)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- The block average `(Qψ_k)(y) = L^{-d} ∑_{y' ⊂ y} ψ_k(y')` of the field of the `k`-blocks over
the `k`-blocks of the `(k+1)`-block `y` (P1 (1.10); as `qCoarseK` for the variables of a history). -/
noncomputable def stepAvg (k : ℕ) (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (y : BlockAt S n M K (k + 1)) : EuclideanSpace ℝ (Fin N) :=
  ((S.L : ℝ) ^ S.d)⁻¹ • ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K k =>
      blockMap S.L (M * n K * S.L ^ (K - (k + 1))) y' = y), ψ y'

theorem continuous_stepAvg (k : ℕ) :
    Continuous (stepAvg (S := S) (n := n) (M := M) (K := K) (N := N) k) := by
  unfold stepAvg
  refine continuous_pi fun y => ?_
  exact Continuous.const_smul (c := ((S.L : ℝ) ^ S.d)⁻¹) (continuous_finsetSum _ fun y' _ =>
    continuous_apply (A := fun _ : BlockAt S n M K k => EuclideanSpace ℝ (Fin N)) y')

/-- **The kernel of `S^{(k)} T^{(k)}`** (P1 (1.10)–(1.11), LFR Theorem IV.1.1):
`∏_{y ∈ T^{(k+1)}} t_k(z ψ_{k+1}(y), (Qψ_k)(y))`, with the Gaussian `t_k = gaussT` of constant `c`
(`c = β_k a L^{d-2}`) and the field renormalization `z = z_{k+1}`. -/
noncomputable def stepKernel (k : ℕ) (c z : ℝ) (θ : BlockAt S n M K (k + 1) → EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∏ y, gaussT N c (z • θ y) (stepAvg k ψ y)

end Step

section Density

/-- **The density of one renormalization step** (LFR Theorem IV.1.1; P1 (1.11), P4 (4.1)), with the
vacuum normalization of the step (P4 (2.63); rulings R5, R5′):
`ρ'(ψ_{k+1}) = e^{-s |T^{(k+1)}_1|} z^{N|T^{(k+1)}|} (T^{(k)} ρ)(z ψ_{k+1})` on every torus of the
family, where `(T^{(k)} ρ)(θ) = ∫ ∏_y t_k(θ(y), (Qψ_k)(y)) ρ(ψ_k) dψ_k`, `t_k` is the Gaussian of
constant `c` and `|T^{(k+1)}_1| = (M n_K L^{K-k-1})^d` is the number of `(k+1)`-blocks. The constant `s` is the part of the
vacuum energy of the step that is put into the normalization, so that the vacuum constants of the flow
stay of order `log β_k` (the forward flow `E_{k+1} = L^d E_k + g_k` grows like `L^{dk}`,
`Fluctuation/VacuumFlow.lean`); `s = 0` is LFR's `ρ' = S^{(k)} T^{(k)} ρ`. -/
noncomputable def stepDensity (d N : ℕ) (T : Typing) (β a : ℝ) (K k : ℕ) [NeZero T.M] [NeZero T.L]
    (c z s : ℝ) (ρ : 𝒟[d, N, T, β, a, K, k]) : 𝒟[d, N, T, β, a, K, k + 1] :=
  fun nK _ θ g =>
    ((Real.exp (-(s * ((T.M * sides T.L K nK K * T.L ^ (K - (k + 1))) ^ d : ℕ))) : ℝ) : ℂ) *
      (((z ^ (N * Fintype.card (BlockAt 𝒮[d, T, β, a] (sides T.L K nK) T.M K (k + 1))) : ℝ) : ℂ) *
        ∫ ψ, ((stepKernel k c z θ ψ : ℝ) : ℂ) * ρ nK ψ g)

/-- **`∫ ρ' = e^{-s |T^{(k+1)}_1|} ∫ ρ`** (LFR Theorem IV.1.1 (a); P1 (1.11)): for `c, z > 0` and a
density whose sections are integrable on the unit `ℓ¹` ball, one step multiplies the integral by the
positive constant `e^{-s |T^{(k+1)}_1|}` of each torus, independent of the source `g`. -/
theorem integralStep_stepDensity {d N : ℕ} {T : Typing} {β a : ℝ} {K k : ℕ} [NeZero T.M]
    [NeZero T.L] {c z : ℝ} (s : ℝ) (hc : 0 < c) (hz : 0 < z) (ρ : 𝒟[d, N, T, β, a, K, k])
    (hint : ∀ (nK : ℕ) [NeZero nK]
      (g : GIdx 𝒮[d, T, β, a] (sides T.L K nK) T.M K N → ℂ), g ∈ l1Ball _ →
        Integrable (fun ψ => ρ nK ψ g)) :
    IntegralStep d N T β a K k ρ (stepDensity d N T β a K k c z s ρ) := by
  refine ⟨fun nK => Real.exp (-(s * ((T.M * sides T.L K nK K * T.L ^ (K - (k + 1))) ^ d : ℕ))),
    fun _ => Real.exp_pos _, fun nK _ g hg => ?_⟩
  simp only [stepDensity]
  rw [integral_const_mul]
  congr 1
  exact integral_stepKernel_mul hc hz (stepAvg k) (continuous_stepAvg k) (hint nK g hg)

end Density

end Balaban.RootFSpine
