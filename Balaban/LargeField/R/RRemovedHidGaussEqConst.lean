/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidGaussEq
public import Balaban.LargeField.R.CancelIdentity

/-!
# The composed Gaussian densities are `const^♮ e^{-𝒢^♮}` (W938)

`notes/phase1/LF4R-PLAN.md` §8.5.  `constNat_mul_exp_neg_gaussNat`: for real data, the product over the `k`-blocks
`z ∈ Zb` of the Gaussian densities `g_{β_k a^♮_z}(ψ_k(z) - 𝒬^♮_z ψ̃)` is `constNat · e^{-Re 𝒢^♮}`
(`CancelIdentity.lean`).  `prod_roots_eq_constNat_exp`: the product of `lintegral_gauss_coords_eq` over the fixed
roots, given the identification (hypotheses `hP`, `hμ`) of the composed precision and mean of the block tree of
each root with `β_k a^♮_z` and `ψ_k(z) - 𝒬^♮_z ψ̃`, is `constNat · e^{-Re 𝒢^♮}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem constNat_mul_exp_neg_gaussNat (G : GeneratingSet d L N₀ k ϱ) (ϖ : ℕ → ℝ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) {βk : ℝ} (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hreal : ∀ z ∈ Zb, ∀ i, (ψk z i - compMeanT G ϖ Ψ z i).im = 0) :
    constNat N βk aN Zb * Real.exp (-(gaussNat G ϖ Ψ βk aN ψk Zb).re) =
      ∏ z ∈ Zb, gaussDens (βk * aN z)
        (WithLp.toLp 2 fun i => (ψk z i - compMeanT G ϖ Ψ z i).re :
          EuclideanSpace ℝ (Fin N)) := by
  have hre : (gaussNat G ϖ Ψ βk aN ψk Zb).re = ∑ z ∈ Zb, 1 / 2 * (βk * aN z) *
      ∑ i, ((ψk z i - compMeanT G ϖ Ψ z i).re) ^ 2 := by
    unfold gaussNat
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have h1 : (1 / 2 : ℂ) * (βk : ℂ) * (aN z : ℂ) = ((1 / 2 * (βk * aN z) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, Complex.re_ofReal_mul]
    congr 1
    unfold dotC
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := hreal z hz i
    rw [Complex.mul_re, h2]
    ring
  rw [hre, ← Finset.sum_neg_distrib, Real.exp_sum]
  unfold constNat
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z hz => ?_
  unfold gaussDens
  rw [finrank_euclideanSpace_fin, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 2
  ring


open Classical in
/-- **The product of the composed Gaussian densities over the fixed roots** of `lintegral_gauss_coords_eq`
(the indices `r` with `Fx r`, in bijection `zb` with the `k`-blocks `Zb`), with the identification `hP`, `hμ` of
the precision and the centred value of each root with `β_k a^♮_z` and `ψ_k(z) - 𝒬^♮_z ψ̃`, is
`const^♮ e^{-Re 𝒢^♮}`. -/
theorem prod_roots_eq_constNat_exp {ρ : Type*} [Fintype ρ] (Fx : ρ → Prop) (Pt : ρ → ℝ)
    (vt : ρ → EuclideanSpace ℝ (Fin N)) (G : GeneratingSet d L N₀ k ϱ) (ϖ : ℕ → ℝ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) {βk : ℝ} (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hreal : ∀ z ∈ Zb, ∀ i, (ψk z i - compMeanT G ϖ Ψ z i).im = 0)
    (hpos : ∀ z ∈ Zb, 0 < βk * aN z) (zb : {r : ρ // Fx r} ≃ ↥Zb)
    (hP : ∀ r : {r : ρ // Fx r}, Pt r.1 = βk * aN (zb r).1)
    (hμ : ∀ r : {r : ρ // Fx r}, vt r.1 =
      (WithLp.toLp 2 fun i => (ψk (zb r).1 i - compMeanT G ϖ Ψ (zb r).1 i).re :
        EuclideanSpace ℝ (Fin N))) :
    ∏ r : ρ, (if Fx r then ENNReal.ofReal (gaussDens (Pt r) (vt r)) else 1) =
      ENNReal.ofReal (constNat N βk aN Zb * Real.exp (-(gaussNat G ϖ Ψ βk aN ψk Zb).re)) := by
  have hnn : ∀ z ∈ Zb, 0 ≤ gaussDens (βk * aN z)
      (WithLp.toLp 2 fun i => (ψk z i - compMeanT G ϖ Ψ z i).re : EuclideanSpace ℝ (Fin N)) :=
    fun z hz => (gaussDens_pos (hpos z hz) _).le
  rw [constNat_mul_exp_neg_gaussNat G ϖ Ψ aN ψk Zb hreal, ENNReal.ofReal_prod_of_nonneg hnn]
  have h1 : ∏ r : ρ, (if Fx r then ENNReal.ofReal (gaussDens (Pt r) (vt r)) else 1) =
      ∏ r : {r : ρ // Fx r}, ENNReal.ofReal (gaussDens (Pt r.1) (vt r.1)) := by
    rw [← Finset.prod_filter]
    exact Finset.prod_subtype (Finset.univ.filter Fx) (by simp)
      (fun r => ENNReal.ofReal (gaussDens (Pt r) (vt r)))
  rw [h1, ← Finset.prod_coe_sort Zb]
  refine Fintype.prod_equiv zb _ _ fun r => ?_
  rw [hP r, hμ r]

end Balaban.LargeField.ActionConv
