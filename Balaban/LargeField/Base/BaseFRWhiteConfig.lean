/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartComponent

/-!
# Transport of a real whitening matrix to a linear equivalence of the configuration space

Let `K` be the matrix of the chart form `gaussForm e Hα` in the coordinate basis of
`Config ι N`, and let `W_c`, `D_c` be complex matrices indexed by a finite type `κ` identified
with the coordinates by `c : κ ≃ Σ _ : ι, Fin N`, with `W_c` of real entries and invertible, such
that `⟨W_c ψ, A_c W_c ψ⟩ = ⟨ψ, ψ⟩ + ⟨ψ, D_c ψ⟩` for all complex `ψ`, where `A_c` is the
complexification of `K` (the bilinear whitening identity of `baseWhite_bilinear`). Then
`exists_config_whitening` produces a real linear equivalence `W` of `Config ι N` with
`|det W| = |det W_c|` and
`⟨Wφ, gaussForm(Wφ)⟩ = ⟨φ, φ⟩ + Re ⟨ψ_φ, D_c ψ_φ⟩` for every real configuration `φ`
(`ψ_φ = φ ∘ c`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.LargeField.Base Matrix

section Transport

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The standard coordinate basis of the configuration space. -/
noncomputable abbrev configBasis (ι : Type*) [Fintype ι] (N : ℕ) :=
  Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)

theorem configBasis_repr (φ : Config ι N) (a : Σ _ : ι, Fin N) :
    (configBasis ι N).repr φ a = φ a.1 a.2 := by
  simp [configBasis]

theorem cinner_eq_repr_dot (u v : Config ι N) :
    cinner u v = ((configBasis ι N).repr u) ⬝ᵥ ((configBasis ι N).repr v) := by
  simp [cinner, configBasis, dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    Finset.sum_sigma', mul_comm]

theorem repr_toLin (M : Matrix (Σ _ : ι, Fin N) (Σ _ : ι, Fin N) ℝ) (φ : Config ι N) :
    ⇑((configBasis ι N).repr (Matrix.toLin (configBasis ι N) (configBasis ι N) M φ)) =
      M *ᵥ ⇑((configBasis ι N).repr φ) := by
  ext a
  rw [Matrix.toLin_apply]
  simp only [configBasis, Matrix.mulVec, dotProduct]
  simp
  rw [Finset.sum_eq_single a]
  · simp
  · rintro ⟨b1, b2⟩ - hb
    obtain ⟨a1, a2⟩ := a
    by_cases h1 : b1 = a1
    · subst h1
      have h2 : b2 ≠ a2 := fun h => hb (by rw [h])
      simp [h2]
    · simp [h1]
  · simp

local notation "𝔅" => configBasis ι N

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The whitening matrix as a linear equivalence of the configuration space.** -/
theorem exists_config_whitening (e : Config ι N) (Hα : Config ι N →ₗ[ℝ] Config ι N)
    (c : κ ≃ (Σ _ : ι, Fin N)) (Wc Dc Ac : Matrix κ κ ℂ)
    (hAc : ∀ p q, Ac p q =
      ((LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e Hα) (c p) (c q) :
        ℝ) : ℂ))
    (hWim : ∀ p q, (Wc p q).im = 0) (hdet : Wc.det ≠ 0)
    (hbil : ∀ ψ : κ → ℂ, (Wc *ᵥ ψ) ⬝ᵥ (Ac *ᵥ (Wc *ᵥ ψ)) = ψ ⬝ᵥ ψ + ψ ⬝ᵥ (Dc *ᵥ ψ)) :
    ∃ W : Config ι N ≃ₗ[ℝ] Config ι N,
      |LinearMap.det (W : Config ι N →ₗ[ℝ] Config ι N)| = ‖Wc.det‖ ∧
      ∀ φ : Config ι N,
        cinner (W φ) (gaussForm e Hα (W φ)) = cinner φ φ +
          ((fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ)) ⬝ᵥ
            (Dc *ᵥ fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ))).re := by
  classical
  set K := LinearMap.toMatrix 𝔅 𝔅 (gaussForm e Hα) with hK
  let Wr : Matrix (Σ _ : ι, Fin N) (Σ _ : ι, Fin N) ℝ := fun a b =>
    (Wc (c.symm a) (c.symm b)).re
  have hWc : ∀ p q, Wc p q = ((Wr (c p) (c q) : ℝ) : ℂ) := fun p q => by
    apply Complex.ext
    · simp [Wr]
    · simp [Wr, hWim p q]
  have hdetR : ((Wr.det : ℝ) : ℂ) = Wc.det := by
    have h1 : (algebraMap ℝ ℂ).mapMatrix Wr = Wc.submatrix c.symm c.symm := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
      rw [hWc]
      simp
    have h2 := RingHom.map_det (algebraMap ℝ ℂ) Wr
    rw [h1, Matrix.det_submatrix_equiv_self] at h2
    exact h2
  have hunit : IsUnit (LinearMap.toMatrix 𝔅 𝔅 (Matrix.toLin 𝔅 𝔅 Wr)).det := by
    rw [LinearMap.toMatrix_toLin, isUnit_iff_ne_zero]
    intro h0
    apply hdet
    rw [← hdetR, h0]; simp
  refine ⟨LinearEquiv.ofIsUnitDet hunit, ?_, ?_⟩
  · rw [LinearEquiv.coe_ofIsUnitDet, LinearMap.det_toLin, ← hdetR, Complex.norm_real,
      Real.norm_eq_abs]
  · intro φ
    have hW : ∀ u, (LinearEquiv.ofIsUnitDet hunit) u = Matrix.toLin 𝔅 𝔅 Wr u := fun u => rfl
    set x : (Σ _ : ι, Fin N) → ℝ := ⇑((configBasis ι N).repr φ) with hx
    have hrep : (configBasis ι N).repr ((LinearEquiv.ofIsUnitDet hunit) φ) = Wr *ᵥ x := by
      rw [hW, repr_toLin]
    have hG : (configBasis ι N).repr (gaussForm e Hα ((LinearEquiv.ofIsUnitDet hunit) φ)) =
        K *ᵥ (Wr *ᵥ x) := by
      have h : gaussForm e Hα ((LinearEquiv.ofIsUnitDet hunit) φ) =
          Matrix.toLin 𝔅 𝔅 K ((LinearEquiv.ofIsUnitDet hunit) φ) := by
        rw [hK, Matrix.toLin_toMatrix]
      rw [h, repr_toLin, hrep]
    set y := Wr *ᵥ x with hy
    have hq : cinner ((LinearEquiv.ofIsUnitDet hunit) φ)
        (gaussForm e Hα ((LinearEquiv.ofIsUnitDet hunit) φ)) = y ⬝ᵥ (K *ᵥ y) := by
      rw [cinner_eq_repr_dot, hG, hrep]
    have hxx : cinner φ φ = x ⬝ᵥ x := cinner_eq_repr_dot φ φ
    set ψ : κ → ℂ := fun p => ((φ (c p).1 (c p).2 : ℝ) : ℂ) with hψdef
    have hψ : ∀ p, ψ p = ((x (c p) : ℝ) : ℂ) := fun p => by
      rw [hx]; simp only [hψdef]; exact congrArg Complex.ofReal (configBasis_repr φ (c p)).symm
    have hWψ : Wc *ᵥ ψ = fun p => ((y (c p) : ℝ) : ℂ) := by
      ext p
      have h := Equiv.sum_comp c (fun b => Wr (c p) b * x b)
      simp only [Matrix.mulVec, dotProduct, hWc, hψ, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
        hy]
      exact congrArg _ h
    have hAψ : Ac *ᵥ (fun p => ((y (c p) : ℝ) : ℂ)) = fun p => (((K *ᵥ y) (c p) : ℝ) : ℂ) := by
      ext p
      have h := Equiv.sum_comp c (fun b => K (c p) b * y b)
      simp only [Matrix.mulVec, dotProduct, hAc, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
      exact congrArg _ h
    have hL : (Wc *ᵥ ψ) ⬝ᵥ (Ac *ᵥ (Wc *ᵥ ψ)) = ((y ⬝ᵥ (K *ᵥ y) : ℝ) : ℂ) := by
      rw [hWψ, hAψ]
      have h := Equiv.sum_comp c (fun b => y b * (K *ᵥ y) b)
      simp only [dotProduct, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
      exact congrArg _ h
    have hR : ψ ⬝ᵥ ψ = ((x ⬝ᵥ x : ℝ) : ℂ) := by
      have h := Equiv.sum_comp c (fun b => x b * x b)
      simp only [dotProduct, hψ, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
      exact congrArg _ h
    have h := hbil ψ
    rw [hL, hR] at h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    rw [hq, hxx]
    exact hre

end Transport

end Balaban.LargeField
