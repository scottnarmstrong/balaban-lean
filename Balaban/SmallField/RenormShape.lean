/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormRot
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Consequences of the rotation invariance at the reference point

For a polymer `X` and `f = 𝓔(0, X; ·)`, analytic on the polydisc around the reference point `P₀`
and invariant under the admissible rotations (`rot_inv`):

* `fderiv_eq_of_fix`, `D2_eq_of_fix`: a rotation fixing `P₀` leaves `f'(P₀)` and `f''(P₀)`
  invariant;
* the reflections `x_j ↦ -x_j` (`j ≠ i₀`) kill the transverse first derivatives, the mixed
  second derivatives, and the swap of two transverse coordinates identifies the diagonal ones;
* the Ward identity (WI) of the rotation in the plane `(i₀, i₁)`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section Fix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Invariance of `f` under a continuous linear `S` on a neighbourhood of a fixed point `P`
gives invariance of the first and second derivatives at `P`. -/
theorem deriv_inv_of_fix {f : E → ℂ} {P : E} {U : Set E} (hU : IsOpen U) (hP : P ∈ U)
    (hana : AnalyticOnNhd ℂ f U) (S : E →L[ℂ] E) (hSP : S P = P)
    (hinv : ∀ c ∈ U, S c ∈ U → f (S c) = f c) :
    (∀ v, fderiv ℂ f P (S v) = fderiv ℂ f P v) ∧
    (∀ v w, D2 f P (S v) (S w) = D2 f P v w) := by
  set V : Set E := U ∩ S ⁻¹' U with hV
  have hVo : IsOpen V := hU.inter (hU.preimage S.continuous)
  have hVP : P ∈ V := ⟨hP, by simpa [hSP] using hP⟩
  have hfd : ∀ c ∈ V, DifferentiableAt ℂ f (S c) := fun c hc => (hana _ hc.2).differentiableAt
  have hfd' : ∀ c ∈ V, DifferentiableAt ℂ f c := fun c hc => (hana _ hc.1).differentiableAt
  -- pointwise: f' (S c) ∘ S = f' c
  have key : ∀ c ∈ V, ∀ v, fderiv ℂ f (S c) (S v) = fderiv ℂ f c v := by
    intro c hc v
    have h1 : (f ∘ S) =ᶠ[nhds c] f := by
      filter_upwards [hVo.mem_nhds hc] with y hy using hinv y hy.1 hy.2
    have h2 : HasFDerivAt (f ∘ S) ((fderiv ℂ f (S c)).comp S) c :=
      (hfd c hc).hasFDerivAt.comp c S.hasFDerivAt
    have h3 := h2.fderiv
    rw [h1.fderiv_eq] at h3
    rw [h3]; rfl
  refine ⟨fun v => by simpa [hSP] using key P hVP v, fun w v => ?_⟩
  -- second derivative
  have hg : (fun c => fderiv ℂ f (S c) (S v)) =ᶠ[nhds P] fun c => fderiv ℂ f c v := by
    filter_upwards [hVo.mem_nhds hVP] with c hc using key c hc v
  have hd2 : DifferentiableAt ℂ (fderiv ℂ f) P := (hana.fderiv_of_isOpen hU P hP).differentiableAt
  have hd2' : DifferentiableAt ℂ (fderiv ℂ f) (S P) := by rwa [hSP]
  have hL : HasFDerivAt (fun c => fderiv ℂ f (S c) (S v))
      ((ContinuousLinearMap.apply ℂ ℂ (S v)).comp ((fderiv ℂ (fderiv ℂ f) (S P)).comp S)) P := by
    have h1 : HasFDerivAt (fun c => fderiv ℂ f (S c)) ((fderiv ℂ (fderiv ℂ f) (S P)).comp S) P :=
      hd2'.hasFDerivAt.comp P S.hasFDerivAt
    exact (ContinuousLinearMap.apply ℂ ℂ (S v)).hasFDerivAt.comp P h1
  have hR : HasFDerivAt (fun c => fderiv ℂ f c v)
      ((ContinuousLinearMap.apply ℂ ℂ v).comp (fderiv ℂ (fderiv ℂ f) P)) P :=
    (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp P hd2.hasFDerivAt
  have := hg.fderiv_eq (𝕜 := ℂ)
  rw [hL.fderiv, hR.fderiv] at this
  have h := congrArg (fun L => L w) this
  simpa [D2, hSP] using h

end Fix

section Basis

variable (X : Finset (Site d))

theorem single_inl_eq_pack (x : ↥X) (k : Fin N) :
    (Pi.single (Sum.inl (x, k)) (1 : ℂ) : Cfg d N X) =
      pack X (fun x' => if x' = x.1 then (Pi.single k 1 : Spin N) else 0) 0 := by
  ext (⟨x', i⟩ | i)
  · by_cases h : x' = x <;> by_cases hi : i = k <;>
      simp [pack, h, hi]
  · simp [pack]

theorem single_inr_eq_pack (k : Fin N) :
    (Pi.single (Sum.inr k) (1 : ℂ) : Cfg d N X) =
      pack X (fun _ => 0) (Pi.single k 1 : Spin N) := by
  ext (⟨x', i⟩ | i)
  · simp [pack]
  · by_cases hi : i = k <;> simp [pack, hi]

/-- If the matrix `R` carries `e_j` to `s • e_k`, then it carries the basis vector `(x, j)` to
`s` times the basis vector `(x, k)`. -/
theorem rotCfgL_single_inl_of (R : Matrix (Fin N) (Fin N) ℂ) (x : ↥X) (j k : Fin N) (s : ℂ)
    (h : R.mulVec (Pi.single j 1) = s • (Pi.single k 1 : Spin N)) :
    rotCfgL R X (Pi.single (Sum.inl (x, j)) 1) = s • Pi.single (Sum.inl (x, k)) 1 := by
  rw [single_inl_eq_pack, single_inl_eq_pack, rotCfgL_pack]
  ext (⟨x', i⟩ | i)
  · by_cases hx : x' = x
    · simp [pack, hx, h]
    · simp [pack, hx]
  · simp [pack]

theorem rotCfgL_single_inr_of (R : Matrix (Fin N) (Fin N) ℂ) (j k : Fin N) (s : ℂ)
    (h : R.mulVec (Pi.single j 1) = s • (Pi.single k 1 : Spin N)) :
    rotCfgL R X (Pi.single (Sum.inr j) 1) = s • Pi.single (Sum.inr k) 1 := by
  rw [single_inr_eq_pack, single_inr_eq_pack, rotCfgL_pack]
  ext (⟨x', i⟩ | i)
  · simp [pack]
  · simp [pack, h]

theorem rotCfgL_refPt (i₀ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (h : R.mulVec (Pi.single i₀ 1) = (Pi.single i₀ 1 : Spin N)) :
    rotCfgL R X (refPt i₀ ν X) = refPt i₀ ν X := by
  unfold refPt
  rw [rotCfgL_pack, Matrix.mulVec_smul, h]

theorem pack_e1_eq (i₁ : Fin N) (ν : ℝ) :
    pack X (fun _ => (Pi.single i₁ 1 : Spin N)) ((ν : ℂ) • (Pi.single i₁ 1 : Spin N)) =
      (∑ x : ↥X, (Pi.single (Sum.inl (x, i₁)) (1 : ℂ) : Cfg d N X)) +
        (ν : ℂ) • (Pi.single (Sum.inr i₁) (1 : ℂ) : Cfg d N X) := by
  ext (⟨x, i⟩ | i)
  · simp only [pack, Sum.elim_inl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = i₁ <;> simp [Pi.single_apply, hi]
  · by_cases hi : i = i₁ <;> simp [pack, Pi.single_apply, hi]

end Basis

theorem flipMat_mulVec_ne (j i : Fin N) (hji : j ≠ i) (x : ℂ) :
    (flipMat j).mulVec (Pi.single i x) = Pi.single i x := by
  ext l
  have h1 : (flipMat j).mulVec (Pi.single i x) l = flipMat j l i * x := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  have h2 := flipMat_mul_apply j (1 : Matrix (Fin N) (Fin N) ℂ) l i
  rw [mul_one] at h2
  by_cases hl : l = j
  · subst hl; simp [hji] at h2; simp [h2, hji]
  · simp only [hl, ↓reduceIte] at h2
    rw [h2]; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem planeRot_mulVec_first (i k : Fin N) (hik : i ≠ k) :
    (planeRot i k 0 1).mulVec (Pi.single i 1) = (1 : ℂ) • (Pi.single k 1 : Spin N) := by
  have hki : k ≠ i := hik.symm
  ext a
  simp only [Matrix.mulVec, dotProduct, planeRot, planeProj, planeGen, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply, Pi.single_apply,
    smul_eq_mul]
  rcases eq_or_ne a i with rfl | hai <;> rcases eq_or_ne a k with rfl | hak <;>
    simp_all [eq_comm]

theorem planeRot_mulVec_other (i k l : Fin N) (hik : i ≠ k) (hil : l ≠ i) (hkl : l ≠ k) :
    (planeRot i k 0 1).mulVec (Pi.single l 1) = (1 : ℂ) • (Pi.single l 1 : Spin N) := by
  have hki : k ≠ i := hik.symm
  ext a
  simp only [Matrix.mulVec, dotProduct, planeRot, planeProj, planeGen, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply, Pi.single_apply,
    smul_eq_mul]
  rcases eq_or_ne a i with rfl | hai <;> rcases eq_or_ne a k with rfl | hak <;>
    simp_all [eq_comm, Pi.single_apply]

theorem rotCfgL_add (R S : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X) :
    rotCfgL (R + S) X c = rotCfgL R X c + rotCfgL S X c := by
  ext (p | i) <;> simp [rotCfgL_apply_inl, rotCfgL_apply_inr, add_mul, Finset.sum_add_distrib]

theorem rotCfgL_smul (t : ℂ) (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X) :
    rotCfgL (t • R) X c = t • rotCfgL R X c := by
  ext (p | i) <;> simp [rotCfgL_apply_inl, rotCfgL_apply_inr, Finset.mul_sum, mul_assoc]

theorem planeGen_mulVec_first (i k : Fin N) (hik : i ≠ k) :
    (planeGen i k).mulVec (Pi.single i 1) = (1 : ℂ) • (Pi.single k 1 : Spin N) := by
  have hki : k ≠ i := hik.symm
  ext a
  simp only [Matrix.mulVec, dotProduct, planeGen, Matrix.sub_apply, Matrix.single_apply,
    Pi.single_apply]
  rcases eq_or_ne a i with rfl | hai <;> rcases eq_or_ne a k with rfl | hak <;>
    simp_all [eq_comm]

theorem planeGen_mulVec_second (i k : Fin N) (hik : i ≠ k) :
    (planeGen i k).mulVec (Pi.single k 1) = (-1 : ℂ) • (Pi.single i 1 : Spin N) := by
  have hki : k ≠ i := hik.symm
  ext a
  simp only [Matrix.mulVec, dotProduct, planeGen, Matrix.sub_apply, Matrix.single_apply,
    Pi.single_apply]
  rcases eq_or_ne a i with rfl | hai <;> rcases eq_or_ne a k with rfl | hak <;>
    simp_all [eq_comm]

section Local



variable (i₀ : Fin N) (ν ρ : ℝ) (X : Finset (Site d)) (f : Cfg d N X → ℂ)

/-- The hypotheses on a single term used in this file: analyticity on the analyticity domain and
invariance under the admissible rotations. -/
structure TermOK : Prop where
  rho_pos : 0 < ρ
  analytic : AnalyticOnNhd ℂ f (Tube i₀ ν ρ X)
  inv : ∀ c ∈ Tube i₀ ν ρ X, ∀ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R → EntryBd N R →
    rotCfgL R X c ∈ Tube i₀ ν ρ X → f (rotCfgL R X c) = f c

variable {i₀ ν ρ X f}

theorem TermOK.analytic_ball (h : TermOK i₀ ν ρ X f) :
    AnalyticOnNhd ℂ f (ball (refPt i₀ ν X) ρ) :=
  h.analytic.mono (ball_subset_tube i₀ ν ρ X)

/-- Derivatives at the reference point are invariant under rotations fixing it. -/
theorem TermOK.deriv_inv (h : TermOK i₀ ν ρ X f) (S : Matrix (Fin N) (Fin N) ℂ) (hS : IsOrth S)
    (hSb : EntryBd N S) (hfix : rotCfgL S X (refPt i₀ ν X) = refPt i₀ ν X) :
    (∀ v, fderiv ℂ f (refPt i₀ ν X) (rotCfgL S X v) = fderiv ℂ f (refPt i₀ ν X) v) ∧
    (∀ v w, D2 f (refPt i₀ ν X) (rotCfgL S X v) (rotCfgL S X w) =
      D2 f (refPt i₀ ν X) v w) := by
  have := deriv_inv_of_fix (f := f) (P := refPt i₀ ν X) (U := ball (refPt i₀ ν X) ρ)
    isOpen_ball (mem_ball_self h.rho_pos) h.analytic_ball
    (LinearMap.toContinuousLinearMap (rotCfgL S X)) hfix
    (fun c hc hSc => h.inv c (ball_subset_tube i₀ ν ρ X hc) S hS hSb
      (ball_subset_tube i₀ ν ρ X hSc))
  exact this

variable (hf : TermOK i₀ ν ρ X f)
include hf

theorem TermOK.fderiv_inl_transverse {j : Fin N} (hj : j ≠ i₀) (x : ↥X) :
    fderiv ℂ f (refPt i₀ ν X) (Pi.single (Sum.inl (x, j)) 1) = 0 := by
  have hfix := rotCfgL_refPt (X := X) i₀ ν (flipMat j) (flipMat_mulVec_ne j i₀ hj 1)
  have h1 := (hf.deriv_inv (flipMat j) (flipMat_isOrth j) (entryBd_flipMat j) hfix).1
    (Pi.single (Sum.inl (x, j)) 1)
  rw [rotCfgL_single_inl_of X (flipMat j) x j j (-1)
    (by rw [flipMat_mulVec_single]; simp)] at h1
  rw [map_smul, smul_eq_mul] at h1
  linear_combination (-1 / 2 : ℂ) * h1

theorem TermOK.fderiv_inr_transverse {j : Fin N} (hj : j ≠ i₀) :
    fderiv ℂ f (refPt i₀ ν X) (Pi.single (Sum.inr j) 1) = 0 := by
  have hfix := rotCfgL_refPt (X := X) i₀ ν (flipMat j) (flipMat_mulVec_ne j i₀ hj 1)
  have h1 := (hf.deriv_inv (flipMat j) (flipMat_isOrth j) (entryBd_flipMat j) hfix).1
    (Pi.single (Sum.inr j) 1)
  rw [rotCfgL_single_inr_of X (flipMat j) j j (-1)
    (by rw [flipMat_mulVec_single]; simp)] at h1
  rw [map_smul, smul_eq_mul] at h1
  linear_combination (-1 / 2 : ℂ) * h1

theorem TermOK.D2_inl_inl_ne {j k : Fin N} (hj : j ≠ i₀) (hjk : j ≠ k) (x x' : ↥X) :
    D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, j)) 1) (Pi.single (Sum.inl (x', k)) 1) = 0 := by
  have hfix := rotCfgL_refPt (X := X) i₀ ν (flipMat j) (flipMat_mulVec_ne j i₀ hj 1)
  have h1 := (hf.deriv_inv (flipMat j) (flipMat_isOrth j) (entryBd_flipMat j) hfix).2
    (Pi.single (Sum.inl (x, j)) 1) (Pi.single (Sum.inl (x', k)) 1)
  rw [rotCfgL_single_inl_of X (flipMat j) x j j (-1) (by rw [flipMat_mulVec_single]; simp),
    rotCfgL_single_inl_of X (flipMat j) x' k k 1
      (by rw [flipMat_mulVec_ne j k hjk]; simp), D2_smul_left, D2_smul_right] at h1
  linear_combination (-1 / 2 : ℂ) * h1

theorem TermOK.D2_swap {i₁ j : Fin N} (hne : i₁ ≠ i₀) (hj : j ≠ i₀) (x x' : ↥X) :
    D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, j)) 1) (Pi.single (Sum.inl (x', j)) 1) =
      D2 f (refPt i₀ ν X) (Pi.single (Sum.inl (x, i₁)) 1) (Pi.single (Sum.inl (x', i₁)) 1) := by
  by_cases hji : j = i₁
  · rw [hji]
  have hji' : j ≠ i₁ := hji
  have hfix := rotCfgL_refPt (X := X) i₀ ν (planeRot j i₁ 0 1)
    (by rw [planeRot_mulVec_other j i₁ i₀ hji' hj.symm hne.symm]; simp)
  have hor : IsOrth (planeRot j i₁ 0 1) := planeRot_isOrth j i₁ hji' 0 1 (by norm_num)
  have hbd : EntryBd N (planeRot j i₁ 0 1) := entryBd_planeRot j i₁ 0 1 (by norm_num) (by norm_num)
  have h1 := (hf.deriv_inv _ hor hbd hfix).2
    (Pi.single (Sum.inl (x, j)) 1) (Pi.single (Sum.inl (x', j)) 1)
  rw [rotCfgL_single_inl_of X _ x j i₁ 1 (planeRot_mulVec_first j i₁ hji'),
    rotCfgL_single_inl_of X _ x' j i₁ 1 (planeRot_mulVec_first j i₁ hji'), D2_smul_left,
    D2_smul_right] at h1
  simpa using h1.symm

theorem TermOK.lie {i₁ : Fin N} (hi : i₁ ≠ i₀) {c : Cfg d N X} (hc : c ∈ ball (refPt i₀ ν X) ρ) :
    fderiv ℂ f c (rotCfgL (planeGen i₀ i₁) X c) = 0 := by
  have hne : i₀ ≠ i₁ := hi.symm
  set J := planeGen i₀ i₁ with hJ
  set Pm := planeProj i₀ i₁ with hPm
  set γ : ℂ → Cfg d N X := fun τ =>
    c + (Complex.cos τ - 1) • rotCfgL Pm X c + Complex.sin τ • rotCfgL J X c with hγ
  have hγ' : ∀ τ, rotCfgL (planeRot i₀ i₁ (Complex.cos τ) (Complex.sin τ)) X c = γ τ := by
    intro τ
    simp only [planeRot, rotCfgL_add, rotCfgL_smul, rotCfgL_one, hγ]
    rfl
  have hd : HasDerivAt γ (rotCfgL J X c) 0 := by
    have h1 : HasDerivAt (fun τ : ℂ => Complex.cos τ - 1) 0 0 := by
      simpa using (Complex.hasDerivAt_cos 0).sub_const 1
    have h2 : HasDerivAt (fun τ : ℂ => Complex.sin τ) 1 0 := by
      simpa using Complex.hasDerivAt_sin 0
    have := ((h1.smul_const (rotCfgL Pm X c)).const_add c).add (h2.smul_const (rotCfgL J X c))
    convert this using 1
    simp
  have hγ0 : γ 0 = c := by simp [hγ]
  have hcont : ContinuousAt γ 0 := hd.continuousAt
  have hopen : IsOpen (ball (refPt i₀ ν X) ρ) := isOpen_ball
  have hev1 : ∀ᶠ τ in nhds (0 : ℂ), γ τ ∈ ball (refPt i₀ ν X) ρ :=
    hcont.preimage_mem_nhds (by rw [hγ0]; exact hopen.mem_nhds hc)
  have hev2 : ∀ᶠ τ in nhds (0 : ℂ), ‖Complex.cos τ‖ ≤ 2 := by
    have := Complex.continuous_cos.continuousAt (x := 0)
    filter_upwards [this.preimage_mem_nhds (Metric.ball_mem_nhds (Complex.cos 0) one_pos)]
      with τ hτ
    have : ‖Complex.cos τ - 1‖ < 1 := by simpa [dist_eq_norm] using hτ
    calc ‖Complex.cos τ‖ = ‖(Complex.cos τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Complex.cos τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hev3 : ∀ᶠ τ in nhds (0 : ℂ), ‖Complex.sin τ‖ ≤ 2 := by
    have := Complex.continuous_sin.continuousAt (x := 0)
    filter_upwards [this.preimage_mem_nhds (Metric.ball_mem_nhds (Complex.sin 0) one_pos)]
      with τ hτ
    have : ‖Complex.sin τ - 0‖ < 1 := by simpa [dist_eq_norm] using hτ
    rw [sub_zero] at this; linarith
  have hconst : (fun τ => f (γ τ)) =ᶠ[nhds (0 : ℂ)] fun _ => f c := by
    filter_upwards [hev1, hev2, hev3] with τ h1 h2 h3
    have hR : IsOrth (planeRot i₀ i₁ (Complex.cos τ) (Complex.sin τ)) :=
      planeRot_isOrth i₀ i₁ hne _ _ (by rw [Complex.cos_sq_add_sin_sq])
    have := hf.inv c (ball_subset_tube i₀ ν ρ X hc) _ hR (entryBd_planeRot _ _ _ _ h2 h3)
      (by rw [hγ']; exact ball_subset_tube i₀ ν ρ X h1)
    rw [hγ'] at this
    exact this
  have hfd : DifferentiableAt ℂ f (γ 0) := by
    rw [hγ0]; exact (hf.analytic_ball c hc).differentiableAt
  have hchain : HasDerivAt (fun τ => f (γ τ)) (fderiv ℂ f (γ 0) (rotCfgL J X c)) 0 :=
    hfd.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hd
  have h0 : HasDerivAt (fun τ => f (γ τ)) 0 0 := (hasDerivAt_const (0 : ℂ) (f c)).congr_of_eventuallyEq hconst
  have := hchain.unique h0
  rwa [hγ0] at this

theorem TermOK.ward {i₁ : Fin N} (hi : i₁ ≠ i₀) (x' : ↥X) :
    ∑ x : ↥X, tensB i₀ i₁ ν X f x x' + (ν : ℂ) * tensM i₀ i₁ ν X f x' -
      tensA i₀ ν X f x' = 0 := by
  have hne : i₀ ≠ i₁ := hi.symm
  set J := planeGen i₀ i₁ with hJ
  set P := refPt i₀ ν X with hP
  set Jc : Cfg d N X →L[ℂ] Cfg d N X := LinearMap.toContinuousLinearMap (rotCfgL J X) with hJc
  have hPb : P ∈ ball P ρ := mem_ball_self hf.rho_pos
  have hF : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) P) P :=
    ((hf.analytic_ball.fderiv_of_isOpen isOpen_ball) P hPb).differentiableAt.hasFDerivAt
  have hu : HasFDerivAt (fun c => Jc c) Jc P := Jc.hasFDerivAt
  have hΦ := hF.clm_apply hu
  have hzero : (fun y => fderiv ℂ f y (Jc y)) =ᶠ[nhds P] fun _ => (0 : ℂ) := by
    filter_upwards [isOpen_ball.mem_nhds hPb] with y hy
    exact hf.lie hi hy
  have hder := hΦ.fderiv
  rw [hzero.fderiv_eq (𝕜 := ℂ)] at hder
  have hw := congrArg (fun L => L (Pi.single (Sum.inl (x', i₁)) (1 : ℂ) : Cfg d N X)) hder
  have hz0 : fderiv ℂ (fun _ : Cfg d N X => (0 : ℂ)) P = 0 := by simp
  rw [hz0] at hw
  simp only [_root_.zero_apply,
    _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hw
  -- evaluate `J w` and `J P`
  have hJw : Jc (Pi.single (Sum.inl (x', i₁)) 1) = (-1 : ℂ) • Pi.single (Sum.inl (x', i₀)) 1 :=
    rotCfgL_single_inl_of X J x' i₁ i₀ (-1) (planeGen_mulVec_second i₀ i₁ hne)
  have hJP : Jc P = (∑ x : ↥X, (Pi.single (Sum.inl (x, i₁)) (1 : ℂ) : Cfg d N X)) +
      (ν : ℂ) • (Pi.single (Sum.inr i₁) (1 : ℂ) : Cfg d N X) := by
    rw [← pack_e1_eq (X := X) i₁ ν]
    show rotCfgL J X (refPt i₀ ν X) = _
    unfold refPt
    rw [rotCfgL_pack, Matrix.mulVec_smul, planeGen_mulVec_first i₀ i₁ hne, one_smul]
  rw [hJw, hJP] at hw
  have hs := D2_symm (hf.analytic_ball P hPb)
  simp only [map_smul, map_add, map_sum, smul_eq_mul] at hw
  have e1 : ∀ x : ↥X, D2 f P (Pi.single (Sum.inl (x, i₁)) 1) (Pi.single (Sum.inl (x', i₁)) 1) =
      D2 f P (Pi.single (Sum.inl (x', i₁)) 1) (Pi.single (Sum.inl (x, i₁)) 1) :=
    fun x => hs _ _
  have e2 : D2 f P (Pi.single (Sum.inr i₁) 1) (Pi.single (Sum.inl (x', i₁)) 1) =
      D2 f P (Pi.single (Sum.inl (x', i₁)) 1) (Pi.single (Sum.inr i₁) 1) := hs _ _
  unfold tensB tensM tensA
  rw [← hP]
  simp only [e1, e2]
  simp only [D2] at hw ⊢
  linear_combination (-1 : ℂ) * hw

end Local

end Balaban.SmallField
