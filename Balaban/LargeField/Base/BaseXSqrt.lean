/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXCov
public import Balaban.Localization.DecoupledCovParam
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Localization.DecoupledCovCont
public import Balaban.Localization.Decoupled2XBounds
public import Balaban.Localization.Decoupled2XGreen

/-!
# The square root of the first step's operator: decay in the shift

The mass shift `ν ↦ ν + x` of the cube operators is the identity shift, so the cube operators of the
x-variant chain at `x' = 0` and mass `ν + x` are `x`-coercive.  This gives the decay `C / (1 + x)`
of the constrained covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of `BaseXCov.lean`, which is
the missing integrability at infinity for the Stieltjes integral of the square root.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Shift

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The mass enters the cut matrix as a multiple of the identity. -/
theorem cutXFullMatrix_add_mass (G : GeneratingSet d L N₀ (k + 1) ϱ) (a : ℕ → ℝ) (aT x' ν x : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)) :
    cutXFullMatrix G a aT x' (ν + x) cut =
      cutXFullMatrix G a aT x' ν cut +
        x • (1 : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ) := by
  unfold cutXFullMatrix cutLaplacian latticeLaplacian
  have e : (2 * (d : ℝ) + (ν + x)) •
      (1 : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ) =
      (2 * (d : ℝ) + ν) • (1 : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ) +
        x • (1 : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ) := by
    rw [← add_smul]; congr 1; ring
  rw [e]; abel

/-- **The cut x-variant operator at mass `ν + x` is the operator at mass `ν` plus `x`.** -/
theorem cutXOperator_add_mass (G : GeneratingSet d L N₀ (k + 1) ϱ) (a : ℕ → ℝ) (aT x' ν x : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ (k + 1)) × Fin d)) (α : G.Ω 1 → ℂ) :
    cutXOperator G a aT x' (ν + x) cut α =
      cutXOperator G a aT x' ν cut α + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ) := by
  have h2 : ((cutXFullMatrix G a aT x' ν cut +
      x • (1 : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ)).map
        (algebraMap ℝ ℂ)) =
      (cutXFullMatrix G a aT x' ν cut).map (algebraMap ℝ ℂ) +
        (x : ℂ) • (1 : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have h3 : ∀ B : Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℂ,
      Green.restrictOp (B + (x : ℂ) • 1) (G.Ω 1) =
        Green.restrictOp B (G.Ω 1) + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ) := by
    intro B
    ext i j
    by_cases h : i = j
    · subst h; simp [Green.restrictOp]
    · have h' : (i : Torus d (N₀ * L ^ (k + 1))) ≠ j := fun hh => h (Subtype.ext hh)
      simp [Green.restrictOp, h, h']
  unfold cutXOperator
  rw [cutXFullMatrix_add_mass, h2, h3]
  abel

end Shift

section Cube

open Balaban.Localization.Dec2

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : Balaban.Localization.DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν x Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- **The cube operators at `x' = 0` and mass `ν + x` are `x`-coercive.**  The cube Green function
`G^{(z)}` of the mass-shifted step contracts the Euclidean norm of the source by
`((1/8) L^{-2(k+1)} + x)⁻¹`. -/
theorem cubeGx_sqNorm_le (S : XCover C H a aT (ν + x) Cx) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (hα : AdmPot H α) {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx)
    (g : H.Ω 1 → ℂ) :
    ((1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x) ^ 2 *
        Green.sqNorm (cubeGx H a aT 0 (ν + x) α q *ᵥ g) ≤ Green.sqNorm (cD H q *ᵥ g) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hco : Green.IsCoercive (cutXOperator H a aT 0 ν (cubeCut H (intBox q)) α)
      ((1 / 4 - 1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) :=
    cutXOperator_isCoercive_sharp_of_ak H (cubeCut_aligned H (S.blockAligned q hq)) S.hL hν S.ha
      ⟨S.hak1, S.hak2⟩ S.haT1 S.haT2 le_rfl (θ := 1 / 8) (by norm_num) (by norm_num) α
      (AdmPot.le_eighth' S.hd hα) (γ := (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) fun y => by
        have hp : 0 < H.spacing y := spacing_pos H
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le H y.2) 2)
  have hco' := hco.add_smul_one x
  have e : cubeHx H a aT 0 (ν + x) α q =
      cutXOperator H a aT 0 ν (cubeCut H (intBox q)) α + (x : ℂ) • 1 := by
    unfold cubeHx
    exact cutXOperator_add_mass H a aT 0 ν x _ α
  have hγ : 0 < (1 / 4 - 1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x := by positivity
  have h := sqNorm_le_of_isCoercive (e ▸ hco') (cubeGx H a aT 0 (ν + x) α q *ᵥ g) hγ.le
  rw [cubeHx_cubeGx S hα (by linarith : 0 ≤ (0 : ℝ)) hq g] at h
  have e2 : (1 / 4 - 1 / 8 : ℝ) = 1 / 8 := by norm_num
  rwa [e2] at h

/-- The sum of squares of the zero extension is the Euclidean norm. -/
theorem sum_zeroExt_sq (f : H.Ω 1 → ℂ) :
    ∑ z, ‖zeroExt (H.Ω 1) f z‖ ^ 2 = Green.sqNorm f := by
  rw [Green.sum_eq_sum_subtype (H.Ω 1) _ (fun i hi => by simp [zeroExt, hi])]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : zeroExt (H.Ω 1) f y = f y := by simp [zeroExt]
  rw [this]

/-- The interaction cubes overlap at most `3 * 5 ^ d` times. -/
theorem sum_sqNorm_cD_le (S : XCover C H a aT ν Cx) (g : H.Ω 1 → ℂ) :
    ∑ q ∈ C.cubeIdx, Green.sqNorm (cD H q *ᵥ g) ≤ (3 * 5 ^ d : ℝ) * Green.sqNorm g := by
  classical
  unfold Green.sqNorm
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have e : ∀ q, ‖(cD H q *ᵥ g) y‖ ^ 2 =
      if (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ intBox q then ‖g y‖ ^ 2 else 0 := by
    intro q
    rw [cD_mulVec]
    split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h3 : (((C.cubeIdx).filter (fun q =>
      (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ intBox q)).card : ℝ)
      ≤ 3 * 5 ^ d := by exact_mod_cast card_overlap_le S y
  exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

/-- **The first approximation `G*` decays like `(L^{-2(k+1)}/8 + x)⁻¹`.** -/
theorem Gstarx_sqNorm_le {κ : ℝ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (D : XData C H a aT (ν + x) 0 α κ s Cx) (hν : 0 ≤ ν) (hx : 0 ≤ x) (g : H.Ω 1 → ℂ) :
    ((1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x) ^ 2 *
        Green.sqNorm (Gstarx C H a aT 0 (ν + x) α s *ᵥ g) ≤
      (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 * Green.sqNorm g := by
  set Γ : ℝ := (1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x with hΓ
  have hn0 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
  have h1 : Green.sqNorm (Gstarx C H a aT 0 (ν + x) α s *ᵥ g) ≤
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        Green.sqNorm (cubeGx H a aT 0 (ν + x) α q *ᵥ g)) := by
    rw [← sum_zeroExt_sq]
    calc ∑ z, ‖zeroExt (H.Ω 1) (Gstarx C H a aT 0 (ν + x) α s *ᵥ g) z‖ ^ 2
        ≤ ∑ z, (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
          ‖zeroExt (H.Ω 1) (cubeGx H a aT 0 (ν + x) α q *ᵥ g) z‖ ^ 2) :=
          Finset.sum_le_sum fun z _ => norm_sq_Gstarx_le D g z
      _ = _ := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
          simp only [sum_zeroExt_sq]
  have h2 : Γ ^ 2 * ∑ q ∈ C.cubeIdx, Green.sqNorm (cubeGx H a aT 0 (ν + x) α q *ᵥ g) ≤
      ∑ q ∈ C.cubeIdx, Green.sqNorm (cD H q *ᵥ g) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => cubeGx_sqNorm_le D.st hν hx D.pot hq g
  have h3 := sum_sqNorm_cD_le D.st g
  have hE : 0 ≤ Real.exp (N0 d L * κ) ^ 2 := by positivity
  calc Γ ^ 2 * Green.sqNorm (Gstarx C H a aT 0 (ν + x) α s *ᵥ g)
      ≤ Γ ^ 2 * ((3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        Green.sqNorm (cubeGx H a aT 0 (ν + x) α q *ᵥ g))) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) ^ 2 *
        (Γ ^ 2 * ∑ q ∈ C.cubeIdx, Green.sqNorm (cubeGx H a aT 0 (ν + x) α q *ᵥ g)) := by ring
    _ ≤ (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) ^ 2 * ((3 * 5 ^ d : ℝ) * Green.sqNorm g) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = _ := by ring

/-- The unweighted norm is dominated by the zero-weight source norm, which is at most
`L^{2(k+1)}` times the unweighted norm. -/
theorem sqNorm_le_agmonSource_zero (hL : 1 ≤ L) (f : H.Ω 1 → ℂ) :
    Green.sqNorm f ≤ agmonSource H 0 (fun _ => 0) f ∧
      agmonSource H 0 (fun _ => 0) f ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm f := by
  rw [agmonSource_eq]
  unfold Green.sqNorm
  rw [Finset.mul_sum]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  refine ⟨Finset.sum_le_sum fun y _ => ?_, Finset.sum_le_sum fun y _ => ?_⟩
  · obtain ⟨h1, h2, _⟩ := H.layerIndex_spec y.2
    have : (1 : ℝ) ≤ H.spacing y := one_le_pow₀ hL1
    simp only [zero_mul, Real.exp_zero, one_pow, mul_one]
    have h3 : (1 : ℝ) ≤ H.spacing y ^ 2 := one_le_pow₀ this
    exact le_mul_of_one_le_left (sq_nonneg _) h3
  · have hp : 0 < H.spacing y := spacing_pos H
    have : H.spacing y ≤ (L : ℝ) ^ (k + 1) := spacing_le H y.2
    simp only [zero_mul, Real.exp_zero, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.le this 2) (sq_nonneg _)

/-- **The Green function `Ĝ_{0,s}` of the mass-shifted step decays like `(L^{-2(k+1)}/8 + x)⁻¹`.** -/
theorem Gsx_sqNorm_le {κ : ℝ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
    (D : XData C H a aT (ν + x) 0 α κ s Cx) (hν : 0 ≤ ν) (hx : 0 ≤ x) (g : H.Ω 1 → ℂ) :
    ((1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x) ^ 2 *
        Green.sqNorm (Gsx C H a aT 0 (ν + x) α s *ᵥ g) ≤
      (16 / 9) * ((L : ℝ) ^ (k + 1)) ^ 2 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 *
        Green.sqNorm g := by
  have hd : 0 < d := by have := D.st.hd; omega
  have W : XWeight H 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero H, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  set h : H.Ω 1 → ℂ := (1 - Kcalx C H a aT 0 (ν + x) α s)⁻¹ *ᵥ g with hh
  have h1 : Green.sqNorm h ≤ (16 / 9) * (((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm g) :=
    ((sqNorm_le_agmonSource_zero hL1 h).1.trans (D.neumann_src W g)).trans
      (mul_le_mul_of_nonneg_left (sqNorm_le_agmonSource_zero hL1 g).2 (by norm_num))
  have h2 := Gstarx_sqNorm_le D hν hx h
  rw [Dec2.Gsx_mulVec]
  have hΓ : 0 ≤ ((1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 := by positivity
  calc _ ≤ (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 * Green.sqNorm h := h2
    _ ≤ (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 *
        ((16 / 9) * (((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm g)) :=
        mul_le_mul_of_nonneg_left h1 hA
    _ = _ := by ring

end Cube

section Vector

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The squared norm of a vector field is the sum over its components. -/
theorem sqNorm_eq_sum_comp (w : H.Ω 1 × Fin N → ℂ) :
    Green.sqNorm w = ∑ i, Green.sqNorm (Multiscale.comp H w i) := by
  unfold Green.sqNorm Multiscale.comp
  rw [Fintype.sum_prod_type_right]

/-- A scalar operator bound lifts to the vector fields. -/
theorem sqNorm_liftOp_le (A : Matrix (H.Ω 1) (H.Ω 1) ℂ) {c b : ℝ}
    (hA : ∀ g : H.Ω 1 → ℂ, c * Green.sqNorm (A *ᵥ g) ≤ b * Green.sqNorm g)
    (w : H.Ω 1 × Fin N → ℂ) :
    c * Green.sqNorm (liftOp N A *ᵥ w) ≤ b * Green.sqNorm w := by
  rw [sqNorm_eq_sum_comp, sqNorm_eq_sum_comp, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [comp_liftOp']
  exact hA _

/-- The zero-weight source norm of a vector field versus its Euclidean norm. -/
theorem sqNorm_le_vecSrc_zero (hL : 1 ≤ L) (w : H.Ω 1 × Fin N → ℂ) :
    Green.sqNorm w ≤ vecSrc H 0 (fun _ => 0) w ∧
      vecSrc H 0 (fun _ => 0) w ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm w := by
  unfold vecSrc
  rw [sqNorm_eq_sum_comp, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun i _ => (sqNorm_le_agmonSource_zero hL _).1,
    Finset.sum_le_sum fun i _ => (sqNorm_le_agmonSource_zero hL _).2⟩

/-- An entry of a matrix is bounded by the Euclidean norm of the image of a basis vector. -/
theorem norm_sq_entry_le_sqNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (y z : ι) : ‖M y z‖ ^ 2 ≤ Green.sqNorm (M *ᵥ (Pi.single z 1 : ι → ℂ)) := by
  have h := Finset.single_le_sum (f := fun i : ι => ‖(M *ᵥ (Pi.single z 1 : ι → ℂ)) i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  rw [mulVec_single_entry] at h
  exact h

omit [NeZero N₁] [NeZero L] in
/-- A basis vector has unit Euclidean norm. -/
theorem sqNorm_single {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι) :
    Green.sqNorm (Pi.single z 1 : ι → ℂ) = 1 := by
  unfold Green.sqNorm
  rw [Finset.sum_eq_single z]
  · simp
  · intro i _ hi; simp [hi]
  · simp

end Vector

section Pi

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν x Cx κ δ : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- **The correction `Π_{0,s}` of the mass-shifted step decays like
`(L^{-2(k+1)}/8 + x)⁻¹`.** -/
theorem decPi_sqNorm_le (D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx) (hν : 0 ≤ ν)
    (hx : 0 ≤ x) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (f : G.Ω 1 × Fin N → ℂ) :
    ((1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ + x) ^ 2 *
        Green.sqNorm (Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f) ≤
      (16 / 9) * ((L : ℝ) ^ (k + 1)) ^ 2 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 *
        (45 * ((L : ℝ) ^ (k + 1)) ^ 2) * Green.sqNorm f := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  have W : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  set h : G.Ω 1 → ℂ := (Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ *ᵥ
    (Dec2.decN (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f) with hh
  have hsrc : agmonSource G 0 (fun _ => 0) h ≤ 20 * vecSrc G 0 (fun _ => 0) f := by
    have h4 : agmonSource G 0 (fun _ => 0) ((Dec2.decM (coverOf G) G a aT 0 (ν + x) α s φ)⁻¹ *ᵥ
        (Dec2.decN (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f)) ≤
        4 * agmonSource G 0 (fun _ => 0) (Dec2.decN (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f) :=
      decM_inv_le_cover D W hφ hδ hsm (Dec2.decN (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f)
    have h5 : agmonSource G 0 (fun _ => 0) (Dec2.decN (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f) ≤
        5 * vecSrc G 0 (fun _ => 0) f := decN_src_le_cover D W hφ hδ hsm f
    linarith
  have hPi : Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ *ᵥ f =
      liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) *ᵥ
        (fieldMul (restrictField G φ) *ᵥ h) := by
    unfold Dec2.decPi
    rw [hh, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [hPi]
  set w : G.Ω 1 × Fin N → ℂ := fieldMul (restrictField G φ) *ᵥ h with hw
  have h1 := sqNorm_liftOp_le (N := N) (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s)
    (fun g => Gsx_sqNorm_le D hν hx g) w
  have h2 : Green.sqNorm w ≤ 45 * (((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm f) := by
    calc Green.sqNorm w ≤ vecSrc G 0 (fun _ => 0) w := (sqNorm_le_vecSrc_zero hL1 w).1
      _ ≤ 9 / 4 * agmonSource G 0 (fun _ => 0) h := vecSrc_fieldMul_le hφ h
      _ ≤ 9 / 4 * (20 * vecSrc G 0 (fun _ => 0) f) := by gcongr
      _ ≤ 9 / 4 * (20 * (((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm f)) := by
          gcongr; exact (sqNorm_le_vecSrc_zero hL1 f).2
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg ((L : ℝ) ^ (k + 1))) (Green.sqNorm_nonneg f)]
  have hK : 0 ≤ (16 / 9) * ((L : ℝ) ^ (k + 1)) ^ 2 * (3 * 5 ^ d : ℝ) ^ 2 *
      Real.exp (N0 d L * κ) ^ 2 := by positivity
  calc _ ≤ _ := h1
    _ ≤ (16 / 9) * ((L : ℝ) ^ (k + 1)) ^ 2 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 *
        (45 * (((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm f)) := mul_le_mul_of_nonneg_left h2 hK
    _ = _ := by ring

end Pi

section Decay

/-- An entry of an operator that contracts the Euclidean norm by `Γ⁻¹ √K`. -/
theorem norm_entry_le_of_sqNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℂ)
    {Γ K : ℝ} (hΓ : 0 < Γ) (h : ∀ w : ι → ℂ, Γ ^ 2 * Green.sqNorm (T *ᵥ w) ≤ K * Green.sqNorm w)
    (y z : ι) : ‖T y z‖ ≤ Real.sqrt K / Γ := by
  have h1 := norm_sq_entry_le_sqNorm T y z
  have h2 := h (Pi.single z 1 : ι → ℂ)
  rw [sqNorm_single, mul_one] at h2
  rw [le_div_iff₀ hΓ]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg Γ)]

/-- **The x-dependent constrained covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of the first
step decays like `(1 + x)⁻¹`.**  The bound `B` depends only on `d, L, κ` and holds for every
`x ≥ 0` and every `s` with `‖s_P‖ ≤ e^κ`, in the regime `δ² C(κ) ≤ 1/4`. -/
theorem baseCovX_decay (d L : ℕ) [NeZero L] (κ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ N : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (_hCx : 0 ≤ Cx) (_hν : 0 ≤ ν)
      (_hx : 0 ≤ x) (_hκ : 0 ≤ κ)
      (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      {α : G.Ω 1 → ℂ} (_hα : AdmPot G α)
      {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ} (_hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintField G δ φ) (y z : G.Ω 1 × Fin N),
      ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z‖ ≤ B / (1 + x) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set γ0 : ℝ := (1 / 8) * (((L : ℝ) ^ (0 + 1)) ^ 2)⁻¹ with hγ0
  have hγ0p : 0 < γ0 := by rw [hγ0]; positivity
  set c : ℝ := min 1 γ0 with hc
  have hcp : 0 < c := lt_min one_pos hγ0p
  set K1 : ℝ := (16 / 9) * ((L : ℝ) ^ (0 + 1)) ^ 2 * (3 * 5 ^ d : ℝ) ^ 2 *
    Real.exp (N0 d L * κ) ^ 2 with hK1
  set K2 : ℝ := K1 * (45 * ((L : ℝ) ^ (0 + 1)) ^ 2) with hK2
  refine ⟨9 / 4 + (Real.sqrt K1 + Real.sqrt K2) / c, by positivity, ?_⟩
  intro N₁ m₁ N _ ϱ G a aT ν Cx x S hCx hν hx hκ hM δ hδ hsm α hα s hs φ hφ y z
  obtain ⟨p, i⟩ := y
  obtain ⟨q, j⟩ := z
  have D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx := ⟨S, hCx, hα, le_rfl, hκ, hM, hs⟩
  have hΓ : 0 < γ0 + x := by positivity
  have hG := norm_entry_le_of_sqNorm (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s)) hΓ
    (K := K1) (fun w => sqNorm_liftOp_le _ (fun g => Gsx_sqNorm_le D hν hx g) w) (p, i) (q, j)
  have hP := norm_entry_le_of_sqNorm (Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) hΓ
    (K := K2) (fun w => decPi_sqNorm_le D hν hx hφ hδ hsm w) (p, i) (q, j)
  have hinv : ∀ r : ℝ, (r / (γ0 + x)) ≤ (r / c) / (1 + x) ∨ r < 0 := by
    intro r
    by_cases hr : 0 ≤ r
    · left
      rw [div_div, div_le_div_iff₀ hΓ (by positivity)]
      have h1 : c ≤ γ0 := min_le_right _ _
      have h2 : c ≤ 1 := min_le_left _ _
      nlinarith [mul_nonneg hr hx, mul_nonneg hr (sub_nonneg.2 h1), mul_nonneg (mul_nonneg hr hx) (sub_nonneg.2 h2)]
    · right; linarith
  have hBase : ‖basePart (restrictField G φ) (p, i) (q, j)‖ ≤ 9 / 4 := by
    rw [basePart_apply]
    split_ifs
    · have h1 : ‖restrictField G φ p i‖ ≤ 3 / 2 :=
        (norm_le_vn (φ p) i).trans (hφ.bound p p.2)
      have h2 : ‖restrictField G φ p j‖ ≤ 3 / 2 :=
        (norm_le_vn (φ p) j).trans (hφ.bound p p.2)
      rw [norm_mul]
      nlinarith [norm_nonneg (restrictField G φ p i), norm_nonneg (restrictField G φ p j)]
    · simp; norm_num
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hc1 : ‖(1 + (x : ℂ))⁻¹‖ = (1 + x)⁻¹ := by
    have : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_inv, Complex.norm_real, Real.norm_of_nonneg h1x.le]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have t1 := norm_sub_le ((1 + (x : ℂ))⁻¹ * basePart (restrictField G φ) (p, i) (q, j) +
    liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) (p, i) (q, j))
    (Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ (p, i) (q, j))
  have t2 := norm_add_le ((1 + (x : ℂ))⁻¹ * basePart (restrictField G φ) (p, i) (q, j))
    (liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) (p, i) (q, j))
  rw [norm_mul, hc1] at t2
  have t3 : (1 + x)⁻¹ * ‖basePart (restrictField G φ) (p, i) (q, j)‖ ≤ (1 + x)⁻¹ * (9 / 4) :=
    mul_le_mul_of_nonneg_left hBase (inv_nonneg.2 h1x.le)
  have hs1 : Real.sqrt K1 / (γ0 + x) ≤ Real.sqrt K1 / c / (1 + x) := by
    rcases hinv (Real.sqrt K1) with h | h
    · exact h
    · exact absurd h (not_lt.2 (Real.sqrt_nonneg _))
  have hs2 : Real.sqrt K2 / (γ0 + x) ≤ Real.sqrt K2 / c / (1 + x) := by
    rcases hinv (Real.sqrt K2) with h | h
    · exact h
    · exact absurd h (not_lt.2 (Real.sqrt_nonneg _))
  have e : (9 / 4 + (Real.sqrt K1 + Real.sqrt K2) / c) / (1 + x) =
      (1 + x)⁻¹ * (9 / 4) + Real.sqrt K1 / c / (1 + x) + Real.sqrt K2 / c / (1 + x) := by
    field_simp
    ring
  rw [e]
  linarith

end Decay

end Balaban.LargeField.Base
