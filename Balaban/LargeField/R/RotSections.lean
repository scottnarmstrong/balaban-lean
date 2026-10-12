/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The two-chart section `R_±(u)` and the rotated representation (LF-RECONSTRUCTION §III.9.2)

**Definition III.9.2**: `A(u) = u e₁ᵀ − e₁ uᵀ`,
`R₊(u) = I + A(u) + A(u)²/(1 + u·e₁)` (`u·e₁ ≠ −1`),
`R₋(u) = (I − A(u) + A(u)²/(1 − u·e₁)) D` (`u·e₁ ≠ 1`), `D e₁ = −e₁`, `D ∈ SO(N)`.
`e₁ = e_{i₀}`, and `D` is the rotation by `π` in the plane of `e_{i₀}, e_{j₀}` (`i₀ ≠ j₀`).

**Lemma III.9.3** (a) analyticity (`secPlus_analytic`, `secMinus_analytic`), orthogonality
(`sec_orth_plus`, `sec_orth_minus`), `R_±(u) e₁ = u` (`sec_e1_plus`, `sec_e1_minus`), real rotations for real unit
`u` (`sec_plus_real`, `sec_minus_real`, including `det = 1`); (b) `sec_overlap`; (c) the Lipschitz bound is in
`RotSectionsLip`.
**Definition III.9.4**, algebraic part: `rotRep`, `rotRep_dot`, `rotRepEquiv`, `rotRep_ref_site`.
The sections are defined over an arbitrary field `K` (`ℝ` for real configurations, `ℂ` for the quadric).
(P7 pp. 520-525.)
-/

@[expose] public section

open Matrix

namespace Balaban.LargeField

variable {K : Type*} [Field K] {N : ℕ}

/-- The first basis vector `e₁ = e_{i₀}`: the reference direction, `Pi.single i₀ 1`. -/
def eVec (i₀ : Fin N) : Fin N → K := Pi.single i₀ 1

/-- **LF-RECONSTRUCTION Definition III.9.2** (P7 pp. 520-525): `A(u) := u e₁ᵀ − e₁ uᵀ`, an antisymmetric matrix, for any `u` (over any field `K`; the source uses `K = ℂ`, real unit `u` use `K = ℝ`). -/
def Aof (i₀ : Fin N) (u : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  vecMulVec u (eVec i₀) - vecMulVec (eVec i₀) u

theorem eVec_dot_self (i₀ : Fin N) : (eVec i₀ : Fin N → K) ⬝ᵥ eVec i₀ = 1 := by
  simp [eVec]
theorem dot_eVec (i₀ : Fin N) (u : Fin N → K) : u ⬝ᵥ eVec i₀ = u i₀ := by
  simp [eVec]
theorem eVec_dot (i₀ : Fin N) (u : Fin N → K) : eVec i₀ ⬝ᵥ u = u i₀ := by
  simp [eVec]

/-- `A(u)` is antisymmetric (**Def. III.9.2**). -/
theorem Aof_transpose (i₀ : Fin N) (u : Fin N → K) : (Aof i₀ u)ᵀ = -Aof i₀ u := by
  ext i j; simp [Aof, vecMulVec]; ring

theorem Aof_neg (i₀ : Fin N) (u : Fin N → K) : Aof i₀ (-u) = -Aof i₀ u := by
  ext i j; simp [Aof, vecMulVec]; ring

/-- `A(u)² = c (u e₁ᵀ + e₁ uᵀ) − u uᵀ − e₁ e₁ᵀ` on the quadric `u·u = 1`, `c = u·e₁`. -/
theorem Aof_sq (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) :
    Aof i₀ u * Aof i₀ u = (u i₀) • (vecMulVec u (eVec i₀) + vecMulVec (eVec i₀) u)
      - vecMulVec u u - vecMulVec (eVec i₀) (eVec i₀) := by
  simp only [Aof, sub_mul, mul_sub, vecMulVec_mul_vecMulVec, dot_eVec, eVec_dot, hu]
  ext i j; simp [vecMulVec, eVec]; ring

/-- `A(u)³ = (c² − 1) A(u)` on the quadric (the identity behind **Lemma III.9.3 (a)**). -/
theorem Aof_cube (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) :
    Aof i₀ u * Aof i₀ u * Aof i₀ u = ((u i₀)^2 - 1) • Aof i₀ u := by
  rw [Aof_sq i₀ u hu]
  simp only [Aof, sub_mul, add_mul, smul_mul_assoc, vecMulVec_mul_vecMulVec, dot_eVec, eVec_dot, hu, mul_sub]
  ext i j; simp [vecMulVec, eVec]; ring

/-- The matrix `D ∈ SO(N)` of **Definition III.9.2** with `D e₁ = −e₁`: the rotation by `π` in the plane of `e₁ = e_{i₀}` and `e₂ = e_{j₀}`, i.e. `diag(−1 at i₀, j₀; 1 elsewhere)`. It is a rotation (determinant `1`) when `i₀ ≠ j₀` (`Dmat_det`). -/
def Dmat (i₀ j₀ : Fin N) : Matrix (Fin N) (Fin N) K :=
  Matrix.diagonal fun k => if k = i₀ ∨ k = j₀ then -1 else 1

/-- **LF-RECONSTRUCTION Definition III.9.2**, the chart section `R₊(u) := I + A(u) + A(u)²/(1 + u·e₁)`, defined where `u·e₁ = u i₀ ≠ −1`. (Where `u i₀ = −1`, `Field.inv` makes the value `I + A(u)`, which is junk; all theorems carry the hypothesis `1 + u i₀ ≠ 0`.) -/
def secPlus (i₀ : Fin N) (u : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  1 + Aof i₀ u + (1 + u i₀)⁻¹ • (Aof i₀ u * Aof i₀ u)

/-- **LF-RECONSTRUCTION Definition III.9.2**, the chart section `R₋(u) := (I − A(u) + A(u)²/(1 − u·e₁)) D`, defined where `u·e₁ = u i₀ ≠ 1`, with `D = Dmat i₀ j₀`. All theorems carry the hypothesis `1 - u i₀ ≠ 0`. -/
def secMinus (i₀ j₀ : Fin N) (u : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  (1 - Aof i₀ u + (1 - u i₀)⁻¹ • (Aof i₀ u * Aof i₀ u)) * Dmat i₀ j₀

/-- **LF-RECONSTRUCTION Lemma III.9.3 (a)**, orthogonality of `R₊`: `R₊(u)ᵀ R₊(u) = I` for `u·u = 1`, `u·e₁ ≠ −1`. Proved as an algebraic identity from `A³ = (c²−1)A` over any field (not only on the real sphere and by Zariski density as in the source). -/
theorem sec_orth_plus (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) (hs : 1 + u i₀ ≠ 0) :
    (secPlus i₀ u)ᵀ * secPlus i₀ u = 1 := by
  have hc := Aof_cube i₀ u hu
  have hA := Aof_transpose i₀ u
  have hP : (Aof i₀ u * Aof i₀ u)ᵀ = Aof i₀ u * Aof i₀ u := by
    rw [transpose_mul, hA]; simp
  have hAP : Aof i₀ u * (Aof i₀ u * Aof i₀ u) = ((u i₀)^2 - 1) • Aof i₀ u := by
    rw [← mul_assoc]; exact hc
  have hPA := hc
  have hPP : (Aof i₀ u * Aof i₀ u) * (Aof i₀ u * Aof i₀ u) = ((u i₀)^2 - 1) • (Aof i₀ u * Aof i₀ u) := by
    rw [mul_assoc, hAP]; simp
  have ha : (1 + u i₀)⁻¹ * (1 + u i₀) = 1 := inv_mul_cancel₀ hs
  unfold secPlus
  simp only [transpose_add, transpose_one, transpose_smul, hA, hP]
  simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, neg_mul, hAP, hPA, hPP, smul_smul]
  match_scalars <;> field_simp <;> ring

theorem Aof_mulVec_e (i₀ : Fin N) (u : Fin N → K) :
    Aof i₀ u *ᵥ eVec i₀ = u - (u i₀) • eVec i₀ := by
  ext i; simp [Aof, mulVec, vecMulVec, dotProduct, eVec, Pi.single_apply]

theorem Aof_mulVec_u (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) :
    Aof i₀ u *ᵥ u = (u i₀) • u - eVec i₀ := by
  ext i; simp [Aof, sub_mulVec, vecMulVec_mulVec, hu, eVec_dot]


theorem Aof_sq_mulVec_e (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) :
    (Aof i₀ u * Aof i₀ u) *ᵥ eVec i₀ = ((u i₀)^2 - 1) • eVec i₀ := by
  rw [← mulVec_mulVec, Aof_mulVec_e, mulVec_sub, mulVec_smul, Aof_mulVec_u i₀ u hu, Aof_mulVec_e]
  ext i; simp [Pi.sub_apply]; ring

/-- **Lemma III.9.3 (a)**: `R₊(u) e₁ = u` on the quadric, `u·e₁ ≠ −1`. -/
theorem sec_e1_plus (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) (hs : 1 + u i₀ ≠ 0) :
    secPlus i₀ u *ᵥ eVec i₀ = u := by
  unfold secPlus
  rw [add_mulVec, add_mulVec, one_mulVec, Aof_mulVec_e, smul_mulVec, Aof_sq_mulVec_e i₀ u hu]
  ext i
  have h : (1 + u i₀)⁻¹ * ((u i₀)^2 - 1) = u i₀ - 1 := by field_simp; ring
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have := congrFun (show ((1 + u i₀)⁻¹ * ((u i₀)^2 - 1)) • eVec i₀ = (u i₀ - 1) • (eVec i₀ : Fin N → K) by rw [h]) i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [mul_comm ((1 + u i₀)⁻¹)] at this ⊢
  linear_combination this

theorem Dmat_mulVec_e (i₀ j₀ : Fin N) : Dmat i₀ j₀ *ᵥ (eVec i₀ : Fin N → K) = -eVec i₀ := by
  ext i; simp [Dmat, eVec, mulVec_diagonal, Pi.single_apply]
  by_cases h : i = i₀ <;> simp [h]

theorem Dmat_transpose_mul (i₀ j₀ : Fin N) : (Dmat i₀ j₀ : Matrix (Fin N) (Fin N) K)ᵀ * Dmat i₀ j₀ = 1 := by
  unfold Dmat
  rw [diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext k; by_cases h : k = i₀ ∨ k = j₀ <;> simp [h]

theorem Dmat_det (i₀ j₀ : Fin N) (hij : i₀ ≠ j₀) : (Dmat i₀ j₀ : Matrix (Fin N) (Fin N) K).det = 1 := by
  unfold Dmat
  rw [det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have : Finset.filter (fun k => k = i₀ ∨ k = j₀) Finset.univ = ({i₀, j₀} : Finset (Fin N)) := by
    ext k; simp
  rw [this, Finset.card_pair hij]; norm_num

/-- `R₋(u) = R₊(−u) D`: the second chart is the first for `−u` followed by `D` (used to transfer the `R₊` results to `R₋`). -/
theorem secMinus_eq (i₀ j₀ : Fin N) (u : Fin N → K) :
    secMinus i₀ j₀ u = secPlus i₀ (-u) * Dmat i₀ j₀ := by
  unfold secMinus secPlus
  rw [Aof_neg]
  have : (-u) i₀ = -(u i₀) := rfl
  rw [this, neg_mul_neg]
  congr 2
  · abel
  · rw [sub_eq_add_neg]

/-- **Lemma III.9.3 (a)**, orthogonality of `R₋`: `R₋(u)ᵀ R₋(u) = I` for `u·u = 1`, `u·e₁ ≠ 1`. -/
theorem sec_orth_minus (i₀ j₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) (hs : 1 - u i₀ ≠ 0) :
    (secMinus i₀ j₀ u)ᵀ * secMinus i₀ j₀ u = 1 := by
  have hu' : (-u) ⬝ᵥ (-u) = 1 := by simpa using hu
  have hs' : 1 + (-u) i₀ ≠ 0 := by simpa [sub_eq_add_neg] using hs
  rw [secMinus_eq, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (secPlus i₀ (-u))ᵀ,
    sec_orth_plus i₀ (-u) hu' hs', one_mul, Dmat_transpose_mul]

/-- **Lemma III.9.3 (a)**: `R₋(u) e₁ = u` on the quadric, `u·e₁ ≠ 1`. -/
theorem sec_e1_minus (i₀ j₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) (hs : 1 - u i₀ ≠ 0) :
    secMinus i₀ j₀ u *ᵥ eVec i₀ = u := by
  have hu' : (-u) ⬝ᵥ (-u) = 1 := by simpa using hu
  have hs' : 1 + (-u) i₀ ≠ 0 := by simpa [sub_eq_add_neg] using hs
  rw [secMinus_eq, ← mulVec_mulVec, Dmat_mulVec_e, mulVec_neg, sec_e1_plus i₀ (-u) hu' hs', neg_neg]

/-- `det R₊(u) = 1` on the quadric (so `R₊(u) ∈ SO(N, K)`; for real unit `u` this is the statement that `R₊` is a real rotation, **Lemma III.9.3 (a)**). Proof: `(I − K) R₊ = I + K` with `K = A/(1+c)` antisymmetric and `I − K` invertible. -/
theorem sec_det_plus [CharZero K] (i₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) (hs : 1 + u i₀ ≠ 0) :
    (secPlus i₀ u).det = 1 := by
  have hc := Aof_cube i₀ u hu
  have hA := Aof_transpose i₀ u
  have hAP : Aof i₀ u * (Aof i₀ u * Aof i₀ u) = ((u i₀)^2 - 1) • Aof i₀ u := by
    rw [← mul_assoc]; exact hc
  have hPP : (Aof i₀ u * Aof i₀ u) * (Aof i₀ u * Aof i₀ u) = ((u i₀)^2 - 1) • (Aof i₀ u * Aof i₀ u) := by
    rw [mul_assoc, hAP]; simp
  have ha : (1 + u i₀)⁻¹ * (1 + u i₀) = 1 := inv_mul_cancel₀ hs
  have h1 : (1 - (1 + u i₀)⁻¹ • Aof i₀ u) * secPlus i₀ u = 1 + (1 + u i₀)⁻¹ • Aof i₀ u := by
    unfold secPlus
    simp only [mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hAP, smul_smul, smul_sub]
    match_scalars <;> field_simp <;> ring
  have two : (2 : K) ≠ 0 := two_ne_zero
  have h2 : (1 - (1 + u i₀)⁻¹ • Aof i₀ u) *
      (1 + ((1 + u i₀) / 2) • ((1 + u i₀)⁻¹ • Aof i₀ u + ((1 + u i₀)⁻¹ * (1 + u i₀)⁻¹) •
        (Aof i₀ u * Aof i₀ u))) = 1 := by
    simp only [mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hAP, smul_smul, smul_add, smul_sub]
    match_scalars <;> field_simp <;> ring
  have hd2 := congrArg Matrix.det h2
  rw [det_mul, det_one] at hd2
  have hd1 := congrArg Matrix.det h1
  rw [det_mul] at hd1
  have ht : (1 + (1 + u i₀)⁻¹ • Aof i₀ u) = (1 - (1 + u i₀)⁻¹ • Aof i₀ u)ᵀ := by
    rw [transpose_sub, transpose_one, transpose_smul, hA]; simp
  rw [ht, det_transpose] at hd1
  have hne : (1 - (1 + u i₀)⁻¹ • Aof i₀ u).det ≠ 0 := left_ne_zero_of_mul_eq_one hd2
  have := mul_left_cancel₀ hne (hd1.trans (mul_one _).symm)
  exact this

/-- `det R₋(u) = 1` on the quadric (`i₀ ≠ j₀`), **Lemma III.9.3 (a)**. -/
theorem sec_det_minus [CharZero K] (i₀ j₀ : Fin N) (hij : i₀ ≠ j₀) (u : Fin N → K) (hu : u ⬝ᵥ u = 1)
    (hs : 1 - u i₀ ≠ 0) : (secMinus i₀ j₀ u).det = 1 := by
  have hu' : (-u) ⬝ᵥ (-u) = 1 := by simpa using hu
  have hs' : 1 + (-u) i₀ ≠ 0 := by simpa [sub_eq_add_neg] using hs
  rw [secMinus_eq, det_mul, sec_det_plus i₀ (-u) hu' hs', Dmat_det i₀ j₀ hij, one_mul]

theorem sec_mul_transpose_of_transpose_mul {R : Matrix (Fin N) (Fin N) K} (h : Rᵀ * R = 1) : R * Rᵀ = 1 :=
  mul_eq_one_comm.mp h

/-- `V ∈ O_{e₁}(N) := {V ∈ O(N) : V e₁ = e₁}` (**Lemma III.9.3 (b)**), as the pair of conditions `Vᵀ V = 1`, `V e₁ = e₁`. -/
def IsOrthFixE1 (i₀ : Fin N) (V : Matrix (Fin N) (Fin N) K) : Prop :=
  Vᵀ * V = 1 ∧ V *ᵥ eVec i₀ = eVec i₀

/-- The matrix `V(u) := R₊(u)ᵀ R₋(u) = R₊(u)⁻¹ R₋(u)` of **Lemma III.9.3 (b)**. -/
def overlapV (i₀ j₀ : Fin N) (u : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  (secPlus i₀ u)ᵀ * secMinus i₀ j₀ u

/-- **Lemma III.9.3 (b)**: where both charts are defined on the quadric, `R₋(u) = R₊(u) V(u)` with `V(u) ∈ O_{e₁}(N)`. For real `u` (`K = ℝ`) this is the real statement. -/
theorem sec_overlap (i₀ j₀ : Fin N) (u : Fin N → K) (hu : u ⬝ᵥ u = 1) (hp : 1 + u i₀ ≠ 0)
    (hm : 1 - u i₀ ≠ 0) :
    secMinus i₀ j₀ u = secPlus i₀ u * overlapV i₀ j₀ u ∧ IsOrthFixE1 i₀ (overlapV i₀ j₀ u) := by
  have ho := sec_orth_plus i₀ u hu hp
  have ho' := sec_mul_transpose_of_transpose_mul ho
  have hom := sec_orth_minus i₀ j₀ u hu hm
  refine ⟨?_, ?_, ?_⟩
  · unfold overlapV; rw [← Matrix.mul_assoc, ho', one_mul]
  · unfold overlapV
    have e1 : ((secPlus i₀ u)ᵀ * secMinus i₀ j₀ u)ᵀ * ((secPlus i₀ u)ᵀ * secMinus i₀ j₀ u)
        = (secMinus i₀ j₀ u)ᵀ * (secPlus i₀ u * (secPlus i₀ u)ᵀ) * secMinus i₀ j₀ u := by
      simp [transpose_mul, Matrix.mul_assoc]
    rw [e1, ho', Matrix.mul_one, hom]
  · unfold overlapV
    rw [← mulVec_mulVec, sec_e1_minus i₀ j₀ u hu hm]
    have h3 : (secPlus i₀ u)ᵀ *ᵥ (secPlus i₀ u *ᵥ eVec i₀) = eVec i₀ := by
      rw [mulVec_mulVec, ho, one_mulVec]
    rwa [sec_e1_plus i₀ u hu hp] at h3

theorem Aof_map {L : Type*} [Field L] (f : K →+* L) (i₀ : Fin N) (u : Fin N → K) :
    (Aof i₀ u).map f = Aof i₀ (f ∘ u) := by
  ext i j
  by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;> simp [Aof, vecMulVec, eVec, Pi.single_apply, hi, hj]

/-- Field homomorphisms commute with `R₊` (so `R₊` of a real unit vector is the real matrix `R₊` viewed in `ℂ`). -/
theorem secPlus_map {L : Type*} [Field L] (f : K →+* L) (i₀ : Fin N) (u : Fin N → K) :
    (secPlus i₀ u).map f = secPlus i₀ (f ∘ u) := by
  have hm : (Aof i₀ u * Aof i₀ u).map f = Aof i₀ (f ∘ u) * Aof i₀ (f ∘ u) := by
    rw [← Aof_map f i₀ u]
    exact f.mapMatrix.map_mul _ _
  unfold secPlus
  rw [Matrix.map_add _ (map_add f), Matrix.map_add _ (map_add f), Matrix.map_one f (map_zero f) (map_one f), Aof_map]
  congr 1
  ext i j
  have := congrFun (congrFun hm i) j
  simp only [Matrix.map_apply] at this
  simp [Matrix.smul_apply, this]

theorem Dmat_map {L : Type*} [Field L] (f : K →+* L) (i₀ j₀ : Fin N) :
    (Dmat i₀ j₀ : Matrix (Fin N) (Fin N) K).map f = Dmat i₀ j₀ := by
  ext i j
  by_cases h : i = j
  · subst h; by_cases h2 : i = i₀ ∨ i = j₀ <;> simp [Dmat, h2]
  · simp [Dmat, h]

theorem secMinus_map {L : Type*} [Field L] (f : K →+* L) (i₀ j₀ : Fin N) (u : Fin N → K) :
    (secMinus i₀ j₀ u).map f = secMinus i₀ j₀ (f ∘ u) := by
  have hn : (-(f ∘ u)) = f ∘ (-u) := by ext; simp
  rw [secMinus_eq, secMinus_eq, hn, ← secPlus_map f i₀ (-u)]
  have := f.mapMatrix.map_mul (secPlus i₀ (-u)) (Dmat i₀ j₀)
  simp only [RingHom.mapMatrix_apply] at this
  rw [this, Dmat_map]

/-- Reality (**Lemma III.9.3 (a)**): the complex `R₊` of a real vector is the real `R₊` mapped to `ℂ`; with `sec_orth_plus` and `sec_det_plus` over `ℝ` it is a real rotation. -/
theorem secPlus_ofReal (i₀ : Fin N) (u : Fin N → ℝ) :
    (secPlus i₀ u).map Complex.ofReal = secPlus i₀ (fun k => (u k : ℂ)) :=
  secPlus_map Complex.ofRealHom i₀ u

/-- Reality of `R₋` (**Lemma III.9.3 (a)**), see `secPlus_ofReal`. -/
theorem secMinus_ofReal (i₀ j₀ : Fin N) (u : Fin N → ℝ) :
    (secMinus i₀ j₀ u).map Complex.ofReal = secMinus i₀ j₀ (fun k => (u k : ℂ)) :=
  secMinus_map Complex.ofRealHom i₀ j₀ u

theorem secPlus_apply (i₀ : Fin N) (u : Fin N → ℂ) (i j : Fin N) :
    secPlus i₀ u i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + (u i * eVec i₀ j - eVec i₀ i * u j)
      + (1 + u i₀)⁻¹ * ∑ k, (u i * eVec i₀ k - eVec i₀ i * u k) * (u k * eVec i₀ j - eVec i₀ k * u j) := by
  simp [secPlus, Aof, Matrix.mul_apply, vecMulVec]

/-- **Lemma III.9.3 (a)**, analyticity: every entry of `R₊` is analytic in `u ∈ ℂ^N` on the open set `{1 + u·e₁ ≠ 0}` (hence on the quadric minus the pole). -/
theorem secPlus_analytic (i₀ : Fin N) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun u : Fin N → ℂ => secPlus i₀ u i j) {u | 1 + u i₀ ≠ 0} := by
  intro u hu
  simp only [secPlus_apply]
  have hp : ∀ k, AnalyticAt ℂ (fun u : Fin N → ℂ => u k) u := fun k =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).analyticAt u
  refine AnalyticAt.add (AnalyticAt.add analyticAt_const ?_) ?_
  · exact ((hp i).mul analyticAt_const).sub (analyticAt_const.mul (hp j))
  · refine AnalyticAt.mul (AnalyticAt.inv (analyticAt_const.add (hp i₀)) hu) ?_
    refine Finset.analyticAt_fun_sum _ fun k _ => ?_
    exact (((hp i).mul analyticAt_const).sub (analyticAt_const.mul (hp k))).mul
      (((hp k).mul analyticAt_const).sub (analyticAt_const.mul (hp j)))

/-- **Lemma III.9.3 (a)**, analyticity of the entries of `R₋` on `{1 − u·e₁ ≠ 0}`. -/
theorem secMinus_analytic (i₀ j₀ : Fin N) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun u : Fin N → ℂ => secMinus i₀ j₀ u i j) {u | 1 - u i₀ ≠ 0} := by
  intro u hu
  have h : ∀ v : Fin N → ℂ, secMinus i₀ j₀ v i j = secPlus i₀ (-v) i j * (if j = i₀ ∨ j = j₀ then -1 else 1) := by
    intro v
    rw [secMinus_eq]
    simp [Dmat, Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [h]
  refine AnalyticAt.mul ?_ analyticAt_const
  have hn : AnalyticAt ℂ (fun v : Fin N → ℂ => -v) u := (analyticAt_id).neg
  have := secPlus_analytic i₀ i j (-u) (by simpa [sub_eq_add_neg] using hu)
  exact this.comp hn

/-- The chart section `R_σ(u)` of **Definition III.9.2** for a complex `u`: `σ = +` if `Re (u·e₁) ≥ 0` and `σ = −` otherwise. -/
noncomputable def secChart (i₀ j₀ : Fin N) (u : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if 0 ≤ (u i₀).re then secPlus i₀ u else secMinus i₀ j₀ u

/-- Denominator margins for the chart choice: `Re (u·e₁) ≥ 0` gives `|1 + u·e₁| ≥ 1`, otherwise `|1 − u·e₁| > 1`. -/
theorem sec_chart_den (i₀ : Fin N) (u : Fin N → ℂ) :
    (0 ≤ (u i₀).re → 1 ≤ ‖1 + u i₀‖) ∧ (¬ 0 ≤ (u i₀).re → 1 < ‖1 - u i₀‖) := by
  constructor
  · intro h
    refine le_trans ?_ (Complex.re_le_norm _)
    simp; linarith
  · intro h
    refine lt_of_lt_of_le ?_ (Complex.re_le_norm _)
    simp; linarith

/-- Non-vacuity of the chart cover (**Def. III.9.2**): every real vector, in particular every point of the unit sphere, lies in the chart `+` with `1 + u·e₁ ≥ 1` or the chart `−` with `|1 − u·e₁| > 1`. -/
theorem sec_charts_cover (i₀ : Fin N) (u : Fin N → ℝ) :
    (0 ≤ u i₀ ∧ 1 ≤ |1 + u i₀|) ∨ (u i₀ < 0 ∧ 1 < |1 - u i₀|) := by
  rcases le_or_gt 0 (u i₀) with h | h
  · left; exact ⟨h, by rw [abs_of_nonneg (by linarith)]; linarith⟩
  · right; exact ⟨h, by rw [abs_of_nonneg (by linarith)]; linarith⟩

theorem sec_den_plus_ne (i₀ : Fin N) (u : Fin N → ℂ) (h : 0 ≤ (u i₀).re) : 1 + u i₀ ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le one_pos ((sec_chart_den i₀ u).1 h))

theorem sec_den_minus_ne (i₀ : Fin N) (u : Fin N → ℂ) (h : ¬ 0 ≤ (u i₀).re) : 1 - u i₀ ≠ 0 :=
  norm_pos_iff.mp (lt_trans one_pos ((sec_chart_den i₀ u).2 h))

/-- **Lemma III.9.3 (a)** for the chart section `R_σ(u)`: complex orthogonality on the quadric, with no side condition (the chart choice guarantees a nonzero denominator). -/
theorem secChart_orth (i₀ j₀ : Fin N) (u : Fin N → ℂ) (hu : u ⬝ᵥ u = 1) :
    (secChart i₀ j₀ u)ᵀ * secChart i₀ j₀ u = 1 := by
  unfold secChart
  by_cases h : 0 ≤ (u i₀).re
  · simp only [h, ↓reduceIte]
    exact sec_orth_plus i₀ u hu (sec_den_plus_ne i₀ u h)
  · simp only [h, ↓reduceIte]
    exact sec_orth_minus i₀ j₀ u hu (sec_den_minus_ne i₀ u h)

/-- **Lemma III.9.3 (a)** for the chart section: `R_σ(u) e₁ = u` on the quadric. -/
theorem secChart_e1 (i₀ j₀ : Fin N) (u : Fin N → ℂ) (hu : u ⬝ᵥ u = 1) :
    secChart i₀ j₀ u *ᵥ eVec i₀ = u := by
  unfold secChart
  by_cases h : 0 ≤ (u i₀).re
  · simp only [h, ↓reduceIte]
    exact sec_e1_plus i₀ u hu (sec_den_plus_ne i₀ u h)
  · simp only [h, ↓reduceIte]
    exact sec_e1_minus i₀ j₀ u hu (sec_den_minus_ne i₀ u h)

/-- `det R_σ(u) = 1` on the quadric for the chart section (`i₀ ≠ j₀`). -/
theorem secChart_det (i₀ j₀ : Fin N) (hij : i₀ ≠ j₀) (u : Fin N → ℂ) (hu : u ⬝ᵥ u = 1) :
    (secChart i₀ j₀ u).det = 1 := by
  unfold secChart
  by_cases h : 0 ≤ (u i₀).re
  · simp only [h, ↓reduceIte]
    exact sec_det_plus i₀ u hu (sec_den_plus_ne i₀ u h)
  · simp only [h, ↓reduceIte]
    exact sec_det_minus i₀ j₀ hij u hu (sec_den_minus_ne i₀ u h)

/-- **LF-RECONSTRUCTION Definition III.9.4** (algebraic part; P7 p. 521): the change of variables `ψ ↦ Rψ` applied sitewise to a configuration `ψ : ι → ℝ^N` (or `ℂ^N`). The reference measure and kernels are not part of this definition. -/
def rotRep {ι : Type*} (R : Matrix (Fin N) (Fin N) K) (ψ : ι → Fin N → K) : ι → Fin N → K :=
  fun x => R *ᵥ ψ x

/-- **Definition III.9.4** (algebraic part): `ψ ↦ Rψ` preserves the bilinear product of any two sites, in particular the hard-spin constraint `ψ x · ψ x = 1`, and every function of the Gram matrix. -/
theorem rotRep_dot {ι : Type*} {R : Matrix (Fin N) (Fin N) K} (hR : Rᵀ * R = 1)
    (ψ : ι → Fin N → K) (x y : ι) : rotRep R ψ x ⬝ᵥ rotRep R ψ y = ψ x ⬝ᵥ ψ y := by
  unfold rotRep
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hR, one_mulVec]

/-- `rotRep Rᵀ` is a left inverse of `rotRep R` when `Rᵀ R = 1`. -/
theorem rotRep_inv {ι : Type*} {R : Matrix (Fin N) (Fin N) K} (hR : Rᵀ * R = 1)
    (ψ : ι → Fin N → K) : rotRep Rᵀ (rotRep R ψ) = ψ := by
  funext x; unfold rotRep; rw [mulVec_mulVec, hR, one_mulVec]

/-- `rotRep Rᵀ` is a right inverse of `rotRep R` when `Rᵀ R = 1`. -/
theorem rotRep_inv' {ι : Type*} {R : Matrix (Fin N) (Fin N) K} (hR : Rᵀ * R = 1)
    (ψ : ι → Fin N → K) : rotRep R (rotRep Rᵀ ψ) = ψ := by
  funext x; unfold rotRep; rw [mulVec_mulVec, sec_mul_transpose_of_transpose_mul hR, one_mulVec]

/-- `rotRep R` is a bijection of configurations when `Rᵀ R = 1`, with inverse `rotRep Rᵀ` (**Definition III.9.4**). -/
def rotRepEquiv {ι : Type*} {R : Matrix (Fin N) (Fin N) K} (hR : Rᵀ * R = 1) :
    (ι → Fin N → K) ≃ (ι → Fin N → K) where
  toFun := rotRep R
  invFun := rotRep Rᵀ
  left_inv := rotRep_inv hR
  right_inv := rotRep_inv' hR

/-- **Lemma III.9.3 (a)**, real unit vectors give real rotations: for real `u` with `u·u = 1`, `u·e₁ ≠ −1`,
`R₊(u)` (over `ℝ`) satisfies `Rᵀ R = I`, `det R = 1`, and its image in `ℂ` is the complex `R₊(u)`. -/
theorem sec_plus_real (i₀ : Fin N) (u : Fin N → ℝ) (hu : u ⬝ᵥ u = 1) (hs : 1 + u i₀ ≠ 0) :
    (secPlus i₀ u)ᵀ * secPlus i₀ u = 1 ∧ (secPlus i₀ u).det = 1 ∧
      (secPlus i₀ u).map Complex.ofReal = secPlus i₀ (fun k => (u k : ℂ)) :=
  ⟨sec_orth_plus i₀ u hu hs, sec_det_plus i₀ u hu hs, secPlus_ofReal i₀ u⟩

/-- **Lemma III.9.3 (a)**, real unit vectors give real rotations, chart `−` (`i₀ ≠ j₀`). -/
theorem sec_minus_real (i₀ j₀ : Fin N) (hij : i₀ ≠ j₀) (u : Fin N → ℝ) (hu : u ⬝ᵥ u = 1)
    (hs : 1 - u i₀ ≠ 0) :
    (secMinus i₀ j₀ u)ᵀ * secMinus i₀ j₀ u = 1 ∧ (secMinus i₀ j₀ u).det = 1 ∧
      (secMinus i₀ j₀ u).map Complex.ofReal = secMinus i₀ j₀ (fun k => (u k : ℂ)) :=
  ⟨sec_orth_minus i₀ j₀ u hu hs, sec_det_minus i₀ j₀ hij u hu hs, secMinus_ofReal i₀ j₀ u⟩

/-- **Definition III.9.4** (reference site): with `R = R_σ(ψ₀)` on the quadric, `R e₁ = ψ₀` and
`R⁻¹ ψ₀ = Rᵀ ψ₀ = e₁`, i.e. the rotated reference value is `e₁` (`χ⁰(Rx; ψ₀) = χ⁰(x; R⁻¹ψ₀)`). -/
theorem secChart_transpose_ref (i₀ j₀ : Fin N) (u : Fin N → ℂ) (hu : u ⬝ᵥ u = 1) :
    (secChart i₀ j₀ u)ᵀ *ᵥ u = eVec i₀ := by
  have h3 : (secChart i₀ j₀ u)ᵀ *ᵥ (secChart i₀ j₀ u *ᵥ eVec i₀) = eVec i₀ := by
    rw [mulVec_mulVec, secChart_orth i₀ j₀ u hu, one_mulVec]
  rwa [secChart_e1 i₀ j₀ u hu] at h3

/-- **Definition III.9.4**: rotating a configuration by `R_σ(ψ₀)⁻¹ = R_σ(ψ₀)ᵀ`, `ψ₀ = ψ x₀` the value at the
reference site `x₀`, sends the reference value to `e₁`. -/
theorem rotRep_ref_site {ι : Type*} (i₀ j₀ : Fin N) (ψ : ι → Fin N → ℂ) (x₀ : ι)
    (hu : ψ x₀ ⬝ᵥ ψ x₀ = 1) :
    rotRep (secChart i₀ j₀ (ψ x₀))ᵀ ψ x₀ = eVec i₀ :=
  secChart_transpose_ref i₀ j₀ (ψ x₀) hu

/-- **Definition III.9.4**: the hard-spin constraint `ψ x · ψ x = 1` at every site is preserved. -/
theorem rotRep_hardSpin {ι : Type*} {R : Matrix (Fin N) (Fin N) K} (hR : Rᵀ * R = 1)
    (ψ : ι → Fin N → K) (h : ∀ x, ψ x ⬝ᵥ ψ x = 1) (x : ι) : rotRep R ψ x ⬝ᵥ rotRep R ψ x = 1 := by
  rw [rotRep_dot hR]; exact h x

end Balaban.LargeField
