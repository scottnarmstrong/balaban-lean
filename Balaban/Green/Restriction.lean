/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.CombesThomas

/-!
# Domain restrictions and the geometric resolvent identity

For `Λ : Finset ι` the restriction `restrictOp A Λ : Matrix Λ Λ ℂ` is the submatrix of `A` on
`Λ`.  This file proves

* `Balaban.Green.combesThomas_restrict`: the Combes–Thomas estimate for `(A_Λ + t)⁻¹`, with the
  same constants as for `A` (the ball sums and the coercivity pass to subsets);
* `Balaban.Green.greenFn_resolvent_identity`: for `Λ ⊆ Λ'` and `y ∈ Λ`,
  `G_Λ(x,y) = G_{Λ'}(x,y) + ∑_{u ∈ Λ'∖Λ} ∑_{z ∈ Λ} G_{Λ'}(x,u) A(u,z) G_Λ(z,y)`,
  where `G_Λ = greenFn A t Λ` is `(A_Λ + t)⁻¹` extended by zero to `ι × ι`.

Both are by our own route; the method for the first follows
`FroehlichSpencer.Infra.Green.CombesThomasGap` (Armstrong–Loher; public repository
`scottnarmstrong/Frohlich-Spencer`, commit b47bc3d).
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The restriction of `A` to the finite set `Λ`. -/
def restrictOp (A : Matrix ι ι ℂ) (Λ : Finset ι) : Matrix Λ Λ ℂ :=
  A.submatrix (fun x : Λ => (x : ι)) (fun y : Λ => (y : ι))

/-- The entries of `A + t`. -/
def bm (A : Matrix ι ι ℂ) (t : ℂ) (x z : ι) : ℂ := A x z + if x = z then t else 0

omit [Fintype ι] in
lemma restrictOp_add_smul_one_apply (A : Matrix ι ι ℂ) (t : ℂ) (Λ : Finset ι) (x z : Λ) :
    (restrictOp A Λ + t • (1 : Matrix Λ Λ ℂ)) x z = bm A t x z := by
  simp only [restrictOp, bm, Matrix.add_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : (x : ι) = (z : ι)
  · have : x = z := Subtype.ext h
    simp [this]
  · have : x ≠ z := fun e => h (e ▸ rfl)
    simp [h, this]

omit [DecidableEq ι] in
/-- A sum over `ι` of a function vanishing off `Λ` is the sum over the subtype `Λ`. -/
lemma sum_eq_sum_subtype {M : Type*} [AddCommMonoid M] (Λ : Finset ι) (g : ι → M)
    (h : ∀ i, i ∉ Λ → g i = 0) : ∑ i, g i = ∑ i : Λ, g i :=
  (Finset.sum_subset (Finset.subset_univ Λ) (fun i _ hi => h i hi)).symm.trans
    (Finset.sum_coe_sort Λ g).symm

/-- Restriction preserves coercivity. -/
theorem isCoercive_restrictOp {A : Matrix ι ι ℂ} {γ : ℝ} (h : IsCoercive A γ) (Λ : Finset ι) :
    IsCoercive (restrictOp A Λ) γ := by
  intro v
  set w : ι → ℂ := fun i => if hi : i ∈ Λ then v ⟨i, hi⟩ else 0 with hw
  have hwΛ : ∀ i : Λ, w i = v i := fun i => by simp [hw, i.2]
  have hN : sqNorm w = sqNorm v := by
    unfold sqNorm
    rw [sum_eq_sum_subtype Λ _ (fun i hi => by simp [hw, hi])]
    exact Finset.sum_congr rfl fun i _ => by rw [hwΛ]
  have hQ : reQuad A w = reQuad (restrictOp A Λ) v := by
    unfold reQuad
    congr 1
    rw [sum_eq_sum_subtype Λ _ (fun i hi => by simp [hw, hi])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwΛ]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_eq_sum_subtype Λ _ (fun j hj => by simp [hw, hj])]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [restrictOp, hwΛ]
  have := h w
  rwa [hN, hQ] at this

variable [PseudoMetricSpace ι] {c₀ δ₀ γ₀ κ : ℝ}

/-- **Combes–Thomas for a restriction**: same constants as for the whole space. -/
theorem combesThomas_restrict {A : Matrix ι ι ℂ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀)
    (hκ : 0 ≤ κ)
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hcoer : IsCoercive A γ₀) (Λ : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (restrictOp A Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ)) ∧
      ∀ x y : Λ, ‖(restrictOp A Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ))⁻¹ x y‖ ≤
        2 * (γ₀ + t)⁻¹ * Real.exp (-(ctRate c₀ δ₀ γ₀ κ) * dist (x : ι) (y : ι)) := by
  refine combesThomas (ι := Λ) hc hδ hγ hκ ?_ ?_ (isCoercive_restrictOp hcoer Λ) ht
  · intro x y; simpa [restrictOp, Subtype.dist_eq] using hA x y
  · intro x
    calc ∑ y : Λ, Real.exp (-(δ₀ / 4) * dist x y)
        = ∑ y ∈ Λ, Real.exp (-(δ₀ / 4) * dist (x : ι) y) := by
          rw [← Finset.sum_coe_sort Λ]; rfl
      _ ≤ ∑ y, Real.exp (-(δ₀ / 4) * dist (x : ι) y) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ κ := hK x

/-! ### Perturbation bound -/

omit [DecidableEq ι] in
/-- Convolution of two exponentially decaying kernels, losing half of the rate. -/
lemma norm_mul_entry_le {P Q : Matrix ι ι ℂ} {b p q κ : ℝ} (hb : 0 < b) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q)
    (hp : ∀ x y, ‖P x y‖ ≤ p * Real.exp (-b * dist x y))
    (hq : ∀ x y, ‖Q x y‖ ≤ q * Real.exp (-b * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(b / 2) * dist x y) ≤ κ) (x y : ι) :
    ‖(P * Q) x y‖ ≤ p * q * κ * Real.exp (-(b / 2) * dist x y) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have key : ∀ z, ‖P x z * Q z y‖ ≤
      p * q * (Real.exp (-(b / 2) * dist x y) * Real.exp (-(b / 2) * dist x z)) := by
    intro z
    rw [norm_mul]
    have e : Real.exp (-b * dist x z) * Real.exp (-b * dist z y)
        ≤ Real.exp (-(b / 2) * dist x y) * Real.exp (-(b / 2) * dist x z) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := dist_triangle x z y
      have := dist_nonneg (x := z) (y := y)
      nlinarith
    calc ‖P x z‖ * ‖Q z y‖ ≤ (p * Real.exp (-b * dist x z)) * (q * Real.exp (-b * dist z y)) :=
          mul_le_mul (hp x z) (hq z y) (norm_nonneg _) (by positivity)
      _ = p * q * (Real.exp (-b * dist x z) * Real.exp (-b * dist z y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e (by positivity)
  calc ∑ z, ‖P x z * Q z y‖ ≤ ∑ z, p * q * (Real.exp (-(b / 2) * dist x y) *
        Real.exp (-(b / 2) * dist x z)) := Finset.sum_le_sum fun z _ => key z
    _ = p * q * Real.exp (-(b / 2) * dist x y) * ∑ z, Real.exp (-(b / 2) * dist x z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ p * q * Real.exp (-(b / 2) * dist x y) * κ :=
        mul_le_mul_of_nonneg_left (hK x) (by positivity)
    _ = _ := by ring

/-- Perturbation bound: if `B` and `B'` are invertible with inverses `G`, `G'` decaying at rate
`a` (constants `C`, `C'`) and `B - B'` decays at rate `a` (constant `p`), then `G' - G`
decays at rate `a / 4` with constant `C p C' κ²`, where `κ` bounds the ball sums at `a / 4`. -/
theorem perturbation_decay {B B' : Matrix ι ι ℂ} (hB : IsUnit B) (hB' : IsUnit B')
    {a C C' p κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hp0 : 0 ≤ p)
    (hG : ∀ x y, ‖B⁻¹ x y‖ ≤ C * Real.exp (-a * dist x y))
    (hG' : ∀ x y, ‖B'⁻¹ x y‖ ≤ C' * Real.exp (-a * dist x y))
    (hP : ∀ x y, ‖(B - B') x y‖ ≤ p * Real.exp (-a * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(a / 4) * dist x y) ≤ κ) (x y : ι) :
    ‖(B'⁻¹ - B⁻¹) x y‖ ≤ C * p * C' * κ * κ * Real.exp (-(a / 4) * dist x y) := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 hB
  have hdet' : IsUnit B'.det := (Matrix.isUnit_iff_isUnit_det _).1 hB'
  have hid : B'⁻¹ - B⁻¹ = B⁻¹ * ((B - B') * B'⁻¹) := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ hdet', Matrix.mul_sub, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul, Matrix.mul_one]
  have wk : ∀ {b b' : ℝ}, b' ≤ b → ∀ x y : ι, Real.exp (-b * dist x y) ≤ Real.exp (-b' * dist x y) :=
    fun hbb x y => Real.exp_le_exp.2 (by nlinarith [dist_nonneg (x := x) (y := y)])
  have hK2 : ∀ x : ι, ∑ y, Real.exp (-(a / 2) * dist x y) ≤ κ := fun x =>
    (Finset.sum_le_sum fun y _ => wk (by linarith) x y).trans (hK x)
  have h1 := norm_mul_entry_le ha hp0 hC' hP hG' hK2
  have hK4 : ∀ x : ι, ∑ y, Real.exp (-(a / 2 / 2) * dist x y) ≤ κ := by
    intro x
    rw [show a / 2 / 2 = a / 4 by ring]
    exact hK x
  have h2 := norm_mul_entry_le (P := B⁻¹) (Q := (B - B') * B'⁻¹) (b := a / 2) (p := C)
    (q := p * C' * κ) (κ := κ) (by linarith) hC (by positivity)
    (fun x y => (hG x y).trans (mul_le_mul_of_nonneg_left (wk (by linarith) x y) hC))
    h1 hK4 x y
  rw [hid]
  rw [show a / 2 / 2 = a / 4 by ring] at h2
  calc _ ≤ _ := h2
    _ = _ := by ring

end Balaban.Green
