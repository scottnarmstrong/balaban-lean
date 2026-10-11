/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Restriction

/-!
# The geometric resolvent identity

For `Λ ⊆ Λ'` and `y ∈ Λ`,
`G_Λ(x,y) = G_{Λ'}(x,y) + ∑_{u ∈ Λ'∖Λ} ∑_{z ∈ Λ} G_{Λ'}(x,u) A(u,z) G_Λ(z,y)`,
where `G_Λ = greenFn A t Λ` is `(A_Λ + t)⁻¹` extended by zero to `ι × ι`
(`Balaban.Green.greenFn_resolvent_identity`).  Algebraic route of our own; no decay is used.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

variable {ι : Type*} [DecidableEq ι]

/-- `(A_Λ + t)⁻¹`, extended by zero to `ι × ι`. -/
noncomputable def greenFn (A : Matrix ι ι ℂ) (t : ℂ) (Λ : Finset ι) (x y : ι) : ℂ :=
  if h : x ∈ Λ ∧ y ∈ Λ then
    (restrictOp A Λ + t • (1 : Matrix Λ Λ ℂ))⁻¹ ⟨x, h.1⟩ ⟨y, h.2⟩
  else 0

lemma greenFn_of_not_mem_left {A : Matrix ι ι ℂ} {t : ℂ} {Λ : Finset ι} {x : ι} (y : ι)
    (hx : x ∉ Λ) : greenFn A t Λ x y = 0 := by
  simp [greenFn, hx]

lemma greenFn_of_not_mem_right {A : Matrix ι ι ℂ} {t : ℂ} {Λ : Finset ι} {y : ι} (x : ι)
    (hy : y ∉ Λ) : greenFn A t Λ x y = 0 := by
  simp [greenFn, hy]

lemma sum_bm_greenFn {A : Matrix ι ι ℂ} {t : ℂ} {Λ : Finset ι}
    (hU : IsUnit (restrictOp A Λ + t • (1 : Matrix Λ Λ ℂ))) {x y : ι} (hx : x ∈ Λ)
    (hy : y ∈ Λ) : ∑ z ∈ Λ, bm A t x z * greenFn A t Λ z y = if x = y then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 hU)) ⟨x, hx⟩) ⟨y, hy⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← Finset.sum_coe_sort Λ]
  simp only [Subtype.ext_iff] at h
  convert h using 2 with z _
  · rw [restrictOp_add_smul_one_apply, greenFn]; simp [z.2, hy]

lemma sum_greenFn_bm {A : Matrix ι ι ℂ} {t : ℂ} {Λ : Finset ι}
    (hU : IsUnit (restrictOp A Λ + t • (1 : Matrix Λ Λ ℂ))) {x y : ι} (hx : x ∈ Λ)
    (hy : y ∈ Λ) : ∑ z ∈ Λ, greenFn A t Λ x z * bm A t z y = if x = y then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 hU)) ⟨x, hx⟩) ⟨y, hy⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← Finset.sum_coe_sort Λ]
  simp only [Subtype.ext_iff] at h
  convert h using 2 with z _
  · rw [restrictOp_add_smul_one_apply, greenFn]; simp [z.2, hx]

/-- Applying the inverse: `w x = ∑_{x'} G x x' ∑_z B x' z w z` for `x ∈ Λ`. -/
lemma eq_sum_greenFn_bm {A : Matrix ι ι ℂ} {t : ℂ} {Λ : Finset ι}
    (hU : IsUnit (restrictOp A Λ + t • (1 : Matrix Λ Λ ℂ))) {x : ι} (hx : x ∈ Λ)
    (w : ι → ℂ) :
    w x = ∑ x' ∈ Λ, greenFn A t Λ x x' * ∑ z ∈ Λ, bm A t x' z * w z := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ z ∈ Λ, ∑ x' ∈ Λ, greenFn A t Λ x x' * (bm A t x' z * w z)
      = (if x = z then 1 else 0) * w z := by
    intro z hz
    rw [← sum_greenFn_bm hU hx hz, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [Finset.sum_congr rfl this]
  simp [hx]

/-- **Geometric resolvent identity.** For `Λ ⊆ Λ'` and `y ∈ Λ`,
`G_Λ(x,y) = G_{Λ'}(x,y) + ∑_{u ∈ Λ'∖Λ} ∑_{z ∈ Λ} G_{Λ'}(x,u) A(u,z) G_Λ(z,y)`. -/
theorem greenFn_resolvent_identity {A : Matrix ι ι ℂ} {t : ℂ} {Λ Λ' : Finset ι}
    (hΛ : Λ ⊆ Λ') (hU : IsUnit (restrictOp A Λ + t • (1 : Matrix Λ Λ ℂ)))
    (hU' : IsUnit (restrictOp A Λ' + t • (1 : Matrix Λ' Λ' ℂ))) (x : ι) {y : ι} (hy : y ∈ Λ) :
    greenFn A t Λ x y = greenFn A t Λ' x y +
      ∑ u ∈ Λ' \ Λ, ∑ z ∈ Λ, greenFn A t Λ' x u * A u z * greenFn A t Λ z y := by
  set u : ι → ℂ := fun z => greenFn A t Λ z y with hu
  set g : ι → ℂ := fun z => greenFn A t Λ' z y with hg
  have hy' : y ∈ Λ' := hΛ hy
  -- the equation satisfied by `u - g` on `Λ'`
  have heq : ∀ x' ∈ Λ', ∑ z ∈ Λ', bm A t x' z * (u z - g z)
      = if x' ∈ Λ then 0 else ∑ z ∈ Λ, A x' z * u z := by
    intro x' hx'
    have ha : ∑ z ∈ Λ', bm A t x' z * g z = if x' = y then 1 else 0 :=
      sum_bm_greenFn hU' hx' hy'
    have hb : ∑ z ∈ Λ', bm A t x' z * u z = ∑ z ∈ Λ, bm A t x' z * u z := by
      symm
      refine Finset.sum_subset hΛ fun z _ hz => ?_
      simp [hu, greenFn_of_not_mem_left y hz]
    simp only [mul_sub, Finset.sum_sub_distrib, ha, hb]
    by_cases hx : x' ∈ Λ
    · simp only [hx, ↓reduceIte]; rw [sum_bm_greenFn hU hx hy]; ring
    · have hxy : x' ≠ y := fun e => hx (e ▸ hy)
      simp only [hx, hxy, ↓reduceIte]
      have : ∀ z ∈ Λ, bm A t x' z * u z = A x' z * u z := by
        intro z hz
        have : x' ≠ z := fun e => hx (e ▸ hz)
        simp [bm, this]
      rw [Finset.sum_congr rfl this]; ring
  by_cases hx : x ∈ Λ'
  · have key := eq_sum_greenFn_bm hU' hx (fun z => u z - g z)
    rw [Finset.sum_congr rfl fun x' hx' => by rw [heq x' hx']] at key
    set f' : ι → ℂ := fun x' =>
      greenFn A t Λ' x x' * (if x' ∈ Λ then 0 else ∑ z ∈ Λ, A x' z * u z) with hf'
    have hsub : ∑ x' ∈ Λ' \ Λ, f' x' = ∑ x' ∈ Λ', f' x' := by
      refine Finset.sum_subset Finset.sdiff_subset fun x' hx' hn => ?_
      have : x' ∈ Λ := by
        by_contra h; exact hn (Finset.mem_sdiff.2 ⟨hx', h⟩)
      simp [hf', this]
    have hsub2 : ∑ x' ∈ Λ' \ Λ, f' x'
        = ∑ x' ∈ Λ' \ Λ, ∑ z ∈ Λ, greenFn A t Λ' x x' * A x' z * u z := by
      refine Finset.sum_congr rfl fun x' hx' => ?_
      have : x' ∉ Λ := (Finset.mem_sdiff.1 hx').2
      simp only [hf', this, ite_false, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hfin : u x - g x = ∑ x' ∈ Λ' \ Λ, ∑ z ∈ Λ, greenFn A t Λ' x x' * A x' z * u z := by
      rw [← hsub2, hsub]
      exact key
    show u x = _
    linear_combination hfin
  · have h1 : x ∉ Λ := fun h => hx (hΛ h)
    simp [greenFn_of_not_mem_left y h1, greenFn_of_not_mem_left y hx,
      greenFn_of_not_mem_left _ hx]

end Balaban.Green
