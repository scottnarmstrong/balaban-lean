/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxResolvent
public import Balaban.Green.LimitCauchy
public import Balaban.Polymer.TwoTorusFinal
public import Balaban.Green.FinalMassSqrt

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closeness of the final resolvent on two tori (W798, blocker 7, estimate (I2))

The final operator `finalOp d L m k v a` of the torus of side `m` (a Schur complement of the fine
operator `-N²Δ + v + a P`, `N = L^k`) and the one of side `m'` are not equal on a common box: their
entries differ by terms that are exponentially small in the distance to the torus boundary.  The
sites of a centred cube `{|u_μ| ≤ R}` of `ℤ^d` are lifted to both tori by the cast `castL1`
(the identity on residues).

* `fineGreen_close`, `boxGreen_fine_eq`: the entries of the inverse of the fine operator at sites of
  a cube of the two tori differ by `2 ctDiff exp(-ctDecay · 2 N (Rm - Rc))`, because both are within
  that distance of the Dirichlet Green function of the same large cube, on which the two fine
  operators have the same entries (the cube is small for the block structure).
* `finalOp_entry_close`: the entries of `finalOp` at the sites of a cube of radius `Rc` differ by
  `C exp(-c (Rm - Rc))` (a finite sum over the two blocks of `ℤ^d`).
* `final_sub_boxG_le`: the entry `(U + t)⁻¹ x y` against the box resolvent `boxG`
  (`Green/FinalBoxResolvent`) for `y` in the box and `x` at distance `≥ ρ` from its complement,
  by the exact identity `Gb - G P = G (1 - P) U Gb`; `final_boxG_close`: the box resolvents of
  two operators whose entries differ by at most `ε` on the box differ by `|B|² ε / (g + t)²`.
* `final_resolvent_close_of_entries`: the bound for a box centred at one of the two sites.
* **`finalResolvent_twoTorus_close`**: `‖R_m(u, w) - R_{m'}(u, w)‖ ≤ C exp(-c (min m m' / 2 - R))
  / (finalGap + t)` for `u, w` in the cube of radius `R`, `2 R < min m m'`, all `t ≥ 0`.  The
  constants depend on `d`, `L`, `k` only (the factor `L^k` enters the fine-lattice decay).
-/

@[expose] public section

open Finset Matrix MeasureTheory Set

namespace Balaban.Green

section BoxDifference

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The complement projection is the diagonal of the indicator of the complement. -/
theorem one_sub_boxP_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Finset ι) :
    (1 : Matrix ι ι ℂ) - boxP B = Matrix.diagonal fun i => if i ∈ B then 0 else 1 := by
  ext x y
  by_cases h : x = y
  · subst h; by_cases hx : x ∈ B <;> simp [boxP, hx]
  · simp [boxP, h]

/-- **Resolvent versus box resolvent.**  For `y ∈ B` the entry `(U + t)⁻¹ x y` differs from
`boxG x y` by at most `K exp (-(r/2) ρ)` if `x` is at distance `≥ ρ` from the complement of `B`. -/
theorem final_sub_boxG_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N₀)) (x y : L1Torus d N₀) (hy : y ∈ B) {ρ : ℝ}
    (hρ : ∀ z, z ∉ B → ρ ≤ dist x z) :
    ‖((finalOp d L N₀ k v a + (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹) x y -
        boxG (finalOp d L N₀ k v a) B t x y‖ ≤
      (2 / (finalGap d L + t)) ^ 2 * finalDecayC d L * ballConst d (blockDecayRate d) *
        ballConst d (finalRate d L / 2) * Real.exp (-(finalRate d L / 2) * ρ) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hr := finalRate_pos (L := L) hd
  have hδ := blockDecayRate_pos hd
  have hC := finalDecayC_pos (L := L) hd
  have hbδ : 0 ≤ ballConst d (blockDecayRate d) := ballConst_nonneg hδ
  have hbr : 0 ≤ ballConst d (finalRate d L / 2) := ballConst_nonneg (by positivity)
  set U := finalOp d L N₀ k v a with hU
  set G := (U + (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ with hGdef
  obtain ⟨hunit, hdec⟩ := finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1
    ha2 hmass ht
  have hH := boxH_isUnit_final (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht B
  have hAG : shiftMat U t * G = 1 := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hunit
    exact Matrix.mul_nonsing_inv _ hdet
  have hGA : G * shiftMat U t = 1 := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hunit
    exact Matrix.nonsing_inv_mul _ hdet
  set Gb := boxG U B t with hGb
  have h1 : boxP B * shiftMat U t * Gb = boxP B := boxP_mul_shift_mul_boxG hH
  have h2 : boxP B * Gb = Gb := boxP_mul_boxG hH
  have h3 := boxP_mul_self B
  have h4 : (1 - boxP B) * shiftMat U t * boxP B = (1 - boxP B) * U * boxP B := by
    unfold shiftMat
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, boxP_one_sub_mul B]
    simp
  have h5 : shiftMat U t * Gb = boxP B + (1 - boxP B) * U * Gb := by
    have e1 : shiftMat U t * Gb = boxP B * shiftMat U t * Gb + (1 - boxP B) * shiftMat U t * Gb := by
      rw [← add_mul, ← add_mul, add_sub_cancel, one_mul]
    have e2 : (1 - boxP B) * shiftMat U t * Gb = (1 - boxP B) * U * Gb := by
      calc (1 - boxP B) * shiftMat U t * Gb = (1 - boxP B) * shiftMat U t * (boxP B * Gb) := by
            rw [h2]
        _ = ((1 - boxP B) * shiftMat U t * boxP B) * Gb := by rw [mul_assoc _ (boxP B)]
        _ = _ := by rw [h4, mul_assoc ((1 - boxP B) * U) (boxP B) Gb, h2]
    rw [e1, e2, h1]
  have h6 : Gb = G * boxP B + G * ((1 - boxP B) * U * Gb) := by
    have := congrArg (fun M => G * M) h5
    simp only [mul_add] at this
    rw [← mul_assoc, hGA, one_mul] at this
    exact this
  have h7 : G x y - Gb x y = -(∑ z, G x z * ((if z ∈ B then 0 else 1) *
      ∑ w, U z w * Gb w y)) := by
    have e := congrFun (congrFun h6 x) y
    rw [Matrix.add_apply] at e
    have e1 : (G * boxP B) x y = G x y := by
      simp [boxP, Matrix.mul_diagonal, hy]
    have e2 : (G * ((1 - boxP B) * U * Gb)) x y = ∑ z, G x z * ((if z ∈ B then 0 else 1) *
        ∑ w, U z w * Gb w y) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [one_sub_boxP_eq, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply]
    rw [e1, e2] at e
    linear_combination -e
  rw [h7, norm_neg]
  have hb1 : ∀ z, ‖G x z‖ ≤ 2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x z) := fun z =>
    hdec x z
  have hb2 : ∀ w, ‖Gb w y‖ ≤ 2 / (finalGap d L + t) := fun w => by
    refine (boxG_final_entry_bound (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht B
      w y).trans ?_
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 ?_) (by positivity)).trans
      (by rw [mul_one])
    have : 0 ≤ finalRate d L * dist w y := mul_nonneg hr.le dist_nonneg
    linarith
  have hb3 : ∀ z, ∑ w, ‖U z w * Gb w y‖ ≤ finalDecayC d L * ballConst d (blockDecayRate d) *
      (2 / (finalGap d L + t)) := fun z => by
    calc ∑ w, ‖U z w * Gb w y‖ ≤ ∑ w, finalDecayC d L * Real.exp (-blockDecayRate d * dist z w) *
          (2 / (finalGap d L + t)) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [norm_mul]
          exact mul_le_mul (finalMass_entry_decay hd hk hv0 ha1 ha2 z w) (hb2 w) (norm_nonneg _)
            (by positivity)
      _ = finalDecayC d L * (2 / (finalGap d L + t)) * ∑ w, Real.exp (-blockDecayRate d * dist z w) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => ?_; ring
      _ ≤ finalDecayC d L * (2 / (finalGap d L + t)) * ballConst d (blockDecayRate d) :=
          mul_le_mul_of_nonneg_left (ballSum_L1Torus (d := d) (m := N₀) hδ z) (by positivity)
      _ = _ := by ring
  have hterm : ∀ z, ‖G x z * ((if z ∈ B then (0 : ℂ) else 1) * ∑ w, U z w * Gb w y)‖ ≤
      (if z ∈ B then 0 else 2 / (finalGap d L + t) * (finalDecayC d L * ballConst d (blockDecayRate d) *
        (2 / (finalGap d L + t))) * (Real.exp (-(finalRate d L / 2) * ρ) *
          Real.exp (-(finalRate d L / 2) * dist x z))) := by
    intro z
    by_cases hz : z ∈ B
    · simp [hz]
    · simp only [hz, ite_false, one_mul]
      rw [norm_mul]
      have hs : ‖∑ w, U z w * Gb w y‖ ≤ finalDecayC d L * ballConst d (blockDecayRate d) *
          (2 / (finalGap d L + t)) := (norm_sum_le _ _).trans (hb3 z)
      have hexp : Real.exp (-finalRate d L * dist x z) ≤ Real.exp (-(finalRate d L / 2) * ρ) *
          Real.exp (-(finalRate d L / 2) * dist x z) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have := hρ z hz
        nlinarith
      calc ‖G x z‖ * ‖∑ w, U z w * Gb w y‖ ≤
            (2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x z)) *
              (finalDecayC d L * ballConst d (blockDecayRate d) * (2 / (finalGap d L + t))) :=
            mul_le_mul (hb1 z) hs (norm_nonneg _) (by positivity)
        _ ≤ (2 / (finalGap d L + t) * (Real.exp (-(finalRate d L / 2) * ρ) *
              Real.exp (-(finalRate d L / 2) * dist x z))) *
              (finalDecayC d L * ballConst d (blockDecayRate d) * (2 / (finalGap d L + t))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := by ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z _ => hterm z).trans ?_)
  have hK : 0 ≤ ballConst d (finalRate d L / 2) := ballConst_nonneg (by positivity)
  calc ∑ z, (if z ∈ B then (0 : ℝ) else 2 / (finalGap d L + t) * (finalDecayC d L *
        ballConst d (blockDecayRate d) * (2 / (finalGap d L + t))) * (Real.exp (-(finalRate d L / 2) * ρ) *
          Real.exp (-(finalRate d L / 2) * dist x z)))
      ≤ ∑ z, 2 / (finalGap d L + t) * (finalDecayC d L *
        ballConst d (blockDecayRate d) * (2 / (finalGap d L + t))) * (Real.exp (-(finalRate d L / 2) * ρ) *
          Real.exp (-(finalRate d L / 2) * dist x z)) := by
        refine Finset.sum_le_sum fun z _ => ?_
        split_ifs
        · positivity
        · exact le_rfl
    _ = 2 / (finalGap d L + t) * (finalDecayC d L * ballConst d (blockDecayRate d) * (2 / (finalGap d L + t))) *
        Real.exp (-(finalRate d L / 2) * ρ) *
          ∑ z, Real.exp (-(finalRate d L / 2) * dist x z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_; ring
    _ ≤ 2 / (finalGap d L + t) * (finalDecayC d L * ballConst d (blockDecayRate d) * (2 / (finalGap d L + t))) *
        Real.exp (-(finalRate d L / 2) * ρ) * ballConst d (finalRate d L / 2) :=
        mul_le_mul_of_nonneg_left (ballSum_L1Torus (d := d) (m := N₀) (by positivity) x)
          (by positivity)
    _ = _ := by ring

/-- **Perturbation of the box resolvent.**  If the entries of `U` on `B × B` and of `U'` on the
image of `B` under the injective map `f` differ by at most `ε`, the box resolvents differ by at most
`|B|² ε / g²` on `B × B`. -/
theorem final_boxG_close {m m' : ℕ} [NeZero m] [NeZero m'] (hd : 0 < d) {v a : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d m))
    (f : L1Torus d m → L1Torus d m') (hinj : Set.InjOn f (B : Set (L1Torus d m))) {ε : ℝ}
    (hε : ∀ p ∈ B, ∀ q ∈ B,
      ‖finalOp d L m k v a p q - finalOp d L m' k v a (f p) (f q)‖ ≤ ε)
    {x y : L1Torus d m} (hx : x ∈ B) (hy : y ∈ B) :
    ‖boxG (finalOp d L m k v a) B t x y -
        boxG (finalOp d L m' k v a) (B.image f) t (f x) (f y)‖ ≤
      (B.card : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2 := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  set U := finalOp d L m k v a with hU
  set U' := finalOp d L m' k v a with hU'
  have hc1 : IsCoercive (shiftMat U t) (finalGap d L + t) :=
    (finalMass_isCoercive (L := L) (N₀ := m) (k := k) hd hv0 hv1 ha1 hmass).add_smul_one t
  have hc2 : IsCoercive (shiftMat U' t) (finalGap d L + t) :=
    (finalMass_isCoercive (L := L) (N₀ := m') (k := k) hd hv0 hv1 ha1 hmass).add_smul_one t
  have hgt : 0 < finalGap d L + t := by linarith
  set e1 : B → L1Torus d m := fun q => (q : L1Torus d m) with he1
  set e2 : B → L1Torus d m' := fun q => f (q : L1Torus d m) with he2
  have hi1 : Function.Injective e1 := fun p q h => Subtype.ext h
  have hi2 : Function.Injective e2 := fun p q h => Subtype.ext (hinj p.2 q.2 h)
  set T₁ := (shiftMat U t).submatrix e1 e1 with hT₁
  set T₂ := (shiftMat U' t).submatrix e2 e2 with hT₂
  have hC1 : IsCoercive T₁ (finalGap d L + t) := isCoercive_submatrix hc1 e1 hi1
  have hC2 : IsCoercive T₂ (finalGap d L + t) := isCoercive_submatrix hc2 e2 hi2
  have hU1 : T₁ * T₁⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isCoercive hgt hC1))
  have hU2 : T₂ * T₂⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isCoercive hgt hC2))
  have hdiff : ∀ p q : B, ‖T₁ p q - T₂ p q‖ ≤ ε := by
    intro p q
    have hpq : ((p : L1Torus d m) = q) ↔ (f p = f q) :=
      ⟨fun h => by rw [h], fun h => hinj p.2 q.2 h⟩
    have : T₁ p q - T₂ p q = U p q - U' (f p) (f q) := by
      simp only [hT₁, hT₂, Matrix.submatrix_apply, shiftMat, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply, he1, he2, hpq]
      ring
    rw [this]
    exact hε p p.2 q q.2
  have key := entry_diff_le hgt hC1 hC2 hU1 hU2 hdiff ⟨x, hx⟩ ⟨y, hy⟩
  have hfx : f x ∈ B.image f := Finset.mem_image_of_mem f hx
  have hfy : f y ∈ B.image f := Finset.mem_image_of_mem f hy
  have eq1 : boxG U B t x y = T₁⁻¹ ⟨x, hx⟩ ⟨y, hy⟩ := boxG_apply_eq_inv U B t hx hy
  have hbij : Function.Bijective
      (fun q : B => (⟨f q, Finset.mem_image_of_mem f q.2⟩ : B.image f)) := by
    constructor
    · intro p q hpq
      have := congrArg Subtype.val hpq
      exact Subtype.ext (hinj p.2 q.2 this)
    · intro b
      obtain ⟨a', ha, hab⟩ := Finset.mem_image.1 b.2
      exact ⟨⟨a', ha⟩, Subtype.ext hab⟩
  set ε' : B ≃ B.image f := Equiv.ofBijective _ hbij with hε'
  have hsub : T₂ = ((shiftMat U' t).submatrix (fun q : B.image f => (q : L1Torus d m'))
      (fun q : B.image f => (q : L1Torus d m'))).submatrix ε' ε' := by
    ext p q
    simp [hT₂, he2, hε']
  have eq2 : boxG U' (B.image f) t (f x) (f y) = T₂⁻¹ ⟨x, hx⟩ ⟨y, hy⟩ := by
    rw [boxG_apply_eq_inv U' (B.image f) t hfx hfy, hsub, Matrix.inv_submatrix_equiv]
    rfl
  rw [eq1, eq2]
  rw [Fintype.card_coe] at key
  exact key

end BoxDifference

section FineClose

variable {d : ℕ}

/-- One torus: the entry of the inverse of the fine operator against the box Green function. -/
theorem fineGreen_sub_boxGreen {L k : ℕ} [NeZero L] (hd : 0 < d) {ν a : ℝ} (hν0 : 0 ≤ ν)
    (hν1 : ν ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {m : ℕ} [NeZero m] {Rm R₀ : ℕ}
    (hm : 2 * Rm + 1 < m) (hR₀ : R₀ + 1 ≤ L ^ k * (Rm + 1))
    {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R₀) (hu' : u' ∈ sqBox d R₀) :
    ‖(((fineHamiltonian d (m * L ^ k) (L ^ k) m ν a)⁻¹ (castTorus (m * L ^ k) u)
          (castTorus (m * L ^ k) u') : ℝ) : ℂ) -
        boxGreen (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1)
          ⟨u, sqBox_mono (by omega) hu⟩ ⟨u', sqBox_mono (by omega) hu'⟩‖ ≤
      ctDiff d ((4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 3) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1)) 1
          (min (2 / (d : ℝ)) (1 / 2)) *
        Real.exp (-ctDecay d ((4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 3) *
          Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1)) 1 (min (2 / (d : ℝ)) (1 / 2)) *
          (2 * (((L ^ k * (Rm + 1) - 1 : ℕ) : ℝ) + 1 - R₀))) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hNr : (0 : ℝ) ≤ ((L ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 3) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1) := by
    positivity
  have hγ : 0 < min (2 / (d : ℝ)) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hRle : R₀ ≤ L ^ k * (Rm + 1) - 1 := by omega
  have hs : 2 * (L ^ k * (Rm + 1) - 1) < m * L ^ k := by
    have : 2 * (Rm + 1) ≤ m := by omega
    have h2 : L ^ k * (2 * (Rm + 1)) ≤ L ^ k * m := Nat.mul_le_mul_left _ this
    have h3 : 1 ≤ L ^ k * (Rm + 1) := Nat.mul_pos hN (Nat.succ_pos _)
    have h4 : 2 * (L ^ k * (Rm + 1)) ≤ m * L ^ k := by
      calc 2 * (L ^ k * (Rm + 1)) = L ^ k * (2 * (Rm + 1)) := by ring
        _ ≤ L ^ k * m := h2
        _ = m * L ^ k := mul_comm _ _
    omega
  have hdec : ∀ x y, |fineHamiltonian d (m * L ^ k) (L ^ k) m ν a x y| ≤
      ((4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 3) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1)) *
        Real.exp (-1 * torusDist d (m * L ^ k) x y) := fun x y => by
    refine (fineHamiltonian_decay (N₀ := m) (L := L) (k := k) hν0 (by linarith) ha2 x y).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      (Real.exp_pos _).le
    linarith
  have hcoer := fineHamiltonian_coercive hd (ℓ := m * L ^ k) (N := L ^ k) (m := m) (mul_comm _ _)
    hN hν0 ha1
  have := inv_sub_boxGreen_le (d := d) (s := m * L ^ k) hc one_pos hγ hdec hcoer hRle hs hu hu'
  exact this

/-- The box Green functions of the fine operators of two tori coincide. -/
theorem boxGreen_fine_eq {L k : ℕ} [NeZero L] (hd : 0 < d) {ν a : ℝ} (hν0 : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) {m m' : ℕ} [NeZero m] [NeZero m'] {Rm : ℕ}
    (hm : 2 * Rm + 1 < m) (hm' : 2 * Rm + 1 < m') :
    boxGreen (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1) =
      boxGreen (fineHamiltonian d (m' * L ^ k) (L ^ k) m' ν a) (L ^ k * (Rm + 1) - 1) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ : 0 < min (2 / (d : ℝ)) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hRlt : L ^ k * (Rm + 1) - 1 < L ^ k * (Rm + 1) := by
    have : 1 ≤ L ^ k * (Rm + 1) := Nat.mul_pos hN (Nat.succ_pos _)
    omega
  have hs : ∀ m'' : ℕ, 2 * Rm + 1 < m'' → 2 * (L ^ k * (Rm + 1) - 1) < m'' * L ^ k := by
    intro m'' hm''
    have : 2 * (Rm + 1) ≤ m'' := by omega
    have h2 : L ^ k * (2 * (Rm + 1)) ≤ L ^ k * m'' := Nat.mul_le_mul_left _ this
    have h3 : 1 ≤ L ^ k * (Rm + 1) := Nat.mul_pos hN (Nat.succ_pos _)
    have h4 : 2 * (L ^ k * (Rm + 1)) ≤ m'' * L ^ k := by
      calc 2 * (L ^ k * (Rm + 1)) = L ^ k * (2 * (Rm + 1)) := by ring
        _ ≤ L ^ k * m'' := h2
        _ = m'' * L ^ k := mul_comm _ _
    omega
  have hc1 := fineHamiltonian_coercive hd (ℓ := m * L ^ k) (N := L ^ k) (m := m) (mul_comm _ _)
    hN hν0 ha1
  have hc2 := fineHamiltonian_coercive hd (ℓ := m' * L ^ k) (N := L ^ k) (m := m') (mul_comm _ _)
    hN hν0 ha1
  have e1 := boxMat_mul_boxGreen (d := d) hγ hc1 (hs m hm)
  have e2 := boxMat_mul_boxGreen (d := d) hγ hc2 (hs m' hm')
  have hT : boxMat (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1) =
      boxMat (fineHamiltonian d (m' * L ^ k) (L ^ k) m' ν a) (L ^ k * (Rm + 1) - 1) := by
    ext u u'
    have := fineHamiltonian_castTorus_fine (d := d) (ℓ := m * L ^ k) (N := L ^ k) (m := m)
      (R := L ^ k * (Rm + 1) - 1) (Rm := Rm) (mul_comm _ _) hN hm hRlt ν a
      (u := (u : Fin d → ℤ)) (u' := u') u.2 u'.2
    have h' := fineHamiltonian_castTorus_fine (d := d) (ℓ := m' * L ^ k) (N := L ^ k) (m := m')
      (R := L ^ k * (Rm + 1) - 1) (Rm := Rm) (mul_comm _ _) hN hm' hRlt ν a
      (u := (u : Fin d → ℤ)) (u' := u') u.2 u'.2
    simp only [boxMat, Matrix.of_apply, cplxOp, Matrix.map_apply, castL1]
    rw [this, h']
  rw [← hT] at e2
  have e1' : boxGreen (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1) *
      boxMat (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1) = 1 :=
    mul_eq_one_comm.1 e1
  calc _ = boxGreen (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1) *
        (boxMat (fineHamiltonian d (m * L ^ k) (L ^ k) m ν a) (L ^ k * (Rm + 1) - 1) *
          boxGreen (fineHamiltonian d (m' * L ^ k) (L ^ k) m' ν a) (L ^ k * (Rm + 1) - 1)) := by
        rw [e2, mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, e1', one_mul]

/-- Closeness of the fine Green functions of two tori at sites of a cube. -/
theorem fineGreen_close {L k : ℕ} [NeZero L] (hd : 0 < d) {ν a : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {m m' : ℕ} [NeZero m] [NeZero m'] {Rm R₀ : ℕ}
    (hm : 2 * Rm + 1 < m) (hm' : 2 * Rm + 1 < m') (hR₀ : R₀ + 1 ≤ L ^ k * (Rm + 1))
    {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R₀) (hu' : u' ∈ sqBox d R₀) :
    ‖(((fineHamiltonian d (m * L ^ k) (L ^ k) m ν a)⁻¹ (castTorus (m * L ^ k) u)
          (castTorus (m * L ^ k) u') : ℝ) : ℂ) -
        (((fineHamiltonian d (m' * L ^ k) (L ^ k) m' ν a)⁻¹ (castTorus (m' * L ^ k) u)
          (castTorus (m' * L ^ k) u') : ℝ) : ℂ)‖ ≤
      2 * (ctDiff d ((4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 3) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1)) 1
          (min (2 / (d : ℝ)) (1 / 2)) *
        Real.exp (-ctDecay d ((4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 3) *
          Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1)) 1 (min (2 / (d : ℝ)) (1 / 2)) *
          (2 * (((L ^ k * (Rm + 1) - 1 : ℕ) : ℝ) + 1 - R₀)))) := by
  have h1 := fineGreen_sub_boxGreen (L := L) (k := k) hd hν0 hν1 ha1 ha2 hm hR₀ hu hu'
  have h2 := fineGreen_sub_boxGreen (L := L) (k := k) hd hν0 hν1 ha1 ha2 hm' hR₀ hu hu'
  rw [boxGreen_fine_eq (L := L) (k := k) hd hν0 ha1 hm hm'] at h1
  calc _ = ‖((((fineHamiltonian d (m * L ^ k) (L ^ k) m ν a)⁻¹ (castTorus (m * L ^ k) u)
          (castTorus (m * L ^ k) u') : ℝ) : ℂ) - boxGreen (fineHamiltonian d (m' * L ^ k)
            (L ^ k) m' ν a) (L ^ k * (Rm + 1) - 1) ⟨u, sqBox_mono (by omega) hu⟩
              ⟨u', sqBox_mono (by omega) hu'⟩) - ((((fineHamiltonian d (m' * L ^ k) (L ^ k) m' ν
                a)⁻¹ (castTorus (m' * L ^ k) u) (castTorus (m' * L ^ k) u') : ℝ) : ℂ) -
                  boxGreen (fineHamiltonian d (m' * L ^ k) (L ^ k) m' ν a)
                    (L ^ k * (Rm + 1) - 1) ⟨u, sqBox_mono (by omega) hu⟩
                      ⟨u', sqBox_mono (by omega) hu'⟩)‖ := by congr 1; ring
    _ ≤ _ := (norm_sub_le _ _).trans (by linarith)

theorem finalOp_castTorus_apply {L k : ℕ} [NeZero L] {m : ℕ} [NeZero m] (v a : ℝ)
    (y y' : Fin d → ℤ) :
    finalOp d L m k v a (castL1 m y) (castL1 m y') =
      ((a * (if castTorus m y = castTorus m y' then 1 else 0) - a ^ 2 *
        ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * ∑ x ∈ intFibre (L ^ k) y, ∑ x'' ∈ intFibre (L ^ k) y',
          (fineHamiltonian d (m * L ^ k) (L ^ k) m v a)⁻¹ (castTorus (m * L ^ k) x)
            (castTorus (m * L ^ k) x'')) : ℝ) : ℂ) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have := unconstrainedUnitOperator_castTorus (d := d) (ℓ := m * L ^ k) (N := L ^ k) (m := m)
    (mul_comm _ _) hN v a y y'
  exact congrArg (fun r : ℝ => (r : ℂ)) this

/-- **Entries of the final operator on two tori.**  The constants depend on `d`, `L`, `k` only. -/
theorem finalOp_entry_close {L k : ℕ} [NeZero L] (hd : 0 < d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {Rm Rc : ℕ}, 2 * Rm + 1 < m → 2 * Rm + 1 < m' →
      Rc + 1 ≤ Rm → ∀ {y y' : Fin d → ℤ}, y ∈ sqBox d Rc → y' ∈ sqBox d Rc →
      ‖finalOp d L m k v a (castL1 m y) (castL1 m y') -
          finalOp d L m' k v a (castL1 m' y) (castL1 m' y')‖ ≤
        C * Real.exp (-c * ((Rm : ℝ) - Rc)) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  set N : ℝ := ((L ^ k : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  set c₀ := (4 * d * N ^ 2 + 3) * Real.exp (d * N + 1) with hc₀
  set γ₀ := min (2 / (d : ℝ)) (1 / 2) with hγ₀
  have hc : 0 ≤ c₀ := by positivity
  have hγ : 0 < γ₀ := lt_min (by positivity) (by norm_num)
  have hμ := ctDecay_pos (d := d) hc one_pos hγ
  refine ⟨8 * N ^ d * ctDiff d c₀ 1 γ₀ + 1, 2 * ctDecay d c₀ 1 γ₀, by
    have := ctDiff_nonneg (d := d) hc one_pos hγ
    positivity, by positivity, ?_⟩
  intro v a hv0 hv1 ha1 ha2 m m' _ _ Rm Rc hm hm' hRc y y' hy hy'
  have hRle : L ^ k * (Rc + 1) + 1 ≤ L ^ k * (Rm + 1) := by
    have := Nat.mul_le_mul_left (L ^ k) hRc
    nlinarith
  have hc2 : ∀ {m'' : ℕ}, 2 * Rm + 1 < m'' → ∀ μ, |y μ - y' μ| < m'' := by
    intro m'' hm'' μ
    have h1 := abs_le.1 (mem_sqBox.1 hy μ)
    have h2 := abs_le.1 (mem_sqBox.1 hy' μ)
    have h5 : ((2 * Rm + 1 : ℕ) : ℤ) < m'' := by exact_mod_cast hm''
    have h6 : ((Rc + 1 : ℕ) : ℤ) ≤ Rm := by exact_mod_cast hRc
    push_cast at h5 h6
    rw [abs_lt]; constructor <;> linarith
  have hind : (castTorus m y = castTorus m y') ↔ (castTorus m' y = castTorus m' y') := by
    rw [castTorus_eq_iff (hc2 hm), castTorus_eq_iff (hc2 hm')]
  rw [finalOp_castTorus_apply v a y y', finalOp_castTorus_apply v a y y']
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp only [hind]
  have hE : ∀ x ∈ intFibre (L ^ k) y, ∀ x'' ∈ intFibre (L ^ k) y',
      |(fineHamiltonian d (m * L ^ k) (L ^ k) m v a)⁻¹ (castTorus (m * L ^ k) x)
          (castTorus (m * L ^ k) x'') -
        (fineHamiltonian d (m' * L ^ k) (L ^ k) m' v a)⁻¹ (castTorus (m' * L ^ k) x)
          (castTorus (m' * L ^ k) x'')| ≤
      2 * (ctDiff d c₀ 1 γ₀ * Real.exp (-(2 * ctDecay d c₀ 1 γ₀) * ((Rm : ℝ) - Rc))) := by
    intro x hx x'' hx''
    have hx1 := intFibre_subset_sqBox (N := L ^ k) hy hx
    have hx2 := intFibre_subset_sqBox (N := L ^ k) hy' hx''
    have h := fineGreen_close (L := L) (k := k) hd hv0 hv1 ha1 ha2 hm hm' hRle hx1 hx2
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    refine h.trans ?_
    have hcast : (((L ^ k * (Rm + 1) - 1 : ℕ) : ℝ) + 1 - ((L ^ k * (Rc + 1) : ℕ) : ℝ)) =
        N * ((Rm : ℝ) - Rc) := by
      have h1 : 1 ≤ L ^ k * (Rm + 1) := by omega
      rw [Nat.cast_sub h1]
      simp only [hNdef]
      push_cast
      ring
    have hd1 : (1 : ℝ) ≤ (Rm : ℝ) - Rc := by
      have : ((Rc + 1 : ℕ) : ℝ) ≤ Rm := by exact_mod_cast hRc
      push_cast at this; linarith
    have hexp : Real.exp (-ctDecay d c₀ 1 γ₀ * (2 * (((L ^ k * (Rm + 1) - 1 : ℕ) : ℝ) + 1 -
        ((L ^ k * (Rc + 1) : ℕ) : ℝ)))) ≤
        Real.exp (-(2 * ctDecay d c₀ 1 γ₀) * ((Rm : ℝ) - Rc)) := by
      rw [hcast]
      apply Real.exp_le_exp.2
      have h3 : (Rm : ℝ) - Rc ≤ N * ((Rm : ℝ) - Rc) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hμ.le]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp
      (ctDiff_nonneg (d := d) hc one_pos hγ)) (by norm_num)
  set E' := 2 * (ctDiff d c₀ 1 γ₀ * Real.exp (-(2 * ctDecay d c₀ 1 γ₀) * ((Rm : ℝ) - Rc))) with hE'
  have hctd := ctDiff_nonneg (d := d) hc one_pos hγ
  have hE'0 : 0 ≤ E' := by positivity
  have hNd : (0 : ℝ) < N ^ d := by positivity
  set F := intFibre (L ^ k) y with hF
  set F' := intFibre (L ^ k) y' with hF'
  set h1 : (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun x x'' =>
    (fineHamiltonian d (m * L ^ k) (L ^ k) m v a)⁻¹ (castTorus (m * L ^ k) x)
      (castTorus (m * L ^ k) x'') with hh1
  set h2 : (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun x x'' =>
    (fineHamiltonian d (m' * L ^ k) (L ^ k) m' v a)⁻¹ (castTorus (m' * L ^ k) x)
      (castTorus (m' * L ^ k) x'') with hh2
  have hsum : |∑ x ∈ F, ∑ x'' ∈ F', h1 x x'' - ∑ x ∈ F, ∑ x'' ∈ F', h2 x x''| ≤
      (N ^ d) ^ 2 * E' := by
    calc |∑ x ∈ F, ∑ x'' ∈ F', h1 x x'' - ∑ x ∈ F, ∑ x'' ∈ F', h2 x x''|
        = |∑ x ∈ F, ∑ x'' ∈ F', (h1 x x'' - h2 x x'')| := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ x ∈ F, ∑ x'' ∈ F', |h1 x x'' - h2 x x''| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ x ∈ F, ∑ x'' ∈ F', E' :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x'' hx'' => hE x hx x'' hx''
      _ = (N ^ d) ^ 2 * E' := by
          simp only [Finset.sum_const, hF, hF', card_intFibre, nsmul_eq_mul]
          rw [hNdef]
          push_cast
          ring
  have ha0 : 0 ≤ a := by linarith
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  generalize (if castTorus m' y = castTorus m' y' then (1 : ℝ) else 0) = I
  have e : a * I - a ^ 2 * ((N ^ d)⁻¹ * ∑ x ∈ F, ∑ x'' ∈ F', h1 x x'') -
      (a * I - a ^ 2 * ((N ^ d)⁻¹ * ∑ x ∈ F, ∑ x'' ∈ F', h2 x x'')) =
      a ^ 2 * (N ^ d)⁻¹ * (∑ x ∈ F, ∑ x'' ∈ F', h2 x x'' - ∑ x ∈ F, ∑ x'' ∈ F', h1 x x'') := by
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2 * (N ^ d)⁻¹), abs_sub_comm]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans ?_
  have e2 : a ^ 2 * (N ^ d)⁻¹ * ((N ^ d) ^ 2 * E') = a ^ 2 * N ^ d * E' := by
    field_simp
  rw [e2]
  have hexp0 : 0 ≤ Real.exp (-(2 * ctDecay d c₀ 1 γ₀) * ((Rm : ℝ) - Rc)) := (Real.exp_pos _).le
  have : a ^ 2 * N ^ d * E' ≤ 4 * N ^ d * E' :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha4 hNd.le) hE'0
  refine this.trans ?_
  simp only [hE']
  nlinarith [mul_nonneg (mul_nonneg hNd.le hctd) hexp0]

end FineClose

section Geometry

variable {d : ℕ}

/-- Points of the torus outside the image of the cube of radius `ρ` around `u` are at distance
`> ρ` from `u`. -/
theorem dist_gt_of_not_mem_cube {s : ℕ} [NeZero s] (u : Fin d → ℤ) (ρ : ℕ) {z : L1Torus d s}
    (hz : z ∉ (Fintype.piFinset fun μ => Finset.Icc (u μ - (ρ : ℤ)) (u μ + ρ)).image (castL1 s)) :
    (ρ : ℝ) + 1 ≤ dist (castL1 s u) z := by
  set w : Fin d → ℤ := fun μ => u μ + cycRep (z μ - castTorus s u μ) with hw
  have hcast : castL1 s w = z := by
    funext μ
    simp only [castL1, castTorus, hw]
    push_cast
    have := cast_cycRep (z μ - castTorus s u μ)
    simp only [castTorus] at this
    rw [this]; ring
  have hwn : w ∉ (Fintype.piFinset fun μ => Finset.Icc (u μ - (ρ : ℤ)) (u μ + ρ)) := by
    intro h
    exact hz (Finset.mem_image.2 ⟨w, h, hcast⟩)
  rw [Fintype.mem_piFinset] at hwn
  push Not at hwn
  obtain ⟨μ, hμ⟩ := hwn
  have hbig : ρ + 1 ≤ (cycRep (z μ - castTorus s u μ)).natAbs := by
    rw [Finset.mem_Icc] at hμ
    have : ¬ (u μ - (ρ : ℤ) ≤ w μ ∧ w μ ≤ u μ + ρ) := hμ
    simp only [hw] at this
    omega
  rw [dist_L1Torus]
  unfold torusDist
  have h1 : ((cycRep (castL1 s u μ - z μ)).natAbs : ℝ) ≤
      ∑ i, ((cycRep (castL1 s u i - z i)).natAbs : ℝ) :=
    Finset.single_le_sum (f := fun i => ((cycRep (castL1 s u i - z i)).natAbs : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ μ)
  refine le_trans ?_ h1
  have e : (cycRep (castL1 s u μ - z μ)).natAbs = (cycRep (z μ - castTorus s u μ)).natAbs := by
    rw [← natAbs_cycRep_neg, neg_sub]; rfl
  rw [e]
  exact_mod_cast hbig

/-- Identity of residues: the centred lift of the torus of side `m` to the torus of side `m'`. -/
theorem lift_castL1 {m m' : ℕ} [NeZero m] [NeZero m'] {R : ℕ} (hm : 2 * R < m)
    {w : Fin d → ℤ} (hw : w ∈ sqBox d R) :
    castTorus m' (fun μ => cycRep ((castL1 m w : L1Torus d m) μ)) = castL1 m' w := by
  funext μ
  have h := mem_sqBox.1 hw μ
  have hs : 2 * (w μ).natAbs < m := by
    have : (w μ).natAbs ≤ R := by rw [Int.abs_eq_natAbs] at h; exact_mod_cast h
    omega
  simp only [castL1, castTorus]
  rw [cycRep_intCast_of_small _ hs]

end Geometry

section Assembly

variable {d L k : ℕ} [NeZero L]

/-- **Closeness of the resolvent on two tori, given the closeness of the entries on a cube.**
The constant `K` depends on `d` and `L` only (it is chosen before `k`); the bound carries the
factor `(finalGap + t)⁻¹`. -/
theorem final_resolvent_close_of_entries_core {d L : ℕ} [NeZero L] (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v → ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {R ρ : ℕ},
      2 * (R + ρ) < m → 2 * (R + ρ) < m' → ∀ {ε : ℝ},
      (∀ q ∈ sqBox d (R + ρ), ∀ q' ∈ sqBox d (R + ρ),
        ‖finalOp d L m k v a (castL1 m q) (castL1 m q') -
            finalOp d L m' k v a (castL1 m' q) (castL1 m' q')‖ ≤ ε) →
      ∀ {t : ℝ}, 0 ≤ t → ∀ {u w : Fin d → ℤ}, u ∈ sqBox d R → w ∈ sqBox d R →
      ‖((finalOp d L m k v a + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹)
            (castL1 m u) (castL1 m w) -
          ((finalOp d L m' k v a + (t : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹)
            (castL1 m' u) (castL1 m' w)‖ ≤
        (K * Real.exp (-(finalRate d L / 2) * ((ρ : ℝ) + 1)) +
          ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε * (finalGap d L)⁻¹) * (finalGap d L + t)⁻¹ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hr := finalRate_pos (L := L) hd
  have hδ := blockDecayRate_pos hd
  have hC := finalDecayC_pos (L := L) hd
  have hbδ : 0 ≤ ballConst d (blockDecayRate d) := ballConst_nonneg hδ
  have hbr : 0 ≤ ballConst d (finalRate d L / 2) := ballConst_nonneg (by positivity)
  set Kb := finalDecayC d L * ballConst d (blockDecayRate d) * ballConst d (finalRate d L / 2)
    with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  refine ⟨4 + 8 * (finalGap d L)⁻¹ * Kb, by positivity, ?_⟩
  intro k hk v a hv0 hv1 ha1 ha2 hmass m m' _ _ R ρ hm hm' ε hε t ht u w hu hw
  set T := (finalGap d L + t)⁻¹ with hTdef
  have hT0 : 0 < T := by positivity
  have hTg : T ≤ (finalGap d L)⁻¹ := inv_anti₀ hg (by linarith)
  have hT2 : T ^ 2 ≤ (finalGap d L)⁻¹ * T := by
    rw [pow_two]; exact mul_le_mul_of_nonneg_right hTg hT0.le
  have h2T : 2 / (finalGap d L + t) = 2 * T := by rw [div_eq_mul_inv]
  set E := Real.exp (-(finalRate d L / 2) * ((ρ : ℝ) + 1)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set Q : Finset (Fin d → ℤ) := Fintype.piFinset fun μ => Finset.Icc (u μ - (ρ : ℤ)) (u μ + ρ)
    with hQ
  have hQsq : ∀ q ∈ Q, q ∈ sqBox d (R + ρ) := by
    intro q hq
    rw [hQ, Fintype.mem_piFinset] at hq
    rw [mem_sqBox]; intro μ
    have h1 := hq μ
    rw [Finset.mem_Icc] at h1
    have h2 := abs_le.1 (mem_sqBox.1 hu μ)
    rw [abs_le]; push_cast; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have huR : ∀ q ∈ sqBox d R, q ∈ sqBox d (R + ρ) := fun q hq => sqBox_mono (by omega) hq
  have hinj : ∀ {s : ℕ} [NeZero s], 2 * (R + ρ) < s →
      Set.InjOn (castL1 (d := d) s) (sqBox d (R + ρ) : Set (Fin d → ℤ)) :=
    fun hs => castL1_injOn hs
  have hnotmem : ∀ {s : ℕ} [NeZero s], 2 * (R + ρ) < s → w ∉ Q →
      castL1 s w ∉ Q.image (castL1 s) := by
    intro s _ hs hwQ hmem
    obtain ⟨q, hq, hqw⟩ := Finset.mem_image.1 hmem
    have := hinj hs (hQsq q hq) (huR w hw) hqw
    exact hwQ (this ▸ hq)
  have far : ∀ (s : ℕ) [NeZero s], 2 * (R + ρ) < s → w ∉ Q →
      ‖((finalOp d L s k v a + (t : ℂ) • (1 : Matrix (L1Torus d s) (L1Torus d s) ℂ))⁻¹)
          (castL1 s u) (castL1 s w)‖ ≤ 2 * T * Real.exp (-finalRate d L * ((ρ : ℝ) + 1)) := by
    intro s _ hs hwQ
    have hdist := dist_gt_of_not_mem_cube (s := s) u ρ (hnotmem hs hwQ)
    refine ((finalMass_resolvent_decay (L := L) (N₀ := s) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
      ht).2 _ _).trans ?_
    rw [h2T]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    nlinarith
  have hexpm : Real.exp (-finalRate d L * ((ρ : ℝ) + 1)) ≤ E := by
    apply Real.exp_le_exp.2
    have : 0 ≤ finalRate d L * ((ρ : ℝ) + 1) := by positivity
    nlinarith
  have hεnn : 0 ≤ ε := (norm_nonneg _).trans (hε u (huR u hu) u (huR u hu))
  have hrest : 0 ≤ ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε * (finalGap d L)⁻¹ := by positivity
  have hKE : 0 ≤ 8 * (finalGap d L)⁻¹ * Kb * E * T := by positivity
  by_cases hwQ : w ∈ Q
  · have huQ : u ∈ Q := by
      rw [hQ, Fintype.mem_piFinset]
      intro μ
      rw [Finset.mem_Icc]
      constructor <;> omega
    set B : Finset (L1Torus d m) := Q.image (castL1 m) with hB
    set B' : Finset (L1Torus d m') := Q.image (castL1 m') with hB'
    set f : L1Torus d m → L1Torus d m' :=
      fun x => (castTorus m' (fun μ => cycRep (x μ)) : L1Torus d m') with hf
    have hfq : ∀ q ∈ Q, f (castL1 m q) = castL1 m' q := fun q hq =>
      lift_castL1 (m' := m') hm (hQsq q hq)
    have hinjf : Set.InjOn f (B : Set (L1Torus d m)) := by
      intro a ha b hb hab
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      rw [hfq q hq, hfq q2 hq2] at hab
      rw [hinj hm' (hQsq q hq) (hQsq q2 hq2) hab]
    have himg : B.image f = B' := by
      rw [hB, Finset.image_image]
      exact Finset.image_congr fun q hq => hfq q hq
    have hxB : castL1 m u ∈ B := Finset.mem_image_of_mem _ huQ
    have hyB : castL1 m w ∈ B := Finset.mem_image_of_mem _ hwQ
    have hyB' : castL1 m' w ∈ B' := Finset.mem_image_of_mem _ hwQ
    have hε' : ∀ p ∈ B, ∀ q ∈ B,
        ‖finalOp d L m k v a p q - finalOp d L m' k v a (f p) (f q)‖ ≤ ε := by
      intro p hp q hq
      obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.1 hq
      rw [hfq q1 hq1, hfq q2 hq2]
      exact hε q1 (hQsq q1 hq1) q2 (hQsq q2 hq2)
    have hGb := final_boxG_close (L := L) (k := k) hd hv0 hv1 ha1 hmass ht B f hinjf hε' hxB hyB
    rw [himg, hfq u huQ, hfq w hwQ] at hGb
    have hcardQ : (Q.card : ℝ) = ((2 * ρ + 1 : ℕ) : ℝ) ^ d := by
      have h1 : ∀ μ : Fin d, (Finset.Icc (u μ - (ρ : ℤ)) (u μ + ρ)).card = 2 * ρ + 1 := by
        intro μ; rw [Int.card_Icc]; omega
      rw [hQ, Fintype.card_piFinset]
      simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      push_cast; rfl
    have hcardB : B.card = Q.card :=
      Finset.card_image_of_injOn ((hinj hm).mono fun q hq => hQsq q hq)
    have e1 := final_sub_boxG_le (L := L) (k := k) (N₀ := m) hd hk hv0 hv1 ha1 ha2 hmass ht B
      (castL1 m u) (castL1 m w) hyB (ρ := (ρ : ℝ) + 1)
      (fun z hz => dist_gt_of_not_mem_cube u ρ hz)
    have e2 := final_sub_boxG_le (L := L) (k := k) (N₀ := m') hd hk hv0 hv1 ha1 ha2 hmass ht B'
      (castL1 m' u) (castL1 m' w) hyB' (ρ := (ρ : ℝ) + 1)
      (fun z hz => dist_gt_of_not_mem_cube u ρ hz)
    rw [h2T] at e1 e2
    set G := (finalOp d L m k v a + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹
      with hG
    set G' := (finalOp d L m' k v a + (t : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹
      with hG'
    set Gb := boxG (finalOp d L m k v a) B t (castL1 m u) (castL1 m w) with hGbdef
    set Gb' := boxG (finalOp d L m' k v a) B' t (castL1 m' u) (castL1 m' w) with hGb'def
    have htri : G (castL1 m u) (castL1 m w) - G' (castL1 m' u) (castL1 m' w) =
        (G (castL1 m u) (castL1 m w) - Gb) + (Gb - Gb') -
          (G' (castL1 m' u) (castL1 m' w) - Gb') := by
      ring
    rw [htri]
    refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add e1 hGb)) e2)
      |>.trans ?_)
    have hcsq : (B.card : ℝ) ^ 2 = ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) := by
      rw [hcardB, hcardQ, ← pow_mul, mul_comm d 2]
    rw [hcsq]
    set N2 := ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) with hN2
    have hN20 : 0 ≤ N2 := by positivity
    have hA : (2 * T) ^ 2 * Kb * E ≤ 4 * ((finalGap d L)⁻¹ * T) * Kb * E := by
      have : (2 * T) ^ 2 = 4 * T ^ 2 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hT2 (by norm_num : (0 : ℝ) ≤ 4)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hKb0) hE0
    have hBt : N2 * ε * T ^ 2 ≤ N2 * ε * ((finalGap d L)⁻¹ * T) :=
      mul_le_mul_of_nonneg_left hT2 (by positivity)
    have e1' : (2 * T) ^ 2 * finalDecayC d L * ballConst d (blockDecayRate d) *
        ballConst d (finalRate d L / 2) * E = (2 * T) ^ 2 * Kb * E := by rw [hKb]; ring
    rw [e1'] at e1 e2
    have hfin : (4 + 8 * (finalGap d L)⁻¹ * Kb) * E * T =
        4 * E * T + 8 * (finalGap d L)⁻¹ * Kb * E * T := by ring
    have hfin2 : N2 * ε * ((finalGap d L)⁻¹ * T) = N2 * ε * (finalGap d L)⁻¹ * T := by ring
    have h4 : 4 * ((finalGap d L)⁻¹ * T) * Kb * E * 2 = 8 * (finalGap d L)⁻¹ * Kb * E * T := by
      ring
    nlinarith [mul_nonneg hE0 hT0.le]
  · refine (norm_sub_le _ _).trans ?_
    have h1 := far m hm hwQ
    have h2 := far m' hm' hwQ
    have h3 : 2 * T * Real.exp (-finalRate d L * ((ρ : ℝ) + 1)) ≤ 2 * T * E :=
      mul_le_mul_of_nonneg_left hexpm (by positivity)
    have hfin : (4 + 8 * (finalGap d L)⁻¹ * Kb) * E * T + ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε *
        (finalGap d L)⁻¹ * T = 4 * E * T + 8 * (finalGap d L)⁻¹ * Kb * E * T +
          ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε * (finalGap d L)⁻¹ * T := by ring
    have hr0 : 0 ≤ ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε * (finalGap d L)⁻¹ * T := by positivity
    have : (4 + 8 * (finalGap d L)⁻¹ * Kb) * E * T + ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε *
        (finalGap d L)⁻¹ * T = ((4 + 8 * (finalGap d L)⁻¹ * Kb) * E + ((2 * ρ + 1 : ℕ) : ℝ) ^
          (2 * d) * ε * (finalGap d L)⁻¹) * T := by ring
    rw [← this]
    nlinarith

/-- **Closeness of the resolvent on two tori, given the closeness of the entries on a cube.**
The constant `K` depends on `d` and `L` only; the bound carries the factor `(finalGap + t)⁻¹`. -/
theorem final_resolvent_close_of_entries (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ (1 ≤ k → ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v → ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {R ρ : ℕ},
      2 * (R + ρ) < m → 2 * (R + ρ) < m' → ∀ {ε : ℝ},
      (∀ q ∈ sqBox d (R + ρ), ∀ q' ∈ sqBox d (R + ρ),
        ‖finalOp d L m k v a (castL1 m q) (castL1 m q') -
            finalOp d L m' k v a (castL1 m' q) (castL1 m' q')‖ ≤ ε) →
      ∀ {t : ℝ}, 0 ≤ t → ∀ {u w : Fin d → ℤ}, u ∈ sqBox d R → w ∈ sqBox d R →
      ‖((finalOp d L m k v a + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹)
            (castL1 m u) (castL1 m w) -
          ((finalOp d L m' k v a + (t : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹)
            (castL1 m' u) (castL1 m' w)‖ ≤
        (K * Real.exp (-(finalRate d L / 2) * ((ρ : ℝ) + 1)) +
          ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * ε * (finalGap d L)⁻¹) * (finalGap d L + t)⁻¹) := by
  obtain ⟨K, hK0, hK⟩ := final_resolvent_close_of_entries_core (d := d) (L := L) hd
  exact ⟨K, hK0, fun hk => hK hk⟩

theorem pow_mul_exp_neg_le (n : ℕ) {b : ℝ} (hb : 0 < b) {x : ℝ} (hx : 0 ≤ x) :
    x ^ n * Real.exp (-(2 * b) * x) ≤ (n.factorial : ℝ) / b ^ n * Real.exp (-b * x) := by
  have h := Real.pow_div_factorial_le_exp (b * x) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : x ^ n ≤ (n.factorial : ℝ) / b ^ n * Real.exp (b * x) := by
    rw [mul_pow, div_le_iff₀ hf] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc x ^ n * Real.exp (-(2 * b) * x) ≤ ((n.factorial : ℝ) / b ^ n * Real.exp (b * x)) *
        Real.exp (-(2 * b) * x) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The elementary estimate closing the proof of `finalResolvent_twoTorus_close`. -/
theorem final_close_tail {g r K C₀ c₀ c : ℝ} {D ρ Rm Rc : ℕ} (hg : 0 < g)
    (hK0 : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hc₀ : 0 < c₀) (hcr : c ≤ r / 4)
    (hcc : c ≤ c₀ / 8) (hr : 0 < r) (hρ1 : (D : ℝ) / 4 ≤ (ρ : ℝ) + 1)
    (hRmρ : (D : ℝ) / 8 ≤ (Rm : ℝ) - (Rc : ℝ)) (h2ρ : ((2 * ρ + 1 : ℕ) : ℝ) ≤ (D : ℝ)) :
    K * Real.exp (-(r / 2) * ((ρ : ℝ) + 1)) +
        ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * (C₀ * Real.exp (-c₀ * ((Rm : ℝ) - (Rc : ℝ)))) *
          g⁻¹ ≤
      (K + ((2 * d).factorial : ℝ) / (c₀ / 16) ^ (2 * d) * C₀ * g⁻¹) *
        Real.exp (-c * ((D : ℝ) / 2)) := by
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  set b : ℝ := c₀ / 16 with hbdef
  have hb : 0 < b := by positivity
  set P : ℝ := ((2 * d).factorial : ℝ) / b ^ (2 * d) with hP
  have hP0 : 0 ≤ P := by positivity
  have hA : K * Real.exp (-(r / 2) * ((ρ : ℝ) + 1)) ≤ K * Real.exp (-c * ((D : ℝ) / 2)) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_left hρ1 (by positivity : (0 : ℝ) ≤ r / 2)
    have h2 := mul_nonneg hD0 (by linarith : 0 ≤ r / 4 - c)
    nlinarith
  have hB1 : ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) ≤ (D : ℝ) ^ (2 * d) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h2ρ _
  have hB2 : Real.exp (-c₀ * ((Rm : ℝ) - (Rc : ℝ))) ≤ Real.exp (-(2 * b) * (D : ℝ)) := by
    apply Real.exp_le_exp.2
    have : 2 * b = c₀ / 8 := by rw [hbdef]; ring
    rw [this]
    have h1 := mul_le_mul_of_nonneg_left hRmρ hc₀.le
    nlinarith
  have hB3 := pow_mul_exp_neg_le (2 * d) hb hD0
  have hB4 : Real.exp (-b * (D : ℝ)) ≤ Real.exp (-c * ((D : ℝ) / 2)) := by
    apply Real.exp_le_exp.2
    have : c / 2 ≤ b := by rw [hbdef]; linarith
    have h' := mul_le_mul_of_nonneg_right this hD0
    linarith
  have e1 : ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * Real.exp (-c₀ * ((Rm : ℝ) - (Rc : ℝ))) ≤
      P * Real.exp (-c * ((D : ℝ) / 2)) := by
    calc _ ≤ (D : ℝ) ^ (2 * d) * Real.exp (-(2 * b) * (D : ℝ)) :=
          mul_le_mul hB1 hB2 (Real.exp_pos _).le (by positivity)
      _ ≤ P * Real.exp (-b * (D : ℝ)) := hB3
      _ ≤ P * Real.exp (-c * ((D : ℝ) / 2)) := mul_le_mul_of_nonneg_left hB4 hP0
  have hB : ((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * (C₀ * Real.exp (-c₀ * ((Rm : ℝ) - (Rc : ℝ)))) *
      g⁻¹ ≤ P * C₀ * g⁻¹ * Real.exp (-c * ((D : ℝ) / 2)) := by
    calc _ = (((2 * ρ + 1 : ℕ) : ℝ) ^ (2 * d) * Real.exp (-c₀ * ((Rm : ℝ) - (Rc : ℝ)))) *
          (C₀ * g⁻¹) := by ring
      _ ≤ (P * Real.exp (-c * ((D : ℝ) / 2))) * (C₀ * g⁻¹) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = _ := by ring
  have : (K + P * C₀ * g⁻¹) * Real.exp (-c * ((D : ℝ) / 2)) =
      K * Real.exp (-c * ((D : ℝ) / 2)) + P * C₀ * g⁻¹ * Real.exp (-c * ((D : ℝ) / 2)) := by
    ring
  rw [this]
  exact add_le_add hA hB

/-- **Closeness of the final resolvent on two tori, from the closeness of the entries.**  The
entries of `finalOp` at the sites of a cube of the two tori are assumed to differ by at most
`C₀ exp(-c₀ (Rm - Rc))` (`hent`); then the resolvent entries differ by at most
`C exp(-c (min m m' / 2 - R)) / (finalGap + t)`, where `C, c` depend on `d`, `L`, `C₀`, `c₀` only
(not on `k`). -/
theorem finalResolvent_twoTorus_close_of_entries {d L : ℕ} [NeZero L] (hd : 0 < d) {C₀ c₀ : ℝ}
    (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a →
      a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      (∀ {m m' : ℕ} [NeZero m] [NeZero m'] {Rm Rc : ℕ}, 2 * Rm + 1 < m → 2 * Rm + 1 < m' →
        Rc + 1 ≤ Rm → ∀ {y y' : Fin d → ℤ}, y ∈ sqBox d Rc → y' ∈ sqBox d Rc →
        ‖finalOp d L m k v a (castL1 m y) (castL1 m y') -
            finalOp d L m' k v a (castL1 m' y) (castL1 m' y')‖ ≤
          C₀ * Real.exp (-c₀ * ((Rm : ℝ) - Rc))) →
      ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {R : ℕ},
      2 * R < m → 2 * R < m' → ∀ {t : ℝ}, 0 ≤ t → ∀ {u w : Fin d → ℤ},
      u ∈ sqBox d R → w ∈ sqBox d R →
      ‖((finalOp d L m k v a + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹)
            (castL1 m u) (castL1 m w) -
          ((finalOp d L m' k v a + (t : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹)
            (castL1 m' u) (castL1 m' w)‖ ≤
        C * Real.exp (-c * (((min m m' : ℕ) : ℝ) / 2 - R)) * (finalGap d L + t)⁻¹ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hr := finalRate_pos (L := L) hd
  obtain ⟨K, hK0, hKmain⟩ := final_resolvent_close_of_entries_core (d := d) (L := L) hd
  set c : ℝ := min (finalRate d L / 4) (c₀ / 8) with hcdef
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcr : c ≤ finalRate d L / 4 := min_le_left _ _
  have hcc : c ≤ c₀ / 8 := min_le_right _ _
  set P : ℝ := ((2 * d).factorial : ℝ) / (c₀ / 16) ^ (2 * d) with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨4 * Real.exp (6 * c) + K + P * C₀ * (finalGap d L)⁻¹ + 1, c,
    by positivity, hc, ?_⟩
  intro k hk v a hv0 hv1 ha1 ha2 hmass hent m m' _ _ R hm hm' t ht u w hu hw
  set S := min m m' with hS
  have hSm : S ≤ m := min_le_left _ _
  have hSm' : S ≤ m' := min_le_right _ _
  obtain ⟨D, hD⟩ : ∃ D : ℕ, S = 2 * R + D := ⟨S - 2 * R, by omega⟩
  have hDr : ((S : ℕ) : ℝ) / 2 - R = (D : ℝ) / 2 := by
    have : (S : ℝ) = 2 * R + D := by exact_mod_cast hD
    linarith
  rw [hDr]
  set T := (finalGap d L + t)⁻¹ with hTdef
  have hT0 : 0 < T := by positivity
  have h2T : 2 / (finalGap d L + t) = 2 * T := by rw [div_eq_mul_inv]
  have hE : 0 < Real.exp (-c * ((D : ℝ) / 2)) := Real.exp_pos _
  have hCpos : 0 ≤ P * C₀ * (finalGap d L)⁻¹ := by positivity
  by_cases hD12 : D < 12
  · -- trivial regime
    obtain ⟨_, hdec⟩ := finalMass_resolvent_decay (L := L) (N₀ := m) (k := k) hd hk hv0 hv1 ha1
      ha2 hmass ht
    obtain ⟨_, hdec'⟩ := finalMass_resolvent_decay (L := L) (N₀ := m') (k := k) hd hk hv0 hv1 ha1
      ha2 hmass ht
    have e1 : ‖((finalOp d L m k v a + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹)
        (castL1 m u) (castL1 m w)‖ ≤ 2 * T :=
      (hdec _ _).trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg hr.le (dist_nonneg (x := castL1 m u) (y := castL1 m w))]))
          (by positivity)).trans (by rw [mul_one, h2T]))
    have e2 : ‖((finalOp d L m' k v a + (t : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹)
        (castL1 m' u) (castL1 m' w)‖ ≤ 2 * T :=
      (hdec' _ _).trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg hr.le (dist_nonneg (x := castL1 m' u) (y := castL1 m' w))]))
          (by positivity)).trans (by rw [mul_one, h2T]))
    refine (norm_sub_le _ _).trans ?_
    have hD' : (D : ℝ) < 12 := by exact_mod_cast hD12
    have h6 : 1 ≤ Real.exp (6 * c) * Real.exp (-c * ((D : ℝ) / 2)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    have h7 : 4 * T ≤ 4 * Real.exp (6 * c) * Real.exp (-c * ((D : ℝ) / 2)) * T := by
      have : 4 * T * 1 ≤ 4 * T * (Real.exp (6 * c) * Real.exp (-c * ((D : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      linarith
    have h8 : 0 ≤ (K + P * C₀ * (finalGap d L)⁻¹ + 1) * Real.exp (-c * ((D : ℝ) / 2)) * T := by
      positivity
    have hrhs : (4 * Real.exp (6 * c) + K + P * C₀ * (finalGap d L)⁻¹ + 1) *
        Real.exp (-c * ((D : ℝ) / 2)) * T =
        4 * Real.exp (6 * c) * Real.exp (-c * ((D : ℝ) / 2)) * T +
          (K + P * C₀ * (finalGap d L)⁻¹ + 1) * Real.exp (-c * ((D : ℝ) / 2)) * T := by ring
    rw [hrhs]
    linarith
  · push Not at hD12
    set ρ : ℕ := D / 4 with hρ
    set Rm : ℕ := (S - 2) / 2 with hRm
    have hm1 : 2 * (R + ρ) < m := by omega
    have hm2 : 2 * (R + ρ) < m' := by omega
    have hfm : 2 * Rm + 1 < m := by omega
    have hfm' : 2 * Rm + 1 < m' := by omega
    have hRc : (R + ρ) + 1 ≤ Rm := by omega
    have hεb : ∀ q ∈ sqBox d (R + ρ), ∀ q' ∈ sqBox d (R + ρ),
        ‖finalOp d L m k v a (castL1 m q) (castL1 m q') -
            finalOp d L m' k v a (castL1 m' q) (castL1 m' q')‖ ≤
          C₀ * Real.exp (-c₀ * ((Rm : ℝ) - ((R + ρ : ℕ) : ℝ))) :=
      fun q hq q' hq' => hent hfm hfm' hRc hq hq'
    have h := hKmain hk hv0 hv1 ha1 ha2 hmass hm1 hm2 hεb ht hu hw
    refine h.trans ?_
    have hρ1 : (D : ℝ) / 4 ≤ (ρ : ℝ) + 1 := by
      have : D ≤ 4 * (ρ + 1) := by omega
      have h' : (D : ℝ) ≤ 4 * ((ρ : ℝ) + 1) := by exact_mod_cast this
      linarith
    have hRmρ : (D : ℝ) / 8 ≤ (Rm : ℝ) - ((R + ρ : ℕ) : ℝ) := by
      have : D + 8 * (R + ρ) ≤ 8 * Rm := by omega
      have h' : (D : ℝ) + 8 * ((R + ρ : ℕ) : ℝ) ≤ 8 * (Rm : ℝ) := by exact_mod_cast this
      linarith
    have h2ρ : ((2 * ρ + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by
      have : 2 * ρ + 1 ≤ D := by omega
      exact_mod_cast this
    have htail := final_close_tail (d := d) hg hK0 hC₀.le hc₀ hcr hcc hr hρ1 hRmρ h2ρ
    refine mul_le_mul_of_nonneg_right (htail.trans ?_) hT0.le
    have h0 : 0 ≤ 4 * Real.exp (6 * c) := by positivity
    nlinarith [mul_nonneg h0 hE.le]



/-- **Closeness of the final resolvent on two tori (blocker 7, estimate (I2), first piece).**
For the final operator `finalOp` on the tori of sides `m` and `m'`, uniformly in `t ≥ 0`, the
resolvent entries at the sites `castL1 m u`, `castL1 m w` and `castL1 m' u`, `castL1 m' w` of a
centred cube `|u_μ|, |w_μ| ≤ R` (the identity on residues, a box that does not wind) differ by at
most `C exp (-c (min m m' / 2 - R)) / (finalGap + t)`.  The constants depend on `d`, `L`, `k`
only. -/
theorem finalResolvent_twoTorus_close (hd : 0 < d) (hk : 1 ≤ k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v → ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {R : ℕ},
      2 * R < m → 2 * R < m' → ∀ {t : ℝ}, 0 ≤ t → ∀ {u w : Fin d → ℤ},
      u ∈ sqBox d R → w ∈ sqBox d R →
      ‖((finalOp d L m k v a + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹)
            (castL1 m u) (castL1 m w) -
          ((finalOp d L m' k v a + (t : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹)
            (castL1 m' u) (castL1 m' w)‖ ≤
        C * Real.exp (-c * (((min m m' : ℕ) : ℝ) / 2 - R)) * (finalGap d L + t)⁻¹ := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hent⟩ := finalOp_entry_close (d := d) (L := L) (k := k) hd
  obtain ⟨C, c, hC, hc, hcore⟩ := finalResolvent_twoTorus_close_of_entries (d := d) (L := L) hd hC₀ hc₀
  refine ⟨C, c, hC, hc, ?_⟩
  intro v a hv0 hv1 ha1 ha2 hmass m m' _ _ R hm hm' t ht u w hu hw
  exact hcore hk hv0 hv1 ha1 ha2 hmass (hent hv0 hv1 ha1 ha2) hm hm' ht hu hw

end Assembly


section Sqrt

variable {d L k : ℕ} [NeZero L]

/-- **Closeness of the inverse square root of the final operator on two tori, from the closeness
of the entries** (same hypothesis `hent` as `finalResolvent_twoTorus_close_of_entries`; the
constants `C, c` do not depend on `k`). -/
theorem finalSqrt_twoTorus_close_of_entries {d L : ℕ} [NeZero L] (hd : 0 < d) {C₀ c₀ : ℝ}
    (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a →
      a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      (∀ {m m' : ℕ} [NeZero m] [NeZero m'] {Rm Rc : ℕ}, 2 * Rm + 1 < m → 2 * Rm + 1 < m' →
        Rc + 1 ≤ Rm → ∀ {y y' : Fin d → ℤ}, y ∈ sqBox d Rc → y' ∈ sqBox d Rc →
        ‖finalOp d L m k v a (castL1 m y) (castL1 m y') -
            finalOp d L m' k v a (castL1 m' y) (castL1 m' y')‖ ≤
          C₀ * Real.exp (-c₀ * ((Rm : ℝ) - Rc))) →
      ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {R : ℕ},
      2 * R < m → 2 * R < m' → ∀ {u w : Fin d → ℤ}, u ∈ sqBox d R → w ∈ sqBox d R →
      ‖Localization.sqrtMat (finalOp d L m k v a) (castL1 m u) (castL1 m w) -
          Localization.sqrtMat (finalOp d L m' k v a) (castL1 m' u) (castL1 m' w)‖ ≤
        C * Real.exp (-c * (((min m m' : ℕ) : ℝ) / 2 - R)) / Real.sqrt (finalGap d L) := by
  obtain ⟨C, c, hC, hc, hmain⟩ := finalResolvent_twoTorus_close_of_entries (d := d) (L := L) hd hC₀ hc₀
  refine ⟨C, c, hC, hc, ?_⟩
  intro k hk v a hv0 hv1 ha1 ha2 hmass hent m m' _ _ R hm hm' u w hu hw
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have : Nonempty (L1Torus d m) := ⟨(0 : Torus d m)⟩
  have : Nonempty (L1Torus d m') := ⟨(0 : Torus d m')⟩
  have hA := finalMass_resOK (L := L) (N₀ := m) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
  have hA' := finalMass_resOK (L := L) (N₀ := m') (k := k) hd hk hv0 hv1 ha1 ha2 hmass
  set Bd : ℝ := C * Real.exp (-c * (((min m m' : ℕ) : ℝ) / 2 - R)) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have e1 := Localization.integrable_sqrt_entry hA (castL1 m u) (castL1 m w)
  have e2 := Localization.integrable_sqrt_entry hA' (castL1 m' u) (castL1 m' w)
  have hdiff : Localization.sqrtMat (finalOp d L m k v a) (castL1 m u) (castL1 m w) -
      Localization.sqrtMat (finalOp d L m' k v a) (castL1 m' u) (castL1 m' w) =
      ((1 / Real.pi : ℝ) : ℂ) * ∫ y, (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + finalOp d L m k v a)⁻¹
            (castL1 m u) (castL1 m w) -
        ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ) + finalOp d L m' k v a)⁻¹
            (castL1 m' u) (castL1 m' w)) ∂μ := by
    rw [integral_sub e1 e2]
    simp only [Localization.sqrtMat, Localization.intMat, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hdiff]
  have hint : Integrable (fun s : ℝ => Bd * (s ^ (-(1 / 2 : ℝ)) * (finalGap d L + s)⁻¹)) μ :=
    (Localization.integrableOn_rpow_inv_add hg).const_mul Bd
  have hbound := norm_integral_le_of_norm_le
    (f := fun y : ℝ => (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + finalOp d L m k v a)⁻¹
            (castL1 m u) (castL1 m w) -
        ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ) + finalOp d L m' k v a)⁻¹
            (castL1 m' u) (castL1 m' w)))
    hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => by
      have hs0 : 0 < s := mem_Ioi.mp hs
      have h3 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
      have hres := hmain hk hv0 hv1 ha1 ha2 hmass hent hm hm' hs0.le hu hw
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      rw [add_comm ((s : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ)),
        add_comm ((s : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))]
      calc s ^ (-(1 / 2 : ℝ)) * ‖(finalOp d L m k v a + (s : ℂ) • (1 : Matrix (L1Torus d m)
            (L1Torus d m) ℂ))⁻¹ (castL1 m u) (castL1 m w) - (finalOp d L m' k v a + (s : ℂ) •
              (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ))⁻¹ (castL1 m' u) (castL1 m' w)‖
          ≤ s ^ (-(1 / 2 : ℝ)) * (Bd * (finalGap d L + s)⁻¹) :=
            mul_le_mul_of_nonneg_left hres h3.le
        _ = _ := by ring))
  rw [integral_const_mul, Localization.integral_rpow_inv_add hg] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 hg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc 1 / Real.pi * ‖∫ y, (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + finalOp d L m k v a)⁻¹
            (castL1 m u) (castL1 m w) -
        ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (L1Torus d m') (L1Torus d m') ℂ) + finalOp d L m' k v a)⁻¹
            (castL1 m' u) (castL1 m' w)) ∂μ‖
      ≤ 1 / Real.pi * (Bd * (Real.pi / Real.sqrt (finalGap d L))) := by gcongr
    _ = Bd / Real.sqrt (finalGap d L) := by field_simp
    _ = _ := by rw [hBd]


/-- **Closeness of the inverse square root of the final operator on two tori.**  The Stieltjes
integral of `finalResolvent_twoTorus_close`, whose bound carries the factor `(finalGap + t)⁻¹`:
`π⁻¹ ∫₀^∞ t^{-1/2} (finalGap + t)⁻¹ dt = (finalGap)^{-1/2}`. -/
theorem finalSqrt_twoTorus_close (hd : 0 < d) (hk : 1 ≤ k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v → ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {R : ℕ},
      2 * R < m → 2 * R < m' → ∀ {u w : Fin d → ℤ}, u ∈ sqBox d R → w ∈ sqBox d R →
      ‖Localization.sqrtMat (finalOp d L m k v a) (castL1 m u) (castL1 m w) -
          Localization.sqrtMat (finalOp d L m' k v a) (castL1 m' u) (castL1 m' w)‖ ≤
        C * Real.exp (-c * (((min m m' : ℕ) : ℝ) / 2 - R)) / Real.sqrt (finalGap d L) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hent⟩ := finalOp_entry_close (d := d) (L := L) (k := k) hd
  obtain ⟨C, c, hC, hc, hcore⟩ := finalSqrt_twoTorus_close_of_entries (d := d) (L := L) hd hC₀ hc₀
  refine ⟨C, c, hC, hc, ?_⟩
  intro v a hv0 hv1 ha1 ha2 hmass m m' _ _ R hm hm' u w hu hw
  exact hcore hk hv0 hv1 ha1 ha2 hmass (hent hv0 hv1 ha1 ha2) hm hm' hu hw

end Sqrt

end Balaban.Green
