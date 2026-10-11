/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.KernelStd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Locality of the constrained sandwich `Π` (GREEN.md G-2(vi′), §4.6)
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-! ### Entries of the operators -/

section Entries

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem liftOp_sub (A B : Matrix ι ι ℂ) : liftOp N (A - B) = liftOp N A - liftOp N B := by
  ext p q
  simp only [liftOp, Matrix.sub_apply]
  split_ifs <;> simp

omit [Fintype ι] in
theorem liftOp_diagonal (β : ι → ℂ) :
    liftOp N (Matrix.diagonal β) = Matrix.diagonal (fun p : ι × Fin N => β p.1) := by
  ext p q
  simp only [liftOp, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq; simp
  · by_cases h1 : p.1 = q.1
    · have h2 : ¬ p.2 = q.2 := fun h2 => hpq (Prod.ext h1 h2)
      simp [h2, hpq]
    · simp [h1, hpq]

theorem fieldMul_transpose_mul (φ : ι → Fin N → ℂ) :
    (fieldMul φ)ᵀ * fieldMul φ = Matrix.diagonal (fun x => ∑ i, φ x i * φ x i) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fieldMul, Fintype.sum_prod_type,
    Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte]
    rw [Finset.sum_eq_single x]
    · refine Finset.sum_congr rfl fun i _ => by simp
    · intro u _ hu; simp [hu]
    · simp
  · simp only [hxy, ↓reduceIte]
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : u = x
    · subst h1; simp [hxy]
    · simp [h1]

theorem commK_apply (H : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) (x y : ι) (i : Fin N) :
    commK H φ x (y, i) = H x y * (φ x i - φ y i) := by
  unfold commK
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, fieldMul, liftOp,
    Fintype.sum_prod_type]
  have h1 : ∑ u, ∑ j, (if u = x then φ x j else 0) * (if j = i then H u y else 0) = φ x i * H x y := by
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    · intro u _ hu; simp [hu]
    · simp
  have h2 : ∑ u, H x u * (if y = u then φ u i else 0) = H x y * φ y i := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro u _ hu; simp [Ne.symm hu]
    · simp
  rw [h1, h2]; ring

theorem commK_sub_field (H : Matrix ι ι ℂ) (ψ₁ ψ₂ : ι → Fin N → ℂ) :
    commK H (fun x j => ψ₁ x j - ψ₂ x j) = commK H ψ₁ - commK H ψ₂ := by
  ext x ⟨y, i⟩
  simp only [commK_apply, Matrix.sub_apply]
  ring

theorem commK_add_diagonal (H : Matrix ι ι ℂ) (β : ι → ℂ) (φ : ι → Fin N → ℂ) :
    commK (H + Matrix.diagonal β) φ = commK H φ := by
  ext x ⟨y, i⟩
  simp only [commK_apply, Matrix.add_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

end Entries

/-! ### Site-local operators are in `Dec` -/

section SiteLocal

variable {N : ℕ} (G : GeneratingSet d L N₀ k ϱ)

theorem bn_id_sq (j : ℕ) (y : Torus d (N₀ * L ^ k)) (s : G.Ω 1 → ℂ) :
    bn G (id : G.Ω 1 → G.Ω 1) j y s ^ 2 =
      ∑ x : G.Ω 1, if jBlock d L N₀ k j (x : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y
        then ‖s x‖ ^ 2 else 0 := by
  unfold bn
  rw [l2_sq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [bproj, id]
  split_ifs <;> simp

theorem bn_fst_sq' (j : ℕ) (y : Torus d (N₀ * L ^ k)) (g : G.Ω 1 × Fin N → ℂ) :
    bn G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j y g ^ 2 =
      ∑ x : G.Ω 1, if jBlock d L N₀ k j (x : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y
        then ∑ i, ‖g (x, i)‖ ^ 2 else 0 := by
  unfold bn
  rw [l2_sq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [bproj]
  split_ifs <;> simp

variable {G}

/-- `bn` is dominated by the product of a block-wise bound: from squares. -/
theorem bn_le_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (pow_le_pow_iff_left₀ ha hb two_ne_zero).1 h

/-- Multiplication by a vector field `ψ` with `|ψ| ≤ c` is blockwise `c`-bounded. -/
theorem fieldMul_dec {ψ : G.Ω 1 → Fin N → ℂ} {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hψ : ∀ x, vn (ψ x) ≤ c) :
    Dec G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) (id : G.Ω 1 → G.Ω 1) (fieldMul ψ) 0 γ noTail
      (c * Real.exp (γ * (4 * d))) := by
  refine Dec.of_blockwise hc hγ fun j y hj1 hjk hy f => ?_
  refine bn_le_of_sq_le (bn_nonneg _ _ _ _) (by have := bn_nonneg (G := G) (id : G.Ω 1 → G.Ω 1) j y f; positivity) ?_
  rw [bn_fst_sq', mul_pow, bn_id_sq, Finset.mul_sum]
  simp only [zpow_zero, mul_one]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs
  · have e : ∑ i, ‖(fieldMul ψ *ᵥ f) (x, i)‖ ^ 2 = vn (ψ x) ^ 2 * ‖f x‖ ^ 2 := by
      rw [vn_sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fieldMul_mulVec, norm_mul, mul_pow]
    rw [e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (vn_nonneg _) (hψ x) 2) (sq_nonneg _)
  · simp

/-- The transpose `φ ·` of the field multiplication is blockwise `c`-bounded. -/
theorem fieldMulT_dec {ψ : G.Ω 1 → Fin N → ℂ} {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hψ : ∀ x, vn (ψ x) ≤ c) :
    Dec G (id : G.Ω 1 → G.Ω 1) (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) (fieldMul ψ)ᵀ 0 γ noTail
      (c * Real.exp (γ * (4 * d))) := by
  refine Dec.of_blockwise hc hγ fun j y hj1 hjk hy f => ?_
  refine bn_le_of_sq_le (bn_nonneg _ _ _ _)
    (by have := bn_nonneg (G := G) (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j y f; positivity) ?_
  rw [bn_id_sq, mul_pow, bn_fst_sq', Finset.mul_sum]
  simp only [zpow_zero, mul_one]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs
  · rw [fieldMul_transpose_mulVec]
    have h1 := norm_dot_le (ψ x) (fun i => f (x, i))
    have h2 : ‖∑ i, ψ x i * f (x, i)‖ ^ 2 ≤ (c * vn (fun i => f (x, i))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h1.trans (mul_le_mul_of_nonneg_right (hψ x) (vn_nonneg _))) 2
    refine h2.trans (le_of_eq ?_)
    rw [mul_pow, vn_sq]
  · simp

/-- A diagonal operator with `|β(x)| ≤ b (ℓ(x)²)^w` is blockwise bounded. -/
theorem diagonal_dec {β : G.Ω 1 → ℂ} {b γ : ℝ} {w : ℤ} (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hβ : ∀ x : G.Ω 1, ‖β x‖ ≤ b * ((G.spacing (x : Torus d (N₀ * L ^ k)) *
      G.spacing (x : Torus d (N₀ * L ^ k))) ^ w)) :
    Dec G (id : G.Ω 1 → G.Ω 1) (id : G.Ω 1 → G.Ω 1) (Matrix.diagonal β) w γ noTail
      (b * Real.exp (γ * (4 * d))) := by
  refine Dec.of_blockwise hb hγ fun j y hj1 hjk hy f => ?_
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hQ : 0 < ((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w := by positivity
  refine bn_le_of_sq_le (bn_nonneg _ _ _ _)
    (by have := bn_nonneg (G := G) (id : G.Ω 1 → G.Ω 1) j y f; positivity) ?_
  rw [bn_id_sq, mul_pow, mul_pow, bn_id_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with hx
  · have hxl : (x : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk hx).2 hy
    have hsp := G.spacing_eq hj1 hjk hxl
    have h1 := hβ x
    rw [hsp] at h1
    rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
    have h2 : ‖β x‖ ^ 2 ≤ (b * ((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖β x‖ ^ 2 * ‖f x‖ ^ 2 ≤ (b * ((L : ℝ) ^ j * (L : ℝ) ^ j) ^ w) ^ 2 * ‖f x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by ring
  · simp

end SiteLocal

/-! ### Operators localized near `Z` -/

section Localized

variable {ι ι₂ ι₃ : Type*} [Fintype ι] [Fintype ι₂] [Fintype ι₃] (G : GeneratingSet d L N₀ k ϱ)

theorem OutNear.of_close {s : ι → G.Ω 1} {Z : Finset (G.Ω 1)} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {T : Matrix ι ι₂ ℂ}
    (hT : ∀ (g : ι₂ → ℂ) (p : ι), (T *ᵥ g) p ≠ 0 →
      ∃ z ∈ Z, G.pathDist (s p : Torus d (N₀ * L ^ k)) (z : Torus d (N₀ * L ^ k)) ≤
        ENNReal.ofReal c₀) :
    OutNear G s Z (2 * d + c₀) T := by
  intro j y hj1 hjk hy hfar g
  by_contra hne
  have hne' : l2 (bproj G s j y (T *ᵥ g)) ≠ 0 := hne
  obtain ⟨p, hp⟩ := exists_ne_of_l2_ne hne'
  have hpb : jBlock d L N₀ k j (s p : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y := by
    by_contra h; simp [bproj, h] at hp
  have hpT : (T *ᵥ g) p ≠ 0 := by
    intro h; simp [bproj, h] at hp
  obtain ⟨z, hz, hdz⟩ := hT g p hpT
  have h1 := G.pathDist_block_le hj1 hjk hy hpb
  apply hfar
  refine (G.distSet_le y hz).trans ((G.pathDist_triangle y (s p) z).trans ?_)
  rw [ENNReal.ofReal_add (by positivity) hc₀]
  exact add_le_add h1 hdz

theorem OutNear.of_supp {s : ι → G.Ω 1} {Z : Finset (G.Ω 1)} {T : Matrix ι ι₂ ℂ}
    (hT : ∀ (g : ι₂ → ℂ) (p : ι), (T *ᵥ g) p ≠ 0 → s p ∈ Z) :
    OutNear G s Z (2 * d) T := by
  have := OutNear.of_close G (s := s) (Z := Z) (c₀ := 0) le_rfl (T := T) (fun g p hp =>
    ⟨s p, hT g p hp, by rw [G.pathDist_self (s p).2]; exact zero_le⟩)
  simpa using this

theorem OutNear.mul_right {s : ι → G.Ω 1} {Z : Finset (G.Ω 1)} {c : ℝ} {E : Matrix ι ι₂ ℂ}
    (hE : OutNear G s Z c E) (R : Matrix ι₂ ι₃ ℂ) : OutNear G s Z c (E * R) := by
  intro j y hj1 hjk hy hfar g
  rw [← Matrix.mulVec_mulVec]
  exact hE j y hj1 hjk hy hfar _

end Localized

/-! ### Range of the Dirichlet operator -/

section Range

variable (G : GeneratingSet d L N₀ k ϱ)

theorem latticeLaplacian_adj {ℓ : ℕ} [NeZero ℓ] (ν : ℝ) {x y : Torus d ℓ} (hxy : x ≠ y)
    (h : latticeLaplacian d ℓ ν x y ≠ 0) : ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ x = y + Pi.single μ 1 := by
  by_contra hno
  push Not at hno
  apply h
  simp only [latticeLaplacian, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hxy,
    ↓reduceIte, smul_zero, zero_sub, neg_eq_zero, Matrix.sum_apply, Matrix.add_apply,
    Matrix.transpose_apply, shiftMatrix]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have h1 := (hno μ).1
  have h2 := (hno μ).2
  simp [h1, h2]

theorem dirichlet_entry_close (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) {x y : G.Ω 1}
    (h : dirichletOperator G a ν α x y ≠ 0) :
    G.pathDist (x : Torus d (N₀ * L ^ k)) y ≤ ENNReal.ofReal (2 * d + 1) := by
  by_cases hxy : x = y
  · subst hxy
    rw [G.pathDist_self x.2]; exact zero_le
  have hxy' : (x : Torus d (N₀ * L ^ k)) ≠ y := fun h' => hxy (Subtype.ext h')
  have hfull : fullMatrix G a ν x y ≠ 0 := by
    intro h0
    apply h
    simp [dirichletOperator, Green.restrictOp, Matrix.submatrix_apply,
      hxy, h0]
  have hsplit : latticeLaplacian d (N₀ * L ^ k) ν x y ≠ 0 ∨ avgMatrix G a x y ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hfull
    simp [fullMatrix, hc.1, hc.2]
  rcases hsplit with hl | ha
  · obtain ⟨μ, hμ⟩ := latticeLaplacian_adj ν hxy' hl
    have hadj : Adj (x : Torus d (N₀ * L ^ k)) y := ⟨μ, hμ⟩
    refine (G.pathDist_le_bondCost x.2 y.2 hadj).trans (ENNReal.ofReal_le_ofReal ?_)
    have := G.bondCost_le_one x.2 (y : Torus d (N₀ * L ^ k))
    have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
    linarith
  · unfold avgMatrix at ha
    rw [Matrix.sum_apply] at ha
    obtain ⟨j, hj, hjne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    have hjr := Finset.mem_Icc.1 hj
    simp only [Matrix.smul_apply, smul_eq_mul] at hjne
    have hl : layerProjMatrix G j x y ≠ 0 := fun h0 => hjne (by rw [h0, mul_zero])
    unfold layerProjMatrix at hl
    by_cases hxl : (x : Torus d (N₀ * L ^ k)) ∈ G.layer j ∧ (y : Torus d (N₀ * L ^ k)) ∈ G.layer j
    · simp only [hxl, and_self, ↓reduceIte] at hl
      unfold blockProjMatrix at hl
      by_cases hb : blockMap (L ^ j) (N₀ * L ^ (k - j)) (x : Torus d (N₀ * L ^ k)) =
          blockMap (L ^ j) (N₀ * L ^ (k - j)) (y : Torus d (N₀ * L ^ k))
      · have hb' : jBlock d L N₀ k j (y : Torus d (N₀ * L ^ k)) =
            jBlock d L N₀ k j (x : Torus d (N₀ * L ^ k)) := hb.symm
        refine (G.pathDist_block_le hjr.1 hjr.2 hxl.1 hb').trans (ENNReal.ofReal_le_ofReal ?_)
        linarith
      · exact absurd (by simp [hb]) hl
    · exact absurd (by simp [hxl]) hl

/-- The commutator `K(ψ)` of a field `ψ` supported in `Z` has output near `Z`. -/
theorem commK_outNear (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) {N : ℕ}
    {ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Z : Finset (G.Ω 1)}
    (hψ : ∀ x : G.Ω 1, x ∉ Z → ψ x = 0) :
    OutNear G (id : G.Ω 1 → G.Ω 1) Z (2 * d + (2 * d + 1))
      (commK (dirichletOperator G a ν α) (restrictField G ψ)) := by
  refine OutNear.of_close G (by positivity) fun g x hx => ?_
  rw [commK_mulVec] at hx
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have hH : dirichletOperator G a ν α x y ≠ 0 := fun h0 => hi (by rw [h0]; ring)
  have hd : restrictField G ψ x i - restrictField G ψ y i ≠ 0 := fun h0 => hi (by rw [h0]; ring)
  by_cases hxZ : x ∈ Z
  · exact ⟨x, hxZ, by rw [id, G.pathDist_self x.2]; exact zero_le⟩
  · by_cases hyZ : y ∈ Z
    · exact ⟨y, hyZ, dirichlet_entry_close G a ν α hH⟩
    · exfalso
      apply hd
      simp only [restrictField]
      rw [hψ x hxZ, hψ y hyZ]; simp

end Range

end Balaban.Multiscale
