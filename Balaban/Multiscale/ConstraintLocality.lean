/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.KernelStd
public import Balaban.Multiscale.ConstraintPerturb
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

/-! ### The data of the locality statement -/

/-- The data of G-2(vi′): two instances `(α, φ₀)`, `(α′, φ₀′)` of the hypotheses of G-2(v) with the
same `a`, `ν`, `δ`, which agree off the set `Z ⊆ Ω₁`; `ϱ` is large (`log L ≤ κ (ϱ - 1)`). -/
structure LocData (d L N : ℕ) [NeZero L] where
  N₀ : ℕ
  [hN₀ : NeZero N₀]
  k : ℕ
  ϱ : ℝ
  G : GeneratingSet d L N₀ k ϱ
  a : ℕ → ℝ
  ν : ℝ
  α : G.Ω 1 → ℂ
  α' : G.Ω 1 → ℂ
  δ : ℝ
  φ : Torus d (N₀ * L ^ k) → Fin N → ℂ
  φ' : Torus d (N₀ * L ^ k) → Fin N → ℂ
  Z : Finset (G.Ω 1)
  St : Standing G a ν α δ φ
  St' : Standing G a ν α' δ φ'
  hZα : ∀ x : G.Ω 1, x ∉ Z → α x = α' x
  hZφ : ∀ x : G.Ω 1, x ∉ Z → φ x = φ' x
  hϱ : 1 < ϱ
  hlog : Real.log L ≤ locKappa d * (ϱ - 1)

attribute [instance] LocData.hN₀

namespace LocData

variable {d L N : ℕ} [NeZero L] (D : LocData d L N)

/-- `H_D(α)`. -/
noncomputable def H : Matrix (D.G.Ω 1) (D.G.Ω 1) ℂ := dirichletOperator D.G D.a D.ν D.α
/-- `H_D(α′)`. -/
noncomputable def H' : Matrix (D.G.Ω 1) (D.G.Ω 1) ℂ := dirichletOperator D.G D.a D.ν D.α'
/-- `Ĝ = G_D(α)` acting on vector fields. -/
noncomputable def Gh : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1 × Fin N) ℂ := liftOp N D.H⁻¹
noncomputable def Gh' : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1 × Fin N) ℂ := liftOp N D.H'⁻¹
/-- `φ₀ ·` (multiplication of a scalar field by `φ₀`). -/
noncomputable def Ph : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1) ℂ := fieldMul (restrictField D.G D.φ)
noncomputable def Ph' : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1) ℂ := fieldMul (restrictField D.G D.φ')
/-- The difference field `ψ = φ₀ - φ₀′` and the corresponding multiplication. -/
noncomputable def ψ : Torus d (D.N₀ * L ^ D.k) → Fin N → ℂ := fun x j => D.φ x j - D.φ' x j
noncomputable def Ps : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1) ℂ := fieldMul (restrictField D.G D.ψ)
/-- The commutators `K(φ₀)` and `K(ψ)`. -/
noncomputable def K : Matrix (D.G.Ω 1) (D.G.Ω 1 × Fin N) ℂ := commK D.H (restrictField D.G D.φ)
noncomputable def Ks : Matrix (D.G.Ω 1) (D.G.Ω 1 × Fin N) ℂ := commK D.H (restrictField D.G D.ψ)
/-- `M`, `M′`, `Nn`, `Nn′` of the sandwich formula. -/
noncomputable def Mm : Matrix (D.G.Ω 1) (D.G.Ω 1) ℂ :=
  constraintM D.H D.H⁻¹ (restrictField D.G D.φ)
noncomputable def Mm' : Matrix (D.G.Ω 1) (D.G.Ω 1) ℂ :=
  constraintM D.H' D.H'⁻¹ (restrictField D.G D.φ')
noncomputable def Nn : Matrix (D.G.Ω 1) (D.G.Ω 1 × Fin N) ℂ :=
  constraintN D.H D.H⁻¹ (restrictField D.G D.φ)
noncomputable def Nn' : Matrix (D.G.Ω 1) (D.G.Ω 1 × Fin N) ℂ :=
  constraintN D.H' D.H'⁻¹ (restrictField D.G D.φ')
/-- The difference of the diagonal operators and of the bilinear squares. -/
noncomputable def D0 : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1 × Fin N) ℂ :=
  liftOp N (Matrix.diagonal (D.α - D.α'))
noncomputable def Xa : Matrix (D.G.Ω 1) (D.G.Ω 1) ℂ :=
  Matrix.diagonal (fun x => ∑ i, D.φ' x i * D.φ' x i - ∑ i, D.φ x i * D.φ x i)
/-- The constrained operators `Π`, `Π′`. -/
noncomputable def Pi : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1 × Fin N) ℂ :=
  constrainedOp D.H⁻¹ (restrictField D.G D.φ)
noncomputable def Pi' : Matrix (D.G.Ω 1 × Fin N) (D.G.Ω 1 × Fin N) ℂ :=
  constrainedOp D.H'⁻¹ (restrictField D.G D.φ')

end LocData

/-! ### The telescoping identity -/

section Telescope

theorem tele_alg {V S : Type*} [Fintype V] [Fintype S] [DecidableEq S] (A A' : Matrix V V ℂ) (B B' : Matrix V S ℂ) (X X' M M' : Matrix S S ℂ)
    (C C' : Matrix S V ℂ) (hX : X * M = 1) (hX' : M' * X' = 1) :
    A * B * X * C - A' * B' * X' * C' =
      (A - A') * B * X * C + A' * (B - B') * X * C + A' * B' * (X * (M' - M) * X') * C +
        A' * B' * X' * (C - C') := by
  have hXX : X * (M' - M) * X' = X - X' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hX', mul_one, hX, Matrix.one_mul]
  rw [hXX]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem Mdiff_alg {V S : Type*} [Fintype V] (K Ks Kp : Matrix S V ℂ) (Gh Gh' : Matrix V V ℂ) (Ph Ph' Ps : Matrix V S ℂ)
    (T T' Xa : Matrix S S ℂ) (hK : Kp = K - Ks) (hP : Ph - Ph' = Ps) (hT : T' - T = Xa) :
    (T' - Kp * Gh' * Ph') - (T - K * Gh * Ph) =
      Xa + Ks * Gh' * Ph' - K * (Gh' - Gh) * Ph' + K * Gh * Ps := by
  have hPh : Ph = Ph' + Ps := by rw [← hP]; abel
  have hT' : T' = T + Xa := by rw [← hT]; abel
  subst hK hPh hT'
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem Ndiff_alg {V S : Type*} [Fintype V] (K Ks Kp : Matrix S V ℂ) (Gh Gh' : Matrix V V ℂ) (Ph Ph' Ps : Matrix V S ℂ)
    (hK : Kp = K - Ks) (hP : Ph - Ph' = Ps) :
    (Phᵀ - K * Gh) - (Ph'ᵀ - Kp * Gh') = Psᵀ + K * (Gh' - Gh) - Ks * Gh' := by
  have hPh : Ph = Ph' + Ps := by rw [← hP]; abel
  subst hK hPh
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_add]
  abel

end Telescope

namespace LocData

variable {d L N : ℕ} [NeZero L] (D : LocData d L N)

noncomputable def Pst : Matrix (D.G.Ω 1) (D.G.Ω 1 × Fin N) ℂ := (D.Ps)ᵀ

theorem H_mul_inv : D.H * D.H⁻¹ = 1 := dirichlet_mul_inv D.St
theorem inv_mul_H : D.H⁻¹ * D.H = 1 := dirichlet_inv_mul D.St
theorem H'_mul_inv : D.H' * D.H'⁻¹ = 1 := dirichlet_mul_inv D.St'
theorem inv_mul_H' : D.H'⁻¹ * D.H' = 1 := dirichlet_inv_mul D.St'

theorem H_eq : D.H = D.H' + Matrix.diagonal (D.α - D.α') :=
  dirichletOperator_eq_add D.G D.a D.ν D.α D.α'

theorem Hinv_sub : D.H⁻¹ - D.H'⁻¹ = -(D.H⁻¹ * Matrix.diagonal (D.α - D.α') * D.H'⁻¹) := by
  have h1 : D.H⁻¹ - D.H'⁻¹ = D.H⁻¹ * (D.H' - D.H) * D.H'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, D.H'_mul_inv, Matrix.mul_one,
      D.inv_mul_H, Matrix.one_mul]
  rw [h1]
  have h2 : D.H' - D.H = -Matrix.diagonal (D.α - D.α') := by rw [D.H_eq]; abel
  rw [h2]
  simp only [Matrix.mul_neg, Matrix.neg_mul]

omit [NeZero L] in
theorem liftOp_neg' {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    liftOp N (-A) = -liftOp N A := by
  ext p q
  by_cases h : p.2 = q.2 <;> simp [liftOp, h]

theorem Gh_sub : D.Gh - D.Gh' = -(D.Gh * D.D0 * D.Gh') := by
  unfold Gh Gh' D0
  rw [← liftOp_sub, D.Hinv_sub, liftOp_neg', liftOp_mul, liftOp_mul]

theorem Gh_sub' : D.Gh' - D.Gh = D.Gh * D.D0 * D.Gh' := by
  have := D.Gh_sub
  rw [← neg_sub, this, neg_neg]

theorem Ph_sub : D.Ph - D.Ph' = D.Ps := by
  unfold Ph Ph' Ps ψ
  exact (fieldMul_sub' _ _).symm

theorem Kp_eq : commK D.H' (restrictField D.G D.φ') = D.K - D.Ks := by
  have h1 : commK D.H' (restrictField D.G D.φ') = commK D.H (restrictField D.G D.φ') := by
    rw [D.H_eq, commK_add_diagonal]
  rw [h1]
  unfold K Ks ψ restrictField
  rw [commK_sub_field]
  abel

theorem Mm_sub : D.Mm' - D.Mm = D.Xa + D.Ks * D.Gh' * D.Ph' - D.K * D.Gh * D.D0 * D.Gh' * D.Ph'
    + D.K * D.Gh * D.Ps := by
  have hT : (fieldMul (restrictField D.G D.φ'))ᵀ * fieldMul (restrictField D.G D.φ') -
      (fieldMul (restrictField D.G D.φ))ᵀ * fieldMul (restrictField D.G D.φ) = D.Xa := by
    rw [fieldMul_transpose_mul, fieldMul_transpose_mul]
    unfold Xa
    rw [← Matrix.diagonal_sub]
    rfl
  have h := Mdiff_alg (D.K) (D.Ks) (commK D.H' (restrictField D.G D.φ')) D.Gh D.Gh' D.Ph D.Ph'
    D.Ps ((fieldMul (restrictField D.G D.φ))ᵀ * fieldMul (restrictField D.G D.φ))
    ((fieldMul (restrictField D.G D.φ'))ᵀ * fieldMul (restrictField D.G D.φ')) D.Xa D.Kp_eq
    D.Ph_sub hT
  have e : D.Mm' - D.Mm = ((fieldMul (restrictField D.G D.φ'))ᵀ * fieldMul (restrictField D.G D.φ') -
      commK D.H' (restrictField D.G D.φ') * D.Gh' * D.Ph') -
      ((fieldMul (restrictField D.G D.φ))ᵀ * fieldMul (restrictField D.G D.φ) - D.K * D.Gh * D.Ph) := by
    unfold Mm Mm' constraintM Gh Gh' Ph Ph' K
    rfl
  rw [e, h, D.Gh_sub']
  simp only [Matrix.mul_assoc]

theorem Nn_sub : D.Nn - D.Nn' = D.Pst + D.K * D.Gh * D.D0 * D.Gh' - D.Ks * D.Gh' := by
  have h := Ndiff_alg (D.K) (D.Ks) (commK D.H' (restrictField D.G D.φ')) D.Gh D.Gh' D.Ph D.Ph'
    D.Ps D.Kp_eq D.Ph_sub
  have e : D.Nn - D.Nn' = (D.Ph ᵀ - D.K * D.Gh) - (D.Ph' ᵀ - commK D.H' (restrictField D.G D.φ') * D.Gh') := by
    unfold Nn Nn' constraintN Gh Gh' Ph Ph' K
    rfl
  rw [e, h, D.Gh_sub']
  unfold Pst
  simp only [Matrix.mul_assoc]

theorem Pi_eq : D.Pi = D.Gh * D.Ph * D.Mm⁻¹ * D.Nn := by
  unfold Pi Gh Ph Mm Nn
  exact constrainedOp_eq D.H_mul_inv D.inv_mul_H _

theorem Pi'_eq : D.Pi' = D.Gh' * D.Ph' * D.Mm'⁻¹ * D.Nn' := by
  unfold Pi' Gh' Ph' Mm' Nn'
  exact constrainedOp_eq D.H'_mul_inv D.inv_mul_H' _

theorem Mm_mul_inv : D.Mm * D.Mm⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (constraintM_isUnit D.St))

theorem inv_mul_Mm : D.Mm⁻¹ * D.Mm = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (constraintM_isUnit D.St))

theorem Mm'_mul_inv : D.Mm' * D.Mm'⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (constraintM_isUnit D.St'))

/-- **The telescoping decomposition of `Π - Π′`** into products with exactly one localized factor. -/
theorem Pi_sub : D.Pi - D.Pi' =
    -(D.Gh * D.D0 * (D.Gh' * D.Ph * D.Mm⁻¹ * D.Nn))
    + D.Gh' * D.Ps * (D.Mm⁻¹ * D.Nn)
    + D.Gh' * D.Ph' * D.Mm⁻¹ * D.Xa * (D.Mm'⁻¹ * D.Nn)
    + D.Gh' * D.Ph' * D.Mm⁻¹ * (D.Ks * D.Gh') * (D.Ph' * D.Mm'⁻¹ * D.Nn)
    - D.Gh' * D.Ph' * D.Mm⁻¹ * D.K * D.Gh * D.D0 * (D.Gh' * D.Ph' * D.Mm'⁻¹ * D.Nn)
    + D.Gh' * D.Ph' * D.Mm⁻¹ * D.K * D.Gh * D.Ps * (D.Mm'⁻¹ * D.Nn)
    + D.Gh' * D.Ph' * D.Mm'⁻¹ * D.Pst
    + D.Gh' * D.Ph' * D.Mm'⁻¹ * D.K * D.Gh * D.D0 * D.Gh'
    - D.Gh' * D.Ph' * D.Mm'⁻¹ * (D.Ks * D.Gh') := by
  have h := tele_alg D.Gh D.Gh' D.Ph D.Ph' D.Mm⁻¹ D.Mm'⁻¹ D.Mm D.Mm' D.Nn D.Nn' D.inv_mul_Mm
    D.Mm'_mul_inv
  rw [D.Pi_eq, D.Pi'_eq, h, D.Mm_sub, D.Nn_sub, D.Ph_sub]
  have hG : D.Gh - D.Gh' = -(D.Gh * D.D0 * D.Gh') := D.Gh_sub
  rw [hG]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul,
    Matrix.mul_assoc]
  abel

end LocData

/-! ### Facts about the data -/

section Facts

variable {N : ℕ}

theorem vn_sub_le (u w : Fin N → ℂ) : vn (u - w) ≤ vn u + vn w := by
  have h := vn_triangle u 0 w
  rwa [sub_zero, vn_sub_comm 0 w, sub_zero] at h

omit [NeZero N₀] [NeZero L] in
theorem smooth_sub_grad {δ₁ δ₂ : ℝ} {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (x e₁ : Torus d (N₀ * L ^ k)) (s : ℝ)
    (a1 : vn (φ₁ e₁ - φ₁ x) ≤ δ₁ / s) (a2 : vn (φ₂ e₁ - φ₂ x) ≤ δ₂ / s) :
    vn ((fun j => φ₁ e₁ j - φ₂ e₁ j) - (fun j => φ₁ x j - φ₂ x j) : Fin N → ℂ) ≤
      (δ₁ + δ₂) / s := by
  have e : ((fun j => φ₁ e₁ j - φ₂ e₁ j) - (fun j => φ₁ x j - φ₂ x j) : Fin N → ℂ) =
      (φ₁ e₁ - φ₁ x) - (φ₂ e₁ - φ₂ x) := by
    funext j; simp only [Pi.sub_apply]; ring
  rw [e]
  refine (vn_sub_le _ _).trans ?_
  rw [add_div]
  exact add_le_add a1 a2

theorem IsSmoothField.sub {G : GeneratingSet d L N₀ k ϱ} {δ₁ δ₂ : ℝ}
    {φ₁ φ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (h₁ : IsSmoothField G δ₁ φ₁)
    (h₂ : IsSmoothField G δ₂ φ₂) :
    IsSmoothField G (δ₁ + δ₂) (fun x j => φ₁ x j - φ₂ x j) := by
  refine ⟨fun x hx μ => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · exact smooth_sub_grad _ _ _ (h₁.grad x hx μ).1 (h₂.grad x hx μ).1
  · exact smooth_sub_grad _ _ _ (h₁.grad x hx μ).2 (h₂.grad x hx μ).2
  · have a1 := h₁.lap x hx
    have a2 := h₂.lap x hx
    have e : (fun i => ∑ μ : Fin d, ((φ₁ (x + Pi.single μ 1) i - φ₂ (x + Pi.single μ 1) i) +
        (φ₁ (x - Pi.single μ 1) i - φ₂ (x - Pi.single μ 1) i) - 2 * (φ₁ x i - φ₂ x i))) =
        (fun i => ∑ μ : Fin d, (φ₁ (x + Pi.single μ 1) i + φ₁ (x - Pi.single μ 1) i - 2 * φ₁ x i)) -
        (fun i => ∑ μ : Fin d, (φ₂ (x + Pi.single μ 1) i + φ₂ (x - Pi.single μ 1) i - 2 * φ₂ x i)) := by
      funext i
      simp only [Pi.sub_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      ring
    have key : vn (fun i => ∑ μ : Fin d, ((φ₁ (x + Pi.single μ 1) i - φ₂ (x + Pi.single μ 1) i) +
        (φ₁ (x - Pi.single μ 1) i - φ₂ (x - Pi.single μ 1) i) - 2 * (φ₁ x i - φ₂ x i))) ≤
        (δ₁ + δ₂) / G.spacing x ^ 2 := by
      rw [e]
      refine (vn_sub_le _ _).trans ?_
      rw [add_div]
      exact add_le_add a1 a2
    exact key

theorem Standing.delta_le_half {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) : δ ≤ 1 / 2 := by
  have h2 : 2 ≤ smallnessConst d := by
    unfold smallnessConst
    have := poincareConst_inv_nonneg St.pos
    have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hd this]
  have h := St.small
  have h0 := St.nonneg
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg δ)]

end Facts

/-! ### Block decay of the basic operators of the data -/

/-- The constant of `green_dec`. -/
noncomputable def cGreen (d L : ℕ) : ℝ :=
  13 * L / poincareConst d * (L : ℝ) ^ (((2 : ℤ) - 1).natAbs)

theorem cGreen_nonneg (d L : ℕ) : 0 ≤ cGreen d L := by
  unfold cGreen poincareConst
  positivity

theorem locKappa_le_half {d : ℕ} (hd : 0 < d) : locKappa d ≤ agmonRate d / 2 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he := agmonRate_pos hd
  unfold locKappa
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

namespace LocData

variable {d L N : ℕ} [NeZero L] (D : LocData d L N)

include D in
theorem hd : 0 < d := D.St.pos

theorem dec_Gh : Dec D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) Prod.fst D.Gh 1
    (agmonRate d / 2 - locKappa d) noTail (cGreen d L) :=
  Dec.lift (G := D.G) (cGreen_nonneg d L) noTail_nonneg
    (green_dec D.G D.St.pos D.St.mass D.St.weights D.St.alpha D.hϱ D.hlog (locKappa_le_half D.St.pos))

theorem dec_Gh' : Dec D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) Prod.fst D.Gh' 1
    (agmonRate d / 2 - locKappa d) noTail (cGreen d L) :=
  Dec.lift (G := D.G) (cGreen_nonneg d L) noTail_nonneg
    (green_dec D.G D.St'.pos D.St'.mass D.St'.weights D.St'.alpha D.hϱ D.hlog (locKappa_le_half D.St'.pos))

theorem dec_Ph {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) (id : D.G.Ω 1 → D.G.Ω 1) D.Ph 0 γ noTail
      (3 / 2 * Real.exp (γ * (4 * d))) :=
  fieldMul_dec (by norm_num) hγ fun x => D.St.field.bound x x.2

theorem dec_Ph' {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) (id : D.G.Ω 1 → D.G.Ω 1) D.Ph' 0 γ noTail
      (3 / 2 * Real.exp (γ * (4 * d))) :=
  fieldMul_dec (by norm_num) hγ fun x => D.St'.field.bound x x.2

theorem dec_Pht {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) D.Ph.transpose 0 γ
      noTail (3 / 2 * Real.exp (γ * (4 * d))) :=
  fieldMulT_dec (by norm_num) hγ fun x => D.St.field.bound x x.2

theorem dec_Mi : Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) (id : D.G.Ω 1 → D.G.Ω 1) D.Mm⁻¹ 0
    (agmonRate d - locKappa d) noTail (2 * Real.exp (4 * agmonRate d * d) * L) :=
  constraintM_inv_dec D.St D.hϱ D.hlog

theorem dec_Mi' : Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) (id : D.G.Ω 1 → D.G.Ω 1) D.Mm'⁻¹ 0
    (agmonRate d - locKappa d) noTail (2 * Real.exp (4 * agmonRate d * d) * L) :=
  constraintM_inv_dec D.St' D.hϱ D.hlog

theorem dec_KG : Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1)
    (D.K * D.Gh) 0 (agmonRate d - locKappa d) noTail
    (commDecConst d * D.δ * Real.exp (4 * agmonRate d * d) * L) :=
  GreenData.commK_green_dec D.St.greenData D.St.field.toIsSmoothField D.St.nonneg D.hϱ D.hlog

theorem Ks_eq : D.Ks = commK D.H' (restrictField D.G D.ψ) := by
  unfold Ks
  rw [D.H_eq, commK_add_diagonal]

theorem ψ_smooth : IsSmoothField D.G (D.δ + D.δ) D.ψ :=
  IsSmoothField.sub D.St.field.toIsSmoothField D.St'.field.toIsSmoothField

theorem dec_KsGh' : Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1)
    (D.Ks * D.Gh') 0 (agmonRate d - locKappa d) noTail
    (commDecConst d * (D.δ + D.δ) * Real.exp (4 * agmonRate d * d) * L) := by
  rw [D.Ks_eq]
  have h := GreenData.commK_green_dec D.St'.greenData D.ψ_smooth
    (add_nonneg D.St.nonneg D.St.nonneg) D.hϱ D.hlog
  exact h

theorem vn_ψ_le (x : D.G.Ω 1) : vn (restrictField D.G D.ψ x) ≤ 3 := by
  have h1 := D.St.field.bound x x.2
  have h2 := D.St'.field.bound x x.2
  have := vn_sub_le (D.φ x) (D.φ' x)
  have e : restrictField D.G D.ψ x = D.φ x - D.φ' x := rfl
  rw [e]; linarith

theorem dec_Ps {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) (id : D.G.Ω 1 → D.G.Ω 1) D.Ps 0 γ noTail
      (3 * Real.exp (γ * (4 * d))) :=
  fieldMul_dec (by norm_num) hγ D.vn_ψ_le

theorem dec_Pst {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) D.Pst 0 γ noTail
      (3 * Real.exp (γ * (4 * d))) :=
  fieldMulT_dec (by norm_num) hγ D.vn_ψ_le

theorem alpha_diff_le (x : D.G.Ω 1) :
    ‖(D.α - D.α') x‖ ≤ coerciveConst d *
      ((D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)) * D.G.spacing (x : Torus d (D.N₀ * L ^ D.k))) ^
        (-1 : ℤ)) := by
  have h1 := D.St.alpha x
  have h2 := D.St'.alpha x
  have hs : 0 < D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)) := by
    have := D.G.spacing_ge_one (x : Torus d (D.N₀ * L ^ D.k)); linarith
  rw [_root_.zpow_neg_one, Pi.sub_apply]
  refine (norm_sub_le _ _).trans ?_
  have e : coerciveConst d * (D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)) *
      D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)))⁻¹ =
      coerciveConst d / (2 * D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)) ^ 2) +
      coerciveConst d / (2 * D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)) ^ 2) := by
    field_simp; ring
  rw [e]
  exact add_le_add h1 h2

theorem dec_D0 {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) Prod.fst D.D0 (-1) γ noTail
      (coerciveConst d * Real.exp (γ * (4 * d))) := by
  have hc := (coerciveConst_pos D.St.pos).le
  exact Dec.lift (G := D.G) (by positivity) noTail_nonneg
    (diagonal_dec hc hγ D.alpha_diff_le)

theorem sigma_diff_le (x : D.G.Ω 1) :
    ‖∑ i, D.φ' x i * D.φ' x i - ∑ i, D.φ x i * D.φ x i‖ ≤
      1 * ((D.G.spacing (x : Torus d (D.N₀ * L ^ D.k)) *
        D.G.spacing (x : Torus d (D.N₀ * L ^ D.k))) ^ (0 : ℤ)) := by
  have h1 := D.St.field.sq x x.2
  have h2 := D.St'.field.sq x x.2
  have h3 := D.St.delta_le_half
  have e : ∑ i, D.φ' x i * D.φ' x i - ∑ i, D.φ x i * D.φ x i =
      (∑ i, D.φ' x i * D.φ' x i - 1) - (∑ i, D.φ x i * D.φ x i - 1) := by ring
  rw [e, zpow_zero]
  refine (norm_sub_le _ _).trans ?_
  linarith

theorem dec_Xa {γ : ℝ} (hγ : 0 ≤ γ) :
    Dec D.G (id : D.G.Ω 1 → D.G.Ω 1) id D.Xa 0 γ noTail (1 * Real.exp (γ * (4 * d))) :=
  diagonal_dec zero_le_one hγ D.sigma_diff_le

theorem out_D0 : OutNear D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) D.Z (2 * d) D.D0 := by
  refine OutNear.of_supp D.G fun g p hp => ?_
  unfold D0 at hp
  rw [liftOp_diagonal, Matrix.mulVec_diagonal] at hp
  by_contra hx
  apply hp
  simp [D.hZα p.1 hx]

theorem out_Ps : OutNear D.G (Prod.fst : D.G.Ω 1 × Fin N → D.G.Ω 1) D.Z (2 * d) D.Ps := by
  refine OutNear.of_supp D.G fun g p hp => ?_
  unfold Ps at hp
  rw [fieldMul_mulVec] at hp
  by_contra hx
  apply hp
  have : D.ψ (p.1 : Torus d (D.N₀ * L ^ D.k)) p.2 = 0 := by
    simp [ψ, D.hZφ p.1 hx]
  simp [restrictField, this]

theorem out_Pst : OutNear D.G (id : D.G.Ω 1 → D.G.Ω 1) D.Z (2 * d) D.Pst := by
  refine OutNear.of_supp D.G fun g x hp => ?_
  unfold Pst Ps at hp
  rw [fieldMul_transpose_mulVec] at hp
  by_contra hx
  apply hp
  refine Finset.sum_eq_zero fun i _ => ?_
  have : D.ψ (x : Torus d (D.N₀ * L ^ D.k)) i = 0 := by
    simp [ψ, D.hZφ x hx]
  simp [restrictField, this]

theorem out_Xa : OutNear D.G (id : D.G.Ω 1 → D.G.Ω 1) D.Z (2 * d) D.Xa := by
  refine OutNear.of_supp D.G fun g x hp => ?_
  unfold Xa at hp
  rw [Matrix.mulVec_diagonal] at hp
  by_contra hx
  apply hp
  have : D.φ' (x : Torus d (D.N₀ * L ^ D.k)) = D.φ x := (D.hZφ x hx).symm
  simp [this]

theorem out_KsGh' : OutNear D.G (id : D.G.Ω 1 → D.G.Ω 1) D.Z (2 * d + (2 * d + 1))
    (D.Ks * D.Gh') := by
  refine OutNear.mul_right D.G ?_ _
  exact commK_outNear D.G D.a D.ν D.α (ψ := D.ψ) (Z := D.Z) fun x hx => by
    funext j
    simp [ψ, D.hZφ x hx]

end LocData

/-! ### Assembly: uniform constants -/

/-- The common starting rate `e/2 - κ`. -/
noncomputable def baseRate (d : ℕ) : ℝ := agmonRate d / 2 - locKappa d

theorem baseRate_ge (hd : 0 < d) : agmonRate d / 2 - agmonRate d / 400 ≤ baseRate d := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he := agmonRate_pos hd
  unfold baseRate locKappa
  have : agmonRate d / (400 * d) ≤ agmonRate d / 400 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

theorem baseRate_nonneg (hd : 0 < d) : 0 ≤ baseRate d := by
  have := baseRate_ge hd
  have he := agmonRate_pos hd
  linarith

namespace LocData

variable {d L N : ℕ} [NeZero L] (D : LocData d L N)

/-- The site maps of vector and scalar fields. -/
abbrev sV : D.G.Ω 1 × Fin N → D.G.Ω 1 := Prod.fst
abbrev sS : D.G.Ω 1 → D.G.Ω 1 := id

theorem Nn_eq : D.Nn = D.Ph.transpose - D.K * D.Gh := rfl

/-- The block decay of the basic operators at the common rate. -/
structure BaseDec (D : LocData d L N) (C : ℝ) : Prop where
  Gh : Dec D.G D.sV D.sV D.Gh 1 (baseRate d) noTail C
  Gh' : Dec D.G D.sV D.sV D.Gh' 1 (baseRate d) noTail C
  Ph : Dec D.G D.sV D.sS D.Ph 0 (baseRate d) noTail C
  Ph' : Dec D.G D.sV D.sS D.Ph' 0 (baseRate d) noTail C
  Mi : Dec D.G D.sS D.sS D.Mm⁻¹ 0 (baseRate d) noTail C
  Mi' : Dec D.G D.sS D.sS D.Mm'⁻¹ 0 (baseRate d) noTail C
  Nn : Dec D.G D.sS D.sV D.Nn 0 (baseRate d) noTail C
  KG : Dec D.G D.sS D.sV (D.K * D.Gh) 0 (baseRate d) noTail C
  KsGh' : Dec D.G D.sS D.sV (D.Ks * D.Gh') 0 (baseRate d) noTail C
  Ps : Dec D.G D.sV D.sS D.Ps 0 (baseRate d) noTail C
  Pst : Dec D.G D.sS D.sV D.Pst 0 (baseRate d) noTail C
  D0 : Dec D.G D.sV D.sV D.D0 (-1) (baseRate d) noTail C
  Xa : Dec D.G D.sS D.sS D.Xa 0 (baseRate d) noTail C

end LocData

/-- **The basic operators have block decay with a constant depending only on `d, L`.** -/
theorem exists_baseDec (d L N : ℕ) [NeZero L] (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : LocData d L N, D.BaseDec C := by
  have he := agmonRate_pos hd
  have hγ := baseRate_nonneg hd
  set c1 := cGreen d L with hc1
  set c2 : ℝ := 3 / 2 * Real.exp (baseRate d * (4 * d)) with hc2
  set c3 : ℝ := 2 * Real.exp (4 * agmonRate d * d) * L with hc3
  set c4 : ℝ := commDecConst d * (1 / 2) * Real.exp (4 * agmonRate d * d) * L with hc4
  set c5 : ℝ := commDecConst d * 1 * Real.exp (4 * agmonRate d * d) * L with hc5
  set c6 : ℝ := coerciveConst d * Real.exp (baseRate d * (4 * d)) with hc6
  set c7 : ℝ := 3 * Real.exp (baseRate d * (4 * d)) with hc7
  set c8 : ℝ := 1 * Real.exp (baseRate d * (4 * d)) with hc8
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hn1 : 0 ≤ c1 := cGreen_nonneg d L
  have hn2 : 0 ≤ c2 := by positivity
  have hn3 : 0 ≤ c3 := by positivity
  have hcd := commDecConst_nonneg d
  have hn4 : 0 ≤ c4 := by positivity
  have hn5 : 0 ≤ c5 := by positivity
  have hcc := (coerciveConst_pos hd).le
  have hn6 : 0 ≤ c6 := by positivity
  have hn7 : 0 ≤ c7 := by positivity
  have hn8 : 0 ≤ c8 := by positivity
  refine ⟨c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8, by positivity, fun D => ?_⟩
  have hδ0 := D.St.nonneg
  have hδ1 := D.St.delta_le_half
  have hrate : baseRate d ≤ agmonRate d - locKappa d := by
    unfold baseRate; linarith
  have dec_KG : Dec D.G D.sS D.sV (D.K * D.Gh) 0 (baseRate d) noTail c4 := by
    refine (D.dec_KG.mono_rate noTail_nonneg (by positivity) hrate).mono_const noTail_nonneg ?_
    have : commDecConst d * D.δ ≤ commDecConst d * (1 / 2) :=
      mul_le_mul_of_nonneg_left hδ1 hcd
    rw [hc4]
    have hE := (Real.exp_pos (4 * agmonRate d * d)).le
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hE) hL0.le]
  have dec_KsGh' : Dec D.G D.sS D.sV (D.Ks * D.Gh') 0 (baseRate d) noTail c5 := by
    refine (D.dec_KsGh'.mono_rate noTail_nonneg (by positivity) hrate).mono_const noTail_nonneg ?_
    have : commDecConst d * (D.δ + D.δ) ≤ commDecConst d * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hcd
    rw [hc5]
    have hE := (Real.exp_pos (4 * agmonRate d * d)).le
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hE) hL0.le]
  have hT : ∀ y y' : Torus d (D.N₀ * L ^ D.k), 0 ≤ (noTail : Torus d (D.N₀ * L ^ D.k) →
      Torus d (D.N₀ * L ^ D.k) → ℝ) y y' := noTail_nonneg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, dec_KG.mono_const hT (by linarith), dec_KsGh'.mono_const hT
    (by linarith), ?_, ?_, ?_, ?_⟩
  · exact (D.dec_Gh).mono_const hT (by linarith)
  · exact (D.dec_Gh').mono_const hT (by linarith)
  · exact (D.dec_Ph hγ).mono_const hT (by linarith)
  · exact (D.dec_Ph' hγ).mono_const hT (by linarith)
  · exact (D.dec_Mi.mono_rate hT (by positivity) hrate).mono_const hT (by linarith)
  · exact (D.dec_Mi'.mono_rate hT (by positivity) hrate).mono_const hT (by linarith)
  · rw [D.Nn_eq]
    have h1 := (D.dec_Pht hγ).sub dec_KG
    exact h1.mono_const hT (by linarith)
  · exact (D.dec_Ps hγ).mono_const hT (by linarith)
  · exact (D.dec_Pst hγ).mono_const hT (by linarith)
  · exact (D.dec_D0 hγ).mono_const hT (by linarith)
  · exact (D.dec_Xa hγ).mono_const hT (by linarith)

/-! ### Constants by levels -/

/-- The factor `e^{2 γ_t c}` for the largest localization distance `c = 4 d + 1`. -/
noncomputable def locB (d : ℕ) : ℝ := Real.exp (2 * locTail d * (4 * d + 1))

/-- The counting constant, at least `1`. -/
noncomputable def locCC (d L : ℕ) : ℝ := max 1 (countConst d L (locTheta d))

/-- One step of the constant under a composition. -/
noncomputable def Mup (d L : ℕ) (M : ℝ) : ℝ := M * M * locB d * (L : ℝ) ^ 4 * locCC d L

/-- The constants after `n` compositions. -/
noncomputable def lvl (d L : ℕ) (M₀ : ℝ) : ℕ → ℝ
  | 0 => M₀
  | n + 1 => Mup d L (lvl d L M₀ n)

section Lvl

variable {d L : ℕ} [NeZero L]

theorem locB_ge_one (d : ℕ) : 1 ≤ locB d := by
  unfold locB locTail agmonRate poincareConst
  exact Real.one_le_exp (by positivity)

theorem one_le_locCC (d L : ℕ) : 1 ≤ locCC d L := le_max_left _ _

theorem one_le_L : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)

theorem Mup_mono {M M' : ℝ} (h : M ≤ M') (h0 : 0 ≤ M) : Mup d L M ≤ Mup d L M' := by
  unfold Mup
  have hB := locB_ge_one d
  have hC := one_le_locCC d L
  have hL : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ one_le_L
  have h1 : M * M ≤ M' * M' := mul_le_mul h h h0 (h0.trans h)
  have h2 : 0 ≤ locB d * (L : ℝ) ^ 4 * locCC d L :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem le_Mup {M : ℝ} (h : 1 ≤ M) : M ≤ Mup d L M := by
  unfold Mup
  have hB := locB_ge_one d
  have hC := one_le_locCC d L
  have hL : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ one_le_L
  have h1 : 1 ≤ locB d * (L : ℝ) ^ 4 * locCC d L := by
    have := one_le_mul_of_one_le_of_one_le hB hL
    exact one_le_mul_of_one_le_of_one_le this hC
  nlinarith [mul_le_mul h h (by norm_num) (by linarith)]

theorem one_le_lvl {M₀ : ℝ} (h : 1 ≤ M₀) (n : ℕ) : 1 ≤ lvl d L M₀ n := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.trans (le_Mup ih)

theorem lvl_mono {M₀ : ℝ} (h : 1 ≤ M₀) {m n : ℕ} (hmn : m ≤ n) : lvl d L M₀ m ≤ lvl d L M₀ n := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (le_Mup (one_le_lvl h _))

end Lvl

section LvlDec

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]

theorem cmpC_le_Mup {C B : ℝ} {μ : ℕ} (hC : 0 ≤ C) (hB0 : 0 ≤ B) (hB : B ≤ locB d)
    (hμ : μ ≤ 4) : cmpC d L (locTheta d) C C B μ ≤ Mup d L C := by
  unfold cmpC Mup
  have hL : (1 : ℝ) ≤ L := one_le_L
  have hLμ : (L : ℝ) ^ μ ≤ (L : ℝ) ^ 4 := pow_le_pow_right₀ hL hμ
  have hcc : countConst d L (locTheta d) ≤ locCC d L := le_max_right _ _
  have hcc0 := countConst_nonneg d L (locTheta d)
  have h1 : C * C * B * (L : ℝ) ^ μ ≤ C * C * locB d * (L : ℝ) ^ 4 := by
    have hCC : 0 ≤ C * C := mul_nonneg hC hC
    have hLp : 0 ≤ (L : ℝ) ^ μ := by positivity
    have hLp4 : 0 ≤ (L : ℝ) ^ 4 := by positivity
    have hb : 0 ≤ locB d := by have := locB_ge_one d; linarith
    calc C * C * B * (L : ℝ) ^ μ ≤ C * C * locB d * (L : ℝ) ^ μ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hCC) hLp
      _ ≤ _ := mul_le_mul_of_nonneg_left hLμ (mul_nonneg hCC hb)
  have h2 : 0 ≤ C * C * B * (L : ℝ) ^ μ := by positivity
  calc C * C * B * (L : ℝ) ^ μ * countConst d L (locTheta d)
      ≤ C * C * locB d * (L : ℝ) ^ 4 * countConst d L (locTheta d) := by gcongr
    _ ≤ _ := by
        have : 0 ≤ C * C * locB d * (L : ℝ) ^ 4 := by
          have := locB_ge_one d; positivity
        exact mul_le_mul_of_nonneg_left hcc this

theorem Dec.mul_lvl {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γT γS M₀ : ℝ} {n : ℕ}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1)) (hM₀ : 1 ≤ M₀)
    (hμ : w.natAbs + w'.natAbs ≤ 4) (hγ : agmonRate d / 50 ≤ γ) (hT : γ ≤ γT) (hS : γ ≤ γS)
    (hTd : Dec G s₁ s₂ T w γT noTail (lvl d L M₀ n))
    (hSd : Dec G s₂ s₃ S w' γS noTail (lvl d L M₀ n)) :
    Dec G s₁ s₃ (T * S) (w + w') (γ - agmonRate d / 50) noTail (lvl d L M₀ (n + 1)) := by
  have h0 : 0 ≤ lvl d L M₀ n := by have := one_le_lvl (d := d) (L := L) hM₀ n; linarith
  have := Dec.mul_std hd hϱ hlog hμ hγ hT hS h0 h0 hTd hSd
  exact this.mono_const noTail_nonneg (cmpC_le_Mup h0 zero_le_one (locB_ge_one d) hμ)

theorem Dec.mul_out_lvl {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γT γS M₀ c : ℝ} {n : ℕ}
    {Z : Finset (G.Ω 1)}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1)) (hM₀ : 1 ≤ M₀)
    (hμ : w.natAbs + w'.natAbs ≤ 4) (hγ : agmonRate d / 8 ≤ γ) (hT : γ ≤ γT) (hS : γ ≤ γS)
    (hc : 0 ≤ c) (hc' : c ≤ 4 * d + 1)
    (hTd : Dec G s₁ s₂ T w γT noTail (lvl d L M₀ n))
    (hSd : Dec G s₂ s₃ S w' γS noTail (lvl d L M₀ n)) (hE : OutNear G s₂ Z c S) :
    Dec G s₁ s₃ (T * S) (w + w') (γ - agmonRate d / 8) (tailZ G (locTail d) Z)
      (lvl d L M₀ (n + 1)) := by
  have h0 : 0 ≤ lvl d L M₀ n := by have := one_le_lvl (d := d) (L := L) hM₀ n; linarith
  have := Dec.mul_out hd hϱ hlog hμ hγ hT hS h0 h0 hc hTd hSd hE
  refine this.mono_const (tailZ_nonneg G _ Z) ?_
  have hγt : 0 ≤ locTail d := by unfold locTail agmonRate poincareConst; positivity
  have hB : Real.exp (2 * locTail d * c) ≤ locB d :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hc' (by positivity))
  exact cmpC_le_Mup h0 (Real.exp_pos _).le hB hμ

theorem Dec.mul_tail_lvl {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γT γS M₀ : ℝ} {n : ℕ}
    {Z : Finset (G.Ω 1)}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1)) (hM₀ : 1 ≤ M₀)
    (hμ : w.natAbs + w'.natAbs ≤ 4) (hγ : agmonRate d / 8 ≤ γ) (hT : γ ≤ γT) (hS : γ ≤ γS)
    (hTd : Dec G s₁ s₂ T w γT (tailZ G (locTail d) Z) (lvl d L M₀ n))
    (hSd : Dec G s₂ s₃ S w' γS noTail (lvl d L M₀ n)) :
    Dec G s₁ s₃ (T * S) (w + w') (γ - agmonRate d / 8) (tailZ G (locTail d) Z)
      (lvl d L M₀ (n + 1)) := by
  have h0 : 0 ≤ lvl d L M₀ n := by have := one_le_lvl (d := d) (L := L) hM₀ n; linarith
  have := Dec.mul_tail hd hϱ hlog hμ hγ hT hS h0 h0 hTd hSd
  exact this.mono_const (tailZ_nonneg G _ Z) (cmpC_le_Mup h0 zero_le_one (locB_ge_one d) hμ)

/-- **The chain `(P E) Q` with the localized factor `E` in the middle.** -/
theorem Dec.chain_lvl {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {ι₄ : Type*} [Fintype ι₄] {s₄ : ι₄ → G.Ω 1}
    {P : Matrix ι₁ ι₂ ℂ} {E : Matrix ι₂ ι₃ ℂ} {Q : Matrix ι₃ ι₄ ℂ} {w₁ w₂ w₃ : ℤ}
    {γ M₀ c : ℝ} {n : ℕ} {Z : Finset (G.Ω 1)}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1)) (hM₀ : 1 ≤ M₀)
    (hμ₁ : w₁.natAbs + w₂.natAbs ≤ 4) (hμ₂ : (w₁ + w₂).natAbs + w₃.natAbs ≤ 4)
    (hγ : agmonRate d / 4 ≤ γ) (hc : 0 ≤ c) (hc' : c ≤ 4 * d + 1)
    (hP : Dec G s₁ s₂ P w₁ γ noTail (lvl d L M₀ n))
    (hE : Dec G s₂ s₃ E w₂ γ noTail (lvl d L M₀ n)) (hEo : OutNear G s₂ Z c E)
    (hQ : Dec G s₃ s₄ Q w₃ γ noTail (lvl d L M₀ n)) :
    Dec G s₁ s₄ (P * E * Q) (w₁ + w₂ + w₃) (γ - agmonRate d / 8 - agmonRate d / 8)
      (tailZ G (locTail d) Z) (lvl d L M₀ (n + 2)) := by
  have he := agmonRate_pos hd
  have h0 := one_le_lvl (d := d) (L := L) hM₀ n
  have h1 := Dec.mul_out_lvl hd hϱ hlog hM₀ hμ₁ (γ := γ) (by linarith) le_rfl le_rfl hc hc' hP hE hEo
  have hQ' : Dec G s₃ s₄ Q w₃ (γ - agmonRate d / 8) noTail (lvl d L M₀ (n + 1)) :=
    (hQ.mono_rate noTail_nonneg (by linarith) (by linarith)).mono_const noTail_nonneg
      (lvl_mono hM₀ (Nat.le_succ n))
  exact Dec.mul_tail_lvl hd hϱ hlog hM₀ hμ₂ (γ := γ - agmonRate d / 8) (by linarith) le_rfl le_rfl
    h1 hQ'

end LvlDec


/-! ### The terms of `Π - Π′` -/

section Terms

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Adjust weight, rate, and level of a `Dec` fact. -/
theorem Dec.adj {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w w' : ℤ} {γ γ' M₀ : ℝ}
    {m n : ℕ} {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ}
    (hM₀ : 1 ≤ M₀) (hτ : ∀ y y', 0 ≤ τ y y')
    (h : Dec G s₁ s₂ T w γ τ (lvl d L M₀ m)) (hw : w = w') (hγ : γ' ≤ γ) (hmn : m ≤ n) :
    Dec G s₁ s₂ T w' γ' τ (lvl d L M₀ n) := by
  subst hw
  have h0 : 0 ≤ lvl d L M₀ m := by have := one_le_lvl (d := d) (L := L) hM₀ m; linarith
  exact (h.mono_rate hτ h0 hγ).mono_const hτ (lvl_mono hM₀ hmn)

end Terms

namespace LocData

variable {d L N : ℕ} [NeZero L] (D : LocData d L N)

theorem Pi_sub_peq : D.Pi - D.Pi' =
    -((D.Gh * D.D0) * (D.Gh' * D.Ph * D.Mm⁻¹ * D.Nn))
    + (D.Gh' * D.Ps) * (D.Mm⁻¹ * D.Nn)
    + (D.Gh' * D.Ph' * D.Mm⁻¹ * D.Xa) * (D.Mm'⁻¹ * D.Nn)
    + (D.Gh' * D.Ph' * D.Mm⁻¹ * (D.Ks * D.Gh')) * (D.Ph' * D.Mm'⁻¹ * D.Nn)
    - (D.Gh' * D.Ph' * D.Mm⁻¹ * (D.K * D.Gh) * D.D0) * (D.Gh' * D.Ph' * D.Mm'⁻¹ * D.Nn)
    + (D.Gh' * D.Ph' * D.Mm⁻¹ * (D.K * D.Gh) * D.Ps) * (D.Mm'⁻¹ * D.Nn)
    + (D.Gh' * D.Ph' * D.Mm'⁻¹) * D.Pst
    + (D.Gh' * D.Ph' * D.Mm'⁻¹ * (D.K * D.Gh) * D.D0) * D.Gh'
    - (D.Gh' * D.Ph' * D.Mm'⁻¹) * (D.Ks * D.Gh') := by
  rw [D.Pi_sub]
  simp only [Matrix.mul_assoc]

theorem Dec.to_chain {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {G : GeneratingSet d L N₀ k ϱ}
    {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {w : ℤ} {ρ M₀ : ℝ} {m : ℕ}
    (hM₀ : 1 ≤ M₀) (h : Dec G s₁ s₂ T w ρ noTail (lvl d L M₀ m)) (hm : m ≤ 3)
    (hρ : agmonRate d / 3 ≤ ρ) : Dec G s₁ s₂ T w (agmonRate d / 3) noTail (lvl d L M₀ 3) :=
  h.adj hM₀ noTail_nonneg rfl hρ hm

/-- **The telescoped difference has the tails.** -/
theorem dec_Pi_sub {M₀ : ℝ} (hM₀ : 1 ≤ M₀) (hB : D.BaseDec M₀) :
    Dec D.G D.sV D.sV (D.Pi - D.Pi') 1 (agmonRate d / 12) (tailZ D.G (locTail d) D.Z)
      (9 * lvl d L M₀ 5) := by
  have hd := D.St.pos
  have he := agmonRate_pos hd
  have hb := baseRate_ge hd
  have hϱ := D.hϱ
  have hlog := D.hlog
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set e := agmonRate d with he_def
  set γb := baseRate d with hγb
  have hGh := hB.Gh
  have hGh' := hB.Gh'
  have hPh := hB.Ph
  have hPh' := hB.Ph'
  have hMi := hB.Mi
  have hMi' := hB.Mi'
  have hNn := hB.Nn
  have hKG := hB.KG
  have hKs := hB.KsGh'
  have hPs := hB.Ps
  have hPst := hB.Pst
  have hD0 := hB.D0
  have hXa := hB.Xa
  have hT := (noTail_nonneg : ∀ y y' : Torus d (D.N₀ * L ^ D.k), 0 ≤ (noTail :
      Torus d (D.N₀ * L ^ D.k) → Torus d (D.N₀ * L ^ D.k) → ℝ) y y')
  have e50 : e / 50 ≤ γb - 0 := by linarith
  -- level 1
  have A1 : Dec D.G D.sV D.sS (D.Gh' * D.Ph') 1 (γb - 1 * (e / 50)) noTail (lvl d L M₀ 1) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb) (by linarith) le_rfl le_rfl hGh' hPh').adj
      hM₀ hT (by norm_num) (by linarith) le_rfl
  have A1u : Dec D.G D.sV D.sS (D.Gh' * D.Ph) 1 (γb - 1 * (e / 50)) noTail (lvl d L M₀ 1) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb) (by linarith) le_rfl le_rfl hGh' hPh).adj
      hM₀ hT (by norm_num) (by linarith) le_rfl
  have B1 : Dec D.G D.sS D.sV (D.Mm⁻¹ * D.Nn) 0 (γb - 1 * (e / 50)) noTail (lvl d L M₀ 1) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb) (by linarith) le_rfl le_rfl hMi hNn).adj
      hM₀ hT (by norm_num) (by linarith) le_rfl
  have B1' : Dec D.G D.sS D.sV (D.Mm'⁻¹ * D.Nn) 0 (γb - 1 * (e / 50)) noTail (lvl d L M₀ 1) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb) (by linarith) le_rfl le_rfl hMi' hNn).adj
      hM₀ hT (by norm_num) (by linarith) le_rfl
  have B2 : Dec D.G D.sV D.sS (D.Ph' * D.Mm'⁻¹) 0 (γb - 1 * (e / 50)) noTail (lvl d L M₀ 1) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb) (by linarith) le_rfl le_rfl hPh' hMi').adj
      hM₀ hT (by norm_num) (by linarith) le_rfl
  -- level 2
  have A2 : Dec D.G D.sV D.sS (D.Gh' * D.Ph' * D.Mm⁻¹) 1 (γb - 2 * (e / 50)) noTail
      (lvl d L M₀ 2) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 1 * (e / 50)) (by linarith) le_rfl
      (by linarith) A1 (hMi.adj hM₀ hT rfl (γ' := γb - 1 * (e / 50)) (by linarith) (Nat.zero_le 1))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have A2' : Dec D.G D.sV D.sS (D.Gh' * D.Ph' * D.Mm'⁻¹) 1 (γb - 2 * (e / 50)) noTail
      (lvl d L M₀ 2) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 1 * (e / 50)) (by linarith) le_rfl
      (by linarith) A1 (hMi'.adj hM₀ hT rfl (γ' := γb - 1 * (e / 50)) (by linarith) (Nat.zero_le 1))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have A2u : Dec D.G D.sV D.sS (D.Gh' * D.Ph * D.Mm⁻¹) 1 (γb - 2 * (e / 50)) noTail
      (lvl d L M₀ 2) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 1 * (e / 50)) (by linarith) le_rfl
      (by linarith) A1u (hMi.adj hM₀ hT rfl (γ' := γb - 1 * (e / 50)) (by linarith) (Nat.zero_le 1))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have B3 : Dec D.G D.sV D.sV (D.Ph' * D.Mm'⁻¹ * D.Nn) 0 (γb - 2 * (e / 50)) noTail
      (lvl d L M₀ 2) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 1 * (e / 50)) (by linarith) le_rfl
      (by linarith) B2 (hNn.adj hM₀ hT rfl (γ' := γb - 1 * (e / 50)) (by linarith) (Nat.zero_le 1))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  -- level 3
  have A3 : Dec D.G D.sV D.sV (D.Gh' * D.Ph' * D.Mm⁻¹ * (D.K * D.Gh)) 1 (γb - 3 * (e / 50))
      noTail (lvl d L M₀ 3) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 2 * (e / 50)) (by linarith) le_rfl
      (by linarith) A2 (hKG.adj hM₀ hT rfl (γ' := γb - 2 * (e / 50)) (by linarith) (Nat.zero_le 2))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have A3' : Dec D.G D.sV D.sV (D.Gh' * D.Ph' * D.Mm'⁻¹ * (D.K * D.Gh)) 1 (γb - 3 * (e / 50))
      noTail (lvl d L M₀ 3) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 2 * (e / 50)) (by linarith) le_rfl
      (by linarith) A2' (hKG.adj hM₀ hT rfl (γ' := γb - 2 * (e / 50)) (by linarith) (Nat.zero_le 2))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have Q5 : Dec D.G D.sV D.sV (D.Gh' * D.Ph' * D.Mm'⁻¹ * D.Nn) 1 (γb - 3 * (e / 50)) noTail
      (lvl d L M₀ 3) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 2 * (e / 50)) (by linarith) le_rfl
      (by linarith) A2' (hNn.adj hM₀ hT rfl (γ' := γb - 2 * (e / 50)) (by linarith) (Nat.zero_le 2))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have Q1 : Dec D.G D.sV D.sV (D.Gh' * D.Ph * D.Mm⁻¹ * D.Nn) 1 (γb - 3 * (e / 50)) noTail
      (lvl d L M₀ 3) :=
    (Dec.mul_lvl hd hϱ hlog hM₀ (by norm_num) (γ := γb - 2 * (e / 50)) (by linarith) le_rfl
      (by linarith) A2u (hNn.adj hM₀ hT rfl (γ' := γb - 2 * (e / 50)) (by linarith) (Nat.zero_le 2))).adj hM₀ hT
      (by norm_num) (by linarith) le_rfl
  have hc0 : (0 : ℝ) ≤ 2 * d := by positivity
  have hc1 : (2 : ℝ) * d ≤ 4 * d + 1 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hc2 : (0 : ℝ) ≤ 2 * d + (2 * d + 1) := by positivity
  have hc3 : (2 : ℝ) * d + (2 * d + 1) ≤ 4 * d + 1 := by linarith
  have hch : e / 4 ≤ e / 3 := by linarith
  have r3 : e / 3 ≤ γb - 3 * (e / 50) := by linarith
  have r2 : e / 3 ≤ γb - 2 * (e / 50) := by linarith
  have r1 : e / 3 ≤ γb - 1 * (e / 50) := by linarith
  have r0 : e / 3 ≤ γb := by linarith
  -- the nine terms, all with rate `e/12`, level `5`, weight `1`
  have t1 := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch hc0 hc1
    (Dec.to_chain hM₀ hGh (Nat.zero_le 3) r0) (Dec.to_chain hM₀ hD0 (Nat.zero_le 3) r0) D.out_D0
    (Dec.to_chain hM₀ Q1 (by norm_num) r3)
  have t2 := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch hc0 hc1
    (Dec.to_chain hM₀ hGh' (Nat.zero_le 3) r0) (Dec.to_chain hM₀ hPs (Nat.zero_le 3) r0) D.out_Ps
    (Dec.to_chain hM₀ B1 (by norm_num) r1)
  have t3a := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch hc0 hc1
    (Dec.to_chain hM₀ A2 (by norm_num) r2) (Dec.to_chain hM₀ hXa (Nat.zero_le 3) r0) D.out_Xa
    (Dec.to_chain hM₀ B1' (by norm_num) r1)
  have t3b := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch
    (by positivity) hc3 (Dec.to_chain hM₀ A2 (by norm_num) r2)
    (Dec.to_chain hM₀ hKs (Nat.zero_le 3) r0) D.out_KsGh' (Dec.to_chain hM₀ B3 (by norm_num) r2)
  have t3c := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch hc0 hc1
    (Dec.to_chain hM₀ A3 (by norm_num) r3) (Dec.to_chain hM₀ hD0 (Nat.zero_le 3) r0) D.out_D0
    (Dec.to_chain hM₀ Q5 (by norm_num) r3)
  have t3d := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch hc0 hc1
    (Dec.to_chain hM₀ A3 (by norm_num) r3) (Dec.to_chain hM₀ hPs (Nat.zero_le 3) r0) D.out_Ps
    (Dec.to_chain hM₀ B1' (by norm_num) r1)
  have t4b := Dec.chain_lvl hd hϱ hlog hM₀ (by norm_num) (by norm_num) (γ := e / 3) hch hc0 hc1
    (Dec.to_chain hM₀ A3' (by norm_num) r3) (Dec.to_chain hM₀ hD0 (Nat.zero_le 3) r0) D.out_D0
    (Dec.to_chain hM₀ hGh' (Nat.zero_le 3) r0)
  have t4a := Dec.mul_out_lvl hd hϱ hlog hM₀ (by norm_num) (γ := e / 3) (by linarith) le_rfl le_rfl
    hc0 hc1 (Dec.to_chain hM₀ A2' (by norm_num) r2) (Dec.to_chain hM₀ hPst (Nat.zero_le 3) r0)
    D.out_Pst
  have t4c := Dec.mul_out_lvl hd hϱ hlog hM₀ (by norm_num) (γ := e / 3) (by linarith) le_rfl le_rfl
    (by positivity) hc3 (Dec.to_chain hM₀ A2' (by norm_num) r2)
    (Dec.to_chain hM₀ hKs (Nat.zero_le 3) r0) D.out_KsGh'
  have tz := (tailZ_nonneg D.G (locTail d) D.Z)
  rw [D.Pi_sub_peq]
  have a1 := t1.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a2 := t2.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a3 := t3a.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a4 := t3b.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a5 := t3c.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a6 := t3d.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a7 := t4a.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a8 := t4b.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have a9 := t4c.adj hM₀ tz (w' := 1) (by norm_num) (γ' := e / 12) (by linarith) (n := 5) (by norm_num)
  have fin := ((((((((a1.neg.add a2).add a3).add a4).sub a5).add a6).add a7).add a8).sub a9)
  have h5 : 0 ≤ lvl d L M₀ 5 := by have := one_le_lvl (d := d) (L := L) hM₀ 5; linarith
  exact fin.mono_const tz (by linarith)

end LocData

end Balaban.Multiscale
