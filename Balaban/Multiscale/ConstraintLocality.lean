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

end Balaban.Multiscale
