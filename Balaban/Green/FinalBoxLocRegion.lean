/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocConj

/-!
# The block-diagonal extension of a principal block (A6-3, `D_{B,Ω}`, shared)

For a region `Ω` (a finite set of sites) and a matrix `U` put
`regOp Ω U g = P_Ω U P_Ω + g (1 - P_Ω)`: the principal block of `U` on `Ω`, extended by `g` on the
complement.  It is block diagonal for `Ω`, `Ωᶜ`; its `Ω`-block is `U|_Ω` (`restrictOp U Ω`).

* `regionConj Ω`: the twist `matConj id (±1)` (`+1` on `Ω`, `-1` off `Ω`); a matrix is block
  diagonal iff it is fixed (`eq_zero_of_matConj_id_eq`); `regionConj_regOp`;
* `regOp_univ` (`Ω = univ` gives `U`), `conjM_regOp`, `isCoercive_regOp` (gap `γ` for `γ ≤ g`),
  `norm_regOp_apply_le` (the entry decay of `U` for `0 ≤ g ≤ A`), `cutOpHyp_regOp`;
* `boxCutU_regOp_eq_zero`: the cut family of `regOp Ω U g` is block diagonal for every parameter
  (the twist commutes with the whole construction, `matConj_boxCutU`);
* `submatrix_mul_submatrix_inv`: the block of the inverse of a matrix whose rows in a block do not
  read the complement is the inverse of the block; `inv_regOp_submatrix` (resolvents),
  `sqrtMat_regOp_submatrix` (`(sqrtMat (regOp Ω U g))|_Ω = sqrtMat (U|_Ω)`).
-/

@[expose] public section

open Matrix MeasureTheory Set

namespace Balaban.Green

section Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign `+1` on `Ω` and `-1` off `Ω`. -/
def regionSign (Ω : Finset ι) (x : ι) : ℂ := if x ∈ Ω then 1 else -1

omit [Fintype ι] in
theorem regionSign_mul_self (Ω : Finset ι) (x : ι) : regionSign Ω x * regionSign Ω x = 1 := by
  unfold regionSign; split_ifs <;> norm_num

/-- **The region twist** `M ↦ σ M σ`, `σ = +1` on `Ω` and `-1` off `Ω`: the block-diagonal matrices
for `Ω`, `Ωᶜ` are its fixed points. -/
noncomputable abbrev regionConj (Ω : Finset ι) : Matrix ι ι ℂ →+* Matrix ι ι ℂ :=
  matConj (RingHom.id ℂ) (regionSign Ω) (regionSign_mul_self Ω)

/-- The entries of a matrix fixed by a twist `matConj id σ` vanish where `σ x σ y = -1`. -/
theorem eq_zero_of_matConj_id_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {σ : κ → ℂ}
    {hσ : ∀ x, σ x * σ x = 1} {A : Matrix κ κ ℂ} (hA : matConj (RingHom.id ℂ) σ hσ A = A)
    {x y : κ} (hxy : σ x * σ y = -1) : A x y = 0 := by
  have h := congrFun (congrFun hA x) y
  rw [matConj_apply, RingHom.id_apply] at h
  have e : σ x * A x y * σ y = (σ x * σ y) * A x y := by ring
  rw [e, hxy] at h
  linear_combination (-1 / 2 : ℂ) * h

end Sign

section RegOp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The block-diagonal extension of the principal block of `U` on `Ω`**:
`P_Ω U P_Ω + g (1 - P_Ω)`. -/
noncomputable def regOp (Ω : Finset ι) (U : Matrix ι ι ℂ) (g : ℝ) : Matrix ι ι ℂ :=
  boxP Ω * U * boxP Ω + (g : ℂ) • (1 - boxP Ω)

theorem regOp_apply (Ω : Finset ι) (U : Matrix ι ι ℂ) (g : ℝ) (x y : ι) :
    regOp Ω U g x y =
      (if x ∈ Ω ∧ y ∈ Ω then U x y else 0) + (if x = y ∧ x ∉ Ω then (g : ℂ) else 0) := by
  unfold regOp boxP
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hx : x ∈ Ω <;> by_cases hy : y ∈ Ω <;> by_cases hxy : x = y <;> simp_all

theorem regOp_univ (U : Matrix ι ι ℂ) (g : ℝ) : regOp Finset.univ U g = U := by
  ext x y
  rw [regOp_apply]
  simp

theorem regionConj_regOp (Ω : Finset ι) (U : Matrix ι ι ℂ) (g : ℝ) :
    regionConj Ω (regOp Ω U g) = regOp Ω U g := by
  ext x y
  rw [matConj_apply, RingHom.id_apply, regOp_apply]
  unfold regionSign
  by_cases hx : x ∈ Ω <;> by_cases hy : y ∈ Ω <;> by_cases hxy : x = y <;> simp_all

theorem conjM_regOp {U : Matrix ι ι ℂ} (hU : conjM U = U) (Ω : Finset ι) (g : ℝ) :
    conjM (regOp Ω U g) = regOp Ω U g := by
  unfold regOp
  rw [map_add, map_mul, map_mul, conjM_boxP, hU, conjM_ofReal_smul, map_sub, map_one, conjM_boxP]

/-- **The gap of the extension**: `U` coercive with gap `γ ≤ g` gives `regOp Ω U g` coercive with
gap `γ`. -/
theorem isCoercive_regOp {U : Matrix ι ι ℂ} {γ : ℝ} (hU : IsCoercive U γ) {g : ℝ} (hg : γ ≤ g)
    (Ω : Finset ι) : IsCoercive (regOp Ω U g) γ := by
  intro v
  set w : ι → ℂ := fun x => if x ∈ Ω then v x else 0 with hw
  have hPv : boxP Ω *ᵥ v = w := by
    funext x; simp [boxP, Matrix.mulVec_diagonal, hw]
  have hQv : (1 - boxP Ω) *ᵥ v = fun x => if x ∈ Ω then 0 else v x := by
    funext x; simp [boxP, Matrix.sub_mulVec, Matrix.mulVec_diagonal]; split_ifs <;> simp
  have hmv : regOp Ω U g *ᵥ v =
      boxP Ω *ᵥ (U *ᵥ w) + (g : ℂ) • fun x => if x ∈ Ω then 0 else v x := by
    unfold regOp
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv,
      Matrix.smul_mulVec, hQv]
  have hsplit : reQuad (regOp Ω U g) v =
      reQuad U w + g * ∑ x, (if x ∈ Ω then 0 else ‖v x‖ ^ 2) := by
    unfold reQuad
    rw [hmv]
    have e : ∀ x, star (v x) * (boxP Ω *ᵥ (U *ᵥ w) + (g : ℂ) • fun x => if x ∈ Ω then 0 else v x) x =
        star (w x) * (U *ᵥ w) x + (g : ℂ) * ((if x ∈ Ω then 0 else ‖v x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, boxP, Matrix.mulVec_diagonal, hw]
      by_cases hx : x ∈ Ω
      · simp [hx]
      · have hn : ((‖v x‖ ^ 2 : ℝ) : ℂ) = star (v x) * v x := by
          rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
        simp only [hx, ↓reduceIte, star_zero, zero_mul, zero_add, hn]
        ring
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Complex.add_re,
      ← Finset.mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnorm : sqNorm v = sqNorm w + ∑ x, (if x ∈ Ω then 0 else ‖v x‖ ^ 2) := by
    unfold sqNorm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ Ω <;> simp [hw, hx]
  have hS : 0 ≤ ∑ x, (if x ∈ Ω then 0 else ‖v x‖ ^ 2) :=
    Finset.sum_nonneg fun x _ => by split_ifs <;> positivity
  rw [hsplit, hnorm, mul_add]
  have := hU w
  nlinarith [mul_le_mul_of_nonneg_right hg hS]

/-- The entries of the complex Hessian `a P_h + U (1 - P_h)`. -/
theorem hessC_apply {N : ℕ} (a : ℂ) (U : Matrix ι ι ℂ) (h : Fin N → ℂ) (x y : ι) (i j : Fin N) :
    hessC N a U h (x, i) (y, j) =
      a * (if x = y then spinProj h i j else 0) +
        U x y * ((if i = j then 1 else 0) - spinProj h i j) := by
  unfold hessC
  rw [Matrix.add_apply, Matrix.smul_apply, liftOp_mul_one_sub_projHC_apply, projHC_apply,
    smul_eq_mul]
  rfl

/-- A matrix whose rows in the range of `e` do not read the complement: the block of a product is
the product of the blocks. -/
theorem submatrix_mul_of_rows {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ → ι)
    (he : Function.Injective e) {A : Matrix ι ι ℂ} (B : Matrix ι ι ℂ)
    (hzero : ∀ a z, z ∉ Set.range e → A (e a) z = 0) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_image (f := fun z => A (e a) z * B z (e b)) (s := Finset.univ)
    (g := e) fun x _ y _ hxy => he hxy]
  refine (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_).symm
  have : z ∉ Set.range e := fun ⟨c, hc⟩ => hz (Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩)
  rw [hzero a z this, zero_mul]

/-- **The block of a mismatch** (algebra): if the rows in the range of `e` of `Wᵀ` and of `D₀` do
not read the complement, `(Wᵀ D₀ W - 1)|_e = (W|_e)ᵀ (D₀|_e) (W|_e) - 1`. -/
theorem mismatch_submatrix_of_block {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ → ι)
    (he : Function.Injective e) (W D₀ : Matrix ι ι ℂ)
    (hWT : ∀ a z, z ∉ Set.range e → W z (e a) = 0)
    (hD : ∀ a z, z ∉ Set.range e → D₀ (e a) z = 0) :
    (Wᵀ * D₀ * W - 1).submatrix e e =
      (W.submatrix e e)ᵀ * D₀.submatrix e e * W.submatrix e e - 1 := by
  have hWD : ∀ a z, z ∉ Set.range e → (Wᵀ * D₀) (e a) z = 0 := by
    intro a z hz
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ Set.range e
    · obtain ⟨c, rfl⟩ := hy
      rw [hD c z hz, mul_zero]
    · rw [Matrix.transpose_apply, hWT a y hy, zero_mul]
  have h1 : (Wᵀ * D₀ * W - 1).submatrix e e = (Wᵀ * D₀ * W).submatrix e e - 1 := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, he.eq_iff]
  rw [h1, submatrix_mul_of_rows e he W hWD,
    submatrix_mul_of_rows e he D₀ (fun a z hz => by rw [Matrix.transpose_apply]; exact hWT a z hz)]
  rfl

/-- A matrix whose rows in the range of `e` do not read the complement: the block of its inverse is
a right inverse of its block. -/
theorem submatrix_mul_submatrix_inv {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ → ι)
    (he : Function.Injective e) {W : Matrix ι ι ℂ} (hW : IsUnit W)
    (hzero : ∀ a z, z ∉ Set.range e → W (e a) z = 0) :
    W.submatrix e e * (W⁻¹).submatrix e e = 1 := by
  ext a b
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv W ((Matrix.isUnit_iff_isUnit_det W).1 hW))
    (e a)) (e b)
  rw [Matrix.mul_apply] at h ⊢
  simp only [Matrix.submatrix_apply]
  have hsum : ∑ z, W (e a) z * W⁻¹ z (e b) = ∑ c, W (e a) (e c) * W⁻¹ (e c) (e b) := by
    rw [← Finset.sum_image (f := fun z => W (e a) z * W⁻¹ z (e b)) (s := Finset.univ)
      (g := e) fun x _ y _ hxy => he hxy]
    refine (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => ?_).symm
    have : z ∉ Set.range e := fun ⟨c, hc⟩ => hz (Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩)
    rw [hzero a z this, zero_mul]
  rw [← hsum, h, Matrix.one_apply, Matrix.one_apply]
  simp only [he.eq_iff]

end RegOp

section Torus

variable {d N₀ M N : ℕ} [NeZero N₀]

theorem norm_regOp_apply_le {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {A δ : ℝ}
    (hU : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) {g : ℝ} (hg0 : 0 ≤ g) (hgA : g ≤ A)
    (Ω : Finset (L1Torus d N₀)) (x y : L1Torus d N₀) :
    ‖regOp Ω U g x y‖ ≤ A * Real.exp (-δ * dist x y) := by
  rw [regOp_apply]
  split_ifs with h1 h2 h2
  · exact absurd h1.1 h2.2
  · rw [add_zero]; exact hU x y
  · obtain ⟨rfl, -⟩ := h2
    rw [zero_add, dist_self, mul_zero, Real.exp_zero, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hg0]
    exact hgA
  · rw [add_zero, norm_zero]
    exact mul_nonneg (hg0.trans hgA) (Real.exp_pos _).le

/-- **`CutOpHyp` passes to the block-diagonal extension** with the same constants, the gap `g`
being the extension constant (`g ≤ A`). -/
theorem cutOpHyp_regOp {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {g A δ ε κ : ℝ}
    (hU : CutOpHyp d N₀ M U g A δ ε κ) (hgA : g ≤ A) (Ω : Finset (L1Torus d N₀)) :
    CutOpHyp d N₀ M (regOp Ω U g) g A δ ε κ :=
  { hU with
    coercive := isCoercive_regOp hU.coercive le_rfl Ω
    decay := norm_regOp_apply_le hU.decay hU.hg.le hgA Ω }

/-- **The cut family of the extension is block diagonal**: for every `s`, the entries of
`boxCutU (regOp Ω U g) h s` between a site of `Ω` and a site off `Ω` vanish. -/
theorem boxCutU_regOp_eq_zero (a : ℝ) (Ω : Finset (L1Torus d N₀))
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (g : ℝ) (h : Fin N → ℂ)
    (s : MacIdx d N₀ M → ℂ) {p q : L1Torus d N₀ × Fin N}
    (hpq : (p.1 ∈ Ω ∧ q.1 ∉ Ω) ∨ (p.1 ∉ Ω ∧ q.1 ∈ Ω)) :
    boxCutU d N₀ M a (regOp Ω U g) h s p q = 0 := by
  have key : matConj (RingHom.id ℂ) (fun p : L1Torus d N₀ × Fin N => regionSign Ω p.1)
      (fun p => regionSign_mul_self Ω p.1) (boxCutU d N₀ M a (regOp Ω U g) h s) =
      boxCutU d N₀ M a (regOp Ω U g) h s :=
    matConj_boxCutU (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (regionConj_regOp Ω U g) h s
  refine eq_zero_of_matConj_id_eq key ?_
  unfold regionSign
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- **The resolvent of the extension on `Ω`** is the resolvent of the principal block. -/
theorem inv_regOp_submatrix (Ω : Finset (L1Torus d N₀))
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (g t : ℝ)
    (hM : IsUnit ((t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + regOp Ω U g)) :
    (((t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + regOp Ω U g)⁻¹).submatrix
        (Subtype.val : Ω → L1Torus d N₀) Subtype.val =
      ((t : ℂ) • (1 : Matrix Ω Ω ℂ) + restrictOp U Ω)⁻¹ := by
  have hblock : ((t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) +
      regOp Ω U g).submatrix (Subtype.val : Ω → L1Torus d N₀) Subtype.val =
      (t : ℂ) • (1 : Matrix Ω Ω ℂ) + restrictOp U Ω := by
    ext a b
    have h1 : (a : L1Torus d N₀) ∈ Ω ∧ (b : L1Torus d N₀) ∈ Ω := ⟨a.2, b.2⟩
    have h2 : ¬ ((a : L1Torus d N₀) = b ∧ (a : L1Torus d N₀) ∉ Ω) := fun h => h.2 a.2
    rw [Matrix.submatrix_apply, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, regOp_apply, ite_eq_left_of_eq_true _ _ (eq_true h1),
      ite_eq_right_of_eq_false _ _ (eq_false h2), add_zero]
    show _ + U a b = _ + U a b
    congr 1
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (Subtype.ext h))]
  have h := submatrix_mul_submatrix_inv (Subtype.val : Ω → L1Torus d N₀) Subtype.val_injective hM
    (fun a z hz => by
      have hz' : z ∉ Ω := fun hzΩ => hz ⟨⟨z, hzΩ⟩, rfl⟩
      have hne : (a : L1Torus d N₀) ≠ z := fun h => hz' (h ▸ a.2)
      have h1 : ¬ ((a : L1Torus d N₀) ∈ Ω ∧ z ∈ Ω) := fun h => hz' h.2
      have h2 : ¬ ((a : L1Torus d N₀) = z ∧ (a : L1Torus d N₀) ∉ Ω) := fun h => hne h.1
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, regOp_apply,
        ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2), add_zero,
        zero_add])
  rw [hblock] at h
  exact (Matrix.inv_eq_right_inv h).symm

/-- **The inverse square root of the extension on `Ω`** is that of the principal block:
`(sqrtMat (regOp Ω U g))|_Ω = sqrtMat (U|_Ω)`. -/
theorem sqrtMat_regOp_submatrix [Nonempty (L1Torus d N₀)] (Ω : Finset (L1Torus d N₀))
    [Nonempty Ω] (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (g : ℝ)
    (hres : Localization.ResOK (regOp Ω U g)) :
    (Localization.sqrtMat (regOp Ω U g)).submatrix (Subtype.val : Ω → L1Torus d N₀)
        Subtype.val = Localization.sqrtMat (restrictOp U Ω) := by
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      ((((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) +
        regOp Ω U g)⁻¹).submatrix (Subtype.val : Ω → L1Torus d N₀) Subtype.val) =
      ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((t : ℂ) • (1 : Matrix Ω Ω ℂ) + restrictOp U Ω)⁻¹ :=
    fun t ht => by
      rw [← inv_regOp_submatrix Ω U g t (hres t (le_of_lt ht))]
      ext a b
      rfl
  ext a b
  show ((1 / Real.pi : ℝ) : ℂ) * (∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + regOp Ω U g)⁻¹) a b) =
    ((1 / Real.pi : ℝ) : ℂ) * (∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((t : ℂ) • (1 : Matrix Ω Ω ℂ) + restrictOp U Ω)⁻¹) a b)
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact congrFun (congrFun (hF t ht) a) b

end Torus

end Balaban.Green
