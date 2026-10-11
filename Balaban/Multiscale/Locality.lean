/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ScaleMismatch
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# G-2(vi), single-variation locality (GREEN.md §4.6)

For `α, α'` in the polydisc of G-1(a) with `α = α'` off a finite set `Z ⊆ Ω₁` and
`|α(x) - α'(x)| ≤ η ℓ(x)⁻²`, the resolvent identity `G(α) - G(α') = - G(α) (α - α') G(α')` and two
applications of the block decay `green_G2i_green` give, for `f` supported in a block `Δ_{j'}(y')`,

`‖χ_{Δ_j(y)} (G(α) - G(α')) f‖ ≤ η (13 L / c)² ℓ_{j'}² ‖f‖ ∑_{x ∈ Z} e^{-γ d(y,x)} e^{-γ d(x,y')}`,
`γ = ε₀ / 2` (`Balaban.Multiscale.green_sub_green_le_sum`).  Since `d(y,x) ≥ d(y,Z)`,
`d(x,y') ≥ d(y',Z)` and `d(y,x) + d(x,y') ≥ d(y,y')` this yields the product form of G-2(vi)
(`Balaban.Multiscale.green_sub_green_le_prod`).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The `ℓ²` norm of the zero extension of `u` on the `j`-block of `y`. -/
noncomputable def blockNorm (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    (u : G.Ω 1 → ℂ) : ℝ :=
  Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2)

/-- The exponential decay factor `e^{-c D}` of a distance `D ∈ [0, ∞]` (`0` for `D = ∞`). -/
noncomputable def decay (c : ℝ) (D : ENNReal) : ℝ :=
  if D = ⊤ then 0 else Real.exp (-(c * D.toReal))

/-- The distance from a site to a finite set of sites of `Ω₁`. -/
noncomputable def GeneratingSet.distSet (G : GeneratingSet d L N₀ k ϱ) (y : Torus d (N₀ * L ^ k))
    (Z : Finset (G.Ω 1)) : ENNReal :=
  Z.inf fun x => G.pathDist y x

theorem decay_nonneg (c : ℝ) (D : ENNReal) : 0 ≤ decay c D := by
  unfold decay; split_ifs
  exacts [le_rfl, (Real.exp_pos _).le]

theorem decay_le_one {c : ℝ} (hc : 0 ≤ c) (D : ENNReal) : decay c D ≤ 1 := by
  unfold decay; split_ifs
  · exact zero_le_one
  · rw [Real.exp_le_one_iff]
    have := ENNReal.toReal_nonneg (a := D)
    nlinarith

theorem GeneratingSet.distSet_le (G : GeneratingSet d L N₀ k ϱ) (y : Torus d (N₀ * L ^ k))
    {Z : Finset (G.Ω 1)} {x : G.Ω 1} (hx : x ∈ Z) : G.distSet y Z ≤ G.pathDist y x :=
  Finset.inf_le hx

/-- Block vector in Euclidean space, to use the triangle inequality. -/
noncomputable def blockVec (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    (u : G.Ω 1 → ℂ) : EuclideanSpace ℂ (G.blk j y) :=
  WithLp.toLp 2 fun x => zeroExt (G.Ω 1) u x

theorem blockNorm_eq (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    (u : G.Ω 1 → ℂ) : blockNorm G j y u = ‖blockVec G j y u‖ := by
  rw [blockVec, EuclideanSpace.norm_eq, blockNorm]
  congr 1
  exact (Finset.sum_coe_sort (G.blk j y) fun x => ‖zeroExt (G.Ω 1) u x‖ ^ 2).symm

theorem zeroExt_sum {ι : Type*} [DecidableEq ι] (Λ : Finset ι) {κ : Type*} (s : Finset κ)
    (f : κ → Λ → ℂ) (i : ι) :
    zeroExt Λ (∑ x ∈ s, f x) i = ∑ x ∈ s, zeroExt Λ (f x) i := by
  unfold zeroExt
  split_ifs with h
  · simp [Finset.sum_apply]
  · simp

theorem blockVec_sum (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    {κ : Type*} (s : Finset κ) (f : κ → G.Ω 1 → ℂ) :
    blockVec G j y (∑ x ∈ s, f x) = ∑ x ∈ s, blockVec G j y (f x) := by
  ext i
  simp [blockVec, zeroExt_sum]

theorem blockNorm_sum_le (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    {κ : Type*} (s : Finset κ) (f : κ → G.Ω 1 → ℂ) :
    blockNorm G j y (∑ x ∈ s, f x) ≤ ∑ x ∈ s, blockNorm G j y (f x) := by
  simp only [blockNorm_eq, blockVec_sum]
  exact norm_sum_le _ _

theorem blockNorm_nonneg (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    (u : G.Ω 1 → ℂ) : 0 ≤ blockNorm G j y u := Real.sqrt_nonneg _

/-- A single value is bounded by the block norm. -/
theorem norm_le_blockNorm (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (x : G.Ω 1)
    (u : G.Ω 1 → ℂ) : ‖u x‖ ≤ blockNorm G j (x : Torus d (N₀ * L ^ k)) u := by
  unfold blockNorm
  apply Real.le_sqrt_of_sq_le
  have hx : (x : Torus d (N₀ * L ^ k)) ∈ G.blk j (x : Torus d (N₀ * L ^ k)) :=
    GeneratingSet.mem_blk.2 rfl
  have := Finset.single_le_sum (f := fun z => ‖zeroExt (G.Ω 1) u z‖ ^ 2)
    (fun z _ => sq_nonneg _) hx
  simpa [zeroExt, x.2] using this

/-- The exponent split (N-2): for `A ≤ p`, `B ≤ q`, `D ≤ p + q`,
`e^{-c p} e^{-c q} ≤ e^{-(c/2) A} e^{-(c/2) B} e^{-(c/2) D}`. -/
theorem decay_mul_le {c : ℝ} (hc : 0 ≤ c) {p q A B D : ENNReal} (hA : A ≤ p) (hB : B ≤ q)
    (hD : D ≤ p + q) :
    decay c p * decay c q ≤ decay (c / 2) A * decay (c / 2) B * decay (c / 2) D := by
  by_cases hpq : p = ⊤ ∨ q = ⊤
  · have : decay c p * decay c q = 0 := by
      rcases hpq with h | h <;> simp [decay, h]
    rw [this]
    exact mul_nonneg (mul_nonneg (decay_nonneg _ _) (decay_nonneg _ _)) (decay_nonneg _ _)
  · push Not at hpq
    obtain ⟨hp, hq⟩ := hpq
    have hpqt : p + q ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hp, hq⟩
    have hAt : A ≠ ⊤ := ne_top_of_le_ne_top hp hA
    have hBt : B ≠ ⊤ := ne_top_of_le_ne_top hq hB
    have hDt : D ≠ ⊤ := ne_top_of_le_ne_top hpqt hD
    have hA' := ENNReal.toReal_mono hp hA
    have hB' := ENNReal.toReal_mono hq hB
    have hD' := ENNReal.toReal_mono hpqt hD
    rw [ENNReal.toReal_add hp hq] at hD'
    simp only [decay, hp, hq, hAt, hBt, hDt, ite_false]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hc (sub_nonneg.2 hA'), mul_nonneg hc (sub_nonneg.2 hB'),
      mul_nonneg hc (sub_nonneg.2 hD'), ENNReal.toReal_nonneg (a := p),
      ENNReal.toReal_nonneg (a := q)]

section Decay

variable (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
  (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
  (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))

include hd hν ha hα hϱ hsep

/-- **G-2(i), `L²` form with the decay factor.** For `f` supported in the block `Δ_{j'}(y')`,
`‖χ_{Δ_j(y)} G_D(α) f‖ ≤ (13 L / c) e^{-γ d(y,y')} ℓ_{j'}² ‖f‖`, `γ = ε₀ / 2`. -/
theorem green_blockNorm_le {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j')
    (hj'k : j' ≤ k) {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ f) ≤
      13 * L / poincareConst d * decay (agmonRate d / 2) (G.pathDist y y') *
        ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) := by
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set u := (dirichletOperator G a ν α)⁻¹ *ᵥ f with hu
  have hu' : dirichletOperator G a ν α *ᵥ u = f := dirichletOperator_mulVec_inv G hd hν ha α hα f
  obtain ⟨h1, h2⟩ := green_G2i_of_pathDist G hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu' hsupp hϱ hsep
  have hgrad : 0 ≤ (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
      ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) := by positivity
  unfold decay blockNorm
  split_ifs with htop
  · have := h2 htop
    simp only [mul_zero, zero_mul]
    linarith [Real.sqrt_nonneg (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2)]
  · have := h1 htop
    linarith

end Decay

section Resolvent

variable (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
  (ha : IsAdmissibleWeights k a) (α α' : G.Ω 1 → ℂ)
  (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))

theorem dirichletOperator_eq_add (a : ℕ → ℝ) (ν : ℝ) (α α' : G.Ω 1 → ℂ) :
    dirichletOperator G a ν α = dirichletOperator G a ν α' + Matrix.diagonal (α - α') := by
  ext i j
  simp only [dirichletOperator, Matrix.add_apply, Matrix.diagonal_apply, Pi.sub_apply]
  split_ifs <;> ring

include hd hν ha hα in
/-- The resolvent identity in the form used for locality: with `Z` containing the set where
`α ≠ α'`, `G(α) f - G(α') f = ∑_{x ∈ Z} G(α) (δ_x · (-(α - α')(x) · (G(α') f)(x)))`. -/
theorem green_sub_eq_sum
    (hα' : ∀ x, ‖α' x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (Z : Finset (G.Ω 1)) (hZ : ∀ x, x ∉ Z → α x = α' x) (f : G.Ω 1 → ℂ) :
    (dirichletOperator G a ν α)⁻¹ *ᵥ f - (dirichletOperator G a ν α')⁻¹ *ᵥ f =
      ∑ x ∈ Z, (dirichletOperator G a ν α)⁻¹ *ᵥ
        Pi.single x (-(α x - α' x) * ((dirichletOperator G a ν α')⁻¹ *ᵥ f) x) := by
  classical
  set u' := (dirichletOperator G a ν α')⁻¹ *ᵥ f with hu'
  have h1 : dirichletOperator G a ν α' *ᵥ u' = f :=
    dirichletOperator_mulVec_inv G hd hν ha α' hα' f
  have h0 : dirichletOperator G a ν α *ᵥ ((dirichletOperator G a ν α)⁻¹ *ᵥ f) = f :=
    dirichletOperator_mulVec_inv G hd hν ha α hα f
  set g : G.Ω 1 → ℂ := fun i => -(α i - α' i) * u' i with hg
  have hw : dirichletOperator G a ν α *ᵥ
      ((dirichletOperator G a ν α)⁻¹ *ᵥ f - u') = g := by
    rw [Matrix.mulVec_sub, h0, dirichletOperator_eq_add G a ν α α', Matrix.add_mulVec, h1]
    ext i
    simp [hg, Matrix.mulVec_diagonal]
    ring
  have hU := (Matrix.isUnit_iff_isUnit_det _).1 (dirichletOperator_isUnit G hd hν ha α hα)
  have hinv : (dirichletOperator G a ν α)⁻¹ *ᵥ g =
      (dirichletOperator G a ν α)⁻¹ *ᵥ f - u' := by
    rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  have hdec : g = ∑ x ∈ Z, Pi.single x (g x) := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with hi
    · rfl
    · simp [hg, hZ i hi]
  rw [← hinv]
  conv_lhs => rw [hdec]
  rw [Matrix.mulVec_sum]

end Resolvent

section Locality

variable (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
  (ha : IsAdmissibleWeights k a) (α α' : G.Ω 1 → ℂ)
  (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hα' : ∀ x, ‖α' x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))

include hd hν ha hα hα' hϱ hsep in
/-- **G-2(vi), single-variation locality, sum form.**  If `α = α'` off the finite set `Z ⊆ Ω₁`,
`|α(x) - α'(x)| ≤ η ℓ(x)⁻²`, and `f` is supported in the block `Δ_{j'}(y')`, then
`‖χ_{Δ_j(y)} (G_D(α) - G_D(α')) f‖ ≤ η (13 L / c)² ℓ_{j'}² ‖f‖ ∑_{x ∈ Z} e^{-γ d(y,x)} e^{-γ d(x,y')}`
with `γ = ε₀ / 2`. -/
theorem green_sub_green_le_sum (Z : Finset (G.Ω 1)) (hZ : ∀ x, x ∉ Z → α x = α' x) {η : ℝ}
    (hη : ∀ x : G.Ω 1, ‖α x - α' x‖ ≤ η / (G.spacing x) ^ 2)
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j') {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ f - (dirichletOperator G a ν α')⁻¹ *ᵥ f) ≤
      η * (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) *
        ∑ x ∈ Z, decay (agmonRate d / 2) (G.pathDist y x) *
          decay (agmonRate d / 2) (G.pathDist x y') := by
  classical
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [green_sub_eq_sum G hd hν ha α α' hα hα' Z hZ f, Finset.mul_sum]
  refine (blockNorm_sum_le G j y _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  obtain ⟨hjx1, hjxk, hxl⟩ := G.layerIndex_spec x.2
  set jx := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hjx
  set u' := (dirichletOperator G a ν α')⁻¹ *ᵥ f with hu'
  set c : ℂ := -(α x - α' x) * u' x with hc
  set P : ℝ := 13 * L / poincareConst d with hP
  have hP0 : 0 ≤ P := by positivity
  set D1 := decay (agmonRate d / 2) (G.pathDist y x) with hD1
  set D2 := decay (agmonRate d / 2) (G.pathDist x y') with hD2
  have hD10 : 0 ≤ D1 := decay_nonneg _ _
  have hD20 : 0 ≤ D2 := decay_nonneg _ _
  set S := Real.sqrt (Green.sqNorm f) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hℓ : 0 < ((L : ℝ) ^ jx) ^ 2 := by positivity
  -- piece bound from `x` to `y`
  have hsq : Green.sqNorm (Pi.single x c : G.Ω 1 → ℂ) = ‖c‖ ^ 2 := by
    unfold Green.sqNorm
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  have h1 := green_blockNorm_le G hd hν ha α hα hϱ hsep hj1 hjk hjx1 hjxk hy hxl
    (f := Pi.single x c) (by
      intro i hi
      by_cases hix : i = x
      · subst hix; rfl
      · simp [hix] at hi)
  rw [hsq, Real.sqrt_sq (norm_nonneg _)] at h1
  -- the value of `u'` at `x`
  have h2 := green_blockNorm_le G hd hν ha α' hα' hϱ hsep hjx1 hjxk hj'1 hj'k hxl hy' hsupp
  have h3 : ‖u' x‖ ≤ P * D2 * ((L : ℝ) ^ j') ^ 2 * S :=
    (norm_le_blockNorm G jx x u').trans h2
  have h4 : ‖c‖ ≤ η / ((L : ℝ) ^ jx) ^ 2 * ‖u' x‖ := by
    rw [hc, norm_mul, norm_neg]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := hη x
    rwa [G.spacing_eq hjx1 hjxk hxl] at this
  have h5 : ‖c‖ ≤ η / ((L : ℝ) ^ jx) ^ 2 * (P * D2 * ((L : ℝ) ^ j') ^ 2 * S) := by
    refine h4.trans (mul_le_mul_of_nonneg_left h3 ?_)
    have := hη x
    rw [G.spacing_eq hjx1 hjxk hxl] at this
    exact (norm_nonneg _).trans this
  calc blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ Pi.single x c)
      ≤ P * D1 * ((L : ℝ) ^ jx) ^ 2 * ‖c‖ := h1
    _ ≤ P * D1 * ((L : ℝ) ^ jx) ^ 2 *
          (η / ((L : ℝ) ^ jx) ^ 2 * (P * D2 * ((L : ℝ) ^ j') ^ 2 * S)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by field_simp

end Locality

section Product

variable (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
  (ha : IsAdmissibleWeights k a) (α α' : G.Ω 1 → ℂ)
  (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hα' : ∀ x, ‖α' x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))

include hd hν ha hα hα' hϱ hsep in
/-- **G-2(vi), single-variation locality, product form.**  With `γ' = ε₀ / 4`
(`= γ₀ / 2`, `γ₀ = ε₀ / 2`),
`‖χ_{Δ_j(y)} (G_D(α) - G_D(α')) f‖ ≤ |Z| η (13 L / c)² ℓ_{j'}² ‖f‖
  e^{-γ' d(y,Z)} e^{-γ' d(y',Z)} e^{-γ' d(y,y')}`.
The factor `|Z|` is the trivial bound of the sum over `x ∈ Z` in `green_sub_green_le_sum`; the
summation lemma (GREEN.md Lemma 4.4) would replace it by a constant. -/
theorem green_sub_green_le_prod (Z : Finset (G.Ω 1)) (hZ : ∀ x, x ∉ Z → α x = α' x) {η : ℝ}
    (hη : ∀ x : G.Ω 1, ‖α x - α' x‖ ≤ η / (G.spacing x) ^ 2)
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j') {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ f - (dirichletOperator G a ν α')⁻¹ *ᵥ f) ≤
      Z.card * η * (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 *
        Real.sqrt (Green.sqNorm f) *
        (decay (agmonRate d / 4) (G.distSet y Z) * decay (agmonRate d / 4) (G.distSet y' Z) *
          decay (agmonRate d / 4) (G.pathDist y y')) := by
  have hp0 := poincareConst_pos hd
  have hε := agmonRate_pos hd
  refine (green_sub_green_le_sum G hd hν ha α α' hα hα' hϱ hsep Z hZ hη hj1 hjk hj'1 hj'k hy hy'
    hsupp).trans ?_
  have hη0 : 0 ≤ η ∨ Z = ∅ := by
    by_cases hZ0 : Z = ∅
    · exact Or.inr hZ0
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hZ0
      refine Or.inl ?_
      have := (norm_nonneg _).trans (hη x)
      have hsp : 0 < (G.spacing x) ^ 2 := by have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hsp)
  set K : ℝ := (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f)
    with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ x ∈ Z, decay (agmonRate d / 2) (G.pathDist y x) *
      decay (agmonRate d / 2) (G.pathDist x y') ≤
      decay (agmonRate d / 4) (G.distSet y Z) * decay (agmonRate d / 4) (G.distSet y' Z) *
        decay (agmonRate d / 4) (G.pathDist y y') := by
    intro x hx
    have := decay_mul_le (c := agmonRate d / 2) (by positivity)
      (G.distSet_le y hx) (A := G.distSet y Z)
      (B := G.distSet y' Z) (q := G.pathDist x y')
      (by rw [GeneratingSet.pathDist_comm]; exact G.distSet_le y' hx)
      (D := G.pathDist y y') (G.pathDist_triangle y x y')
    have e : agmonRate d / 2 / 2 = agmonRate d / 4 := by ring
    rwa [e] at this
  rcases hη0 with hη0 | hZ0
  · calc η * (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) *
          ∑ x ∈ Z, decay (agmonRate d / 2) (G.pathDist y x) *
            decay (agmonRate d / 2) (G.pathDist x y')
        = η * K * ∑ x ∈ Z, decay (agmonRate d / 2) (G.pathDist y x) *
            decay (agmonRate d / 2) (G.pathDist x y') := by rw [hK]; ring
      _ ≤ η * K * ∑ x ∈ Z, (decay (agmonRate d / 4) (G.distSet y Z) *
            decay (agmonRate d / 4) (G.distSet y' Z) *
            decay (agmonRate d / 4) (G.pathDist y y')) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hK]; ring
  · subst hZ0
    simp

end Product

end Balaban.Multiscale
