/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ScaleMismatch
public import Balaban.Multiscale.Counting
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# G-2(vi), single-variation locality (GREEN.md §4.6)

For `α, α'` in the polydisc of G-1(a) with `α = α'` off a finite set `Z ⊆ Ω₁` and
`|α(x) - α'(x)| ≤ η ℓ(x)⁻²`, the resolvent identity `G(α) - G(α') = - G(α) (α - α') G(α')`
(`Balaban.Multiscale.green_sub_eq_mulVec`) and two applications of the block decay
`Balaban.Multiscale.green_blockNorm_le` (G-2(i)) give, for `f` supported in a block `Δ_{j'}(y')`,

* `green_sub_green_le_sum`: the bound by `∑_{x ∈ Z} e^{-γ d(y,x)} e^{-γ d(x,y')}`;
* `green_sub_green_le_blocksum`: the same with the sum over the sites of the blocks meeting `Z`,
  weighted by the inverse block size (a sum over blocks);
* `green_sub_green_locality`: the product form of G-2(vi),
  `≤ C η ℓ_{j'}² ‖f‖ e^{-γ' d(y,Z)} e^{-γ' d(y',Z)} e^{-γ' d(y,y')}`, `γ' = ε₀/6` (the exponent split
  of N-2, with the counting Lemma 4.4 of `Balaban.Multiscale.Counting`);
* `sqrt_sqNorm_le_of_supp`: the conversion `‖f‖ ≤ ℓ_{j'}^{d/2} ‖f‖_∞` for `f` supported in a block.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The `ℓ²` norm of the zero extension of `u` on the `j`-block of `y`. -/
noncomputable def blockNorm (G : GeneratingSet d L N₀ k ϱ) (j : ℕ) (y : Torus d (N₀ * L ^ k))
    (u : G.Ω 1 → ℂ) : ℝ :=
  Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2)

/-- The distance from a site to a finite set of sites of `Ω₁`. -/
noncomputable def GeneratingSet.distSet (G : GeneratingSet d L N₀ k ϱ) (y : Torus d (N₀ * L ^ k))
    (Z : Finset (G.Ω 1)) : ENNReal :=
  Z.inf fun x => G.pathDist y x

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

/-- The exponent split with a block-diameter loss: for `A ≤ p + s`, `B ≤ q + s`, `D ≤ p + q`,
`e^{-c p} e^{-c q} ≤ e^{(c/3)(2s)} e^{-(c/3)(A + B + D + p)}`. -/
theorem decay_split {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) {p q A B D : ENNReal}
    (hA : A ≤ p + ENNReal.ofReal s) (hB : B ≤ q + ENNReal.ofReal s) (hD : D ≤ p + q) :
    decay c p * decay c q ≤ Real.exp (c / 3 * (2 * s)) *
      (decay (c / 3) A * decay (c / 3) B * decay (c / 3) D * decay (c / 3) p) := by
  by_cases hpq : p = ⊤ ∨ q = ⊤
  · have : decay c p * decay c q = 0 := by
      rcases hpq with h | h <;> simp [decay, h]
    rw [this]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (mul_nonneg (decay_nonneg _ _)
      (decay_nonneg _ _)) (decay_nonneg _ _)) (decay_nonneg _ _))
  · push Not at hpq
    obtain ⟨hp, hq⟩ := hpq
    have hps : p + ENNReal.ofReal s ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hp, ENNReal.ofReal_ne_top⟩
    have hqs : q + ENNReal.ofReal s ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hq, ENNReal.ofReal_ne_top⟩
    have hpqt : p + q ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hp, hq⟩
    have hAt : A ≠ ⊤ := ne_top_of_le_ne_top hps hA
    have hBt : B ≠ ⊤ := ne_top_of_le_ne_top hqs hB
    have hDt : D ≠ ⊤ := ne_top_of_le_ne_top hpqt hD
    have hA' := ENNReal.toReal_mono hps hA
    have hB' := ENNReal.toReal_mono hqs hB
    have hD' := ENNReal.toReal_mono hpqt hD
    rw [ENNReal.toReal_add hp ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs] at hA'
    rw [ENNReal.toReal_add hq ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs] at hB'
    rw [ENNReal.toReal_add hp hq] at hD'
    simp only [decay, hp, hq, hAt, hBt, hDt, ite_false]
    rw [← Real.exp_add, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hc (sub_nonneg.2 hA'), mul_nonneg hc (sub_nonneg.2 hB'),
      mul_nonneg hc (sub_nonneg.2 hD'), ENNReal.toReal_nonneg (a := p),
      ENNReal.toReal_nonneg (a := q), mul_nonneg hc hs]

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
/-- The resolvent identity: `G(α) f - G(α') f = G(α) (-(α - α') · G(α') f)`. -/
theorem green_sub_eq_mulVec
    (hα' : ∀ x, ‖α' x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (f : G.Ω 1 → ℂ) :
    (dirichletOperator G a ν α)⁻¹ *ᵥ f - (dirichletOperator G a ν α')⁻¹ *ᵥ f =
      (dirichletOperator G a ν α)⁻¹ *ᵥ
        (fun i => -(α i - α' i) * ((dirichletOperator G a ν α')⁻¹ *ᵥ f) i) := by
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
  rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]

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
  rw [green_sub_eq_mulVec G hd hν ha α α' hα hα' f]
  set u' := (dirichletOperator G a ν α')⁻¹ *ᵥ f with hu'
  set g : G.Ω 1 → ℂ := fun i => -(α i - α' i) * u' i with hg
  have hdec : g = ∑ x ∈ Z, Pi.single x (g x) := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with hi
    · rfl
    · simp [hg, hZ i hi]
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


section Blocks

variable (G : GeneratingSet d L N₀ k ϱ)

theorem blockNorm_smul (j : ℕ) (y : Torus d (N₀ * L ^ k)) (c : ℝ) (hc : 0 ≤ c) (u : G.Ω 1 → ℂ) :
    blockNorm G j y ((c : ℂ) • u) = c * blockNorm G j y u := by
  have : blockVec G j y ((c : ℂ) • u) = (c : ℂ) • blockVec G j y u := by
    ext i
    simp [blockVec, zeroExt]
  rw [blockNorm_eq, blockNorm_eq, this, norm_smul]
  simp [abs_of_nonneg hc]

/-- Restriction of a vector to the `j`-block of `x`. -/
def blockProj (j : ℕ) (x : Torus d (N₀ * L ^ k)) (v : G.Ω 1 → ℂ) : G.Ω 1 → ℂ :=
  fun i => if jBlock d L N₀ k j i = jBlock d L N₀ k j x then v i else 0

theorem sqNorm_blockProj (j : ℕ) (x : Torus d (N₀ * L ^ k)) (v : G.Ω 1 → ℂ) :
    Green.sqNorm (blockProj G j x v) = blockNorm G j x v ^ 2 := by
  classical
  unfold Green.sqNorm blockNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  unfold GeneratingSet.blk
  rw [Finset.sum_filter]
  rw [Green.sum_eq_sum_subtype (G.Ω 1)
    (fun t => if jBlock d L N₀ k j t = jBlock d L N₀ k j x then ‖zeroExt (G.Ω 1) v t‖ ^ 2 else 0)
    (fun t ht => by simp [zeroExt, ht])]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : zeroExt (G.Ω 1) v i = v i := by simp [zeroExt, i.2]
  simp only [blockProj, this]
  split_ifs <;> simp

open Classical in
/-- `Z⁺`: the sites whose own-layer block meets `Z` (the union of blocks meeting `Z`). -/
noncomputable def Zplus (Z : Finset (G.Ω 1)) : Finset (G.Ω 1) :=
  Finset.univ.filter fun x => ∃ z ∈ Z, jBlock d L N₀ k (G.layerIndex x) z =
    jBlock d L N₀ k (G.layerIndex x) x

theorem card_blk (j : ℕ) (hjk : j ≤ k) (y : Torus d (N₀ * L ^ k)) :
    (G.blk j y).card = (L ^ j) ^ d := by
  have h := card_blockFibre (d := d) (N := L ^ j) (m := N₀ * L ^ (k - j)) (side_eq hjk)
    (jBlock d L N₀ k j y)
  have e : G.blk j y = blockFibre (L ^ j) (N₀ * L ^ (k - j)) (jBlock d L N₀ k j y) := by
    ext x; rw [GeneratingSet.mem_blk, mem_blockFibre]; rfl
  rw [e]; exact h

theorem sum_siteWeight_block {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {i : G.Ω 1}
    (hil : (i : Torus d (N₀ * L ^ k)) ∈ G.layer j) :
    ∑ x ∈ Finset.univ.filter (fun x : G.Ω 1 =>
        jBlock d L N₀ k j x = jBlock d L N₀ k j i), siteWeight G x = 1 := by
  classical
  set F := Finset.univ.filter (fun x : G.Ω 1 =>
        jBlock d L N₀ k j x = jBlock d L N₀ k j i) with hF
  have hw : ∀ x ∈ F, siteWeight G x = (((L : ℝ) ^ j)⁻¹) ^ d := by
    intro x hx
    have hxj : jBlock d L N₀ k j x = jBlock d L N₀ k j i := (Finset.mem_filter.1 hx).2
    have hxl : (x : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk hxj).2 hil
    unfold siteWeight
    rw [G.layerIndex_eq hj1 hjk hxl]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
  have hcard : F.card = (L ^ j) ^ d := by
    rw [← card_blk G j hjk i]
    refine Finset.card_bij (fun x _ => (x : Torus d (N₀ * L ^ k))) ?_ ?_ ?_
    · intro x hx
      exact GeneratingSet.mem_blk.2 (Finset.mem_filter.1 hx).2
    · intro a _ b _ h; exact Subtype.val_injective h
    · intro t ht
      have htj := GeneratingSet.mem_blk.1 ht
      have htl : t ∈ G.layer j := (G.mem_layer_iff hj1 hjk htj).2 hil
      exact ⟨⟨t, G.layer_subset hj1 hjk htl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, htj⟩, rfl⟩
  rw [hcard]
  push_cast
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero _ hL0.ne'), one_pow]

/-- A vector supported on `Z` is the weighted sum of its restrictions to the blocks meeting `Z`. -/
theorem decomp_blocks (Z : Finset (G.Ω 1)) (g : G.Ω 1 → ℂ) (hg : ∀ i, i ∉ Z → g i = 0) :
    g = ∑ x ∈ Zplus G Z,
      ((siteWeight G x : ℝ) : ℂ) • blockProj G (G.layerIndex x) x g := by
  classical
  funext i
  rw [Finset.sum_apply]
  by_cases hgi : g i = 0
  · simp [hgi, blockProj]
  · have hiZ : i ∈ Z := by by_contra h; exact hgi (hg i h)
    obtain ⟨hj1, hjk, hil⟩ := G.layerIndex_spec i.2
    set j := G.layerIndex (i : Torus d (N₀ * L ^ k)) with hj
    have key : ∀ x : G.Ω 1, (x ∈ Zplus G Z ∧ jBlock d L N₀ k (G.layerIndex x) i =
          jBlock d L N₀ k (G.layerIndex x) x) ↔ jBlock d L N₀ k j x = jBlock d L N₀ k j i := by
      intro x
      obtain ⟨hx1, hxk, hxl⟩ := G.layerIndex_spec x.2
      constructor
      · rintro ⟨_, hxj⟩
        have hxj' := hxj.symm
        have hil' : (i : Torus d (N₀ * L ^ k)) ∈ G.layer (G.layerIndex x) :=
          (G.mem_layer_iff hx1 hxk hxj').1 hxl
        have : j = G.layerIndex x := G.layerIndex_eq hx1 hxk hil'
        rw [this]; exact hxj'
      · intro hxj
        have hxl' : (x : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk hxj).2 hil
        have : G.layerIndex x = j := G.layerIndex_eq hj1 hjk hxl'
        rw [this]
        exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hiZ, by rw [this]; exact hxj.symm⟩,
          hxj.symm⟩
    have hterm : ∀ x ∈ Zplus G Z,
        (((siteWeight G x : ℝ) : ℂ) • blockProj G (G.layerIndex x) x g) i =
        if jBlock d L N₀ k j x = jBlock d L N₀ k j i then ((siteWeight G x : ℝ) : ℂ) * g i
          else 0 := by
      intro x hx
      have hk := key x
      simp only [Pi.smul_apply, blockProj, smul_eq_mul]
      by_cases h2 : jBlock d L N₀ k (G.layerIndex x) i = jBlock d L N₀ k (G.layerIndex x) x
      · have := hk.1 ⟨hx, h2⟩
        simp [h2, this]
      · have : ¬ jBlock d L N₀ k j x = jBlock d L N₀ k j i := fun h => h2 (hk.2 h).2
        simp [h2, this]
    rw [Finset.sum_congr rfl hterm]
    have hsub : ∑ x ∈ Zplus G Z, (if jBlock d L N₀ k j x = jBlock d L N₀ k j i then
        ((siteWeight G x : ℝ) : ℂ) * g i else 0) =
        ∑ x : G.Ω 1, (if jBlock d L N₀ k j x = jBlock d L N₀ k j i then
        ((siteWeight G x : ℝ) : ℂ) * g i else 0) := by
      refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
      have : ¬ jBlock d L N₀ k j x = jBlock d L N₀ k j i := fun h => hx ((key x).2 h).1
      simp [this]
    rw [hsub, ← Finset.sum_filter, ← Finset.sum_mul]
    have h1 := sum_siteWeight_block G hj1 hjk hil
    rw [← Complex.ofReal_sum, h1]
    simp

end Blocks

section BlockLocality

variable (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
  (ha : IsAdmissibleWeights k a) (α α' : G.Ω 1 → ℂ)
  (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hα' : ∀ x, ‖α' x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))

include hd hν ha hα hα' hϱ hsep in
/-- **G-2(vi), single-variation locality, block-sum form.**  As `green_sub_green_le_sum` but the
sum runs over the sites of the blocks meeting `Z`, each with weight `ℓ(x)^{-d}` (the inverse block
size), so that the sum is a sum over blocks. -/
theorem green_sub_green_le_blocksum (Z : Finset (G.Ω 1)) (hZ : ∀ x, x ∉ Z → α x = α' x) {η : ℝ}
    (hη : ∀ x : G.Ω 1, ‖α x - α' x‖ ≤ η / (G.spacing x) ^ 2)
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j') {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ f - (dirichletOperator G a ν α')⁻¹ *ᵥ f) ≤
      η * (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) *
        ∑ x ∈ Zplus G Z, siteWeight G x * (decay (agmonRate d / 2) (G.pathDist y x) *
          decay (agmonRate d / 2) (G.pathDist x y')) := by
  classical
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set u' := (dirichletOperator G a ν α')⁻¹ *ᵥ f with hu'
  set g : G.Ω 1 → ℂ := fun i => -(α i - α' i) * u' i with hg
  have hgZ : ∀ i, i ∉ Z → g i = 0 := fun i hi => by simp [hg, hZ i hi]
  rw [green_sub_eq_mulVec G hd hν ha α α' hα hα' f]
  change blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤ _
  conv_lhs => rw [decomp_blocks G Z g hgZ]
  rw [Matrix.mulVec_sum, Finset.mul_sum]
  refine (blockNorm_sum_le G j y _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  obtain ⟨hjx1, hjxk, hxl⟩ := G.layerIndex_spec x.2
  set jx := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hjx
  set P : ℝ := 13 * L / poincareConst d with hP
  have hP0 : 0 ≤ P := by positivity
  set D1 := decay (agmonRate d / 2) (G.pathDist y x) with hD1
  set D2 := decay (agmonRate d / 2) (G.pathDist x y') with hD2
  have hD10 : 0 ≤ D1 := decay_nonneg _ _
  have hD20 : 0 ≤ D2 := decay_nonneg _ _
  set S := Real.sqrt (Green.sqNorm f) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hw0 := siteWeight_nonneg G (x : Torus d (N₀ * L ^ k))
  have hℓ : 0 < ((L : ℝ) ^ jx) ^ 2 := by positivity
  have hη0 : 0 ≤ η / ((L : ℝ) ^ jx) ^ 2 := by
    have := hη x
    rw [G.spacing_eq hjx1 hjxk hxl] at this
    exact (norm_nonneg _).trans this
  rw [Matrix.mulVec_smul]
  -- the smul by a real weight
  rw [blockNorm_smul G j y _ hw0]
  -- bound by the `x → y` block decay
  have h1 := green_blockNorm_le G hd hν ha α hα hϱ hsep hj1 hjk hjx1 hjxk hy hxl
    (f := blockProj G jx x g) (by
      intro i hi
      by_contra hne
      exact hi (by simp [blockProj, hne]))
  -- the size of the restriction of `g`
  have hspace : ∀ i : G.Ω 1, jBlock d L N₀ k jx i = jBlock d L N₀ k jx x →
      G.spacing i = (L : ℝ) ^ jx := by
    intro i hi
    have hil : (i : Torus d (N₀ * L ^ k)) ∈ G.layer jx := (G.mem_layer_iff hjx1 hjxk hi).2 hxl
    exact G.spacing_eq hjx1 hjxk hil
  have h2 : Green.sqNorm (blockProj G jx x g) ≤
      (η / ((L : ℝ) ^ jx) ^ 2) ^ 2 * Green.sqNorm (blockProj G jx x u') := by
    unfold Green.sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : jBlock d L N₀ k jx i = jBlock d L N₀ k jx x
    · simp only [blockProj, hi, ite_true]
      have hb := hη i
      rw [hspace i hi] at hb
      have : ‖g i‖ ≤ η / ((L : ℝ) ^ jx) ^ 2 * ‖u' i‖ := by
        rw [hg]; simp only [norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      calc ‖g i‖ ^ 2 ≤ (η / ((L : ℝ) ^ jx) ^ 2 * ‖u' i‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = _ := by ring
    · simp [blockProj, hi]
  have h3 : blockNorm G jx x g ≤ η / ((L : ℝ) ^ jx) ^ 2 * blockNorm G jx x u' := by
    have e1 : blockNorm G jx x g = Real.sqrt (Green.sqNorm (blockProj G jx x g)) := by
      rw [sqNorm_blockProj, Real.sqrt_sq (blockNorm_nonneg G _ _ _)]
    have e2 : blockNorm G jx x u' = Real.sqrt (Green.sqNorm (blockProj G jx x u')) := by
      rw [sqNorm_blockProj, Real.sqrt_sq (blockNorm_nonneg G _ _ _)]
    rw [e1, e2]
    calc Real.sqrt (Green.sqNorm (blockProj G jx x g))
        ≤ Real.sqrt ((η / ((L : ℝ) ^ jx) ^ 2) ^ 2 * Green.sqNorm (blockProj G jx x u')) :=
          Real.sqrt_le_sqrt h2
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη0]
  have h4 := green_blockNorm_le G hd hν ha α' hα' hϱ hsep hjx1 hjxk hj'1 hj'k hxl hy' hsupp
  have h5 : blockNorm G jx x u' ≤ P * D2 * ((L : ℝ) ^ j') ^ 2 * S := h4
  have h6 : Real.sqrt (Green.sqNorm (blockProj G jx x g)) = blockNorm G jx x g := by
    rw [sqNorm_blockProj, Real.sqrt_sq (blockNorm_nonneg G _ _ _)]
  rw [h6] at h1
  have h7 : blockNorm G jx x g ≤ η / ((L : ℝ) ^ jx) ^ 2 * (P * D2 * ((L : ℝ) ^ j') ^ 2 * S) :=
    h3.trans (mul_le_mul_of_nonneg_left h5 hη0)
  calc siteWeight G x * blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ blockProj G jx x g)
      ≤ siteWeight G x * (P * D1 * ((L : ℝ) ^ jx) ^ 2 * blockNorm G jx x g) :=
        mul_le_mul_of_nonneg_left h1 hw0
    _ ≤ siteWeight G x * (P * D1 * ((L : ℝ) ^ jx) ^ 2 *
          (η / ((L : ℝ) ^ jx) ^ 2 * (P * D2 * ((L : ℝ) ^ j') ^ 2 * S))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h7 (by positivity)) hw0
    _ = _ := by field_simp

end BlockLocality

section Final

variable (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
  (ha : IsAdmissibleWeights k a) (α α' : G.Ω 1 → ℂ)
  (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hα' : ∀ x, ‖α' x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
  (hϱ : 1 < ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
  (hcond : 2 * d * Real.log L ≤ agmonRate d / 6 / 2 * (ϱ - 1))

include hd hν ha hα hα' hϱ hsep hcond in
/-- **G-2(vi), single-variation locality (final form).**  Let `α, α'` lie in the polydisc of
G-1(a), agree off the finite set `Z ⊆ Ω₁`, with `|α(x) - α'(x)| ≤ η ℓ(x)⁻²`.  If `f` is supported
in the block `Δ_{j'}(y')` and `ϱ` is large (`2 d log L ≤ (ε₀/12)(ϱ - 1)`, `L ≤ e^{(ε₀/2)(ϱ-1)}`),
then, with `γ' = ε₀ / 6` (`ε₀ = agmonRate d`), `c = poincareConst d`,

`‖χ_{Δ_j(y)} (G_D(α) - G_D(α')) f‖ ≤ η (13 L / c)² C ℓ_{j'}² ‖f‖
   e^{-γ' d(y,Z)} e^{-γ' d(y',Z)} e^{-γ' d(y,y')}`,

with `C = e^{4 d γ'} · countConst d L γ'` depending only on `d, L, ε₀`; no dependence on `|Z|`,
on the torus or on `k`. -/
theorem green_sub_green_locality (Z : Finset (G.Ω 1)) (hZ : ∀ x, x ∉ Z → α x = α' x) {η : ℝ}
    (hη0 : 0 ≤ η)
    (hη : ∀ x : G.Ω 1, ‖α x - α' x‖ ≤ η / (G.spacing x) ^ 2)
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j') {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    blockNorm G j y ((dirichletOperator G a ν α)⁻¹ *ᵥ f - (dirichletOperator G a ν α')⁻¹ *ᵥ f) ≤
      η * (13 * L / poincareConst d) ^ 2 *
        (Real.exp (agmonRate d / 6 * (4 * d)) * countConst d L (agmonRate d / 6)) *
        ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) *
        (decay (agmonRate d / 6) (G.distSet y Z) * decay (agmonRate d / 6) (G.distSet y' Z) *
          decay (agmonRate d / 6) (G.pathDist y y')) := by
  classical
  have hp0 := poincareConst_pos hd
  have hε := agmonRate_pos hd
  have hyΩ : y ∈ G.Ω 1 := G.layer_subset hj1 hjk hy
  refine (green_sub_green_le_blocksum G hd hν ha α α' hα hα' hϱ.le hsep Z hZ hη hj1 hjk hj'1 hj'k
    hy hy' hsupp).trans ?_
  set K : ℝ := (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f)
    with hK
  have hK0 : 0 ≤ K := by positivity
  set E := Real.exp (agmonRate d / 6 * (4 * d)) with hE
  set Tl := decay (agmonRate d / 6) (G.distSet y Z) * decay (agmonRate d / 6) (G.distSet y' Z) *
    decay (agmonRate d / 6) (G.pathDist y y') with hTl
  have hTl0 : 0 ≤ Tl := by
    rw [hTl]; exact mul_nonneg (mul_nonneg (decay_nonneg _ _) (decay_nonneg _ _)) (decay_nonneg _ _)
  have hterm : ∀ x ∈ Zplus G Z, siteWeight G x * (decay (agmonRate d / 2) (G.pathDist y x) *
      decay (agmonRate d / 2) (G.pathDist x y')) ≤
      E * Tl * (siteWeight G x * decay (agmonRate d / 6) (G.pathDist y x)) := by
    intro x hx
    obtain ⟨z, hzZ, hzx⟩ := (Finset.mem_filter.1 hx).2
    obtain ⟨hx1, hxk, hxl⟩ := G.layerIndex_spec x.2
    have hxz : G.pathDist x z ≤ ENNReal.ofReal (2 * d) :=
      G.pathDist_block_le hx1 hxk hxl hzx
    have hw := siteWeight_nonneg G (x : Torus d (N₀ * L ^ k))
    have hA : G.distSet y Z ≤ G.pathDist y x + ENNReal.ofReal (2 * d) :=
      (G.distSet_le y hzZ).trans ((G.pathDist_triangle y x z).trans (by gcongr))
    have hB : G.distSet y' Z ≤ G.pathDist x y' + ENNReal.ofReal (2 * d) := by
      refine (G.distSet_le y' hzZ).trans ((G.pathDist_triangle y' x z).trans ?_)
      rw [GeneratingSet.pathDist_comm y' x]
      gcongr
    have hsplit := decay_split (c := agmonRate d / 2) (s := 2 * d) (by positivity) (by positivity)
      hA hB (G.pathDist_triangle y x y')
    have e1 : agmonRate d / 2 / 3 = agmonRate d / 6 := by ring
    rw [e1] at hsplit
    calc siteWeight G x * (decay (agmonRate d / 2) (G.pathDist y x) *
          decay (agmonRate d / 2) (G.pathDist x y'))
        ≤ siteWeight G x * (Real.exp (agmonRate d / 6 * (2 * (2 * d))) *
          (decay (agmonRate d / 6) (G.distSet y Z) * decay (agmonRate d / 6) (G.distSet y' Z) *
            decay (agmonRate d / 6) (G.pathDist y y') *
            decay (agmonRate d / 6) (G.pathDist y x))) := mul_le_mul_of_nonneg_left hsplit hw
      _ = _ := by rw [hE, hTl]; ring_nf
  have hsum : ∑ x ∈ Zplus G Z, siteWeight G x * decay (agmonRate d / 6) (G.pathDist y x) ≤
      countConst d L (agmonRate d / 6) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg (siteWeight_nonneg G _) (decay_nonneg _ _))) ?_
    exact sum_siteWeight_decay_le G hϱ (by positivity) hcond hyΩ
  have hE0 : 0 < E := Real.exp_pos _
  calc η * (13 * L / poincareConst d) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) *
        ∑ x ∈ Zplus G Z, siteWeight G x * (decay (agmonRate d / 2) (G.pathDist y x) *
          decay (agmonRate d / 2) (G.pathDist x y'))
      = η * K * ∑ x ∈ Zplus G Z, siteWeight G x * (decay (agmonRate d / 2) (G.pathDist y x) *
          decay (agmonRate d / 2) (G.pathDist x y')) := by rw [hK]; ring
    _ ≤ η * K * ∑ x ∈ Zplus G Z, E * Tl *
          (siteWeight G x * decay (agmonRate d / 6) (G.pathDist y x)) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = η * K * (E * Tl * ∑ x ∈ Zplus G Z, siteWeight G x *
          decay (agmonRate d / 6) (G.pathDist y x)) := by rw [← Finset.mul_sum]
    _ ≤ η * K * (E * Tl * countConst d L (agmonRate d / 6)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity))
          (by positivity)
    _ = _ := by rw [hK]; ring

end Final

section Sup

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **Block `L²` to sup norm.**  For `f` supported in a `j'`-block with `|f| ≤ M`:
`‖f‖ ≤ ℓ_{j'}^{d/2} M`. -/
theorem sqrt_sqNorm_le_of_supp {j' : ℕ} (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)}
    {f : G.Ω 1 → ℂ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ‖f i‖ ≤ M)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y') :
    Real.sqrt (Green.sqNorm f) ≤ Real.sqrt (((L : ℝ) ^ j') ^ d) * M := by
  classical
  have hf : blockProj G j' y' f = f := by
    funext i
    by_cases hi : f i = 0
    · simp [blockProj, hi]
    · simp [blockProj, hsupp i hi]
  have h1 : Green.sqNorm f = blockNorm G j' y' f ^ 2 := by
    rw [← sqNorm_blockProj, hf]
  have h2 : blockNorm G j' y' f ^ 2 ≤ ((L : ℝ) ^ j') ^ d * M ^ 2 := by
    unfold blockNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    calc ∑ x ∈ G.blk j' y', ‖zeroExt (G.Ω 1) f x‖ ^ 2 ≤ ∑ _x ∈ G.blk j' y', M ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          have : ‖zeroExt (G.Ω 1) f x‖ ≤ M := by
            unfold zeroExt; split_ifs
            exacts [hM _, by simpa using hM0]
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = ((L : ℝ) ^ j') ^ d * M ^ 2 := by
          rw [Finset.sum_const, card_blk G j' hj'k, nsmul_eq_mul]; push_cast; ring
  rw [h1]
  calc Real.sqrt (blockNorm G j' y' f ^ 2) ≤ Real.sqrt (((L : ℝ) ^ j') ^ d * M ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]

end Sup

end Balaban.Multiscale
