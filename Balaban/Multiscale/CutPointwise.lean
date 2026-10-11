/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.CutAgmon
public import Balaban.Multiscale.PointwisePotential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Interior equation of the cut operator (statement NC3 of LOCALIZATION.md §3.1, first step)

At a point `p` of `Ω₁` at which no removed bond ends (`NoCutAt cut p`) the row of the cut matrix
`-Δ_cut + ν + Q* a Q` is the row of the uncut matrix.  Hence the equation `H_cut(α) u = f` at such a
point is the uncut equation (`cutOperator_eq_local`), and the Poisson form
(`laplacian_eq_of_cut`) and the bound (4.4) on its right-hand side (`laplacian_bound_cut`) hold
there verbatim.  These two lemmas are the only places where the landed pointwise development
(`PointwisePotential` and the lemmas that call it) looks at the operator; see the report of the
worker W26 for the points where the rest of the landed argument does not extend.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- No removed bond ends at `p` (neither the forward bonds at `p` nor the forward bonds ending
at `p`). -/
def NoCutAt (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (p : Torus d (N₀ * L ^ k)) : Prop :=
  ∀ μ : Fin d, (p, μ) ∉ cut ∧ (p - Pi.single μ 1, μ) ∉ cut

omit [NeZero N₀] [NeZero L] in
theorem bondVec_apply_eq_zero {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    {p : Torus d (N₀ * L ^ k)} (hc : NoCutAt cut p) {b : Torus d (N₀ * L ^ k) × Fin d}
    (hb : b ∈ cut) : bondVec b p = 0 := by
  obtain ⟨x, μ⟩ := b
  have h1 : p ≠ x := by
    rintro rfl
    exact (hc μ).1 hb
  have h2 : p ≠ x + Pi.single μ 1 := by
    rintro rfl
    exact (hc μ).2 (by simpa using hb)
  simp [bondVec, h1, h2]

/-- At a point with no removed bond the row of the cut Laplacian is the row of the Laplacian. -/
theorem cutLaplacian_mulVec_apply {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    {p : Torus d (N₀ * L ^ k)} (hc : NoCutAt cut p) (ν : ℝ) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (cutLaplacian ν cut *ᵥ φ) p = (latticeLaplacian d (N₀ * L ^ k) ν *ᵥ φ) p := by
  unfold cutLaplacian
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.sum_mulVec, Finset.sum_apply]
  have : ∑ b ∈ cut, (bondMatrix b *ᵥ φ) p = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    unfold bondMatrix
    rw [Matrix.vecMulVec_mulVec]
    simp [bondVec_apply_eq_zero hc hb]
  rw [this, sub_zero]

variable (G : GeneratingSet d L N₀ k ϱ)

/-- At a point with no removed bond the row of the cut matrix is the row of the uncut matrix. -/
theorem cutFullMatrix_mulVec_apply {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    {p : Torus d (N₀ * L ^ k)} (hc : NoCutAt cut p) (a : ℕ → ℝ) (ν : ℝ)
    (ψ : Torus d (N₀ * L ^ k) → ℂ) :
    ((cutFullMatrix G a ν cut).map (algebraMap ℝ ℂ) *ᵥ ψ) p =
      ((fullMatrix G a ν).map (algebraMap ℝ ℂ) *ᵥ ψ) p := by
  apply Complex.ext
  · rw [re_mulVec_map, re_mulVec_map]
    unfold cutFullMatrix fullMatrix
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
      cutLaplacian_mulVec_apply hc]
  · rw [im_mulVec_map, im_mulVec_map]
    unfold cutFullMatrix fullMatrix
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
      cutLaplacian_mulVec_apply hc]

/-- **The interior equation.** At `p ∈ Ω₁` with no removed bond, `H_cut(α) u = f` reads as the
equation `H_D(α) u = f` of the landed `dirichlet_eq`. -/
theorem cutOperator_eq_local {a : ℕ → ℝ} {ν : ℝ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} {α : G.Ω 1 → ℂ} {u f : G.Ω 1 → ℂ}
    (hu : cutOperator G a ν cut α *ᵥ u = f) {p : Torus d (N₀ * L ^ k)} (hc : NoCutAt cut p)
    (hp : p ∈ G.Ω 1) :
    ((fullMatrix G a ν).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p +
      α ⟨p, hp⟩ * u ⟨p, hp⟩ = f ⟨p, hp⟩ := by
  have h := cutOperator_eq G hu ⟨p, hp⟩
  rwa [cutFullMatrix_mulVec_apply G hc] at h

/-- The equation `H_D(α) u = f` rewritten as a Poisson equation at each point of `Ω₁`. -/
theorem laplacian_eq_of_cut (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    {α : G.Ω 1 → ℂ} {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) (hc : NoCutAt cut p) :
    ∑ μ : Fin d, (2 * zeroExt (G.Ω 1) u p -
        zeroExt (G.Ω 1) u (p + Pi.single μ 1) - zeroExt (G.Ω 1) u (p - Pi.single μ 1)) =
      f ⟨p, hp⟩ - ν * u ⟨p, hp⟩ - α ⟨p, hp⟩ * u ⟨p, hp⟩ -
        ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p := by
  have h := cutOperator_eq_local G hu hc hp
  unfold fullMatrix at h
  rw [Matrix.map_add (algebraMap ℝ ℂ) (map_add _), Matrix.add_mulVec, Pi.add_apply,
    latticeLaplacian_mulVec_complex] at h
  have hx : zeroExt (G.Ω 1) u p = u ⟨p, hp⟩ := zeroExt_mem _ _ ⟨p, hp⟩
  rw [hx] at h ⊢
  linear_combination h


/-- **(4.4).** The Poisson-equation right-hand side `g = -Δũ` at `p ∈ Ω₁` is bounded by
`|f̃(p)| + (3 + Λ) ℓ(p)⁻² M` when `‖ũ‖ ≤ M` on the block of `p`. -/
theorem laplacian_bound_cut (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν Λ : ℝ}
    {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (hν : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ Λ) (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f)
    {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) (hc : NoCutAt cut p) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q, jBlock d L N₀ k (G.layerIndex p) q = jBlock d L N₀ k (G.layerIndex p) p →
      ‖zeroExt (G.Ω 1) u q‖ ≤ M) :
    ‖∑ μ : Fin d, (2 * zeroExt (G.Ω 1) u p -
        zeroExt (G.Ω 1) u (p + Pi.single μ 1) - zeroExt (G.Ω 1) u (p - Pi.single μ 1))‖ ≤
      ‖zeroExt (G.Ω 1) f p‖ + (3 + Λ) * ((G.spacing p) ^ 2)⁻¹ * M := by
  rw [laplacian_eq_of_cut G hu hp hc]
  have hspk : G.spacing p ≤ (L : ℝ) ^ k := spacing_le G hp
  have hsp0 : 0 < G.spacing p := spacing_pos G
  set s := G.spacing p with hs
  have hfp : zeroExt (G.Ω 1) f p = f ⟨p, hp⟩ := zeroExt_mem _ _ ⟨p, hp⟩
  have hux : ‖u ⟨p, hp⟩‖ ≤ M := by
    have := hM p rfl
    have e : zeroExt (G.Ω 1) u p = u ⟨p, hp⟩ := zeroExt_mem _ _ ⟨p, hp⟩
    rwa [e] at this
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hν1
  have hν' : ν ≤ Λ * (s ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ν * s ^ 2 ≤ ν * ((L : ℝ) ^ k) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp0.le hspk 2) hν
      _ ≤ Λ := hν1
  have hαx : ‖α ⟨p, hp⟩‖ ≤ (s ^ 2)⁻¹ := by
    refine (hα ⟨p, hp⟩).trans ?_
    have h1 : coerciveConst d ≤ 1 / 4 := by
      unfold coerciveConst; linarith [poincareConst_le_half d]
    have : coerciveConst d / (2 * s ^ 2) ≤ (1 / 4) / (2 * s ^ 2) := by
      gcongr
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (s ^ 2)⁻¹ * (2 * s ^ 2) = 2 := by field_simp
    nlinarith [this]
  have hq := avg_row_bound G ha hp (zeroExt (G.Ω 1) u) hM0 hM
  rw [← hs] at hq
  rw [hfp]
  calc _ ≤ ‖f ⟨p, hp⟩‖ + ‖(ν : ℂ) * u ⟨p, hp⟩‖ + ‖α ⟨p, hp⟩ * u ⟨p, hp⟩‖ +
        ‖((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖f ⟨p, hp⟩‖ + Λ * (s ^ 2)⁻¹ * M + (s ^ 2)⁻¹ * M + 2 * (s ^ 2)⁻¹ * M := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν]
          exact mul_le_mul hν' hux (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          exact mul_le_mul hαx hux (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### The pointwise bound that survives the cut without further work -/

theorem single_le_cutBlockGrad {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (j : ℕ)
    (w : Torus d (N₀ * L ^ k) → ℂ) {x : Torus d (N₀ * L ^ k)} {μ : Fin d} (hμ : (x, μ) ∉ cut) :
    ‖w (x + Pi.single μ 1) - w x‖ ^ 2 ≤ cutBlockGrad G cut j x w := by
  unfold cutBlockGrad
  have hxb : x ∈ G.blk j x := G.mem_blk.2 rfl
  have hnn : ∀ (z : Torus d (N₀ * L ^ k)) (μ' : Fin d),
      0 ≤ (if (z, μ') ∈ cut then (0 : ℝ) else ‖w (z + Pi.single μ' 1) - w z‖ ^ 2) := by
    intro z μ'
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have h3 : (if (x, μ) ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ 1) - w x‖ ^ 2) ≤
      ∑ μ' : Fin d, if (x, μ') ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ' 1) - w x‖ ^ 2 :=
    Finset.single_le_sum (fun μ' _ => hnn x μ') (Finset.mem_univ μ)
  simp only [hμ, ↓reduceIte] at h3
  refine h3.trans ?_
  exact Finset.single_le_sum (f := fun z => ∑ μ' : Fin d,
    if (z, μ') ∈ cut then (0 : ℝ) else ‖w (z + Pi.single μ' 1) - w z‖ ^ 2)
    (fun z _ => Finset.sum_nonneg fun μ' _ => hnn z μ') hxb


/-- **Pointwise bound at a point, from the block `L²` decay (NC2).** For `u = H_cut(α)⁻¹ f`,
`f` supported in the `j'`-block of `y'`, `x` in the layer `j` and a bond `(x, μ)` that is not removed,
`|ũ(x)| + ℓ_j |ũ(x + e_μ) - ũ(x)| ≤ (13 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖_{ℓ²}`
for `0 ≤ t ≤ d(x, y')`.  This is the pointwise statement that follows from NC2 alone (a point is
in its own block); it carries `‖f‖_{ℓ²} ≤ ℓ_{j'}^{d/2} ‖f‖_∞`, i.e. it is NC3 up to the factor
`ℓ_{j'}^{d/2}` of the `L²`-to-sup conversion (the Case 1 bound of the landed Lemma P). -/
theorem cut_pointwise_crude {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) (μ : Fin d) (hμ : (x, μ) ∉ cut) :
    ‖zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) x‖ +
        (L : ℝ) ^ j * ‖zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) x‖ ≤
      13 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
        Real.sqrt (Green.sqNorm f) := by
  have h := green_G2i_cut_green G hcut hd hν ha α hα hj1 hjk hj'1 hj'k hx hy' hsupp ht0 ht hε0
    hε1 hϱ hsep
  set w := zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) with hw
  have hxb : x ∈ G.blk j x := G.mem_blk.2 rfl
  have h1 : ‖w x‖ ≤ Real.sqrt (∑ z ∈ G.blk j x, ‖w z‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (w x))]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun z => ‖w z‖ ^ 2)
      (fun _ _ => sq_nonneg _) hxb)
  have h2 : ‖w (x + Pi.single μ 1) - w x‖ ≤ Real.sqrt (cutBlockGrad G cut j x w) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (single_le_cutBlockGrad G j w hμ)
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ j := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hL]

end Balaban.Multiscale
