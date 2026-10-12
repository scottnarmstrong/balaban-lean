/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessGauss
public import Balaban.Multiscale.CoercivitySharp
public import Balaban.Background.ExistenceBounds

/-!
# Absorption of the multiplier term (PSIZERO-HESS §5, row 6)

The quadratic form of the Lagrangian expansion, `A(tJv, τ) + ½ ∑ Re α |τ|²`, is at least `½ A(tJv, τ)` once the
multiplier satisfies `ℓ² |α| ≤ θ` with `θ (1 + 1/g) ≤ 1/8`, `g = ½ γ_LF c_D` (`quad_ge_half`).  The ingredients are
the coercivity `W(τ) ≤ 4 A(0, τ)` of the zero datum (`core_real_sharp`), the block triangle inequality
`A(0, τ) ≤ 2 A(tJv, τ) + t² ∑ w |Jv|²` and the Gaussian lower bound `action_top_ge`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset Matrix

section Coerc

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

theorem source_bgZero : source G a 0 (bgZero G N) = 0 := by
  funext p
  simp [source, qStar, bgZero, boundaryTerm]

theorem actionC_bgZero_zero : actionC G a 0 (bgZero G N) 0 = 0 := by
  have hb : barField G (bgZero G N).Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 :=
    barField_zero _ (fun x _ => rfl)
  unfold actionC
  rw [hb, blockAvg_zero]
  simp [bgZero]

/-- The action of the zero datum is the quadratic form of `H_D(0)`: `A(0, τ) = ½ ∑_i Re ⟨τ_i, H₀ τ_i⟩`. -/
theorem action_bgZero_eq {τ : G.Ω 1 × Fin N → ℂ} (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) :
    action G a 0 (bgZero G N) τ =
      1 / 2 * ∑ i, Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i)) := by
  have h := actionC_add (a := a) (ν := 0) (bgZero G N) 0 τ
  rw [zero_add, actionC_bgZero_zero, Matrix.mulVec_zero, source_bgZero, sub_zero, sub_zero] at h
  have hp : pair G τ (0 : G.Ω 1 × Fin N → ℂ) = 0 := by simp [pair]
  rw [hp, add_zero] at h
  have hc := action_cast (a := a) (ν := 0) (bgZero G N) isReal_bgZero hτ
  rw [← hc] at h
  have h2 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h2
  rw [h2]
  have h3 : ((1 / 2 : ℂ) * pair G τ (liftOp N (dirichletOperator G a 0 0) *ᵥ τ)).re =
      1 / 2 * (pair G τ (liftOp N (dirichletOperator G a 0 0) *ᵥ τ)).re := by simp
  rw [h3, pair_re _ hτ]

/-- The weighted square norm `∑_i ‖ℓ⁻¹ τ_i‖²` of a vector field. -/
noncomputable def wsq (G : GeneratingSet d L N₀ k ϱ) (τ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  ∑ i, weightedSqNorm G (fun x => τ (x, i))

theorem wsq_nonneg (τ : G.Ω 1 × Fin N → ℂ) : 0 ≤ wsq G τ :=
  Finset.sum_nonneg fun _ _ => weightedSqNorm_nonneg G _

/-- **Coercivity of the zero datum**: `‖ℓ⁻¹ τ‖² ≤ 4 A(0, τ)`. -/
theorem wsq_le_four_action {τ : G.Ω 1 × Fin N → ℂ} (ha : IsAdmissibleWeights k a)
    (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) : wsq G τ ≤ 4 * action G a 0 (bgZero G N) τ := by
  rw [action_bgZero_eq hτ]
  unfold wsq
  have : ∀ i : Fin N, weightedSqNorm G (fun x => τ (x, i)) ≤
      2 * Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i)) := by
    intro i
    have h := multiscale_coercive_sharp_gen G (a := a) (ν := 0) le_rfl ha (θ := 0) le_rfl 0
      (fun x => by simp) (fun x => τ (x, i))
    have hDE := dirichletEnergy_nonneg G (fun x => τ (x, i))
    linarith
  calc ∑ i, weightedSqNorm G (fun x => τ (x, i))
      ≤ ∑ i, 2 * Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i)) :=
        Finset.sum_le_sum fun i _ => this i
    _ = 4 * (1 / 2 * ∑ i, Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i))) := by
        rw [← Finset.mul_sum]; ring

/-- A small multiplier costs at most `θ ‖ℓ⁻¹ τ‖²`. -/
theorem alpha_term_ge {α : G.Ω 1 → ℂ} {θ : ℝ} (hα : Small G α θ) (τ : G.Ω 1 × Fin N → ℂ) :
    -(θ * wsq G τ) ≤ ∑ x : G.Ω 1, (α x).re * ∑ i, ‖τ (x, i)‖ ^ 2 := by
  have e : -(θ * wsq G τ) = ∑ x : G.Ω 1, (-(θ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) *
      ∑ i, ‖τ (x, i)‖ ^ 2) := by
    unfold wsq weightedSqNorm
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine Finset.sum_le_sum fun x _ => ?_
  have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) := spacing_pos G
  have hre : -(θ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) ≤ (α x).re := by
    have h1 := Complex.abs_re_le_norm (α x)
    have h2 := hα x
    have : ‖α x‖ ≤ θ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith [neg_abs_le (α x).re]
  exact mul_le_mul_of_nonneg_right hre (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- `∑_{x ∈ Ω₁} w_x ‖E(x)‖²`, the block energy of a tangent datum. -/
noncomputable def normSqE (a : ℕ → ℝ) (E : BgData G N) : ℝ :=
  ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2

/-- **The block triangle inequality**: `A(0, τ) ≤ 2 A(tE, τ) + t² ∑ w |E|²`. -/
theorem action_triangle (ha : IsAdmissibleWeights k a) (E : BgData G N)
    (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (hEh : ∀ x, E.h x = 0) (t : ℝ) (τ : G.Ω 1 × Fin N → ℂ) :
    action G a 0 (bgZero G N) τ ≤
      2 * action G a 0 ((bgZero G N).lineAt E (t : ℂ)) τ + t ^ 2 * normSqE a E := by
  have hb := barField_line (bgZero G N) E hE (t : ℂ) τ
  have hw : ∀ x : G.Ω 1, 0 ≤ a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 := by
    intro x
    obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec x.2
    have := (ha _ hn1 hnk).1
    positivity
  unfold action normSqE
  rw [hb]
  simp only [BgData.lineAt, bgZero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
    hEh, mul_zero, sub_zero, zero_sub, norm_neg, zero_div, zero_mul, add_zero]
  have hB : 0 ≤ ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) τ (x + Pi.single μ 1) i -
          barField G 0 τ x i‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => by
      split_ifs <;> positivity
  have hblk : ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖blockAvg G τ x i‖ ^ 2 ≤
      2 * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(t : ℂ) * E.Ψ x i - blockAvg G τ x i‖ ^ 2 +
        2 * (t ^ 2 * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2) := by
    have hi : ∀ (q e : ℂ), ‖q‖ ^ 2 ≤ 2 * ‖(t : ℂ) * e - q‖ ^ 2 + 2 * (t ^ 2 * ‖e‖ ^ 2) := by
      intro q e
      have h1 : ‖q‖ ≤ ‖(t : ℂ) * e - q‖ + ‖(t : ℂ) * e‖ := by
        calc ‖q‖ = ‖(t : ℂ) * e - ((t : ℂ) * e - q)‖ := by ring_nf
          _ ≤ ‖(t : ℂ) * e‖ + ‖(t : ℂ) * e - q‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      have h2 : ‖(t : ℂ) * e‖ ^ 2 = t ^ 2 * ‖e‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith [norm_nonneg q, norm_nonneg ((t : ℂ) * e - q), norm_nonneg ((t : ℂ) * e),
        sq_nonneg (‖(t : ℂ) * e - q‖ - ‖(t : ℂ) * e‖)]
    have hpt : ∀ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖blockAvg G τ x i‖ ^ 2 ≤
        2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(t : ℂ) * E.Ψ x i - blockAvg G τ x i‖ ^ 2) +
        2 * (t ^ 2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2)) := by
      intro x
      have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
        hi (blockAvg G τ x i) (E.Ψ x i)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at this
      have hwx := hw x
      nlinarith [mul_le_mul_of_nonneg_left this hwx]
    calc _ ≤ ∑ x : G.Ω 1, (2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(t : ℂ) * E.Ψ x i - blockAvg G τ x i‖ ^ 2) +
        2 * (t ^ 2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2))) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  linarith

/-- **The block energy of the top tangent datum**: `∑ w |Jv|² = a_k L^{k(d-2)} ‖v‖²`. -/
theorem normSqE_top (hd : 2 ≤ d) (hk : 1 ≤ k) {Z : Finset (Torus d (N₀ * L ^ (k - k)))}
    (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (v : SuppSpace Z N) :
    normSqE a (topTangent G v) = a k * (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 := by
  classical
  set E := topTangent G v with hE
  set H : Torus d (N₀ * L ^ (k - k)) → ℝ := fun z =>
    a k / ((L : ℝ) ^ k) ^ 2 * ∑ i, extSupp Z v z i ^ 2 with hH
  have hpt : ∀ x : Torus d (N₀ * L ^ k), (if x ∈ G.Ω 1 then
      a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 * ∑ i, ‖E.Ψ x i‖ ^ 2 else 0) =
      if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0 := by
    intro x
    by_cases hz : jBlock d L N₀ k k x ∈ Z
    · have hxk : x ∈ G.Ω k := hΩ x hz
      have h1 : x ∈ G.Ω 1 := G.Ω_antitone le_rfl hk (by omega) hxk
      have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl h1)
      have hli : G.layerIndex x = k := G.layerIndex_eq hk le_rfl (G.mem_layer.2 ⟨hxk, by rw [G.top]; simp⟩)
      simp only [h1, hz, ↓reduceIte, hli, hH]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hE, topTangent_Ψ v hds i]
      simp [Complex.norm_real, sq_abs]
    · simp only [hz, ↓reduceIte]
      by_cases h1 : x ∈ G.Ω 1
      · have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl h1)
        have : ∀ i, E.Ψ x i = 0 := fun i => by
          rw [hE, topTangent_Ψ v hds i]; simp [extSupp, hz]
        simp [h1, this]
      · simp [h1]
  have hsum : normSqE a E = ∑ x : Torus d (N₀ * L ^ k), (if x ∈ G.Ω 1 then
      a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 * ∑ i, ‖E.Ψ x i‖ ^ 2 else 0) := by
    unfold normSqE
    rw [Finset.sum_coe_sort (G.Ω 1) (fun x => a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      ∑ i, ‖E.Ψ x i‖ ^ 2), Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum]
  simp only [hpt]
  have hZ : ∀ y ∈ Z, ((Finset.univ.filter fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z).filter
      fun x => jBlock d L N₀ k k x = y).card = (L ^ k) ^ d := by
    intro y hy
    have h := (topLift_block_count hΩ hk (Finset.mem_coe.2 hy)).1
    rw [← h]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hy, h⟩
  calc ∑ x : Torus d (N₀ * L ^ k), (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0)
      = ∑ x ∈ Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z),
          H (jBlock d L N₀ k k x) := by rw [Finset.sum_filter]
    _ = ∑ y ∈ Z, ∑ x ∈ (Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z)).filter
          (fun x => jBlock d L N₀ k k x = y), H (jBlock d L N₀ k k x) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => (Finset.mem_filter.1 hx).2) _).symm
    _ = ∑ y ∈ Z, ((L : ℝ) ^ k) ^ d * H y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
          hZ y hy, nsmul_eq_mul]
        push_cast; ring
    _ = a k * (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 := by
        rw [← Finset.mul_sum]
        have hs : ∑ y ∈ Z, H y = a k / ((L : ℝ) ^ k) ^ 2 * ‖v‖ ^ 2 := by
          rw [hH]
          simp only
          rw [← Finset.mul_sum]
          congr 1
          have e1 : ∑ y ∈ Z, ∑ i, (extSupp Z v y).ofLp i ^ 2 = ∑ y ∈ Z, ‖extSupp Z v y‖ ^ 2 :=
            Finset.sum_congr rfl fun y _ => (sq_norm_euc _).symm
          have e2 : ∑ y ∈ Z, ‖extSupp Z v y‖ ^ 2 = ∑ y, ‖extSupp Z v y‖ ^ 2 :=
            Finset.sum_subset (Finset.subset_univ Z) (fun x _ hx => by simp [extSupp, hx])
          rw [e1, e2, sum_sq_extSupp]
        rw [hs]
        have hL : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
        have hd2 : ((L : ℝ) ^ k) ^ d = ((L : ℝ) ^ k) ^ (d - 2) * ((L : ℝ) ^ k) ^ 2 := by
          rw [← pow_add]; congr 1; omega
        rw [hd2, ← pow_mul]
        field_simp

end Coerc

end Balaban.LargeField
