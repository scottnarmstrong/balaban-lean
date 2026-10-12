/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Expansion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Lemma 3.5: the renormalization identity at `λ = ∞` (FLUCTUATION.md §3.6)

Setting: a whole-lattice generating set `G` (`IsLevel G n`), kernel sequence `a` (the free flow, the
same for `(ψ, h)` and `(θ, h)` with `θ = (1 + ζ) ψ`), bilinear (complex) products `actionC`.  Fine
units: the scale-`(k+1)` quantities `a‖·‖²` of the source are the weighted block pairings
`blockPair`, `‖∂φ‖²` is `bondPair`, `‖φ - h‖²` is `massPair`.

* `lemma35_i_complete`, `lemma35_i_nuFree` (and `_bg`, with `φ = bgFieldC`, `αu = bgMultC`):
  `β_u A_u(θ, φ_u) = β A(ψ, φ) + β C^{(k+1)}` with `β_u = β (1 + ξ₃)`, `β_u ν_u = β ν (1 + ξ₂)`
  (`hν : ν (1 + ξ₂) = ν_u (1 + ξ₃)`), `C = C₁ - C₂` (complete, `renormC1`, `renormC2`) resp.
  `C = C₁ - C₂ + C₃` (`ν`-free, `renormC3`);
* `isPerturbed_of_EL`, `lemma35_ii_perturbed`: `(δφ, δα) = (φ_u - φ, α_u - α)` solves the perturbed
  system of BG Proposition 5.1 with base `(φ, α)`, mass `ν_u` (mass `0` in the `ν`-free branch, where
  `f₁ = 0`), lifted data `δΨ = ζ ψ` and `f₁ = (ν_u - ν)(h - φ)`;
* `lemma35_ii_bound`: under the hypotheses of Proposition 5.1, `‖δφ‖_*, |δα|₂ ≤ K₂ δ₁`;
* `lemma35_ii_zero`: `δφ = δα = 0` at `ξ = 0`;
* `lemma35_iii`: `(6.2)` (`composeField`) is linear, so `δψ^{(j)} = composeField(δφ, ζ ψ)`.

Not included: analyticity in `(ψ, h, ξ)` and the explicit constant `3 K₂ ε_{k+1} |ξ|_∞`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ} {n : ℕ}

noncomputable def blockPair (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) {N : ℕ}
    (u v : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) * ∑ i, u x i * v x i

noncomputable def bondPair (G : GeneratingSet d L N₀ K ϱ) {N : ℕ}
    (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
          (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) else 0)

noncomputable def massPair (G : GeneratingSet d L N₀ K ϱ) {N : ℕ}
    (h : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x : G.Ω 1, ∑ i, (φ (x, i) - h x i) * (φ (x, i) - h x i)

theorem actionC_eq_pairs (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν D φ =
      (1 / 2) * blockPair G a (fun x i => D.Ψ x i - blockAvg G φ x i)
        (fun x i => D.Ψ x i - blockAvg G φ x i) +
      (1 / 2) * bondPair G D.Ψ φ + (ν : ℂ) / 2 * massPair G D.h φ := rfl


/-- `C₁` of Lemma 3.5 (i), in fine units. -/
noncomputable def renormC1 (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ) {N : ℕ}
    (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ((ξ₃ : ℂ) / 2) * blockPair G a (fun x i => D.Ψ x i - blockAvg G φ x i)
      (fun x i => D.Ψ x i - blockAvg G φ x i) +
    (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * blockPair G a D.Ψ (fun x i => D.Ψ x i - blockAvg G φ x i) +
      ((ζ : ℂ) ^ 2 / 2) * blockPair G a D.Ψ D.Ψ) +
    ((ξ₃ : ℂ) / 2) * bondPair G D.Ψ φ + ((ν * ξ₂ : ℝ) : ℂ) / 2 * massPair G D.h φ

/-- `C₂` of Lemma 3.5 (i). -/
noncomputable def renormC2 (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (νu ξ₃ : ℝ) {N : ℕ}
    (αu : G.Ω 1 → ℂ) (φ φu : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * (1 + (ξ₃ : ℂ)) * pair G (φu - φ)
    (liftOp N (dirichletOperator G a νu αu) *ᵥ (φu - φ))

/-- `C₃` of Lemma 3.5 (i), ν-free convention. -/
noncomputable def renormC3 (G : GeneratingSet d L N₀ K ϱ) (ν ξ₂ : ℝ) {N : ℕ}
    (D : BgData G N) (φ φu : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ((ν * (1 + ξ₂) : ℝ) : ℂ) * (pair G (φu - φ) (fun p => φ p - D.h p.1 p.2) +
    (1 / 2) * pair G (φu - φ) (φu - φ))

theorem blockPair_expand (a : ℕ → ℝ) (ζ : ℝ) (Ψ B : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    blockPair G a (fun x i => (1 + (ζ : ℂ)) * Ψ x i - B x i) (fun x i => (1 + (ζ : ℂ)) * Ψ x i - B x i) =
      blockPair G a (fun x i => Ψ x i - B x i) (fun x i => Ψ x i - B x i) +
        2 * (ζ : ℂ) * blockPair G a Ψ (fun x i => Ψ x i - B x i) +
        (ζ : ℂ) ^ 2 * blockPair G a Ψ Ψ := by
  unfold blockPair
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem pair_neg_mulVec (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (u : G.Ω 1 × Fin N → ℂ) :
    pair G (-u) ((liftOp N A) *ᵥ (-u)) = pair G u ((liftOp N A) *ᵥ u) := by
  rw [Matrix.mulVec_neg]
  unfold pair
  refine Finset.sum_congr rfl fun p _ => ?_
  simp


theorem bondPair_congr (hG : IsLevel G n) (Ψ Ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) : bondPair G Ψ φ = bondPair G Ψ' φ := by
  unfold bondPair
  simp only [barField_eq_svec hG]

theorem lemma35_i_complete (hG : IsLevel G n) (a : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) {D Du : BgData G N}
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsEL G a ν D φ α) (hφu : IsEL G a νu Du φu αu) :
    ((β * (1 + ξ₃) : ℝ) : ℂ) * actionC G a νu Du φu = (β : ℂ) * actionC G a ν D φ +
      (β : ℂ) * (renormC1 G a ν ξ₂ ξ₃ ζ D φ - renormC2 G a νu ξ₃ αu φ φu) := by
  have h1 := actionC_sub_eq (a := a) (ν := νu) Du hφu (σ := φ) hφ.2
  have e : φ - φu = -(φu - φ) := by abel
  rw [e, pair_neg_mulVec] at h1
  have hAu : actionC G a νu Du φ =
      (1 / 2) * (blockPair G a (fun x i => D.Ψ x i - blockAvg G φ x i)
          (fun x i => D.Ψ x i - blockAvg G φ x i) +
        2 * (ζ : ℂ) * blockPair G a D.Ψ (fun x i => D.Ψ x i - blockAvg G φ x i) +
        (ζ : ℂ) ^ 2 * blockPair G a D.Ψ D.Ψ) +
      (1 / 2) * bondPair G D.Ψ φ + (νu : ℂ) / 2 * massPair G D.h φ := by
    rw [actionC_eq_pairs, ← blockPair_expand, bondPair_congr hG Du.Ψ D.Ψ]
    have : massPair G Du.h φ = massPair G D.h φ := by
      unfold massPair; simp only [hh]
    rw [this]
    simp only [hΨ]
  rw [actionC_eq_pairs a ν D φ]
  unfold renormC1 renormC2
  have hνC : (ν : ℂ) * (1 + (ξ₂ : ℂ)) = (νu : ℂ) * (1 + (ξ₃ : ℂ)) := by exact_mod_cast hν
  rw [hAu] at h1
  push_cast
  linear_combination (-(β * (1 + ξ₃) : ℂ)) * h1 - (β / 2 * massPair G D.h φ) * hνC


theorem massPair_add (h : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ δ : G.Ω 1 × Fin N → ℂ) :
    massPair G h (φ + δ) = massPair G h φ + 2 * pair G δ (fun p => φ p - h p.1 p.2) + pair G δ δ := by
  unfold massPair pair
  simp only [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem lemma35_i_nuFree (hG : IsLevel G n) (a : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) {D Du : BgData G N}
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsEL G a 0 D φ α) (hφu : IsEL G a 0 Du φu αu) :
    ((β * (1 + ξ₃) : ℝ) : ℂ) * actionC G a νu Du φu = (β : ℂ) * actionC G a ν D φ +
      (β : ℂ) * (renormC1 G a ν ξ₂ ξ₃ ζ D φ - renormC2 G a 0 ξ₃ αu φ φu +
        renormC3 G ν ξ₂ D φ φu) := by
  have h1 := actionC_sub_eq (a := a) (ν := 0) Du hφu (σ := φ) hφ.2
  have e : φ - φu = -(φu - φ) := by abel
  rw [e, pair_neg_mulVec] at h1
  have hAu : actionC G a 0 Du φ =
      (1 / 2) * (blockPair G a (fun x i => D.Ψ x i - blockAvg G φ x i)
          (fun x i => D.Ψ x i - blockAvg G φ x i) +
        2 * (ζ : ℂ) * blockPair G a D.Ψ (fun x i => D.Ψ x i - blockAvg G φ x i) +
        (ζ : ℂ) ^ 2 * blockPair G a D.Ψ D.Ψ) +
      (1 / 2) * bondPair G D.Ψ φ := by
    rw [actionC_eq_pairs, ← blockPair_expand, bondPair_congr hG Du.Ψ D.Ψ]
    simp only [hΨ]
    push_cast
    ring
  have hφu' : φu = φ + (φu - φ) := by abel
  have hM : massPair G Du.h φu = massPair G D.h φ +
      2 * pair G (φu - φ) (fun p => φ p - D.h p.1 p.2) + pair G (φu - φ) (φu - φ) := by
    have := massPair_add D.h φ (φu - φ)
    rw [← hφu'] at this
    have e2 : massPair G Du.h φu = massPair G D.h φu := by
      unfold massPair; simp only [hh]
    rw [e2, this]
  have hAu2 : actionC G a νu Du φu = actionC G a 0 Du φu + (νu : ℂ) / 2 * massPair G Du.h φu := by
    rw [actionC_eq_pairs a νu Du φu, actionC_eq_pairs a 0 Du φu]
    push_cast
    ring
  rw [actionC_eq_pairs a ν D φ]
  unfold renormC1 renormC2 renormC3
  have hνC : (ν : ℂ) * (1 + (ξ₂ : ℂ)) = (νu : ℂ) * (1 + (ξ₃ : ℂ)) := by exact_mod_cast hν
  rw [hAu] at h1
  rw [hAu2, hM]
  push_cast
  linear_combination (-(β * (1 + ξ₃) : ℂ)) * h1 -
    (β * (massPair G D.h φ + 2 * pair G (φu - φ) (fun p => φ p - D.h p.1 p.2) +
      pair G (φu - φ) (φu - φ)) / 2) * hνC


theorem qStar_add (a : ℕ → ℝ) (Ψ₁ Ψ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    qStar G a (fun x i => Ψ₁ x i + Ψ₂ x i) = qStar G a Ψ₁ + qStar G a Ψ₂ := by
  funext p
  simp only [qStar, Pi.add_apply]
  ring

theorem boundaryTerm_add (Ψ₁ Ψ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    boundaryTerm G (fun x i => Ψ₁ x i + Ψ₂ x i) = boundaryTerm G Ψ₁ + boundaryTerm G Ψ₂ := by
  funext p
  simp only [boundaryTerm, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs <;> ring

theorem dirichlet_mass_apply (a : ℕ → ℝ) (μ μu : ℝ) (α : G.Ω 1 → ℂ) (w : G.Ω 1 × Fin N → ℂ)
    (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a μu α) *ᵥ w) p =
      (liftOp N (dirichletOperator G a μ α) *ᵥ w) p + ((μu - μ : ℝ) : ℂ) * w p := by
  rw [H_alpha_apply (a := a) (ν := μu) α w p, H_alpha_apply (a := a) (ν := μ) α w p,
    H0_apply (a := a) (ν := μu) w p, H0_apply (a := a) (ν := μ) w p]
  push_cast
  ring

/-- **The perturbed system of BG Proposition 5.1** (mode U).  If `(φ, α)` solves (EL) for the datum
`D` at mass `μ` and `(φu, αu)` solves (EL) for `Du`, `Du.Ψ = D.Ψ + δΨ`, `Du.h = D.h`, at mass `μu`,
then `(φu - φ, αu - α)` solves the perturbed system with base `(φ, α)` (any `φ₀` equal to `φ` on
`Ω₁`), mass `μu`, lifted data `δΨ` and `f₁ = (μu - μ)(h - φ)`. -/
theorem isPerturbed_of_EL (a : ℕ → ℝ) {μ μu : ℝ} {D Du : BgData G N}
    {δΨ : Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hΨ : ∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    {φ₀ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i))
    (hφ : IsEL G a μ D φ α) (hφu : IsEL G a μu Du φu αu) :
    IsPerturbed G a μu α φ₀
      (pertSource G a δΨ (fun p => ((μu - μ : ℝ) : ℂ) * (D.h p.1 p.2 - φ p))) (φu - φ) (αu - α) := by
  refine ⟨?_, ?_⟩
  · funext p
    have e1 := congrFun hφ.1 p
    have e2 := congrFun hφu.1 p
    have hDu : Du.Ψ = fun x i => D.Ψ x i + δΨ x i := by
      funext x i; rw [hΨ]
    have hS : source G a μu Du p = source G a μ D p + qStar G a δΨ p +
        boundaryTerm G δΨ p + ((μu - μ : ℝ) : ℂ) * D.h p.1 p.2 := by
      simp only [source, hDu, qStar_add, boundaryTerm_add, Pi.add_apply, hh]
      push_cast
      ring
    rw [Pi.add_apply, Matrix.mulVec_sub]
    simp only [Pi.sub_apply, pertSource, Pi.add_apply]
    have hA : (liftOp N (dirichletOperator G a μu α) *ᵥ φu) p =
        (liftOp N (dirichletOperator G a μu αu) *ᵥ φu) p - (αu p.1 - α p.1) * φu p := by
      rw [H_alpha_apply (a := a) (ν := μu) α φu p, H_alpha_apply (a := a) (ν := μu) αu φu p]
      ring
    have hB := dirichlet_mass_apply a μ μu α φ p
    rw [hφ₀ p.1 p.2, hA, hB, e1, e2, hS]
    push_cast
    ring
  · intro x
    have := hφu.2 x
    have e : ∀ i, φ₀ (x : Torus d (N₀ * L ^ K)) i + (φu - φ) (x, i) = φu (x, i) := by
      intro i; rw [hφ₀]; simp
    simp only [e]
    exact this

/-- **Lemma 3.5 (ii)**, the system, for `δΨ = ζ ψ` and `φ₀ = svec φ`. -/
theorem lemma35_ii_perturbed (a : ℕ → ℝ) {μ μu ζ : ℝ} {D Du : BgData G N}
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsEL G a μ D φ α) (hφu : IsEL G a μu Du φu αu) :
    IsPerturbed G a μu α (svec G φ)
      (pertSource G a (fun x i => (ζ : ℂ) * D.Ψ x i)
        (fun p => ((μu - μ : ℝ) : ℂ) * (D.h p.1 p.2 - φ p))) (φu - φ) (αu - α) :=
  isPerturbed_of_EL a (fun x i => by rw [hΨ]; ring) hh (fun x i => by rw [svec_of_mem]) hφ hφu

section Compose

variable {ϱ' : ℝ} {G' : GeneratingSet d L N₀ K ϱ'}

theorem barField_add_fun (Ψ₁ Ψ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ₁ φ₂ : G'.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    barField G' (fun y j => Ψ₁ y j + Ψ₂ y j) (φ₁ + φ₂) x i =
      barField G' Ψ₁ φ₁ x i + barField G' Ψ₂ φ₂ x i := by
  unfold barField
  split_ifs <;> simp

theorem composeField_add (a : ℕ → ℝ) (Ψ₁ Ψ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ₁ φ₂ : G'.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    composeField G G' a (φ₁ + φ₂) (fun y j => Ψ₁ y j + Ψ₂ y j) x i =
      composeField G G' a φ₁ Ψ₁ x i + composeField G G' a φ₂ Ψ₂ x i := by
  unfold composeField
  split_ifs with h1 h2
  · have e : (fun y => svec G' (φ₁ + φ₂) y i) = fun y => svec G' φ₁ y i + svec G' φ₂ y i := by
      funext y; exact svec_add (G := G') φ₁ φ₂ y i
    rw [e, blockMean_add, blockMean_add]
    ring
  · exact barField_add_fun Ψ₁ Ψ₂ φ₁ φ₂ x i
  · simp

/-- **Lemma 3.5 (iii)**: with `ψ^{(j)}_{k+1} = composeField(φ, ψ)` and `ψ^{(j)}_{k+1,u} =
composeField(φu, (1+ζ) ψ)`, the difference is `composeField` of `(φu - φ, ζ ψ)`: (6.2) is linear. -/
theorem lemma35_iii (a : ℕ → ℝ) (ζ : ℝ) (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ φu : G'.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    composeField G G' a φu (fun y j => (1 + (ζ : ℂ)) * Ψ y j) x i - composeField G G' a φ Ψ x i =
      composeField G G' a (φu - φ) (fun y j => (ζ : ℂ) * Ψ y j) x i := by
  have h := composeField_add (G := G) a Ψ (fun y j => (ζ : ℂ) * Ψ y j) φ (φu - φ) x i
  have e1 : (fun y j => Ψ y j + (ζ : ℂ) * Ψ y j) = fun y j => (1 + (ζ : ℂ)) * Ψ y j := by
    funext y j; ring
  have e2 : φ + (φu - φ) = φu := by abel
  rw [e1, e2] at h
  rw [h]; ring

end Compose


/-- **Lemma 3.5 (ii), the bound**: under the hypotheses `(P1)`--`(P4)` of BG Proposition 5.1 for the
perturbation of `(φ, α)` (extended to `φ₀`) by the lifted data `δΨ = ζ ψ` and
`f₁ = (μu - μ)(h - φ)`, the difference of the small solutions is the solution of Proposition 5.1,
`‖δφ‖_*, |δα|₂ ≤ K₂ δ₁`. -/
theorem lemma35_ii_bound (hd : 0 < d) (a : ℕ → ℝ) {μ μu ζ c₀ : ℝ} {D Du : BgData G N}
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    {φ₀ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i))
    (hφ : IsSmallSolution G a μ c₀ D φ α) (hφu : IsSmallSolution G a μu c₀ Du φu αu)
    (hc₀ : 2 * c₀ ≤ c6 d L N) {δ₀ δ₁ : ℝ}
    (hP : Prop51Hyp G a μu α φ₀ (fun x i => (ζ : ℂ) * D.Ψ x i)
      (fun p => ((μu - μ : ℝ) : ℂ) * (D.h p.1 p.2 - φ p)) δ₀ δ₁) :
    Small G (αu - α) (cK2 d L N * δ₁) ∧ SupBounds G (φu - φ) (cK2 d L N * δ₁) := by
  obtain ⟨δφ, δα, hpert, hsm, hsup, huniq⟩ := prop51_exists_unique hd hP
  have hper := isPerturbed_of_EL a (δΨ := fun x i => (ζ : ℂ) * D.Ψ x i)
    (fun x i => by rw [hΨ]; ring) hh hφ₀ hφ.1 hφu.1
  have hsmall : Small G (αu - α) (c6 d L N) := by
    intro x
    have h1 := hφ.2 x
    have h2 := hφu.2 x
    simp only [Pi.sub_apply]
    calc G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖αu x - α x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * (‖αu x‖ + ‖α x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ = G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖αu x‖ +
          G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖α x‖ := by ring
      _ ≤ c6 d L N := by linarith
  obtain ⟨e1, e2⟩ := huniq _ _ hper hsmall
  rw [e1, e2]
  exact ⟨hsm, hsup⟩

section Background

/-- **Lemma 3.5 (i), complete convention, for the landed backgrounds**: `φ = bgFieldC` of
`(ψ, h)` at mass `ν`, `φu = bgFieldC`, `αu = bgMultC` of `(θ, h)` at mass `νu`, `θ = (1+ζ)ψ`. -/
theorem lemma35_i_complete_bg (hG : IsLevel G n) (a : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) (H : BgHyp d L K ϱ a ν) (Hu : BgHyp d L K ϱ a νu)
    {D Du : BgData G N} (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D)
    (hDu : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) νu Du)
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i) :
    ((β * (1 + ξ₃) : ℝ) : ℂ) * actionC G a νu Du (bgFieldC G a νu (bgC0 d L N) Du) =
      (β : ℂ) * actionC G a ν D (bgFieldC G a ν (bgC0 d L N) D) +
      (β : ℂ) * (renormC1 G a ν ξ₂ ξ₃ ζ D (bgFieldC G a ν (bgC0 d L N) D) -
        renormC2 G a νu ξ₃ (bgMultC G a νu (bgC0 d L N) Du) (bgFieldC G a ν (bgC0 d L N) D)
          (bgFieldC G a νu (bgC0 d L N) Du)) :=
  lemma35_i_complete hG a hν hΨ hh (theorem72 H hD).2.1.1 (theorem72 Hu hDu).2.1.1

/-- **Lemma 3.5 (i), `ν`-free convention, for the landed backgrounds** (variational mass `0`). -/
theorem lemma35_i_nuFree_bg (hG : IsLevel G n) (a : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) (H : BgHyp d L K ϱ a 0) (Hu : BgHyp d L K ϱ a 0)
    {D Du : BgData G N} (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D)
    (hDu : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 Du)
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i) :
    ((β * (1 + ξ₃) : ℝ) : ℂ) * actionC G a νu Du (bgFieldC G a 0 (bgC0 d L N) Du) =
      (β : ℂ) * actionC G a ν D (bgFieldC G a 0 (bgC0 d L N) D) +
      (β : ℂ) * (renormC1 G a ν ξ₂ ξ₃ ζ D (bgFieldC G a 0 (bgC0 d L N) D) -
        renormC2 G a 0 ξ₃ (bgMultC G a 0 (bgC0 d L N) Du) (bgFieldC G a 0 (bgC0 d L N) D)
          (bgFieldC G a 0 (bgC0 d L N) Du) +
        renormC3 G ν ξ₂ D (bgFieldC G a 0 (bgC0 d L N) D) (bgFieldC G a 0 (bgC0 d L N) Du)) :=
  lemma35_i_nuFree hG a hν hΨ hh (theorem72 H hD).2.1.1 (theorem72 Hu hDu).2.1.1

/-- **Lemma 3.5 (ii), vanishing at `ξ = 0`**: for `ζ = 0` and `νu = ν` the data coincide and so do
the backgrounds, `δφ = 0`, `δα = 0`. -/
theorem lemma35_ii_zero (a : ℕ → ℝ) {ν c₀ : ℝ} {D Du : BgData G N}
    (hΨ : ∀ x i, Du.Ψ x i = (1 + ((0 : ℝ) : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i) :
    bgFieldC G a ν c₀ Du - bgFieldC G a ν c₀ D = 0 ∧
      bgMultC G a ν c₀ Du - bgMultC G a ν c₀ D = 0 := by
  have : Du = D := by
    cases Du with
    | mk Ψu hu hl1 hl2 hz1 hz2 =>
      cases D with
      | mk Ψ h hl1' hl2' hz1' hz2' =>
        have e1 : Ψu = Ψ := by funext x i; simpa using hΨ x i
        have e2 : hu = h := by funext x i; simpa using hh x i
        subst e1 e2
        rfl
  subst this
  simp

end Background

end Balaban.Fluctuation
