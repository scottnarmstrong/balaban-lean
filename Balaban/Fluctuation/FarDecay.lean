/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormIdentity
public import Balaban.Localization.DecoupledClose
public import Balaban.Localization.DecoupledCube
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 4.1: decay of the response to a far data change (FLUCTUATION.md §4.1)

Conditional on the weighted form of BG Proposition 5.1 (`WeightedProp51`, the open LOC weighted
response), the unique small solution `(δφ, δα)` of the perturbed system of Proposition 5.1 with
lifted data `δΨ` supported in a set `W` satisfies, on `Ω₁`,
`|δφ| + ℓ|∂δφ| + ℓ²|Δδφ| + ℓ²|δα| ≤ K_far δ₁ e^{-γ_w d(x, W)}` (`FarBounds`), `K_far = K_w C_F`.

What is used, exactly:
* `WeightedProp51 d L N γ Kw δw` (hypothesis): for every generating set `G` of `CTorus` type, every
  data of Proposition 5.1 (`Prop51Hyp`, sizes `δ₀, δ₁ ≤ δw`), every weight `w` with
  `IsWeight G γ w`, and every solution `(δφ, δα)` of the perturbed system in the class
  `|δα|₂ ≤ c₆` whose source satisfies `w ℓ² |F_s| ≤ C`: `w ℓ² |δα| ≤ K_w C` and the weighted
  `SupBounds` with `K_w C`.  (In the source: the proof of BG Prop 5.1 verbatim in the weighted
  norms with `dirichlet_weighted`; uniqueness identifies the weighted fixed point.)
* `isWeight_of_dist` (landed): `e^{γ d(·, W)}` and the constant `T` on the unreachable set is a
  weight; `setDist_triangle`, `setDist_of_mem` (landed): the distance to a set;
* `pertSource_bound` (landed): `ℓ² |F_s| ≤ C_F δ₁`; `isPerturbed_of_EL` (`RenormIdentity`):
  `(δφ, δα)` solves the perturbed system; `prop51Hyp_of_bgBounds` (landed) for the domain form.

Convention: `W` is a set of sites (blocks and collar sites); the distance is the path distance
(inside `Ω₁`) to its `Ω₁`-shadow `shadow G W` (the sites of `Ω₁` in `W` or adjacent to `W`), which
is where the source `F_s = Q* a δΨ + 𝔟(δΨ)` lives; `decay γ ⊤ = 0`.

Not included: the decoupled version (LOC I-4a, mode U or P, decoupling vector `s` fixed in the
polydisc), which needs the decoupled form of the weighted response.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Finset


variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- weighted `Small` -/
def SmallW (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (w : CTorus d L N₁ m₁ K → ℝ)
    (δα : G.Ω 1 → ℂ) (r : ℝ) : Prop :=
  ∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖) ≤ r

/-- weighted `SupBounds` -/
structure SupBoundsW (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (w : CTorus d L N₁ m₁ K → ℝ)
    (u : G.Ω 1 × Fin N → ℂ) (V : ℝ) : Prop where
  val : ∀ (x : G.Ω 1) (i : Fin N), w x * ‖u (x, i)‖ ≤ V
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    w x * (G.spacing x * ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖) ≤ V
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    w x * (G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖) ≤ V
  lap : ∀ x ∈ G.Ω 1, ∀ i : Fin N, w x * (G.spacing x ^ 2 * ‖∑ μ : Fin d, (2 * svec G u x i -
    svec G u (x + Pi.single μ 1) i - svec G u (x - Pi.single μ 1) i)‖) ≤ V

/-- The weighted form of BG Proposition 5.1 (open LOC input). -/
def WeightedProp51 (d L N : ℕ) [NeZero L] (γ Kw δw : ℝ) : Prop :=
  ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ)
    (ν : ℝ) (α₀ : G.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) (δ₀ δ₁ : ℝ),
    Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁ → δ₀ ≤ δw → δ₁ ≤ δw →
    ∀ (w : CTorus d L N₁ m₁ K → ℝ), IsWeight G γ w → ∀ C : ℝ, 0 ≤ C →
    (∀ (x : G.Ω 1) (i : Fin N), w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖pertSource G a δΨ f₁ (x, i)‖) ≤ C) →
    ∀ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ), IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ δα →
    Small G δα (c6 d L N) → SmallW G w δα (Kw * C) ∧ SupBoundsW G w δφ (Kw * C)


open Classical in
/-- The `Ω₁`-shadow of a set `W` of sites (blocks and collar sites): the sites of `Ω₁` in `W` or
adjacent to a site of `W`.  The distance `d(x, W)` of Lemma 4.1 is the path distance to this set. -/
noncomputable def shadow (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (W : Finset (CTorus d L N₁ m₁ K)) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => x ∈ G.Ω 1 ∧ (x ∈ W ∨ ∃ y ∈ W, Adj x y)

/-- The bounds (4.1): `|δφ| , ℓ|∂δφ|, ℓ²|Δδφ|, ℓ²|δα| ≤ B e^{-γ d(x, W)}` on `Ω₁`
(componentwise as in `SupBounds`; `decay γ ⊤ = 0`). -/
structure FarBounds (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (W : Finset (CTorus d L N₁ m₁ K))
    (γ B : ℝ) (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) : Prop where
  val : ∀ (x : G.Ω 1) (i : Fin N), ‖δφ (x, i)‖ ≤ B * decay γ (siteSetDist G W x)
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G δφ (x + Pi.single μ 1) i - svec G δφ x i‖ ≤
      B * decay γ (siteSetDist G W x)
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G δφ (x - Pi.single μ 1) i - svec G δφ x i‖ ≤
      B * decay γ (siteSetDist G W x)
  lap : ∀ x ∈ G.Ω 1, ∀ i : Fin N, G.spacing x ^ 2 * ‖∑ μ : Fin d, (2 * svec G δφ x i -
    svec G δφ (x + Pi.single μ 1) i - svec G δφ (x - Pi.single μ 1) i)‖ ≤
      B * decay γ (siteSetDist G W x)
  alpha : ∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖ ≤
    B * decay γ (siteSetDist G W x)

theorem le_mul_decay {γ B v : ℝ} {D : ENNReal} (hv : 0 ≤ v)
    (h : ∀ T : ℝ, 1 ≤ T → (if D = ⊤ then T else Real.exp (γ * D.toReal)) * v ≤ B) :
    v ≤ B * decay γ D := by
  by_cases hD : D = ⊤
  · rw [hD, decay_top, mul_zero]
    by_contra hpos
    push Not at hpos
    have := h (max 1 (B / v + 1)) (le_max_left _ _)
    simp only [hD, ↓reduceIte] at this
    have h2 : (B / v + 1) * v ≤ max 1 (B / v + 1) * v :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hv
    have h3 : (B / v + 1) * v = B + v := by field_simp
    linarith
  · have := h 1 le_rfl
    simp only [hD, ↓reduceIte] at this
    rw [decay_of_ne_top hD]
    have hE : 0 < Real.exp (γ * D.toReal) := Real.exp_pos _
    calc v = Real.exp (-(γ * D.toReal)) * (Real.exp (γ * D.toReal) * v) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp (-(γ * D.toReal)) * B :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = B * Real.exp (-(γ * D.toReal)) := mul_comm _ _

theorem pertSource_support (a : ℕ → ℝ) (W : Finset (CTorus d L N₁ m₁ K))
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hsupp : ∀ y ∉ W, δΨ y = 0) (x : G.Ω 1) (i : Fin N)
    (hx : (x : CTorus d L N₁ m₁ K) ∉ shadow G W) :
    pertSource G a δΨ (fun _ => 0) (x, i) = 0 := by
  classical
  have hxW : (x : CTorus d L N₁ m₁ K) ∉ W := fun h => hx (by simp [shadow, x.2, h])
  have hadj : ∀ y ∈ W, ¬ Adj (x : CTorus d L N₁ m₁ K) y := fun y hy h => hx (by
    simp only [shadow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x.2, Or.inr ⟨y, hy, h⟩⟩)
  have h1 : qStar G a δΨ (x, i) = 0 := by
    simp [qStar, congrFun (hsupp _ hxW) i]
  have h2 : boundaryTerm G δΨ (x, i) = 0 := by
    unfold boundaryTerm
    refine Finset.sum_eq_zero fun μ _ => ?_
    have e1 : (if (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar G then
        δΨ ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i else 0) = 0 := by
      split_ifs
      · by_cases hw : (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ W
        · exact absurd (adj_add_single _ μ) (hadj _ hw)
        · exact congrFun (hsupp _ hw) i
      · rfl
    have e2 : (if (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar G then
        δΨ ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i else 0) = 0 := by
      split_ifs
      · by_cases hw : (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ W
        · exact absurd (adj_sub_single _ μ) (hadj _ hw)
        · exact congrFun (hsupp _ hw) i
      · rfl
    rw [e1, e2, add_zero]
  simp [pertSource, h1, h2]


/-- **Lemma 4.1 (far data changes; P3 Prop 2.1 (2.55)--(2.56), P6 (2.13) at `λ = ∞`)**, conditional
on the weighted form of BG Proposition 5.1 (`WeightedProp51` at the rate `γ_w = gammaW d`; the
open LOC weighted response).

`(φ, α)` is the small solution for the datum `D`, `(φu, αu)` for `Du`, `Du.Ψ = D.Ψ + δΨ`,
`Du.h = D.h`, mass `ν`, with `δΨ` supported in the set `W` of sites (blocks and collar sites), and
the hypotheses `(P1)`--`(P4)` of Proposition 5.1 (`Prop51Hyp`, with `f₁ = 0`) hold at the base point.
Then, on `Ω₁`, `|δφ| + ℓ|∂δφ| + ℓ²|Δδφ| + ℓ²|δα| ≤ K_far δ₁ e^{-γ_w d(x, W)}` componentwise,
`K_far = K_w C_F`, `d` the path distance to the `Ω₁`-shadow of `W`. -/
theorem lemma41_of_EL {Kw δw : ℝ} (hW : WeightedProp51 d L N (gammaW d) Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) {ν : ℝ} {D Du : BgData G N}
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K))
    (hsupp : ∀ y ∉ W, δΨ y = 0)
    (hΨ : ∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsEL G a ν D φ α) (hφu : IsEL G a ν Du φu αu)
    (hsmall : Small G (αu - α) (c6 d L N)) {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i)) {δ₀ δ₁ : ℝ}
    (hP : Prop51Hyp G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw) :
    FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁)) (φu - φ) (αu - α) := by
  classical
  have hd3 : 3 ≤ d := hP.green.hd
  have hγ : 0 ≤ gammaW d := gammaW_nonneg (by omega)
  have hper0 := isPerturbed_of_EL a hΨ hh hφ₀ hφ hφu
  have hf : (fun p : G.Ω 1 × Fin N => ((ν - ν : ℝ) : ℂ) * (D.h p.1 p.2 - φ p)) = fun _ => 0 := by
    funext p; simp
  rw [hf] at hper0
  set Dist := siteSetDist G (shadow G W) with hDist
  have hC : 0 ≤ cF d L * δ₁ := mul_nonneg (cF_pos d L).le hP.δ₁_nn
  have hFs : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖pertSource G a δΨ (fun _ => 0) (x, i)‖ ≤ cF d L * δ₁ :=
    pertSource_bound hP.green hP.δ₁_nn hP.dPsi hP.f₁_bd
  have key : ∀ T : ℝ, 1 ≤ T →
      SmallW G (fun x => if Dist x = ⊤ then T else Real.exp (gammaW d * (Dist x).toReal))
        (αu - α) (Kw * (cF d L * δ₁)) ∧
      SupBoundsW G (fun x => if Dist x = ⊤ then T else Real.exp (gammaW d * (Dist x).toReal))
        (φu - φ) (Kw * (cF d L * δ₁)) := by
    intro T hT
    refine hW G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁ hP hδ₀ hδ₁ _
      (isWeight_of_dist G hγ hT Dist (fun x y => setDist_triangle _ x y)) _ hC ?_ _ _ hper0 hsmall
    intro x i
    by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ shadow G W
    · have h0 : Dist x = 0 := setDist_of_mem _ hx x.2
      have : (if Dist x = ⊤ then T else Real.exp (gammaW d * (Dist x).toReal)) = 1 := by
        rw [h0]; simp
      rw [this, one_mul]
      exact hFs x i
    · rw [pertSource_support a W hsupp x i hx]
      simpa using hC
  have hs : ∀ y : CTorus d L N₁ m₁ K, 0 ≤ G.spacing y := fun y => (spacing_pos G).le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x i
    refine le_mul_decay (norm_nonneg _) fun T hT => ?_
    exact (key T hT).2.val x i
  · intro x hx μ i
    refine le_mul_decay (mul_nonneg (hs x) (norm_nonneg _)) fun T hT => ?_
    exact (key T hT).2.fwd x hx μ i
  · intro x hx μ i
    refine le_mul_decay (mul_nonneg (hs x) (norm_nonneg _)) fun T hT => ?_
    exact (key T hT).2.bwd x hx μ i
  · intro x hx i
    refine le_mul_decay (mul_nonneg (pow_nonneg (hs x) 2) (norm_nonneg _)) fun T hT => ?_
    exact (key T hT).2.lap x hx i
  · intro x
    refine le_mul_decay (mul_nonneg (pow_nonneg (hs x) 2) (norm_nonneg _)) fun T hT => ?_
    exact (key T hT).1 x


/-- **Lemma 4.1**, with the two small solutions `(φ, α)`, `(φu, αu)` of (EL) in the class
`|α|₂ < c₀`, `2 c₀ ≤ c₆`. -/
theorem lemma41 {Kw δw : ℝ} (hW : WeightedProp51 d L N (gammaW d) Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) {ν c₀ : ℝ} {D Du : BgData G N}
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K))
    (hsupp : ∀ y ∉ W, δΨ y = 0)
    (hΨ : ∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsSmallSolution G a ν c₀ D φ α) (hφu : IsSmallSolution G a ν c₀ Du φu αu)
    (hc₀ : 2 * c₀ ≤ c6 d L N) {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i)) {δ₀ δ₁ : ℝ}
    (hP : Prop51Hyp G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw) :
    FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁)) (φu - φ) (αu - α) :=
  lemma41_of_EL hW a W hsupp hΨ hh hφ.1 hφu.1 (small_sub_of_isSmallSolution hφ hφu hc₀) hφ₀ hP
    hδ₀ hδ₁

/-- **Lemma 4.1 from the data domain**: `D`, `Du` in `Ψ̃^c(δ, ε)`, `Ψ̃^c(δ', ε')` with `δ, δ' ≤ c₁`
(`K₁ δ ≤ δ_*` as in Proposition 5.1), the backgrounds `bgFieldC`, `bgMultC`; `|δΨ| ≤ δ₁ ≤ δ_*`
supported in `W`. -/
theorem lemma41_domain {Kw δw : ℝ} (hW : WeightedProp51 d L N (gammaW d) Kw δw) (hd : 0 < d)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L K ϱ a ν)
    {D Du : BgData G N} {δ ε δ' ε' : ℝ}
    (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ bgC1 d L N)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD : InDomainC G ν δ ε D)
    (hδ0' : 0 < δ') (hδε' : δ' ≤ ε') (hε' : ε' ≤ bgC0 d L N) (hδ' : δ' ≤ bgC1 d L N)
    (hνε' : ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2) (hDu : InDomainC G ν δ' ε' Du)
    (hK : bgK1 d L N * δ ≤ deltaStar d L N) (hKw : bgK1 d L N * δ ≤ δw)
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K))
    (hsupp : ∀ y ∉ W, δΨ y = 0)
    (hΨ : ∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {δ₁ : ℝ} (hδ₁0 : 0 ≤ δ₁) (hδ₁s : δ₁ ≤ deltaStar d L N) (hδ₁w : δ₁ ≤ δw)
    (hdΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) :
    FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁))
      (bgFieldC G a ν (bgC0 d L N) Du - bgFieldC G a ν (bgC0 d L N) D)
      (bgMultC G a ν (bgC0 d L N) Du - bgMultC G a ν (bgC0 d L N) D) := by
  have hDU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩
  have hDU' : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Du :=
    ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hDu⟩
  obtain ⟨-, hs, hb⟩ := theorem72 H hDU
  obtain ⟨-, hs', hb'⟩ := theorem72 H hDU'
  have hb1 := hb δ ε hδ0 hδε hε hδ hνε hD
  have hb2 := hb' δ' ε' hδ0' hδε' hε' hδ' hνε' hDu
  obtain ⟨Wd⟩ := DataWit.exists hD
  have hP := prop51Hyp_of_bgBounds H hδ0 hδ Wd hε hs.1.2 hb1 hK hδ₁0 hδ₁s hdΨ
  have hc1 := (bgC1_facts d L N hd hδ).2.2.2
  have hc1' := (bgC1_facts d L N hd hδ').2.2.2
  have hsmall : Small G (bgMultC G a ν (bgC0 d L N) Du - bgMultC G a ν (bgC0 d L N) D)
      (c6 d L N) := by
    intro x
    simp only [Pi.sub_apply]
    have h1 := hb1.alpha x
    have h2 := hb2.alpha x
    have hc6 : bgC0 d L N ≤ c6 d L N := min_le_left _ _
    calc G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖bgMultC G a ν (bgC0 d L N) Du x -
          bgMultC G a ν (bgC0 d L N) D x‖
        ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖bgMultC G a ν (bgC0 d L N) Du x‖ +
          ‖bgMultC G a ν (bgC0 d L N) D x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ c6 d L N := by
          have := hb1.alpha x
          have := hb2.alpha x
          linarith
  exact lemma41_of_EL hW a W hsupp hΨ hh hs.1 hs'.1 hsmall (fun x i => by simp [barField]) hP hKw
    hδ₁w

end Balaban.Fluctuation
