/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FarDecay
public import Balaban.Fluctuation.WeightedProp51
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 4.1 without the `WeightedProp51` hypothesis (FLUCTUATION.md §4.1)

`Balaban/Fluctuation/FarDecay.lean` proves Lemma 4.1 conditionally on `WeightedProp51`, which is
not provable as stated: it lacks the defect condition `gdef G φ₀ = 0` on `Ω₁` and its separation
(`GreenSetting`, `agmonRate/4`) is weaker than the separation `OpSetting` (`agmonRate/16`) that the
weighted Green's function bound `Dec2.dirichlet_weighted` needs.  `WeightedProp51S`
(`Balaban/Fluctuation/WeightedProp51.lean`) is the corrected statement and is proved
(`weightedProp51S_exists`).  Here:

* `lemma41_of_EL_S`, `lemma41_S`, `lemma41_domain_S`: the statements of `FarDecay` from
  `WeightedProp51S` (the defect condition is automatic: `φ` solves (EL); the separation is the
  typing premise `Dec2.OpSetting G a ν`);
* `lemma41_uncond`, `lemma41_domain_uncond`: the far-data response with constants `K_w, δ_w`
  depending only on `(d, L, N)`, for `3 ≤ d`, `3 ≤ L`, with no hypothesis on the weighted response.

`WeightedProp51` of `FarDecay.lean` is superseded by `WeightedProp51S`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Lemma 4.1 (far data changes; P3 Prop 2.1 (2.55)--(2.56), P6 (2.13) at `λ = ∞`)**, from the
corrected weighted Proposition 5.1 `WeightedProp51S` (rate `γ_w = gammaW d`), with the separation
`OpSetting` as a typing premise.

`(φ, α)` is the small solution for the datum `D`, `(φu, αu)` for `Du`, `Du.Ψ = D.Ψ + δΨ`,
`Du.h = D.h`, mass `ν`, with `δΨ` supported in the set `W` of sites (blocks and collar sites), and
the hypotheses `(P1)`--`(P4)` of Proposition 5.1 (`Prop51Hyp`, with `f₁ = 0`) hold at the base point.
Then, on `Ω₁`, `|δφ| + ℓ|∂δφ| + ℓ²|Δδφ| + ℓ²|δα| ≤ K_far δ₁ e^{-γ_w d(x, W)}` componentwise,
`K_far = K_w C_F`, `d` the path distance to the `Ω₁`-shadow of `W`. -/
theorem lemma41_of_EL_S {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) {ν : ℝ} {D Du : BgData G N}
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K))
    (hsupp : ∀ y ∉ W, δΨ y = 0)
    (hΨ : ∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsEL G a ν D φ α) (hφu : IsEL G a ν Du φu αu) (hOp : Dec2.OpSetting G a ν)
    (hsmall : Small G (αu - α) (c6 d L N)) {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i)) {δ₀ δ₁ : ℝ}
    (hP : Prop51Hyp G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw) :
    FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁)) (φu - φ) (αu - α) := by
  classical
  have hg : ∀ x : G.Ω 1, gdef G φ₀ x = 0 := fun x => by
    show ∑ i, φ₀ x i * φ₀ x i - 1 = 0
    simp only [hφ₀, hφ.2 x, sub_self]
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
    refine hW G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁ hP hOp hg hδ₀ hδ₁ _
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
theorem lemma41_S {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) {ν c₀ : ℝ} {D Du : BgData G N}
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K))
    (hsupp : ∀ y ∉ W, δΨ y = 0)
    (hΨ : ∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsSmallSolution G a ν c₀ D φ α) (hφu : IsSmallSolution G a ν c₀ Du φu αu)
    (hOp : Dec2.OpSetting G a ν)
    (hc₀ : 2 * c₀ ≤ c6 d L N) {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i)) {δ₀ δ₁ : ℝ}
    (hP : Prop51Hyp G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw) :
    FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁)) (φu - φ) (αu - α) :=
  lemma41_of_EL_S hW a W hsupp hΨ hh hφ.1 hφu.1 hOp (small_sub_of_isSmallSolution hφ hφu hc₀) hφ₀ hP
    hδ₀ hδ₁

/-- **Lemma 4.1 from the data domain**: `D`, `Du` in `Ψ̃^c(δ, ε)`, `Ψ̃^c(δ', ε')` with `δ, δ' ≤ c₁`
(`K₁ δ ≤ δ_*` as in Proposition 5.1), the backgrounds `bgFieldC`, `bgMultC`; `|δΨ| ≤ δ₁ ≤ δ_*`
supported in `W`. -/
theorem lemma41_domain_S {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw) (hd : 0 < d)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L K ϱ a ν)
    (hOp : Dec2.OpSetting G a ν)
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
  exact lemma41_of_EL_S hW a W hsupp hΨ hh hs.1 hs'.1 hOp hsmall (fun x i => by simp [barField]) hP hKw
    hδ₁w


/-- **Lemma 4.1 (far data changes), unconditional**: for `3 ≤ d`, `3 ≤ L` there are
`K_w, δ_w > 0` (depending on `(d, L, N)`) such that, for the small solutions `(φ, α)`, `(φu, αu)` of
(EL) for `D`, `Du = D + δΨ` (same `h`, mass `ν`, `δΨ` supported in `W`), the hypotheses
(P1)--(P4) of Proposition 5.1 at the base point with `δ₀, δ₁ ≤ δ_w`, and the separation of
`OpSetting`, one has on `Ω₁`
`|δφ| + ℓ|∂δφ| + ℓ²|Δδφ| + ℓ²|δα| ≤ K_w C_F δ₁ e^{-γ_w d(x, W)}` (`FarBounds`). -/
theorem lemma41_uncond (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) {ν c₀ : ℝ} {D Du : BgData G N}
        {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K)),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ},
        IsSmallSolution G a ν c₀ D φ α → IsSmallSolution G a ν c₀ Du φu αu →
        Dec2.OpSetting G a ν → 2 * c₀ ≤ c6 d L N →
        ∀ {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}, (∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i)) →
        ∀ {δ₀ δ₁ : ℝ}, Prop51Hyp G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁ → δ₀ ≤ δw → δ₁ ≤ δw →
        FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁)) (φu - φ) (αu - α) := by
  obtain ⟨Kw, δw, hK, hδ, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν c₀ D Du δΨ W hsupp hΨ hh φ φu α αu hφ hφu hOp hc₀ φ₀ hφ₀ δ₀ δ₁ hP hδ₀ hδ₁
  exact lemma41_S hW a W hsupp hΨ hh hφ hφu hOp hc₀ hφ₀ hP hδ₀ hδ₁

/-- **Lemma 4.1 from the data domain, unconditional** (`lemma41_domain_S` with the weighted
response of `weightedProp51S_exists`). -/
theorem lemma41_domain_uncond (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → Dec2.OpSetting G a ν →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K)),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        FarBounds G (shadow G W) (gammaW d) (Kw * (cF d L * δ₁))
          (bgFieldC G a ν (bgC0 d L N) Du - bgFieldC G a ν (bgC0 d L N) D)
          (bgMultC G a ν (bgC0 d L N) Du - bgMultC G a ν (bgC0 d L N) D) := by
  obtain ⟨Kw, δw, hK, hδ, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν H hOp D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu
    hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ
  exact lemma41_domain_S hW (by omega) H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu
    hK1 hKw W hsupp hΨ hh hδ₁0 hδ₁s hδ₁w hdΨ

end Balaban.Fluctuation
