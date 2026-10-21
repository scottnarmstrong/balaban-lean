/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgCloseSector

/-!
# The all-good cutoff is one on the small-fluctuation set, from the scale-one cube test

If the coarse field `θ` (= `z₁ψ₁`) passes the cube test `χ₁(□) = 1` of Definition II.3.2 at
tolerance `δ₁` for every cube `□` (`ChiKProp`), then the margins (2.4) of BASE-KERNEL-4 hold for the
chart centre: with `E = K_w c_F (2d+2) K₁ (4 d L δ₀) e^{-γ_w c M₁}` (the closeness of the global
background to the cube-local one, `bgField_close_nested`),

* bond: `|∂e| < (δ₁ + √N E)/L`,
* block: `|θ - Q e| < δ₁ + √N E`,
* site (regime (B)): `√ν |e - h| < δ₁/L + √ν √N E`,

and the all-good cutoff `χ = ∏_c χ'^{(0)}_c` equals one at every chart point of tangent size
`ρ` (`ρ ≤ √β/2`) as soon as `δ₁ ≤ δ₀/2`, `√N E ≤ δ₀/8` and `3 ρ/√β ≤ δ₀/4`
(`baseSectorCubeProduct_eq_one_of_chi1`). No constant depends on the number of fluctuation steps
and nothing grows with `L`: the margins are the `ℓ`-scaled gradient tolerance `δ₁/L` of `Reg`
(`GradClose`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.LargeField

variable {d L : ℕ} [NeZero L]

/-- The numerical inequalities of the margins. -/
theorem margins_arith {δ₀ δ₁ E s ρβ ν L' : ℝ} (hδ : 0 < δ₀) (hL : 3 ≤ L') (_hδ₁0 : 0 ≤ δ₁)
    (hδ₁ : δ₁ ≤ δ₀ / 2) (hE0 : 0 ≤ E) (hE : s * E ≤ δ₀ / 8) (hs0 : 0 ≤ s) (hρ0 : 0 ≤ ρβ)
    (hρ : 3 * ρβ ≤ δ₀ / 4) (hν0 : 0 ≤ ν) (hν : ν * L' ^ 2 ≤ 1) :
    (δ₁ + s * E) / L' < δ₀ - 2 * (3 / 2 * ρβ) ∧
      δ₁ + s * E < 2 * δ₀ - 3 / 2 * ρβ ∧
      δ₁ / L' + Real.sqrt ν * (s * E) < δ₀ - Real.sqrt ν * (3 / 2 * ρβ) := by
  have hL0 : 0 < L' := by linarith
  have hsν : Real.sqrt ν ≤ 1 / L' := by
    rw [le_div_iff₀ hL0]
    calc Real.sqrt ν * L' = Real.sqrt (ν * L' ^ 2) := by
          rw [Real.sqrt_mul hν0, Real.sqrt_sq hL0.le]
      _ ≤ 1 := by rw [Real.sqrt_le_one]; exact hν
  have hs1 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg _
  have hsE : 0 ≤ s * E := mul_nonneg hs0 hE0
  have h1 : (δ₁ + s * E) / L' ≤ (δ₀ / 2 + δ₀ / 8) / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · have h3 : Real.sqrt ν * (s * E) ≤ (1 / L') * (δ₀ / 8) :=
      mul_le_mul hsν hE (hsE) (by positivity)
    have h4 : Real.sqrt ν * (3 / 2 * ρβ) ≤ (1 / L') * (δ₀ / 8) := by
      refine mul_le_mul hsν (by linarith) (by positivity) (by positivity)
    have h5 : δ₁ / L' ≤ (δ₀ / 2) / 3 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
    have h6 : (1 / L') * (δ₀ / 8) ≤ (1 / 3) * (δ₀ / 8) :=
      mul_le_mul_of_nonneg_right (by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith) (by positivity)
    linarith

open Classical in
/-- **The all-good cutoff is one at the small-fluctuation chart points, from the scale-one cube
test** (BASE-KERNEL-4 Lemma 2.2 with margins from `Reg`). -/
theorem baseSectorCubeProduct_eq_one_of_chi1 {N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {n M1 N₁ m₁ c n' : ℕ} [NeZero n] [NeZero M1] [NeZero N₁] [NeZero n']
        (hn : 1 * n = M1 * N₁) (_hM1 : M1 = L ^ m₁) (_hm : N₁ * L ^ (1 - 1) = c * n')
        {ϱ a₁ ν δ₀ δ₁ β ρ : ℝ} (_ha₁ : 0 < a₁)
        (regimeB : Prop)
        (_hδ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (_hh : ‖h‖ = 1)
        (_H : BgHyp d L 1 ϱ (compWeight L a₁) (if regimeB then ν else 0))
        (_hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N) {BG κ : ℝ}
        (_hΛ7 : 4 * d * L * δ₀ ≤ c7 d L N BG κ)
        (_H0 : BgHyp d L 1 (minSep L M1) (compWeight L a₁) (if regimeB then ν else 0))
        (_hν : 0 ≤ ν) (_hνle : (if regimeB then ν else 0) * ((L : ℝ) ^ 1) ^ 2 ≤ 1)
        (_hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
        (_hKs : bgK1 d L N * bgC1 d L N ≤ min (deltaStar d L N) δw)
        (_hδc : 4 * d * L * δ₀ ≤ thm73C1 d L N)
        (_hε' : 4 * d * L * δ₀ ≤ bgC0 d L N)
        (_hK1' : (2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)) ≤ deltaStar d L N)
        (_hKw' : (2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)) ≤ δw)
        (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ₀ φ : CfgT d N L n)
        (_hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0)
        (_hχ : ∀ y0 : Torus d n', ChiKProp (compWeight L a₁) (if regimeB then ν else 0) δ₁
          (fun i => h i) c n' y0
          (show BlockCfg d (M1 * N₁) L 1 1 N from fun y i => baseSectorTheta θ (castCoarse hn y) i))
        (_hβ : 0 < β) (w : Config (Torus d (L * n)) N) (_hρ0 : 0 ≤ ρ) (_hρ : ρ ≤ Real.sqrt β / 2)
        (_hwρ : ∀ x, ‖w x‖ ≤ ρ)
        (_hφ : ∀ y, (φ y : EuclideanSpace ℝ (Fin N)) =
          chartPoint β (baseSectorCenter ϱ (compWeight L a₁) regimeB ν h θ) w y)
        (_hδ₁0 : 0 ≤ δ₁) (_hδ₁ : δ₁ ≤ δ₀ / 2)
        (_hE : Real.sqrt N * (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)))) *
          Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ)))) ≤ δ₀ / 8)
        (_hρ' : 3 * (ρ / Real.sqrt β) ≤ δ₀ / 4),
        baseSectorCubeProduct regimeB ν δ₀ h θ φ = 1 := by
  obtain ⟨Kw, δw, hK, hδw, hsm⟩ := sector_bond_margin (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro n M1 N₁ m₁ c n' _ _ _ _ hn hM1 hm ϱ a₁ ν δ₀ δ₁ β ρ ha₁ regimeB hδ h hh H hΛ1 BG κ hΛ7 H0 hν
    hνle hsep hKs hδc hε' hK1' hKw' θ φ₀ φ hp hχ hβ w hρ0 hρ hwρ hφ hδ₁0 hδ₁ hE hρ'
  obtain ⟨hbond, hblock, hsite⟩ := hsm hn hM1 hm ha₁ (compWeight L a₁) rfl regimeB hδ h hh H hΛ1 hΛ7
    H0 (by by_cases hB : regimeB <;> simp [hB, hν]) hνle hsep hKs hδc hε' hK1' hKw' θ φ₀ hp hχ
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hE0 : 0 ≤ Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)))) *
      Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ))) := by
    have := bgK1_pos d L N
    have := cF_pos d L
    positivity
  have ha := margins_arith (δ₀ := δ₀) (δ₁ := δ₁) (s := Real.sqrt N) (ρβ := ρ / Real.sqrt β)
    (ν := if regimeB then ν else 0) (L' := L) hδ hL3 hδ₁0 hδ₁ hE0 hE (Real.sqrt_nonneg _)
    (div_nonneg hρ0 (Real.sqrt_nonneg _)) hρ' (by by_cases hB : regimeB <;> simp [hB, hν]) (by simpa using hνle)
  have he := baseSectorCenter_unit ϱ (compWeight L a₁) regimeB ν h hh H θ
  refine baseSectorCubeProduct_eq_one_of_chart hβ hν h θ φ _ w he hρ hwρ hφ
    (fun y => lt_of_lt_of_le (hblock y) ?_) (fun x μ' => lt_of_lt_of_le (hbond x μ') ?_) ?_
  · exact ha.2.1.le
  · exact ha.1.le
  · intro hB x
    by_cases hνpos : 0 < ν
    · have := hsite (by simpa [hB] using hνpos) x
      have hμ : (if regimeB then ν else 0) = ν := by simp [hB]
      obtain ⟨-, -, ha3⟩ := ha
      rw [hμ] at this ha3
      exact lt_of_lt_of_le this ha3.le
    · have hν0 : ν = 0 := le_antisymm (not_lt.1 hνpos) hν
      subst hν0
      simp only [Real.sqrt_zero, zero_mul, sub_zero]
      exact hδ

end Balaban.LargeField.Base
