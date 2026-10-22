/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The exact split of the mass term in Lemma 3.5 (ruling R24, option (d))

The mass term of the action is `(ν/2) ∑ ‖φ - h‖²`.  On the constraint `φ·φ = 1` it is
`ν ∑ (1 - φ·h) + τ(h)` with the constant `τ(h) = (ν/2) ∑ (h·h - 1)`, which does not depend on the
field `φ`.  Splitting it off, `A' = A - τ` and `C₁' = C₁ - ξ₂ τ(h)` (`renormC1'`), the identity of
Lemma 3.5 (i) holds for `A'` and `C₁'` with the same `C₂`:

`β_u A'_u = β A' + β (C₁' - C₂)`   (`lemma35_i_split`, `lemma35_i_split_bg`),

as an instance of `lemma35_i_complete(_bg)`, using `β_u ν_u = β ν (1 + ξ₂)`.  The mass part of `C₁'`
is `ν ξ₂ ∑ (1 - φ·h)`, linear in `h` (`renormC1'_eq_of_unit`).  No landed statement changes.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ} {n : ℕ}

/-- **`τ(h) = (ν/2) ∑_{x ∈ Ω₁} (h_x·h_x - 1)`**, the part of the mass term independent of `φ`
(`h_x·h_x = ∑_i h_{x,i}²`, one `-1` per site). -/
noncomputable def tauMass (G : GeneratingSet d L N₀ K ϱ) (ν : ℝ) {N : ℕ}
    (h : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ((ν : ℂ) / 2) * ∑ x : G.Ω 1, (∑ i, h x i * h x i - 1)

/-- The action without the constant `τ`: `A' = A - τ`. -/
noncomputable def actionCSplit (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (ν : ℝ) {N : ℕ}
    (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  actionC G a ν D φ - tauMass G ν D.h

/-- **`C₁' = C₁ - ξ₂ τ(h)`**. -/
noncomputable def renormC1' (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ) {N : ℕ}
    (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  renormC1 G a ν ξ₂ ξ₃ ζ D φ - (ξ₂ : ℂ) * tauMass G ν D.h

/-- The part of `C₁` without the mass term. -/
noncomputable def renormC1Core (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (ξ₃ ζ : ℝ) {N : ℕ}
    (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ((ξ₃ : ℂ) / 2) * blockPair G a (fun x i => D.Ψ x i - blockAvg G φ x i)
      (fun x i => D.Ψ x i - blockAvg G φ x i) +
    (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * blockPair G a D.Ψ (fun x i => D.Ψ x i - blockAvg G φ x i) +
      ((ζ : ℂ) ^ 2 / 2) * blockPair G a D.Ψ D.Ψ) +
    ((ξ₃ : ℂ) / 2) * bondPair G D.Ψ φ

/-- The linear mass functional `∑_{x ∈ Ω₁} (1 - φ_x·h_x)`. -/
noncomputable def massLin (G : GeneratingSet d L N₀ K ϱ) {N : ℕ}
    (h : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x : G.Ω 1, (1 - ∑ i, φ (x, i) * h x i)

theorem renormC1_eq_core_add (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    renormC1 G a ν ξ₂ ξ₃ ζ D φ =
      renormC1Core G a ξ₃ ζ D φ + ((ν * ξ₂ : ℝ) : ℂ) / 2 * massPair G D.h φ := rfl

/-- `massPair = ∑ (φ·φ - 1) + 2 massLin + ∑ (h·h - 1)`. -/
theorem massPair_eq (h : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) :
    massPair G h φ = ∑ x : G.Ω 1, (∑ i, φ (x, i) * φ (x, i) - 1) + 2 * massLin G h φ +
      ∑ x : G.Ω 1, (∑ i, h x i * h x i - 1) := by
  unfold massPair massLin
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∑ i, (φ (x, i) - h x i) * (φ (x, i) - h x i) =
      ∑ i, φ (x, i) * φ (x, i) - 2 * ∑ i, φ (x, i) * h x i + ∑ i, h x i * h x i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

/-- **The mass part of `C₁'` is linear in `h` on the constraint**: for a unit field `φ`,
`C₁' = C₁^{core} + ν ξ₂ ∑_x (1 - φ_x·h_x)`. -/
theorem renormC1'_eq_of_unit (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (hφ : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1) :
    renormC1' G a ν ξ₂ ξ₃ ζ D φ =
      renormC1Core G a ξ₃ ζ D φ + ((ν * ξ₂ : ℝ) : ℂ) * massLin G D.h φ := by
  unfold renormC1'
  rw [renormC1_eq_core_add, massPair_eq]
  have h0 : ∑ x : G.Ω 1, (∑ i, φ (x, i) * φ (x, i) - 1) = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [hφ x]; ring
  rw [h0]
  unfold tauMass
  push_cast
  ring

variable (hG : IsLevel G n)
include hG

/-- **Lemma 3.5 (i), split form**: `β_u A'_u = β A' + β (C₁' - C₂)`, an instance of
`lemma35_i_complete` (`β_u ν_u = β ν (1 + ξ₂)` is `hν`). -/
theorem lemma35_i_split (a : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) {D Du : BgData G N}
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i)
    {φ φu : G.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hφ : IsEL G a ν D φ α) (hφu : IsEL G a νu Du φu αu) :
    ((β * (1 + ξ₃) : ℝ) : ℂ) * actionCSplit G a νu Du φu = (β : ℂ) * actionCSplit G a ν D φ +
      (β : ℂ) * (renormC1' G a ν ξ₂ ξ₃ ζ D φ - renormC2 G a νu ξ₃ αu φ φu) := by
  have h1 := lemma35_i_complete (β := β) hG a hν hΨ hh hφ hφu
  have hνC : (ν : ℂ) * (1 + (ξ₂ : ℂ)) = (νu : ℂ) * (1 + (ξ₃ : ℂ)) := by exact_mod_cast hν
  have ht : tauMass G νu Du.h = tauMass G νu D.h := by
    unfold tauMass; simp only [hh]
  unfold actionCSplit renormC1' tauMass at *
  rw [ht] at *
  push_cast at h1 ⊢
  linear_combination h1 + (β : ℂ) * (∑ x : G.Ω 1, (∑ i, D.h x i * D.h x i - 1)) / 2 * hνC

/-- **Lemma 3.5 (i), split form, for the landed backgrounds** (`lemma35_i_complete_bg`). -/
theorem lemma35_i_split_bg (a : ℕ → ℝ) {ν νu β ξ₂ ξ₃ ζ : ℝ}
    (hν : ν * (1 + ξ₂) = νu * (1 + ξ₃)) (H : BgHyp d L K ϱ a ν) (Hu : BgHyp d L K ϱ a νu)
    {D Du : BgData G N} (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D)
    (hDu : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) νu Du)
    (hΨ : ∀ x i, Du.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i) (hh : ∀ x i, Du.h x i = D.h x i) :
    ((β * (1 + ξ₃) : ℝ) : ℂ) * actionCSplit G a νu Du (bgFieldC G a νu (bgC0 d L N) Du) =
      (β : ℂ) * actionCSplit G a ν D (bgFieldC G a ν (bgC0 d L N) D) +
      (β : ℂ) * (renormC1' G a ν ξ₂ ξ₃ ζ D (bgFieldC G a ν (bgC0 d L N) D) -
        renormC2 G a νu ξ₃ (bgMultC G a νu (bgC0 d L N) Du) (bgFieldC G a ν (bgC0 d L N) D)
          (bgFieldC G a νu (bgC0 d L N) Du)) :=
  lemma35_i_split hG a hν hΨ hh (theorem72 H hD).2.1.1 (theorem72 Hu hDu).2.1.1

end Balaban.Fluctuation
