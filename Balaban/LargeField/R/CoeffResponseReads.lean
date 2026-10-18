/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseRespPiece
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The reads of a datum at its complex background (P7 p. 500 (2.11); P6 p. 14 (2.31))

For the datum `D` in the fixed-`h` class domain `Ξ^c_k(𝔹; 1, ε)` (`XiCOneReal`) the reads at the
complex Euler–Lagrange background `φ⁰ = bgFieldC`, at every site `x ∈ Ω₁`, satisfy

* the block read `∑ᵢ |Ψ(x)ᵢ − (Q φ⁰)(x)ᵢ|² ≤ 4 ε²`,
* the forward and backward bond reads `ℓ(x)² ∑ᵢ |∂ φ̄⁰ᵢ|² ≤ 4 ε²`,
* the mass read `∑ᵢ |s̃(φ⁰)(x)ᵢ − h(x)ᵢ|² ≤ 4 ε² / ν`  (`ν > 0`),

all from `XiCOneReal.factors`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  Balaban.SmallField Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}
  {a : ℕ → ℝ} {ν ε : ℝ}

/-- The block read of a datum of `Ξ^c_k(𝔹; 1, ε)` at its background: at most `4 ε²`. -/
theorem blockRead_le (H : BgHyp d L K ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    ∑ j, ‖D.Ψ x j - blockAvg G (bgFieldC G a ν (bgC0 d L N) D) x j‖ ^ 2 ≤ 4 * ε ^ 2 := by
  have h := (XiCOneReal.factors H hε hsm hc1 hD).1 x hx
  rw [← vn_sq]
  nlinarith [vn_nonneg (fun j => D.Ψ x j - blockAvg G (bgFieldC G a ν (bgC0 d L N) D) x j)]

/-- The forward and backward bond reads at the background: `ℓ(x)² ∑ᵢ |∂ φ̄ᵢ|² ≤ 4 ε²`. -/
theorem bondRead_le (H : BgHyp d L K ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1)
    (μ : Fin d) :
    G.spacing x ^ 2 * ∑ j, ‖barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) (x + Pi.single μ 1) j -
      barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) x j‖ ^ 2 ≤ 4 * ε ^ 2 ∧
    G.spacing x ^ 2 * ∑ j, ‖barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) (x - Pi.single μ 1) j -
      barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) x j‖ ^ 2 ≤ 4 * ε ^ 2 := by
  have h := ((XiCOneReal.factors H hε hsm hc1 hD).2.1 x hx μ)
  have hs : 0 < G.spacing x := lt_of_lt_of_le one_pos (one_le_spacing x)
  have key : ∀ v : Fin N → ℂ, vn v < 2 * ε / G.spacing x →
      G.spacing x ^ 2 * ∑ j, ‖v j‖ ^ 2 ≤ 4 * ε ^ 2 := fun v hv => by
    rw [← vn_sq, lt_div_iff₀ hs] at *
    have h0 := vn_nonneg v
    nlinarith [mul_nonneg hs.le h0]
  exact ⟨key _ h.1, key _ h.2⟩

/-- The mass read at the background: `∑ᵢ |s̃(φ⁰)ᵢ − hᵢ|² ≤ 4 ε² / ν` for `ν > 0`. -/
theorem massRead_le (H : BgHyp d L K ϱ a ν) (hν : 0 < ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    ∑ j, ‖svec G (bgFieldC G a ν (bgC0 d L N) D) x j - D.h x j‖ ^ 2 ≤ 4 * ε ^ 2 / ν := by
  have h := (XiCOneReal.factors H hε hsm hc1 hD).2.2.1 x hx
  rw [← vn_sq, le_div_iff₀ hν]
  have h1 : (1 : ℝ) ≤ G.spacing x ^ 2 := one_le_pow₀ (one_le_spacing x)
  have h0 := sq_nonneg (vn (fun j => svec G (bgFieldC G a ν (bgC0 d L N) D) x j - D.h x j))
  nlinarith [mul_nonneg hν.le h0]

end Balaban.LargeField.ActionConv
