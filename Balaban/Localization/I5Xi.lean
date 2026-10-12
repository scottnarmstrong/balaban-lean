/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiComposeField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monotonicity of the spaces `Ξ^c_n(𝔹; σ, ε)` in `σ` and in the level `n`

* `xiC_scale`: `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; 1, σ² ε)` for `σ ≥ 1` (the constant `σ = C₀ θ` of (Ξ3) is
  absorbed in `ε`);
* `xiC_level_mono`: `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_{n'}(𝔹; σ, ε)` for `n' ≤ n` (only the mass condition
  `hnorm` depends on the level).
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem xiBounds_scale {n : ℕ} {σ ε : ℝ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hσ : 1 ≤ σ) (hε : 0 < ε)
    (hb : XiBounds G ν n σ ε D h₀ φ α) : XiBounds G ν n 1 (σ ^ 2 * ε) D h₀ φ α := by
  have hσ0 : 0 < σ := by linarith
  have h1 : σ * ε ≤ 1 * (σ ^ 2 * ε) := by nlinarith [mul_pos hσ0 hε]
  have h2 : σ ^ 2 * ε = 1 ^ 2 * (σ ^ 2 * ε) := by ring
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun z hz z' hz' hadj => ?_,
    fun z => ?_, ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · rw [← h2]; exact hb.lap x hx
  · rw [← h2]; exact hb.mult x
  · rw [← h2]; exact hb.close x hx
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · exact (hb.mass z).trans_le h1
  · refine hb.hnorm.trans_le ?_
    have : σ * ε ≤ 1 * (σ ^ 2 * ε) := h1
    exact pow_le_pow_left₀ (by positivity) this 2

theorem xiCBounds_scale {σ ε : ℝ} {Dr Dc : BgData G N} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ} (hσ : 1 ≤ σ) (hε : 0 < ε)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν 1 (σ ^ 2 * ε) Dr Dc Ψ'' h'' φr φc αr αc := by
  have hσ0 : 0 < σ := by linarith
  have h1 : σ * ε ≤ 1 * (σ ^ 2 * ε) := by nlinarith [mul_pos hσ0 hε]
  have h2 : σ ^ 2 * ε = 1 ^ 2 * (σ ^ 2 * ε) := by ring
  have h3 : ε ≤ σ ^ 2 * ε := by nlinarith [mul_pos hσ0 hε]
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  have hσε : 0 < σ ^ 2 * ε := by positivity
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · rw [← h2]; exact hb.lap x hx
  · rw [← h2]; exact hb.mult x
  · exact (hb.val x).trans_le h3
  · rw [← h2]; exact hb.close x hx
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · have := hb.hAbs x hx
    have e1 : (σ * ε) ^ 2 / ε = σ ^ 2 * ε := by field_simp
    have e2 : (1 * (σ ^ 2 * ε)) ^ 2 / (σ ^ 2 * ε) = σ ^ 2 * ε := by field_simp
    rw [e1] at this
    rw [e2]; exact this
  · refine (hb.hDot x).trans_le ?_
    exact pow_le_pow_left₀ (by positivity) h1 2

/-- `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; 1, σ² ε)` for `σ ≥ 1`. -/
theorem xiC_scale {n : ℕ} {σ ε : ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 1 ≤ σ)
    (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n 1 (σ ^ 2 * ε) Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨-, hε, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  refine ⟨one_pos, by positivity, Dr, Dc, ⟨hXr.1, hXr.2.1, xiBounds_scale hσ hε hXr.2.2⟩, hC, hDcU,
    xiCBounds_scale hσ hε hb⟩

/-- Only the mass condition `hnorm` depends on the level: `Ξ^c_n ⊆ Ξ^c_{n'}` for `n' ≤ n`. -/
theorem xiC_level_mono {n n' : ℕ} (hn : n' ≤ n) (hν : 0 ≤ ν) (hL : 1 ≤ L) {σ ε : ℝ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n' σ ε Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hσ, hε, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  refine ⟨hσ, hε, Dr, Dc, ⟨hXr.1, hXr.2.1, { hXr.2.2 with hnorm := ?_ }⟩, hC, hDcU, hb⟩
  refine lt_of_le_of_lt ?_ hXr.2.2.hnorm
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have : ((L : ℝ) ^ n') ^ 2 ≤ ((L : ℝ) ^ n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hn) 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hν) (abs_nonneg _)

end Balaban.SmallField
