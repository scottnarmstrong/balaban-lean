/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiD2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The properties (D1), (Ξ1), (Ξ4) of the spaces `Ξ`, in the form used by the localization expansion

* `Balaban.SmallField.xiC1`: the constant `C₁(d) = (4d+8)(2d+1)` of (D1) and (Ξ1);
* `Balaban.SmallField.xi_subset_psiTilde`: **(D1)** `Ξ_k(𝔹; σ, ε) ⊆ Ψ̃(𝔹; C₁ σ ε)`;
* `Balaban.SmallField.xiC_subset_psiTildeC`: **(D1)** `Ξ^c_k(𝔹; σ, ε) ⊆ Ψ̃^c(𝔹; C₁ σ ε, ε)`;
* `Balaban.SmallField.xiC_one_subset`: **(Ξ1)** `Ξ^c_k(𝔹; 1, ε') ⊆ Ψ̃^c(𝔹; C₁ ε', C₁ ε')`
  (the notes have `2(d+2)` in place of `C₁(d)`);
* `Balaban.SmallField.xiC_holder`: **(Ξ4)** the Hölder bound I-1(e) for the field of a member of
  `Ξ^c`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- The constant of (D1) and (Ξ1): `C₁(d) = C₄(d) (2d+1) = (4d+8)(2d+1)`. -/
noncomputable def xiC1 (d : ℕ) : ℝ := (4 * d + 8) * (2 * d + 1)

theorem compC4_mul_xiEta (d : ℕ) (σ ε : ℝ) : compC4 d * xiEta d σ ε = xiC1 d * (σ * ε) := by
  unfold compC4 xiEta xiC1; ring

theorem one_le_xiC1 (d : ℕ) : 1 ≤ xiC1 d := by
  unfold xiC1
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- **(D1), real data**: `Ξ_k(𝔹; σ, ε) ⊆ Ψ̃(𝔹; C₁ σ ε)`, for `σ ≤ 1`, `(4d+6)(2d+1) σ ε ≤ 1`. -/
theorem xi_subset_psiTilde (H : BgHyp d L k ϱ a ν) (hσ1 : σ ≤ 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (σ * ε)) ≤ 1)
    (hX : Xi G a ν k σ ε Ψ₀ h₀) : InPsiTilde G ν (xiC1 d * (σ * ε)) Ψ₀ h₀ := by
  obtain ⟨hσ, hε, D, hD⟩ := hX
  have := xi_inPsiTilde H hσ hε hσ1 hsmall hD
  rwa [compC4_mul_xiEta] at this

/-- **(D1), complex data**: `Ξ^c_k(𝔹; σ, ε) ⊆ Ψ̃^c(𝔹; C₁ σ ε, ε)`, for `σ, ε ≤ 1`,
`(4d+6)(2d+1) σ ε ≤ 1`. -/
theorem xiC_subset_psiTildeC (H : BgHyp d L k ϱ a ν) (hσ1 : σ ≤ 1) (hε1 : ε ≤ 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (σ * ε)) ≤ 1)
    (hX : XiC G a ν k σ ε Ψ₀ h₀ Ψ'' h'') :
    InPsiTildeC G ν (xiC1 d * (σ * ε)) ε Ψ₀ h₀ Ψ'' h'' := by
  have hσ := hX.1
  have hε := hX.2.1
  have hc1 := one_le_xiC1 d
  refine xiC_inPsiTildeC H hσ hε hσ1 hε1 hsmall (δ' := xiC1 d * (σ * ε)) (ε'' := ε)
    (by rw [compC4_mul_xiEta]) le_rfl ?_ hX
  have h1 : (σ * ε) ^ 2 / ε ≤ (xiC1 d * (σ * ε)) ^ 2 / ε := by
    refine div_le_div_of_nonneg_right ?_ hε.le
    have := mul_pos hσ hε
    exact pow_le_pow_left₀ this.le (le_mul_of_one_le_left this.le hc1) 2
  exact h1

/-- **(Ξ1)** (P3 (4.36)): `Ξ^c_k(𝔹; 1, ε') ⊆ Ψ̃^c(𝔹; C₁ ε', C₁ ε')`, `C₁ = (4d+8)(2d+1)`
(the notes have `2(d+2)`), for `(4d+6)(2d+1) ε' ≤ 1`. -/
theorem xiC_one_subset (H : BgHyp d L k ϱ a ν) {ε' : ℝ}
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hX : XiC G a ν k 1 ε' Ψ₀ h₀ Ψ'' h'') :
    InPsiTildeC G ν (xiC1 d * ε') (xiC1 d * ε') Ψ₀ h₀ Ψ'' h'' := by
  have hε := hX.2.1
  have hc1 := one_le_xiC1 d
  have hε1 : ε' ≤ 1 := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h6 : 1 ≤ (4 * (d : ℝ) + 6) * (2 * d + 1) := by nlinarith
    calc ε' = 1 * ε' := (one_mul _).symm
      _ ≤ ((4 * (d : ℝ) + 6) * (2 * d + 1)) * ε' := mul_le_mul_of_nonneg_right h6 hε.le
      _ = (4 * d + 6) * ((2 * d + 1) * ε') := by ring
      _ ≤ 1 := hsmall
  have hsm : (4 * d + 6) * xiEta d 1 ε' ≤ 1 := by unfold xiEta; simpa using hsmall
  refine xiC_inPsiTildeC H one_pos hε le_rfl hε1 hsm (δ' := xiC1 d * ε') (ε'' := xiC1 d * ε')
    (by rw [compC4_mul_xiEta, one_mul]) (by nlinarith) ?_ hX
  have hpos : 0 < xiC1 d * ε' := by have := hc1; positivity
  have e1 : (1 * ε') ^ 2 / ε' = ε' := by field_simp
  have e2 : (xiC1 d * ε') ^ 2 / (xiC1 d * ε') = xiC1 d * ε' := by field_simp
  rw [e1, e2]
  nlinarith

/-- **(Ξ4)** (P3 (4.39)-(4.40) via I-1(e)): the Hölder bound for the field of a member of
`Ξ^c_k(𝔹; 1, ε')`.  For every fixed `θ ∈ (0, 1)`, the extension `bgFieldExt` of the small solution
of its datum satisfies `|∂φ|_{(θ), 2-θ} ≤ ((B/θ)(C₃ + (3/2) K₁) + C_H) C₁ ε'` componentwise, with
constants depending on `(d, L)` only (`bgFieldC_holder` with `δ = C₁ ε'`, using (Ξ1)).  This is the
Hölder input of the second-difference bound of (Ξ4); the transport of the bound to the composed
field `ψ(𝔹_j(X), 𝔹_k(X))` is not part of this statement. -/
theorem xiC_holder (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {N k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L k ϱ a ν →
      ∀ {ε' : ℝ}, (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1 → xiC1 d * ε' ≤ bgC1 d L N →
      ∀ {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
        {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ},
      XiC G a ν k 1 ε' Ψ₀ h₀ Ψ'' h'' →
      ∃ Dc : BgData G N, RealizesC Dc Ψ₀ h₀ Ψ'' h'' ∧ ∀ i : Fin N,
        HolderSeminormLE G (fun y => bgFieldExt G a ν (bgC0 d L N) Dc y i) θ (2 - θ)
          (B / θ * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * (xiC1 d * ε')) +
            cHold d L * (xiC1 d * ε')) := by
  obtain ⟨B, hB0, hB⟩ := bgFieldC_holder (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θ hθ0 hθ1 N k N₀ _ ϱ G a ν H ε' hsmall hc1 Ψ₀ h₀ Ψ'' h'' hX
  have hP := xiC_one_subset H hsmall hX
  obtain ⟨-, hε, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  have hd0 : 0 < d := by omega
  have hδ0 : 0 < xiC1 d * ε' := by have := one_le_xiC1 d; positivity
  have hDC : InDomainC G ν (xiC1 d * ε') (xiC1 d * ε') Dc := ⟨Ψ₀, h₀, Ψ'', h'', hP, hC.1, hC.2⟩
  refine ⟨Dc, hC, fun i => ?_⟩
  refine hB hθ0 hθ1 G H hδ0 le_rfl (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc1 ?_ hDC i
  have := H.massLe
  nlinarith [sq_nonneg (xiC1 d * ε')]

end Balaban.SmallField
