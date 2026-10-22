/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
public import Balaban.Background.CompositionDomain

/-!
# The renormalized datum stays in the real data domain

The renormalization of a step replaces the lifted field `Ψ` by `(1 + ζ) Ψ` and the mass `ν` by
`ν_u = ν (1 + t₂)/(1 + t₃)` (P4 (4.1)).  For real `ζ` the new datum is a real datum, and the conditions
(R1)-(R4) of the real domain `Ψ̃(𝔹_k; δ)` are conditions on the data, not on the solution of the
variational problem:

* (R1) and (R2) scale with `|1 + ζ|` and `(1 + ζ)²`; (R3) is invariant under the scaling
  (`(Ψ · h)/|Ψ|` does not change), and (R3), (R4) change only through the mass factor `ν_u/ν`.

`InPsiTilde.scale` and `InDomainR.scale`: the scaled datum is in the real domain with parameter
`δ' = 2 δ + 3 |ζ|` (for `|ζ| ≤ 1/256`, `ν_u ≤ (17/15) ν`); `isSmallSolution_of_inDomainR`: for a datum
in the real domain with `2 δ' ≤ c₁` the background `(bgField, bgMult)` is a small solution with
`c₀ = c₆/2`, the form that the uniqueness of `IsRenSol.eq_bg` uses.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- **Scaling the real datum.**  Real domain conditions of `(1 + ζ) Ψ` at the mass `ν_u ≤ (17/15) ν`. -/
theorem InPsiTilde.scale {ν νu δ δ' ζ : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h : Fin N → ℝ} (hP : InPsiTilde G ν δ Ψ h) (hζ : |ζ| ≤ 1 / 256)
    (hle : νu ≤ 17 / 15 * ν) (hδ : 0 < δ) (hδ' : 2 * δ + 3 * |ζ| ≤ δ') :
    InPsiTilde G νu δ' (fun x i => (1 + ζ) * Ψ x i) h := by
  have hζ1 := abs_le.mp hζ
  have hu0 : 0 < 1 + ζ := by linarith
  have hu1 : 1 + ζ ≤ 257 / 256 := by linarith
  have hδ'2 : 2 * δ ≤ δ' := by linarith [abs_nonneg ζ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn1 hnk x hx x' hx'
    funext i
    simp only [hP.layerConst n hn1 hnk x hx x' hx']
  · intro x x' hxx
    have e : (fun i => (1 + ζ) * Ψ x i - (1 + ζ) * Ψ x' i) =
        fun i => (1 + ζ) * (Ψ x i - Ψ x' i) := by funext i; ring
    rw [e, rn_smul, abs_of_pos hu0]
    have := hP.r1 x x' hxx
    have h2 : (1 + ζ) * rn (fun i => Ψ x i - Ψ x' i) < (1 + ζ) * δ :=
      mul_lt_mul_of_pos_left this hu0
    nlinarith [abs_nonneg ζ]
  · intro x hx
    have hS : ∑ i, ((1 + ζ) * Ψ x i) ^ 2 = (1 + ζ) ^ 2 * ∑ i, Ψ x i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hS]
    have h1 := hP.r2 x hx
    set S := ∑ i, Ψ x i ^ 2
    have e : (1 + ζ) ^ 2 * S - 1 = (1 + ζ) ^ 2 * (S - 1) + ζ * (2 + ζ) := by ring
    rw [e]
    have hb1 : |ζ * (2 + ζ)| ≤ 3 * |ζ| := by
      rw [abs_mul]
      have : |2 + ζ| ≤ 3 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg ζ]
    have hb2 : |(1 + ζ) ^ 2 * (S - 1)| ≤ 2 * δ := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have : (1 + ζ) ^ 2 ≤ 2 := by nlinarith
      nlinarith [abs_nonneg (S - 1)]
    calc |(1 + ζ) ^ 2 * (S - 1) + ζ * (2 + ζ)| ≤ |(1 + ζ) ^ 2 * (S - 1)| + |ζ * (2 + ζ)| :=
          abs_add_le _ _
      _ < δ' := by
        have hlt : |(1 + ζ) ^ 2 * (S - 1)| < 2 * δ := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          have : (1 + ζ) ^ 2 ≤ 2 := by nlinarith
          have h3 : (1 + ζ) ^ 2 * |S - 1| ≤ 2 * |S - 1| := by
            nlinarith [abs_nonneg (S - 1)]
          nlinarith
        linarith
  · intro x hx
    have hr : rn (fun i => (1 + ζ) * Ψ x i) = (1 + ζ) * rn (Ψ x) := by
      rw [rn_smul, abs_of_pos hu0]
    have hs : ∑ i, (1 + ζ) * Ψ x i * h i = (1 + ζ) * ∑ i, Ψ x i * h i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hr, hs, mul_div_mul_left _ _ hu0.ne']
    have h1 := hP.r3 x hx
    set t := |1 - (∑ i, Ψ x i * h i) / rn (Ψ x)|
    have ht : 0 ≤ t := abs_nonneg _
    set c := ((L : ℝ) ^ G.layerIndex x) ^ 2
    have hc : 0 ≤ c := by positivity
    calc νu * c * t ≤ 17 / 15 * ν * c * t := by
          have : νu * c ≤ 17 / 15 * ν * c := mul_le_mul_of_nonneg_right hle hc
          exact mul_le_mul_of_nonneg_right this ht
      _ = 17 / 15 * (ν * c * t) := by ring
      _ < 17 / 15 * δ ^ 2 := by nlinarith
      _ ≤ δ' ^ 2 := by nlinarith
  · have h1 := hP.r4
    set t := |∑ i, h i ^ 2 - 1|
    have ht : 0 ≤ t := abs_nonneg _
    set c := ((L : ℝ) ^ k) ^ 2
    have hc : 0 ≤ c := by positivity
    calc νu * c * t ≤ 17 / 15 * ν * c * t := by
          have : νu * c ≤ 17 / 15 * ν * c := mul_le_mul_of_nonneg_right hle hc
          exact mul_le_mul_of_nonneg_right this ht
      _ = 17 / 15 * (ν * c * t) := by ring
      _ < 17 / 15 * δ ^ 2 := by nlinarith
      _ ≤ δ' ^ 2 := by nlinarith

/-- **The renormalized datum is in the real domain.**  `D'` has the lifted field `(1 + ζ) Ψ` and the
same external field. -/
theorem InDomainR.scale {ν νu δ δ' ζ : ℝ} {D D' : BgData G N} (hD : InDomainR G ν δ D)
    (hΨ : ∀ x ∈ dataSites G, ∀ i, D'.Ψ x i = (1 + (ζ : ℂ)) * D.Ψ x i)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D'.h x i = D.h x i) (hζ : |ζ| ≤ 1 / 256)
    (hle : νu ≤ 17 / 15 * ν) (hδ : 0 < δ) (hδ' : 2 * δ + 3 * |ζ| ≤ δ') :
    InDomainR G νu δ' D' := by
  obtain ⟨Ψ, h, hP, hΨ0, hh0⟩ := hD
  refine ⟨fun x i => (1 + ζ) * Ψ x i, h, hP.scale hζ hle hδ hδ', fun x hx i => ?_,
    fun x hx i => ?_⟩
  · rw [hΨ x hx i, hΨ0 x hx i]; push_cast; ring
  · rw [hh x hx i, hh0 x hx i]

/-- **The background of a datum in the real domain is a small solution at `c₀ = c₆/2`.**  For
`0 < δ'`, `2 δ' ≤ c₁`, `D'` in the real domain with parameter `δ'`: `(bgField, bgMult)` solves (EL) and
`ℓ² |α| < c₆/2`; this is the uniqueness class of `IsRenSol.eq_bg`. -/
theorem isSmallSolution_of_inDomainR {a : ℕ → ℝ} {νu δ' : ℝ} (H : BgHyp d L k ϱ a νu)
    {D' : BgData G N} (hD' : InDomainR G νu δ' D') (hδ0 : 0 < δ')
    (hδc : 2 * δ' ≤ bgC1 d L N) :
    IsSmallSolution G a νu (c6 d L N / 2) D' (bgField G a νu D') (bgMult G a νu D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hU : InUnionDomainR G (bgC1 d L N) νu D' := ⟨δ', hδ0, by linarith, hD'⟩
  have h71 := theorem71 H hU
  have hb := h71.2.2.2.2 δ' hδ0 (by linarith) hD'
  refine ⟨h71.2.2.1.1, fun x => ?_⟩
  have h1 := hb.alpha x
  have h2 := (bgC1_facts d L N hd0 (δ := 2 * δ') hδc).2.2.2
  have h0 := bgC0_pos d L N hd0
  have h6 := bgC0_le_c6 d L N
  nlinarith [bgK1_pos d L N]

end Balaban.Background
