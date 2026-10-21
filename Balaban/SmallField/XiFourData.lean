/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiFour
public import Balaban.Localization.I5Chain

/-!
# (Ξ4) at a datum of the chart: the second differences of the composed datum

`composeData_second_diff_of_xiCData`: for a datum `D` of a member of `Ξ^c_K(𝔹'; 1, ε)` and
`𝔹 ≺ 𝔹'` with the scale gap `θ`, the second differences of the field of the composed datum
`composeData 𝔹 𝔹' D` on the plaquettes of a layer of `𝔹` are at most `K_Σ θ^{2-θ'} ε`
(`xiC_second_diff`, whose realization is `D` itself by `BgData.eq_of_realizesC`).  This is the
constant `K₂` of P1 (3.107) at the composed data of a label (M3): with the scale gap of the
composition pair, `θ = L^{j-k}`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization

variable {d L : ℕ} [NeZero L]

theorem xiSigma_nonneg (d L N : ℕ) [NeZero L] {B θh : ℝ} (hB : 0 ≤ B) (hθh : 0 < θh) :
    0 ≤ xiSigma d L N B θh := by
  have h1 := lemma53Const_pos d L
  have h2 := bgK1_pos d L N
  have h3 := cHold_nonneg d L
  have h4 := one_le_xiC1 d
  unfold xiSigma
  positivity

/-- **(Ξ4) at a datum of the chart** (`notes/phase1/SMALLFIELD.md` §1.8, (Σ2); P1 (3.107)).  For a
datum `D` of a member of `Ξ^c_K(𝔹'; 1, ε)`, `𝔹 ≺ 𝔹'` with the scale gap `ℓ ≤ θ ℓ'`
(`0 < θ ≤ 1`) and four cells `x, x + L^n e, x + L^n e', x + L^n (e + e')` of one layer `n` of
`𝔹`, the field `ψ` of the composed datum `composeData 𝔹 𝔹' D` satisfies
`‖ψ(x + e + e') - ψ(x + e) - ψ(x + e') + ψ(x)‖ ≤ K_Σ θ^{2-θ'} ε` for every exponent
`θ' ∈ (0, 1)` (`xiC_second_diff`, at the realization `D`). -/
theorem composeData_second_diff_of_xiCData (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 → ∀ {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ ϱ' : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
      (hq : Precedes G G') {a₁ ν θ ε : ℝ},
      0 < a₁ → BgHyp d L K ϱ' (compWeight L a₁) ν → ScaleGap G G' θ → 0 < θ → θ ≤ 1 →
      (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1 → xiC1 d * ε ≤ bgC1 d L N →
      ∀ D : BgData G' N, XiCData G' (compWeight L a₁) ν K 1 ε D →
      ∀ {n : ℕ}, 1 ≤ n → n ≤ K →
        ∀ (e e' : Fin d) {x : Torus d ((N₁ * L ^ m₁) * L ^ K)}, x ∈ G.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) ∈ G.layer n →
        x + Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) ∈ G.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) +
          Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) ∈ G.layer n →
        ‖(composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ
              (x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) +
                Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) -
            (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D)
              D).Ψ (x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) -
            (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D)
              D).Ψ (x + Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) +
            (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D)
              D).Ψ x‖ ≤
          xiSigma d L N B θh * θ ^ (2 - θh) * ε := by
  obtain ⟨B, hB0, hB⟩ := xiC_second_diff (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N₁ m₁ K N _ ϱ ϱ' G G' hq a₁ ν θ ε ha₁ H hgap hθ0 hθ1 hsm hc1 D hD n hn1 hnK
    e e' x h00 h10 h01 h11
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hD
  have hε : 0 < ε := hX.2.1
  obtain ⟨Dc, hDc, hbd⟩ := hB hθh0 hθh1 G G' ha₁ H hq hgap hθ0 hθ1 hsm hc1 hX
  obtain rfl := BgData.eq_of_realizesC hDc hR
  have hK0 : 0 ≤ xiSigma d L N B θh * θ ^ (2 - θh) * ε :=
    mul_nonneg (mul_nonneg (xiSigma_nonneg d L N hB0 hθh0) (Real.rpow_nonneg hθ0.le _)) hε.le
  refine (pi_norm_le_iff_of_nonneg hK0).2 fun i => ?_
  exact hbd hn1 hnK e e' h00 h10 h01 h11 i

end Balaban.SmallField
