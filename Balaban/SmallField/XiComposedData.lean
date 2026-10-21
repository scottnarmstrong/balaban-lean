/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSquare
public import Balaban.Localization.I5Chain

/-!
# The composed datum of a chart datum in scaled coordinates

`composeData_scaledPsiC_of_xiCData`: for a datum `D` of a member of `Ξ^c_K(𝔹'; 1, ε₀)` and
`𝔹 ≺ 𝔹'` with the hypotheses of `HypSle` (`L^j ≤ θ L^K`, the layers of `𝔹` at most `j`, the scale
gap and the collar condition), the field and the external field of the composed datum
`composeData 𝔹 𝔹' D` on `Ω₁(𝔹)` are `p + z` and `h₀ + h''` for a witness `(p, h₀, z, h'')` of
`ScaledPsiC 𝔹 ν (C₀ θ) (C₁ ε₀) j` with the sharp square bound
(`xiC_scaledComposition_square_sharp_le_at` at the realization `D`, `BgData.eq_of_realizesC`).
These are the inputs of `ScaledPsiC.dataHypAnisoOn_of_pullback` at the composed data of a label.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization

variable {d L : ℕ} [NeZero L]

/-- **The composed datum in scaled coordinates.**  For a datum `D` of a member of
`Ξ^c_K(𝔹'; 1, ε₀)` and `𝔹 ≺ 𝔹'` with `L^j ≤ θ L^K`, the layers of `𝔹` at most `j`, the scale gap
`θ ∈ (0, 1]` and the collar condition, there is a witness `(p, h₀, z, h'')` of
`ScaledPsiC 𝔹 ν (C₀ θ) (C₁ ε₀) j` whose fields are those of the composed datum on `Ω₁(𝔹)`
(`Ψ = p + z`, `h = h₀ + h''`), with the sharp square bound `‖(p + z)² - p²‖ < (C₀ θ)² C₁ ε₀`. -/
theorem composeData_scaledPsiC_of_xiCData {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ ϱ' : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
    {a₁ ν ε₀ θ : ℝ} {j : ℕ} (H' : BgHyp d L K ϱ' (compWeight L a₁) ν)
    (hq : Precedes G G') (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hjθ : (L : ℝ) ^ j ≤ θ * (L : ℝ) ^ K)
    (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) (hgap : ScaleGap G G' θ)
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * ε₀) ≤ 1)
    (D : BgData G' N) (hD : XiCData G' (compWeight L a₁) ν K 1 ε₀ D) :
    ∃ (p : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (z h'' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ),
      ScaledPsiC G ν (scaledC0 d * θ) (xiC1 d * ε₀) j p h₀ z h'' ∧
      (∀ x ∈ G.Ω 1, ∀ i,
        (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ
          x i = (p x i : ℂ) + z x i) ∧
      (∀ x ∈ G.Ω 1, ∀ i,
        (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).h
          x i = (h₀ i : ℂ) + h'' x i) ∧
      ∀ x ∈ G.Ω 1, ‖∑ i, ((p x i : ℂ) + z x i) * ((p x i : ℂ) + z x i) -
        ∑ i, (p x i : ℂ) * (p x i : ℂ)‖ < (scaledC0 d * θ) ^ 2 * (xiC1 d * ε₀) := by
  obtain ⟨Ψ0, h0, Ψ'', h'', hX, hR⟩ := hD
  obtain ⟨Dc, hDc, φr, hS, -, hsq, hre⟩ :=
    xiC_scaledComposition_square_sharp_le_at H' hq hL ha₁ hθ0 hθ1 hjθ hnj hgap hcol hsmall hX
  obtain rfl := BgData.eq_of_realizesC hDc hR
  refine ⟨reR G G' a₁ φr Ψ0, h0,
    dPsi G G' a₁ φr (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Ψ0 Ψ'', hRes G h'', hS,
    fun x hx i => ?_, fun x hx i => ?_, hsq⟩
  · have hx' : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl (hq.mem_Ω1 hx))
    have e1 : ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) +
        dPsi G G' a₁ φr (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Ψ0 Ψ'' x i =
        ccv G G' a₁ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) Dc) Ψ0 Ψ'' x i := by
      rw [← hre x i]
      simp [dPsi]
    rw [e1]
    simp only [composeData, ccv, compVec, composeField, hx, ↓reduceIte, psiC, hDc.1 x hx' i]
  · have hx' : x ∈ G'.Ω 1 := hq.mem_Ω1 hx
    simp only [composeData, hx, ↓reduceIte, hRes_of_mem h'' hx, hDc.2 x hx' i]

end Balaban.SmallField
