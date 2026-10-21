/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireStep
public import Balaban.Fluctuation.FarDecayUncond

/-!
# Closeness of the global background and the background of a nested generating set

Let `G₀ ≺ G₁` be nested generating sets at level `k + 1` (for the first step `k = 0`; `G₁` the
global set, `G₀ = G_1(□) = genCube □` the cube-local one), `D'` a datum of `G₁` in the complex domain
`𝒟` with parameter `δ'`, and `D` a datum of `G₀` agreeing with `D'` on the data sites of `G₀`
(for the cube, `D` is the lift of the coarse field `ψ₁`). By Theorem 7.3 the background of `G₁`
restricted to `Ω₁(G₀)` is the background of `G₀` for the composed datum `Du`, and `Du - D` is a
change `δΨ` vanishing where the layers of `G₀` and `G₁` agree (LFR Lemma II.2.5 (c)), of size
`≤ (2d + 2) K₁ δ'`. The weighted perturbation theorem (Lemma 4.1) then gives the bounds

`|δφ(x)|, ℓ|∂δφ(x)|, ℓ²|Δδφ(x)|, ℓ²|δα(x)| ≤ K_w c_F (2d + 2) K₁ δ' e^{-γ_w dist(x, shadow W)}`

for the difference `δφ = φ(G₀; Du) - φ(G₀; D)` of the two backgrounds of `G₀`, where `W` is the set
of sites where the layers disagree (`bgField_close_nested`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

variable {d L : ℕ} [NeZero L]

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.Fluctuation
  Balaban.LargeField

open Classical in
/-- **Closeness of the background of a nested generating set to the restriction of the global
background** (Theorem 7.3 and the weighted Lemma 4.1). -/
theorem bgField_close_nested {N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ0 ϱ1 : ℝ}
        {G0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ0}
        {G1 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ1} {a₁ ν δ ε δ' ε' : ℝ},
        0 < a₁ →
        BgHyp d L (k + 1) ϱ0 (compWeight L a₁) ν → BgHyp d L (k + 1) ϱ1 (compWeight L a₁) ν →
        Dec2.OpSetting G0 (compWeight L a₁) ν → ∀ (hprec : Precedes G0 G1) {D' : BgData G1 N},
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ thm73C1 d L N →
        ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G1 ν δ' ε' D' →
        ∀ {D : BgData G0 N}, (∀ x ∈ dataSites G0, D.Ψ x = D'.Ψ x) →
        (∀ x ∈ G0.Ω 1, D.h x = D'.h x) → 
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G0 ν δ ε D →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        (2 * d + 2) * (bgK1 d L N * δ') ≤ deltaStar d L N →
        (2 * d + 2) * (bgK1 d L N * δ') ≤ δw →
        ∀ {E : Set (Torus d ((N₁ * L ^ m₁) * L ^ (k + 1)))},
        (∀ x ∈ E, ∀ m, 1 ≤ m → m ≤ k + 1 → (x ∈ G0.Ω m ↔ x ∈ G1.Ω m)) →
        bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N)
            (composeData hprec (compWeight L a₁) (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D')
              D') = hprec.restrictφ (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') ∧
          FarBounds G0 (shadow G0 (Finset.univ.filter fun y => y ∉ E)) (gammaW d)
            (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * δ'))))
            (bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N)
                (composeData hprec (compWeight L a₁)
                  (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D') -
              bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D)
            (bgMultC G0 (compWeight L a₁) ν (bgC0 d L N)
                (composeData hprec (compWeight L a₁)
                  (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D') -
              bgMultC G0 (compWeight L a₁) ν (bgC0 d L N) D) := by
  obtain ⟨Kw, δw, hK, hδw, hfar⟩ := lemma41_domain_uncond (d := d) (L := L) (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ0 ϱ1 G0 G1 a₁ ν δ ε δ' ε' ha₁ H0 H1 hOp hprec D' hδ0' hδε' hε' hδc hνε' hD' D
    hΨ hh hδ0 hδε hε hδ1 hνε hD hK1 hKw hK1' hKw' E hE
  obtain ⟨hDuU, hfield, hΨE, hhE, hbound⟩ := composed_change ha₁ H0 H1 hprec hδ0' hδε' hε' hδc
    hνε' hD' hΨ hh hE
  refine ⟨hfield, ?_⟩
  obtain ⟨δu, εu, hδu0, hδuε, hεu, hδu1, hνεu, hDu⟩ := hDuU
  have hK1pos := bgK1_pos d L N
  have hδ₁0 : 0 ≤ (2 * d + 2) * (bgK1 d L N * δ') := by positivity
  refine hfar H0 hOp hδ0 hδε hε hδ1 hνε hD hδu0 hδuε hεu hδu1 hνεu hDu hK1 hKw
    (δΨ := fun y i => (composeData hprec (compWeight L a₁)
      (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ y i - D.Ψ y i)
    (Finset.univ.filter fun y => y ∉ E) ?_ (fun x i => by ring) (fun x i => hhE x i) hδ₁0 hK1' hKw'
    (fun x hx => hbound x hx)
  intro y hy
  have hyE : y ∈ E := by simpa using hy
  funext i
  exact hΨE y hyE i

end Balaban.LargeField.Base
