/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33CloseDomain
public import Balaban.Fluctuation.Prop33CloseC7
public import Balaban.Fluctuation.Lemma25
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domain premise `hreal` of Proposition 3.3 (Lemma 2.3 (d); W136b)

Every layer-constant fluctuation `ψ'` of the ball `|ψ'| < δ₁` is the tangent of a datum `D` of the
level-`n` whole-lattice set `Hm` (`D.Ψ = ψ^{(k)}.Ψ + ψ'`, `D.h = D'.h`), and the disc
`{ψ^{(k)} + t ψ' : |t| < R}` stays in the data domain `𝒟(c₀, c₁)` of Theorem 5.2.  The proof is
`composeData_inDomainC_explicit` (`ψ^{(k)} ∈ Ψ̃^c(δ₀, δ₀)`, `δ₀ = 2 C₄ K₁ C₁ ε`) followed by
`disc_inUnionDomainC_gen`.  The smallness `δ₀ + 5 R δ₁ ≤ c₁` is the source condition
"`δ_b + 5 R t ≤ c₁`" of Lemma 2.3 (d).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Real

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ}

/-- **`hreal` (Lemma 2.3 (d), the domain premise of the expansion)**: for the pair of whole-lattice
levels `Hm` (level `n`), `Gp` (level `n + 1`), every layer-constant fluctuation `ψ'` with
`|ψ'| < δ₁` is the tangent of a datum `D` with the same `h̃` whose disc of radius `R` through the
composed datum `ψ^{(k)}` of a member of `Ξ^c_K(1, ε)` lies in `𝒟`, provided
`2 C₄ K₁ (C₁ ε) + 5 R δ₁ ≤ c₁`. -/
theorem hreal_level {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N) :
    ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t) := by
  intro D' hD' ψ' hψ'b hψ'c
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hH' : BgHyp d L K ϱ (compWeight L a₁) ν := hC.HBp
  have hc1 := one_le_xiC1 d
  have hε0 : 0 < eps := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hc7b : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hbc1 : xiC1 d * eps ≤ bgC1 d L N := hc7b.trans (c7_le_bgC1 d L N BG κ)
  have hbc0 : xiC1 d * eps ≤ bgC0 d L N := hbc1.trans (bgC1_le_bgC0 d L N hd0)
  have hδ3 : xiC1 d * eps ≤ thm73C3 d L N := hc7b.trans hc7
  have hDdom : InDomainC Gp ν (xiC1 d * eps) (xiC1 d * eps) D' :=
    xiCData_inDomainC hH' hC.small1 hD'
  have hν1 : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1 := H.massLe
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨hδj0, hδδj, hδjc0, -, hνj, hcomp⟩ := composeData_inDomainC_explicit ha₁ H hH'
    (hG.precedes hG' hp) hδ0 le_rfl hbc0 hδ3 hνε hDdom
  set B := composeData (hG.precedes hG' hp) (compWeight L a₁)
    (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' with hB
  have hdata : ∀ x : CTorus d L N₁ m₁ K, x ∈ dataSites Hm := fun x =>
    (mem_dataSites Hm).2 (Or.inl (hG x).1)
  let D : BgData Hm N :=
    { Ψ := fun x i => B.Ψ x i + ψ' x i
      h := B.h
      Ψ_layerConst := by
        intro m hm1 hmk x hx x' hx'
        funext i
        simp only [B.Ψ_layerConst m hm1 hmk x hx x' hx', hψ'c m hm1 hmk x hx x' hx']
      h_layerConst := B.h_layerConst
      Ψ_zero := fun x hx => absurd (hdata x) hx
      h_zero := B.h_zero }
  have hDΨ : ∀ x i, D.Ψ x i = B.Ψ x i + ψ' x i := fun x i => rfl
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x i
    have hx := (hG x).1
    show B.h x i = D'.h x i
    simp [hB, composeData, hx]
  · funext x i
    show D.Ψ x i - B.Ψ x i = ψ' x i
    rw [hDΨ]; ring
  · intro t ht
    have hδjc1 : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) ≤ bgC1 d L N := by
      have : 0 ≤ R * δ₁ := mul_nonneg hR0 hC.δ₁_pos.le
      linarith
    have hRt : R * δ₁ ≤ 1 := by
      have h1 := bgC1_le_small d L N hd0
      have : 0 ≤ 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) := hδj0.le
      linarith
    have hbc0' : bgC0 d L N ≤ 1 / 16 := min_le_right _ _
    have hmax : max (xiC1 d * eps) (2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps)))) ≤
        bgC0 d L N := max_le hbc0 hδjc0
    refine disc_inUnionDomainC_gen hd0 (B := B) (E := tangentData D B) hcomp hδj0
      (le_max_right _ _) (hδjc0.trans (by linarith)) (hmax.trans (by linarith)) hmax hνj
      hC.δ₁_pos.le hR0 hRt (fun x i => rfl) ?_ hν1 hsm ht
    intro x hx
    have hv := hψ'b x hx
    have : (tangentData D B).Ψ x = ψ' x := by
      funext i
      show D.Ψ x i - B.Ψ x i = ψ' x i
      rw [hDΨ]; ring
    rw [this]
    exact hv.le
  
end Real

end Balaban.Localization
