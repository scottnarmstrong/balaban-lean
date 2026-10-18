/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotCorr
public import Balaban.Inhabited.E1MarkParamCommonG
public import Balaban.Fluctuation.Prop33SymmEnergy
public import Balaban.Fluctuation.Prop33SymmDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin covariance of the mark family `e1MarkGParamG`

At a parameter whose raw datum lies in the chart, the mark of the root `z` at a bridge label is
unchanged when the raw datum is rotated by a real orthogonal `Q` and the block configuration is
rotated sitewise (`e1MarkGParamG_rot`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section MarkRot

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

/-- **Spin covariance of the mark family.** -/
theorem e1MarkGParamG_rot (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ} {eps : ℝ}
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ b, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSol : ∀ b, SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps δ₁ (Sol b))
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    (he : ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp))
    {ρ : ℝ} (hρ : S.p₁ ≤ ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    (hmark : ∀ u : ℂ, ‖u‖ < (17 / 16 : ℝ) → (‖u‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖(((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁)
    (z : RootIdx d L N₁ m₁ (k + 1)) (θ θ' : physParam N S)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hθθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
      rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    {Φ : ∀ b, (S.blockSplit 1 hp).Ωb b} (hΦc : Φ ∈ physCarrier S 1 hp) :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ' Y' u (fun b x => e (Φ b x)) =
      e1MarkGParamG S F₁ Sol ρ hp z eps θ Y' u Φ := by
  classical
  have hθ'mem : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps := by
    rw [hθθ']; exact rotRaw_mem hQ hθ
  by_cases hu : ‖u‖ < (17 / 16 : ℝ)
  · rw [e1MarkGParamG_of_mem S F₁ Sol ρ hp z eps θ' Y' u (fun b x => e (Φ b x)) hθ'mem hu,
      e1MarkGParamG_of_mem S F₁ Sol ρ hp z eps θ Y' u Φ hθ hu]
    unfold markedOutDec
    refine Finset.sum_congr rfl fun q _ => ?_
    refine congrArg (fun f : ℂ → ℂ => deriv f 0) ?_
    funext t
    obtain ⟨D, hD, hDθ⟩ := hθ
    have hr := decMarkCorr_rot S hC hk hG hcψ hMX hmar hα hsm (hF₁ q.1) (hSol q.1) hQ e he
      (X₁f := LocalCover.nbhdF 1 (LocalCover.blockSite k q.1)) (m₀ := 1) (j := k)
      (𝒦X := LocalCover.fam 1 (LocalCover.blockSite k q.1))
      (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Zm := S.blockU z)
      (En := blockEnergyFun S.G' Hm (compWeight L S.a₁) S.ν k q.1)
      (fun bg δφ u' => energyBlock_rot (isRealOrth_ofReal hQ).1 _ S.ν k bg.2 δφ u'.2 q.1)
      q.2 hρ hρc hp hD (hmark u hu) hΦc
    unfold decMarkCorrTerm
    rw [hθθ', hDθ, hr]
  · rw [e1MarkGParamG_of_not S F₁ Sol ρ hp z eps θ' Y' u (fun b x => e (Φ b x)) (fun h => hu h.2),
      e1MarkGParamG_of_not S F₁ Sol ρ hp z eps θ Y' u Φ (fun h => hu h.2)]

end MarkRot

end Balaban.Inhabited
