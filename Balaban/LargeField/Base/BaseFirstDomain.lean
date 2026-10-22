module

public import Balaban.LargeField.Base.BaseFirstLemma35
public import Balaban.Background.ScaledDomain

/-!
# The perturbation bound of the first step without the small-solution premise

`baseFirst_deltaPhi` takes the small solution of the renormalized datum as a premise.  For a datum
`D(θ)` of the real domain the renormalized datum `D((1 + ε t₁) θ)` is again in the real domain
(`InDomainR.scale`), so its background is that small solution (`isSmallSolution_of_inDomainR`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Fluctuation

variable {d N L n : ℕ} [NeZero L] [NeZero n] {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}

omit [NeZero n] in
/-- **Lemma 3.5 (ii) at the first step** (`baseFirst_deltaPhi` with its premise discharged): for
`D(θ)` in the class domain and in the real domain with parameter `δ`, real `t` with `|t_i| ≤ 1/16`,
`|ε t₁| ≤ 1/256` and `2(2δ + 3|ε t₁|) ≤ c₁`, the renormalized background `bgField` of
`D((1+ε t₁)θ)` at the mass `ν(1+t₂)/(1+t₃)` differs from the old one by `δφ` with
`‖δφ‖_*, |δα|₂ ≤ 8 K₂ ε ‖t‖`. -/
theorem baseFirst_deltaPhi_of_domain (aw : ℕ → ℝ) {ν ε r : ℝ} (H : BgHyp d L 1 ϱ aw ν)
    (hε : 0 < ε) (hr : r ≤ 1 / 16) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * ε * r ≤ deltaStar d L N) :
    ∃ F, IsRenSol (N := N) (topGS d L N₁ m₁ 1 ϱ) aw ν ε ε r (8 * ε) F ∧
      ∀ (hc : N₁ * L ^ m₁ * L ^ (1 - 1) = n) (h : EuclideanSpace ℝ (Fin N))
        (θ : Torus d n → EuclideanSpace ℝ (Fin N)) {δ : ℝ},
        XiCOne (topGS d L N₁ m₁ 1 ϱ) aw ν ε (firstDatum ϱ hc θ h) →
        InDomainR (topGS d L N₁ m₁ 1 ϱ) ν δ (firstDatum ϱ hc θ h) → 0 < δ →
        ∀ (t : Fin 3 → ℝ), (∀ i, |t i| ≤ 1 / 16) → ‖(fun i => ((t i : ℝ) : ℂ))‖ < r →
        |ε * t 0| ≤ 1 / 256 → 2 * (2 * δ + 3 * |ε * t 0|) ≤ bgC1 d L N →
        BgHyp d L 1 ϱ aw (ν * (1 + t 1) / (1 + t 2)) →
        SupBounds (topGS d L N₁ m₁ 1 ϱ)
            (bgField (topGS d L N₁ m₁ 1 ϱ) aw (ν * (1 + t 1) / (1 + t 2))
                (firstDatum ϱ hc ((1 + ε * t 0) • θ) h) -
              bgFieldC (topGS d L N₁ m₁ 1 ϱ) aw ν (bgC0 d L N) (firstDatum ϱ hc θ h))
            (cK2 d L N * (8 * ε * ‖(fun i => ((t i : ℝ) : ℂ))‖)) ∧
          Small (topGS d L N₁ m₁ 1 ϱ)
            (bgMult (topGS d L N₁ m₁ 1 ϱ) aw (ν * (1 + t 1) / (1 + t 2))
                (firstDatum ϱ hc ((1 + ε * t 0) • θ) h) -
              bgMultC (topGS d L N₁ m₁ 1 ϱ) aw ν (bgC0 d L N) (firstDatum ϱ hc θ h))
            (cK2 d L N * (8 * ε * ‖(fun i => ((t i : ℝ) : ℂ))‖)) := by
  obtain ⟨F, hF, key⟩ := baseFirst_deltaPhi (n := n) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) (N := N) aw H hε hr hsm hc1 hK hζ
  refine ⟨F, hF, fun hc h θ δ hD hDr hδ t ht1 htr hζ' hδc Hu => ?_⟩
  have hle : ν * (1 + t 1) / (1 + t 2) ≤ 17 / 15 * ν := by
    have h1 := abs_le.mp (ht1 1)
    have h2 := abs_le.mp (ht1 2)
    have hν := H.mass
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨hΨ, hh⟩ := firstDatum_scale ϱ hc (ε * t 0) θ h
  have hDu : InDomainR (topGS d L N₁ m₁ 1 ϱ) (ν * (1 + t 1) / (1 + t 2))
      (2 * δ + 3 * |ε * t 0|) (firstDatum ϱ hc ((1 + ε * t 0) • θ) h) :=
    InDomainR.scale hDr (fun x _ i => hΨ x i) (fun x _ i => hh x i) hζ' hle hδ le_rfl
  have hpos : 0 < 2 * δ + 3 * |ε * t 0| := by positivity
  have hs := isSmallSolution_of_inDomainR Hu hDu hpos hδc
  exact key hc h θ hD t htr hs

end Balaban.LargeField
