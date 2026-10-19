/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotMark
public import Balaban.Inhabited.E0CoeffFamilyRotBlock
public import Balaban.Fluctuation.DecMarkCorrected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin covariance of the block-level decoupled marks

For a real orthogonal `Q`, the block-level mark `decMarkG` and the corrected mark `decMarkCorr` at
the rotated datum `rotRaw (cmat Q) Θ` and the sitewise rotated block configuration are equal to
those at `(Θ, Φ)`, for `Φ` in the carrier of the step measure and the marks `um` of the radius set.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Matrix

section CorrRot

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {cc : ℂ} {Zm : Finset (unitPts S.G')}

/-- **Spin covariance of the block-level decoupled mark.** -/
theorem decMarkG_rot (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec S.G' Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    (he : ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp))
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) δφ u,
      En (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = En bg δφ u)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ρ : ℝ} (hρ : S.p₁ ≤ ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {um : ℂ}
    (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b} (hΦc : Φ ∈ physCarrier S m₀ hp) :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rotRaw (cmat Q) (rawOf D)) um
      (fun b u => e (Φ b u)) =
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) um Φ := by
  unfold decMarkG decMarkGBg
  rw [hatOf_rot S m₀ hp e he hρ hΦc]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {t : ℂ | (‖um‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} := hum
  filter_upwards [hopen.mem_nhds h0] with t ht
  refine evDec_rot hC hk hG S.hG' cc hcψ hMX hmar hα hsm hF₁ hSol hQ hΦ Zm j 𝒦X ht Y hD ?_
  intro q
  have := S.hatOf_mem m₀ (lt_of_lt_of_le hp hρ) hp Φ q
  exact this.trans hρc

/-- **Spin covariance of the corrected block-level mark.** -/
theorem decMarkCorr_rot (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec S.G' Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (e : Rn N ≃ₗᵢ[ℝ] Rn N)
    (he : ∀ x : Rn N, e x = WithLp.toLp 2 (Q *ᵥ x.ofLp))
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) δφ u,
      En (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = En bg δφ u)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ρ : ℝ} (hρ : S.p₁ ≤ ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {um : ℂ}
    (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b} (hΦc : Φ ∈ physCarrier S m₀ hp) :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rotRaw (cmat Q) (rawOf D)) um
      (fun b u => e (Φ b u)) =
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) um Φ := by
  have hδ₁ : 0 < δ₁ := hC.δ₁_pos
  have hg : ∀ {v : ℂ}, (‖v‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
      decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rotRaw (cmat Q) (rawOf D)) v
        (fun b u => e (Φ b u)) =
      decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) v Φ := fun hv =>
    decMarkG_rot S hC hk hG hcψ hMX hmar hα hsm hF₁ hSol hQ e he hΦ Y hρ hρc hp hD hv hΦc
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ := by
    simpa using hδ₁
  have hopen : IsOpen {v : ℂ | (‖v‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have hd : deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp
        (rotRaw (cmat Q) (rawOf D)) v (fun b u => e (Φ b u))) 0 =
      deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) v Φ) 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds (show (0 : ℂ) ∈ {v : ℂ | (‖v‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} from h0)]
      with v hv using hg hv
  unfold decMarkCorr decMarkCorrBg
  exact congrArg₂ (· - ·) (congrArg₂ (· - ·) (hg hum) (hg h0)) (congrArg (um * ·) hd)

end CorrRot

end Balaban.Fluctuation
