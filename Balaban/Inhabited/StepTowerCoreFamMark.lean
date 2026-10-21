/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCoreFamPin
public import Balaban.Inhabited.E0CoeffFamilyRotCorr
public import Balaban.Inhabited.E0CoeffFamilyRotTowerMark
public import Balaban.Inhabited.E0CoeffFamilyRotMarkG
import Mathlib.Tactic.Linarith

/-!
# Uniqueness of the marks of the core family

For two pinned pairs `(F₁, Sol)`, `(F₁', Sol')` of a step of the general tower, the localized
marked terms `evDec`, the block-level marks `decMarkG`, `decMarkCorr` and the mark family
`e1MarkGParamG` at a parameter in the chart coincide (`e1MarkGParamG_unique_tower`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section MarkPin

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The localized terms along the masked tangent agree for two pinned pairs.** -/
theorem evDec_unique (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    (hSol' : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol')
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, Φ t.1 t.2.1 t.2.2 = Φ' t.1 t.2.1 t.2.2)
    {m₀ j : ℕ} (Zm : Finset (unitPts Gp)) (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) {um tm : ℂ}
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) =
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁' Sol' Φ' Zm um tm Y (rawOf D, ψh) := by
  refine evTerm_congr_polydisc _ (Real.one_lt_exp_iff.2 hC.hκ) _ Y fun s hs => ?_
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hmem := markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁ hsx hD hψh
    Zm hδ
  have hFF := F₁_unique hC hF₁ hF₁' hsx hD
  show fnOfDec Gp Hm X₁f F₁ Sol Φ (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) s =
    fnOfDec Gp Hm X₁f F₁' Sol' Φ' (rawOf D, markedHatPsiF a₁ ν hG' cc F₁' Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) s
  rw [← markedHatPsiF_unique hG' cc hFF]
  refine fnOfDec_unique hC hF₁ hF₁' hSol hSol' (Φ := Φ) (Φ' := Φ') hΦ
    (u := (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)) ?_ hmem.2 hs
  exact ⟨⟨D, hD, rfl⟩, hmem.1⟩

end MarkPin

end Balaban.Localization

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Matrix

section CorrPin

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {cc : ℂ} {Zm : Finset (unitPts S.G')}

/-- **The block-level decoupled mark agrees for two pinned pairs.** -/
theorem decMarkG_unique (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ F₁' : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec S.G' Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    (hSol' : SolSpec S.G' Hm a₁ ν BG BG₂ κ eps δ₁ Sol')
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ρ : ℝ} (hρ : S.p₁ ≤ ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {um : ℂ}
    (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b} :
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) um Φ =
    decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En Zm Y ρ hp (rawOf D) um Φ := by
  unfold decMarkG decMarkGBg
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {t : ℂ | (‖um‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} := hum
  filter_upwards [hopen.mem_nhds h0] with t ht
  refine evDec_unique hC hk hG S.hG' cc hcψ hMX hmar hα hsm hF₁ hF₁' hSol hSol' (Φ' := En) (fun _ _ => rfl) Zm 𝒦X ht Y hD ?_
  intro q
  have := S.hatOf_mem m₀ (lt_of_lt_of_le hp hρ) hp Φ q
  exact this.trans hρc

/-- **The corrected block-level decoupled mark agrees for two pinned pairs.** -/
theorem decMarkCorr_unique (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ F₁' : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec S.G' Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    (hSol' : SolSpec S.G' Hm a₁ ν BG BG₂ κ eps δ₁ Sol')
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ρ : ℝ} (hρ : S.p₁ ≤ ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {um : ℂ}
    (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b} :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) um Φ =
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En Zm Y ρ hp (rawOf D) um Φ := by
  have hδ₁ : 0 < δ₁ := hC.δ₁_pos
  have hg : ∀ {v : ℂ}, (‖v‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
      decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp (rawOf D) v Φ =
      decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En Zm Y ρ hp (rawOf D) v Φ := fun hv =>
    decMarkG_unique S hC hk hG hcψ hMX hmar hα hsm hF₁ hF₁' hSol hSol' Y hρ hρc hp hD hv
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ := by
    simpa using hδ₁
  have hopen : IsOpen {v : ℂ | (‖v‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have hd : deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp
        (rawOf D) v Φ) 0 =
      deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁' Sol' En Zm Y ρ hp (rawOf D) v Φ) 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds (show (0 : ℂ) ∈ {v : ℂ | (‖v‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} from h0)]
      with v hv using hg hv
  unfold decMarkCorr decMarkCorrBg
  exact congrArg₂ (· - ·) (congrArg₂ (· - ·) (hg hum) (hg h0)) (congrArg (um * ·) hd)

end CorrPin

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section MarkUnique

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

/-- **The mark family agrees for two pinned families of pairs** (parameters in the chart). -/
theorem e1MarkGParamG_unique (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ} {eps : ℝ}
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (F₁ F₁' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ b, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ b, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    (Sol Sol' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSol : ∀ b, SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps δ₁ (Sol b))
    (hSol' : ∀ b, SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps δ₁ (Sol' b))
    {ρ : ℝ} (hρ : S.p₁ ≤ ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    (hmark : ∀ u : ℂ, ‖u‖ < (17 / 16 : ℝ) → (‖u‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖(((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ *
        (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁)
    (z : RootIdx d L N₁ m₁ (k + 1)) (θ : physParam N S)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ Y' u Φ =
      e1MarkGParamG S F₁' Sol' ρ hp z eps θ Y' u Φ := by
  classical
  by_cases hu : ‖u‖ < (17 / 16 : ℝ)
  · rw [e1MarkGParamG_of_mem S F₁ Sol ρ hp z eps θ Y' u Φ hθ hu,
      e1MarkGParamG_of_mem S F₁' Sol' ρ hp z eps θ Y' u Φ hθ hu]
    unfold markedOutDec
    refine Finset.sum_congr rfl fun q _ => ?_
    refine congrArg (fun f : ℂ → ℂ => deriv f 0) ?_
    funext t
    obtain ⟨D, hD, hDθ⟩ := hθ
    have hr := decMarkCorr_unique S hC hk hG hcψ hMX hmar hα hsm (hF₁ q.1) (hF₁' q.1) (hSol q.1)
      (hSol' q.1) (X₁f := LocalCover.nbhdF 1 (LocalCover.blockSite k q.1)) (m₀ := 1) (j := k)
      (𝒦X := LocalCover.fam 1 (LocalCover.blockSite k q.1))
      (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Zm := S.blockU z)
      (En := blockEnergyFun S.G' Hm (compWeight L S.a₁) S.ν k q.1)
      q.2 hρ hρc hp hD (hmark u hu) (Φ := Φ)
    rw [hDθ]
    exact congrArg (fun x => t * (-((S.β : ℝ) : ℂ) * x)) hr
  · rw [e1MarkGParamG_of_not S F₁ Sol ρ hp z eps θ Y' u Φ (fun h => hu h.2),
      e1MarkGParamG_of_not S F₁' Sol' ρ hp z eps θ Y' u Φ (fun h => hu h.2)]

end MarkUnique

section General

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

/-- **Uniqueness of the mark family at the clamp radius, from the ray margin.** -/
theorem e1MarkGParamG_unique_of_ray (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {c BG κ Kc Cx c₂ BG₂ eps : ℝ}
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ eps) (hk : 1 ≤ k)
    (hG : IsLevel Hm k)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (F₁ F₁' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ b, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ b, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    (Sol Sol' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSol : ∀ b, SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps eps (Sol b))
    (hSol' : ∀ b, SolSpec S.G' Hm S.a₁ S.ν BG BG₂ κ eps eps (Sol' b))
    (hp : 0 < S.p₁) {r cψ' : ℝ} (hr : 0 < r) (ht : 0 < eps)
    (hray : (2 * 2 + r) * S.p₁ < cψ')
    (hfl : Real.sqrt N * (‖(((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ')) < eps)
    (z : RootIdx d L N₁ m₁ (k + 1)) (θ : physParam N S)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGParamG S F₁ Sol S.p₁ hp z eps θ Y' u Φ =
      e1MarkGParamG S F₁' Sol' S.p₁ hp z eps θ Y' u Φ := by
  refine e1MarkGParamG_unique S hC hk hG (cψ := S.p₁) hp.le hMX hmar hα hsm F₁ F₁' hF₁ hF₁' Sol
    Sol' hSol hSol' le_rfl le_rfl hp ?_ z θ hθ Y' u Φ
  intro u' hu'
  have h := markRadius_of_ray (X := Real.sqrt N * (‖(((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ *
      covSupConstC d L N (compWeight L S.a₁ k) κ)) (cψ := cψ') (p₁ := S.p₁) hp.le hr ht hray
    (by convert hfl using 1; ring) hu'
  nlinarith [h]

end General

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **Uniqueness of the mark family at the general tower.** -/
theorem e1MarkGParamG_unique_tower (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ}
    [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (F₁ F₁' : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ b, ∀ (s : DecParams S.G') (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D' φ α →
        F₁ b (s, rawOf D') = (φ, α))
    (hF₁' : ∀ b, ∀ (s : DecParams S.G') (D' : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D' → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D' φ α →
        F₁' b (s, rawOf D') = (φ, α))
    (Sol Sol' : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N →
        ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ))
    (hSol : ∀ b, SolSpec S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) S.a₁ S.ν T.BG T.BG₂ T.κ
      T.t T.t (Sol b))
    (hSol' : ∀ b, SolSpec S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) S.a₁ S.ν T.BG T.BG₂ T.κ
      T.t T.t (Sol' b))
    (z : RootIdx d L N₁ T.m₁ (k + 1)) (θ : physParam N S)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGParamG S F₁ Sol S.p₁ hp z T.t θ Y' u Φ =
      e1MarkGParamG S F₁' Sol' S.p₁ hp z T.t θ Y' u Φ := by
  subst hS
  refine e1MarkGParamG_unique_of_ray (T.step k hk N₁ ν β p₁) D.core hk
    (T.step k hk N₁ ν β p₁).hG T.large_block T.dom_margin T.coer_margin T.δc_small F₁ F₁' hF₁ hF₁'
    Sol Sol' hSol hSol' hp D.r_pos T.t_pos D.ray_margin ?_ z θ hθ Y' u Φ
  convert D.fl_radius using 1
  have ha : (T.step k hk N₁ ν β p₁).a₁ = 1 := rfl
  rw [ha]

end Balaban.Inhabited
