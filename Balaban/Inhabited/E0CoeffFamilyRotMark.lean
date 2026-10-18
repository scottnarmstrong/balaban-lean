/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotHat
public import Balaban.Fluctuation.MarkedDecBall
public import Balaban.Fluctuation.MarkedVBlockDec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin covariance of the masked fluctuation field and of the marked terms `evDec`

`markedHatPsiF_rot`: the masked decoupled tangent of the rotated datum and the rotated hat variable
is the pointwise rotation of the masked tangent (the mask is a projection on unit points, so it
commutes with the spin rotation).  `evDec_rot`: the localized terms along the masked tangent are
invariant, at the marks of the radius set.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section MarkRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

/-- The mask on unit points commutes with the spin rotation. -/
theorem maskBlock_rotFld (Z : Finset (unitPts Gp)) (R : Matrix (Fin N) (Fin N) ℂ)
    (w : unitPts Gp × Fin N → ℂ) :
    maskBlock Z (rotFld R w) = rotFld R (maskBlock Z w) := by
  classical
  funext q
  simp only [maskBlock, rotFld]
  by_cases h : q.1 ∈ Z
  · simp [h]
  · simp [h]

/-- **Covariance of the masked decoupled tangent under spin rotations.** -/
theorem markedHatPsiF_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (Z : Finset (unitPts Gp)) (u t : ℂ)
    (ψh : unitPts Gp × Fin N → ℂ) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rotRaw (cmat Q) (rawOf D)) (rotFld (cmat Q) ψh) =
      DecEquiv.rotSite (cmat Q) (markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh) := by
  have h1 := hatPsiF_rot hC hk hG' cc hMX hmar hα hsm hF₁ hs hD hQ ψh
  have h2 := hatSqrtF_mulVec_rot hC hk hMX hmar hα hsm hF₁ hs hD hQ ψh
  unfold markedHatPsiF
  rw [h1, h2]
  have h3 : cc • rotFld (cmat Q) (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh) =
      rotFld (cmat Q) (cc • (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh)) := by
    funext p
    simp only [Pi.smul_apply, rotFld, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, maskBlock_rotFld, liftC_rotFld]
  funext x i
  simp only [Pi.add_apply, Pi.smul_apply, DecEquiv.rotSite, Matrix.mulVec, dotProduct,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {m₀ : ℕ}

/-- **The localized terms along the masked tangent are spin invariant** (at marks of the radius
set, for hat variables of sup norm at most `cψ`), the invariance of the functional being required only
at the realizable triples with layer-constant fluctuation whose rotation is again such a triple. -/
theorem evDec_rot_real (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ∈
        FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    (Zm : Finset (unitPts Gp)) (j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ (k + 1)))
    {um tm : ℂ}
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol Φ Zm um tm Y
      (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) =
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) := by
  refine evTerm_congr_polydisc _ (Real.one_lt_exp_iff.2 hC.hκ) _ Y fun s hs => ?_
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hmem := markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁ hsx hD hψh
    Zm hδ
  have hrot := markedHatPsiF_rot hC hk hG' cc hMX hmar hα hsm hF₁ hsx hD hQ Zm um tm ψh
  have key := fnOfDecSol_rot_real hC hF₁ hSol hQ
    (u := (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh))
    (fun bg δφ h1 h2 => hΦ bg δφ _ ⟨h1, hmem.2⟩ ⟨h2, isLayerConstant_rot hmem.2⟩)
    ⟨⟨D, hD, rfl⟩, hmem.1⟩ hs
  have e1 : rotU (cmat Q) (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) =
      (rotRaw (cmat Q) (rawOf D), markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rotRaw (cmat Q) (rawOf D))
        (rotFld (cmat Q) ψh)) := by
    rw [hrot]; rfl
  show fnOfDec Gp Hm X₁f F₁ Sol Φ (rotRaw (cmat Q) (rawOf D), markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rotRaw (cmat Q) (rawOf D))
        (rotFld (cmat Q) ψh)) s =
    fnOfDec Gp Hm X₁f F₁ Sol Φ (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) s
  rw [← e1]
  exact key

/-- **The localized terms along the masked tangent are spin invariant** (at marks of the radius
set, for hat variables of sup norm at most `cψ`). -/
theorem evDec_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    (Zm : Finset (unitPts Gp)) (j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ (k + 1)))
    {um tm : ℂ}
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol Φ Zm um tm Y
      (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) =
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) :=
  evDec_rot_real hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁ hSol hQ
    (fun bg δφ u _ _ => hΦ bg δφ u) Zm j 𝒦X hδ Y hD hψh

end MarkRot

end Balaban.Localization
