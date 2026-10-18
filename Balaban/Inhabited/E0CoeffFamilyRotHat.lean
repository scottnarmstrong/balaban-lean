/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineFan
public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Fluctuation.InteractionSymmSolRot
public import Balaban.Fluctuation.Prop33SymmEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Spin covariance of the hat-variable functional of the decoupled block energy

For a real orthogonal `Q`, the fluctuation field `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` built from the
rotated datum and the rotated hat variable `(1 ⊗ R) ψ̂` is the pointwise rotation of the one built
from the datum and `ψ̂` (`hatPsiF_rot`).  Hence the function of `(s, Θ, ψ̂)` expanded in the direct
terms of the zero class, `Φ (F₁ (s, Θ)) (Sol (s, flEdat …)).1 (Θ, ψ'(s))`, is invariant for every
spin-invariant functional `Φ` (`hatFn_rot`), and so are its expansion terms (`evTermHat_rot`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section HatRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

/-- The lift of a rotated hat variable is the rotation of the lift. -/
theorem liftC_rotFld (hG' : IsLevel Gp (k + 1)) (R : Matrix (Fin N) (Fin N) ℂ)
    (v : unitPts Gp × Fin N → ℂ) :
    liftC hG' (rotFld R v) = DecEquiv.rotSite R (liftC hG' v) := by
  funext x i
  simp only [liftC_apply, rotFld, DecEquiv.rotSite, Matrix.mulVec, dotProduct]

/-- **Covariance of the decoupled square root at the background**: `C^{1/2}(s)` at the rotated
datum applied to the rotated hat variable is the rotation of `C^{1/2}(s) ψ̂`. -/
theorem hatSqrtF_mulVec_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
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
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (ψh : unitPts Gp × Fin N → ℂ) :
    hatSqrtF Gp a₁ ν F₁ s (rotRaw (cmat Q) (rawOf D)) *ᵥ rotFld (cmat Q) ψh =
      rotFld (cmat Q) (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh) := by
  classical
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  obtain ⟨-, φ, α, hI, hFeq⟩ := bg_point hC hF₁ hs hD
  have hrot := F₁_rot hC hF₁ hs hD hQ
  have hdec := decDom_of_isDecBg hC hs hD hI hmar hα
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have hε := hC.eps_pos
      have hc1 := one_le_xiC1 d
      have hδ0 : 0 < xiC1 d * eps := by positivity
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hCS := covStanding_of_mem (N := N) hX hC.hκ.le hMX hδc hsm
    (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice hdec
  have hsq := decCovSqrt_rot (R := cmat Q) hR hCS
  have hbar : barField Gp (rotRaw (cmat Q) (rawOf D)).1 (rotFld (cmat Q) φ) =
      DecEquiv.rotSite (cmat Q) (barField Gp D.Ψ φ) := by
    funext x i
    exact barField_rot_raw (cmat Q) D.Ψ φ x i
  unfold hatSqrtF
  rw [hrot, hFeq]
  simp only
  rw [hbar, hsq, ← Matrix.mulVec_mulVec, rotLift_mulVec (cmat Q)ᵀ, rotFld_rotFld_transpose hR,
    ← Matrix.mulVec_mulVec, rotLift_mulVec]
  rfl

/-- **Covariance of the fluctuation field `ψ'(s)` of a hat variable under spin rotations.** -/
theorem hatPsiF_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
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
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (ψh : unitPts Gp × Fin N → ℂ) :
    hatPsiF Gp a₁ ν hG' cc F₁ s (rotRaw (cmat Q) (rawOf D)) (rotFld (cmat Q) ψh) =
      DecEquiv.rotSite (cmat Q) (hatPsiF Gp a₁ ν hG' cc F₁ s (rawOf D) ψh) := by
  have h := hatSqrtF_mulVec_rot hC hk hMX hmar hα hsm hF₁ hs hD hQ ψh
  unfold hatPsiF
  rw [h, ← liftC_rotFld]
  congr 1
  funext p
  simp only [Pi.smul_apply, rotFld, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end HatRot

section HatRot2

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {m₀ : ℕ}

/-- **The expanded function of a hat-variable functional is spin invariant on the polydisc.** -/
theorem hatFn_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (fun _ => Real.exp κ)) :
    fnOfDec Gp Hm X₁f F₁ Sol Φ
      (rotRaw (cmat Q) (rawOf D), hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rotRaw (cmat Q) (rawOf D))
        (rotFld (cmat Q) ψh)) s =
    fnOfDec Gp Hm X₁f F₁ Sol Φ
      (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) s := by
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hmem := hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hδ₁ hF₁ hsx hD hψh
  have hrot := hatPsiF_rot hC hk hG' cc hMX hmar hα hsm hF₁ hsx hD hQ ψh
  have key := fnOfDecSol_rot hC hF₁ hSol hQ hΦ
    (u := (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh))
    ⟨⟨D, hD, rfl⟩, hmem.1⟩ hs
  have e1 : rotU (cmat Q) (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) =
      (rotRaw (cmat Q) (rawOf D), hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rotRaw (cmat Q) (rawOf D))
        (rotFld (cmat Q) ψh)) := by
    rw [hrot]; rfl
  rw [← e1]
  exact key

/-- **The expansion terms of a hat-variable functional are spin invariant.** -/
theorem evTermHat_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀ X₁
      (fun u s => fnOfDec Gp Hm X₁f F₁ Sol Φ
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y
      (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) =
    evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀ X₁
      (fun u s => fnOfDec Gp Hm X₁f F₁ Sol Φ
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y
      (rawOf D, ψh) :=
  evTerm_congr_polydisc _ (Real.one_lt_exp_iff.2 hC.hκ) X₁ Y fun _ hs =>
    hatFn_rot hC hk hG hG' cc hcψ hMX hmar hα hsm hδ₁ hF₁ hSol hQ hΦ hD hψh hs

end HatRot2

end Balaban.Localization
