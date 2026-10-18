/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotHat
public import Balaban.Inhabited.E0CoeffFamilyRotRay

/-!
# Spin covariance of the ray terms of the hat-variable block expansion

`rayTermHat_rot`: the ray term `rayTerm (dl3 Ev w) ω x₀ σ Θ` of the localized term `Ev` of a
spin-invariant block functional is unchanged when `Θ` is rotated by a real orthogonal `Q` and the
hat variables `x₀`, `w` by `(1 ⊗ Q)`, for hat variables whose rays stay in the sup-norm ball.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section RayRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {m₀ : ℕ}

theorem rotFld_smul' {ι' : Type*} (R : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : ι' × Fin N → ℂ) :
    rotFld R (c • x) = c • rotFld R x := by
  funext p
  simp only [rotFld, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The ray terms of the hat-variable block expansion are spin invariant.** -/
theorem rayTermHat_rot (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
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
    {ω : ℂ → ℂ} {x₀ w : unitPts Gp × Fin N → ℂ} {σ : ℂ} {r : ℝ} (hr : 0 < r)
    (hline : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      ∀ p, ‖((σ * (t : ℂ)) • x₀ + τ • w) p‖ ≤ cψ) :
    rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp
      m₀ X₁ (fun u s => fnOfDec Gp Hm X₁f F₁ Sol Φ
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y)
      (rotFld (cmat Q) w)) ω (rotFld (cmat Q) x₀) σ (rotRaw (cmat Q) (rawOf D)) =
    rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp
      m₀ X₁ (fun u s => fnOfDec Gp Hm X₁f F₁ Sol Φ
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y)
      w) ω x₀ σ (rawOf D) :=
  rayTerm_dl3_equiv_of_invariant (B := {z : unitPts Gp × Fin N → ℂ | ∀ p, ‖z p‖ ≤ cψ})
    (rotRaw (cmat Q)) (rotFld (cmat Q)) (DecEquiv.rotFld_add _) (fun c x => rotFld_smul' _ c x)
    (fun _ hz => evTermHat_rot hC hk hG hG' cc hcψ hMX hmar hα hsm hδ₁ hF₁ hSol hQ hΦ Y hD hz)
    hr (fun t ht τ hτ => hline t ht τ hτ)

end RayRot

end Balaban.Localization
