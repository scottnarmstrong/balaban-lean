/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetRotation
public import Balaban.Fluctuation.LocalHatTerm
public import Balaban.Fluctuation.InteractionSymmSolRot

/-!
# Rotation covariance of the local class (clause `rotE`), real rotations

The square root of the decoupled covariance is covariant under spin rotations
(`decCovSqrt_rot_cover`, in the cover form of the integrability theorem
`integrable_decSqrtInt_cover`; `decCovSqrt_rot` for `CovStanding`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv MeasureTheory
  Finset Matrix

section Sqrt

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- **Covariance of the square root `C^{1/2}(s)` under spin rotations** (cover form): the
hypotheses are those of `integrable_decSqrtInt_cover`, so that the entrywise integral commutes with
the two-sided constant factor. -/
theorem decCovSqrt_rot_cover {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {a : ℕ → ℝ}
    {aT ν : ℝ} {α : G.Ω 1 → ℂ} {κ Cx : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hU : IsUnitLattice G Q P) :
    decCovSqrt G a aT ν α s (rotSite R φ) Q P =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * decCovSqrt G a aT ν α s φ Q P *
        rotLift Rᵀ := by
  have hint := fun p q => integrable_decSqrtInt_cover hfam hφ hδ hsm hU p q
  have hfun : decSqrtInt G a aT ν α s (rotSite R φ) Q P =
      fun x => (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) *
        decSqrtInt G a aT ν α s φ Q P x * rotLift Rᵀ := by
    funext x
    unfold decSqrtInt
    rw [decCov_rot hR, Matrix.mul_smul, Matrix.smul_mul]
  unfold decCovSqrt
  rw [hfun, intMat_conj hint, Matrix.mul_smul, Matrix.smul_mul]

/-- **Covariance of the square root `C^{1/2}(s)` under spin rotations**, under `CovStanding`. -/
theorem decCovSqrt_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {a : ℕ → ℝ}
    {aT ν : ℝ} {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) :
    decCovSqrt G a aT ν α s (rotSite R φ) Q P =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * decCovSqrt G a aT ν α s φ Q P *
        rotLift Rᵀ :=
  decCovSqrt_rot_cover hR (fun x hx => (H.fam x hx).toCover) H.field H.nonneg H.small H.unit

end Sqrt

end Balaban.Fluctuation

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Finset Matrix MeasureTheory

section FanRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- A layer-constant field stays layer-constant under a pointwise rotation. -/
theorem isLayerConstant_rot {R : Matrix (Fin N) (Fin N) ℂ}
    {z : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hz : IsLayerConstant Hm z) :
    IsLayerConstant Hm (fun x => R *ᵥ z x) := by
  intro m h1 h2 x hx x' hx'
  exact congrArg (fun v => R *ᵥ v) (hz m h1 h2 x hx x' hx')

/-- **`O(N)` covariance of the fan composite for the cover of `𝔹_{k+1}`** (cover form of
`fnOfDecSol_rot`, at a point and with the local hypotheses `Dec2.DecSpecs`, `Dec2.CoverBase`
in place of `FlCore`): if `Φ` is invariant under `(R φ, α; R δφ; R u)` on the realizable triples
whose rotation is again realizable, then
`Φ(F₁(s, R Θ), Sol(s, …), (R Θ, R ψ')) = Φ(F₁(s, Θ), Sol(s, …), (Θ, ψ'))`. -/
theorem fanLC_rot_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ∈
        FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    Φ (F₁ (s, rotRaw (cmat Q) (rawOf D)))
      (Sol (s, flEdat Gp Hm (F₁ (s, rotRaw (cmat Q) (rawOf D))) (rotRaw (cmat Q) (rawOf D)).1
        (fun x => cmat Q *ᵥ ψ' x))).1 (rotRaw (cmat Q) (rawOf D), fun x => cmat Q *ᵥ ψ' x) =
    Φ (F₁ (s, rawOf D)) (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1 (rawOf D, ψ') := by
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  have hD' := xiCData_rot hQ hD
  have hψ1 : ψ' ∈ FlBall Hm δ₁ := hψ.1
  have hψ1' : (fun x => cmat Q *ᵥ ψ' x) ∈ FlBall Hm δ₁ := fun x hx => by
    show vn (cmat Q *ᵥ ψ' x) < δ₁
    rw [vn_rot (isRealOrth_ofReal hQ)]
    exact hψ1 x hx
  have hlc' : IsLayerConstant Hm (fun x => cmat Q *ᵥ ψ' x) := isLayerConstant_rot hψ.2
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  obtain ⟨φ, α, δφ, δα, hI, hF, hstr, hS1, hmem⟩ :=
    point_facts_core_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁ hPmp hF₁ hSol hs hs1 hD hψ1
  obtain ⟨φ', α', δφ', δα', hI', hF', hstr', hS1', hmem'⟩ :=
    point_facts_core_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁ hPmp hF₁ hSol hs hs1 hD'
      hψ1'
  have hF'' : F₁ (s, rotRaw (cmat Q) (rawOf D)) = (rotFld (cmat Q) φ, α) := by
    exact F₁_rot_of_isBg (N := N) (Gp := Gp) (ν := ν) (BG := BG) (κ := κ)
      (P := fun s D φ α => Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
      hF₁ hQ (fun s D φ α h =>
        (DecEquiv.isDecBg2_rot_iff (C := coverOf Gp) (H := Gp) (a := compWeight L a₁) (ν := ν) hR
          (rho4 d L N BG κ) s D φ α).2 h) hs hU hI
  have hF3 : F₁ (s, rawOf (D.rot (cmat Q))) = (φ', α') := hF'
  have hpa : (φ', α') = (rotFld (cmat Q) φ, α) := by rw [← hF3]; exact hF''
  obtain ⟨h1, h2⟩ := Prod.mk.inj hpa
  subst φ'
  subst α'
  have hE := flEdat_rot (Gp := Gp) (Hm := Hm) (cmat Q) (φ, α) D.Ψ ψ'
  have hSolr := Sol_rot (Gp := Gp) (Hm := Hm) (a₁ := a₁) (ν := ν) (BG := BG) (BG₂ := BG₂)
    (κ := κ) (eps := eps) (δ₁ := δ₁) hSol hR hs
    (φ₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').1) (α₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1)
    (δΨ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1) (f₁ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)
    hstr (by rw [← hE]; exact hstr')
  have hSa : (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := by rw [hS1]
  have hSb : (Sol (s, flEdat Gp Hm (rotFld (cmat Q) φ, α) (DecEquiv.rotSite (cmat Q) D.Ψ)
      (DecEquiv.rotSite (cmat Q) ψ'))).1 = rotFld (cmat Q) δφ := by
    rw [hE, hSolr, hSa]
  rw [hF'', hF]
  show Φ (rotFld (cmat Q) φ, α) (Sol (s, flEdat Gp Hm (rotFld (cmat Q) φ, α)
      (DecEquiv.rotSite (cmat Q) D.Ψ) (DecEquiv.rotSite (cmat Q) ψ'))).1
      (rotU (cmat Q) (rawOf D, ψ')) = _
  rw [hSb, hS1]
  show Φ (rotFld (cmat Q) (φ, α).1, (φ, α).2) (rotFld (cmat Q) δφ) (rotU (cmat Q) (rawOf D, ψ')) = _
  have hm1 : ((φ, α), δφ, (rawOf D, ψ')) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ :=
    ⟨hmem, hψ.2⟩
  have hm2 : ((rotFld (cmat Q) (φ, α).1, (φ, α).2), rotFld (cmat Q) δφ,
      rotU (cmat Q) (rawOf D, ψ')) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
    have hδ' : δφ' = rotFld (cmat Q) δφ := by
      have h0 := congrArg Prod.fst hS1'
      exact h0.symm.trans hSb
    have h3 : ((rotFld (cmat Q) φ, α), δφ', rawOf (BgData.rot (cmat Q) D),
        fun x => cmat Q *ᵥ ψ' x) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := ⟨hmem', hlc'⟩
    rw [hδ'] at h3
    exact h3
  exact hΦ (φ, α) δφ (rawOf D, ψ') hm1 hm2

end FanRot

end Balaban.Localization
