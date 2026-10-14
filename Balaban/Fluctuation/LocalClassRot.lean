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

section ComposeRot

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem svec_rotFld (R : Matrix (Fin N) (Fin N) ℂ) (φ : G'.Ω 1 × Fin N → ℂ)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    svec G' (rotFld R φ) y i = ∑ j, R i j * svec G' φ y j := by
  classical
  unfold svec zeroExt
  by_cases h : y ∈ G'.Ω 1
  · simp only [h, ↓reduceDIte, rotFld]
  · simp [h]

theorem blockMean_sum (n : ℕ) (c : Fin N → ℂ) (w : Fin N → Torus d (N₀ * L ^ k) → ℂ)
    (x : Torus d (N₀ * L ^ k)) :
    blockMean G n (fun y => ∑ j, c j * w j y) x = ∑ j, c j * blockMean G n (w j) x := by
  unfold blockMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem barField_rot_raw (R : Matrix (Fin N) (Fin N) ℂ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G'.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    barField G' (fun x => R *ᵥ Ψ x) (rotFld R φ) x i = ∑ j, R i j * barField G' Ψ φ x j := by
  classical
  unfold barField
  by_cases h : x ∈ G'.Ω 1
  · simp only [h, ↓reduceDIte, rotFld]
  · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct]

/-- **The composed field is covariant**: `ψ(𝔹_j, 𝔹'_k; R Ψ')` built from `R φ'` is `R` times the
one built from `φ'`. -/
theorem composeField_rot (a : ℕ → ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (φ : G'.Ω 1 × Fin N → ℂ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G G' a (rotFld R φ) (fun x => R *ᵥ Ψ x) x i =
      ∑ j, R i j * composeField G G' a φ Ψ x j := by
  classical
  unfold composeField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte]
    have e1 : (fun y => svec G' (rotFld R φ) y i) =
        fun y => ∑ j, R i j * svec G' φ y j := funext fun y => svec_rotFld R φ y i
    rw [e1, blockMean_sum, blockMean_sum]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_add, Finset.sum_add_distrib,
      mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [hx, ↓reduceIte]
    by_cases hc : x ∈ collar G
    · simp only [hc, ↓reduceIte]
      exact barField_rot_raw R Ψ φ x i
    · simp [hc]

/-- The composed datum is covariant. -/
theorem composeData_rot (h : Precedes G G') (a : ℕ → ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (φ : G'.Ω 1 × Fin N → ℂ) (D : BgData G' N) :
    composeData h a (rotFld R φ) (D.rot R) = (composeData h a φ D).rot R := by
  refine Background.BgData.ext' ?_ ?_
  · funext x i
    exact composeField_rot a R φ D.Ψ x i
  · funext x i
    classical
    simp only [composeData, BgData.rot, Matrix.mulVec, dotProduct]
    by_cases hx : x ∈ G.Ω 1
    · simp [hx]
    · simp [hx]

end ComposeRot

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

section ETermRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- The raw datum of `𝔹_k(X)` composed from a triple is covariant. -/
theorem d1Triple_rot (a : ℕ → ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    d1Triple Gp Gk Hm a (rotFld R φ) (rotFld R δφ) (rotU R u) =
      rotRaw R (d1Triple Gp Gk Hm a φ δφ u) := by
  classical
  refine Prod.ext ?_ ?_
  · funext x i
    show composeField Gk Gp a (rotFld R φ) (fun x => R *ᵥ u.1.1 x) x i +
      composeField Gk Hm a (rotFld R δφ) (fun x => R *ᵥ u.2 x) x i =
        (R *ᵥ fun i => composeField Gk Gp a φ u.1.1 x i + composeField Gk Hm a δφ u.2 x i) i
    rw [composeField_rot, composeField_rot]
    simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  · funext x
    show (fun i => if x ∈ Gk.Ω 1 then (R *ᵥ u.1.2 x) i else 0) =
      R *ᵥ fun i => if x ∈ Gk.Ω 1 then u.1.2 x i else 0
    by_cases hx : x ∈ Gk.Ω 1
    · simp [hx]
    · simp only [hx, ↓reduceIte]
      funext i
      simp [Matrix.mulVec, dotProduct]

/-- **`O(N)`-invariance of the old-term functional on the realizable triples, for a sup-separated
parent** (cover form; for the old term `E` invariant under real rotations on the chart of
`𝔹_j(X)`): `Φ_E(R φ, α; R δφ; R u) = Φ_E(φ, α; δφ; u)` for a triple and its rotation, both
realizable.  The composed datum of `𝔹_k(X)` of the rotated triple is the rotated datum
(`d1Triple_rot`), the old background `Fk` and the composition are covariant
(`bgFieldC_rot`, `composeData_rot`). -/
theorem eTermFun_rot_cover {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ k + 1)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hEr : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), E (rotRaw (cmat Q) r) = E r)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (ht' : ((rotFld (cmat Q) t.1.1, t.1.2), rotFld (cmat Q) t.2.1, rotU (cmat Q) t.2.2) ∈
      FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E (rotFld (cmat Q) t.1.1, t.1.2)
        (rotFld (cmat Q) t.2.1) (rotU (cmat Q) t.2.2) =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 := by
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  obtain ⟨D, ψ', hlc, -, -, hd1, hD2, hXj⟩ :=
    eTerm_chain_cover_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk HBj hP hq colk colj hκ hM
      hnum dsX₀ hN hT hr₀ hj hF hFk ht
  obtain ⟨D2, ψ2, hlc2, -, -, hd1', hD2', -⟩ :=
    eTerm_chain_cover_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk HBj hP hq colk colj hκ hM
      hnum dsX₀ hN hT hr₀ hj hF hFk ht'
  set F := flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc with hFdef
  set F2 := flDatum Gk hP hF.hPm (compWeight L a₁)
    (((rotFld (cmat Q) t.1.1, t.1.2), rotFld (cmat Q) t.2.1, rotU (cmat Q) t.2.2) :
      ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))).1.1
    (((rotFld (cmat Q) t.1.1, t.1.2), rotFld (cmat Q) t.2.1, rotU (cmat Q) t.2.2) :
      ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))).2.1
    D2 ψ2 hlc2 with hF2def
  have hrawF2 : rawOf F2 = rawOf (F.rot (cmat Q)) := by
    rw [← hd1']
    show d1Triple Gp Gk Hm (compWeight L a₁) (rotFld (cmat Q) t.1.1) (rotFld (cmat Q) t.2.1)
      (rotU (cmat Q) t.2.2) = _
    rw [d1Triple_rot, hd1]
    rfl
  have hF2 : F2 = F.rot (cmat Q) :=
    Background.BgData.ext' (congrArg Prod.fst hrawF2) (congrArg Prod.snd hrawF2)
  have e1 : eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      E (rawOf (composeData hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) F) F)) := by
    show E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1
      t.2.2)) = _
    rw [hd1, hD2]
  have e2 : eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E (rotFld (cmat Q) t.1.1, t.1.2)
      (rotFld (cmat Q) t.2.1) (rotU (cmat Q) t.2.2) =
      E (rawOf (composeData hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) F2) F2)) := by
    show E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁)
      (rotFld (cmat Q) t.1.1) (rotFld (cmat Q) t.2.1) (rotU (cmat Q) t.2.2))) = _
    rw [hd1', hD2']
  rw [e1, e2, hF2, (bgFieldC_rot (compWeight L a₁) ν hR (bgC0 d L N) F).1, composeData_rot]
  exact hEr _ ⟨_, hXj, rfl⟩

end ETermRot

end Balaban.Localization
