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

/-- **`O(N)` covariance of the decoupled background for the cover of `𝔹_{k+1}`** (cover form of
`F₁_rot`, with `Dec2.DecSpecs`, `Dec2.CoverBase` in place of `FlCore`):
`F₁ (s, R Θ) = (R φ_{k+1}(s), α_{k+1}(s))` for a real orthogonal `R` and `Θ` a datum of the chart
`Ξ^c(𝔹; 1, ε')`.  The rotation step is `F₁_rot_of_isBg`, shared with `F₁_rot`. -/
theorem F₁_rot_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) :
    F₁ (s, rotRaw (cmat Q) (rawOf D)) =
      (rotFld (cmat Q) (F₁ (s, rawOf D)).1, (F₁ (s, rawOf D)).2) := by
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD
  have hFe : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hU φ α ⟨hI.small, hI.fixed, hI.field⟩
  rw [hFe]
  exact F₁_rot_of_isBg (N := N) (Gp := Gp) (ν := ν) (BG := BG) (κ := κ)
    (P := fun s D φ α => Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    hF₁ hQ (fun s D φ α h =>
      (DecEquiv.isDecBg2_rot_iff (C := coverOf Gp) (H := Gp) (a := compWeight L a₁) (ν := ν) hR
        (rho4 d L N BG κ) s D φ α).2 h) hs hU ⟨hI.small, hI.fixed, hI.field⟩

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
    have := F₁_rot_cover hS S HBp hκ hM heps hsmall hc7 hF₁ hs hD hQ
    rw [this, hF]
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

section HatRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {a₁ ν : ℝ}

/-- `(1 ⊗ Qᵀ)` applied to a real hat vector, cast to the complex numbers. -/
theorem rotFld_transpose_cast {ι : Type*} (Q : Matrix (Fin N) (Fin N) ℝ) (ψ : ι × Fin N → ℝ) :
    rotFld (cmat Q)ᵀ (fun r => (ψ r : ℂ)) =
      fun r => ((∑ j, Q j r.2 * ψ (r.1, j) : ℝ) : ℂ) := by
  funext r
  simp [rotFld, cmat, Matrix.transpose_apply]

/-- **The local hat lift is covariant**: the lift at the rotated datum of `ψ̂` is the rotation of the
lift at the datum of `(1 ⊗ Qᵀ) ψ̂` (cover form: the hypotheses are those of
`decCovSqrt_rot_cover` at the background field of the datum). -/
theorem localHatLift_rot_cover {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {s : Dec2.DecParams (coverOf Gp)} {D : BgData Gp N}
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {φ : Gp.Ω 1 × Fin N → ℂ} {α : Gp.Ω 1 → ℂ} (hFe : F₁ (s, rawOf D) = (φ, α))
    (hFr : F₁ (s, rotRaw (cmat Q) (rawOf D)) = (rotFld (cmat Q) φ, α))
    {κ Cx δc : ℝ}
    (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf Gp) Gp (compWeight L a₁) a₁ ν x α κ
      (Dec2.extS (coverOf Gp) s) Cx)
    (hφ : IsConstraintField Gp δc (barField Gp D.Ψ φ)) (hδ : 0 ≤ δc)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hU : IsUnitLattice Gp (unitQ Gp) (unitP Gp)) (cc : ℂ) (ψ : unitPts Gp × Fin N → ℝ) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rotRaw (cmat Q) (rawOf D))).2
          (Dec2.extS (coverOf Gp) s)
          (barField Gp (rotRaw (cmat Q) (rawOf D)).1 (F₁ (s, rotRaw (cmat Q) (rawOf D))).1)
          (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
      else 0) =
    fun x => cmat Q *ᵥ (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2
          (Dec2.extS (coverOf Gp) s) (barField Gp D.Ψ (F₁ (s, rawOf D)).1)
          (unitQ Gp) (unitP Gp) *ᵥ
          (fun r => ((∑ j, Q j r.2 * ψ (r.1, j) : ℝ) : ℂ)))) (⟨unitBlock x, h⟩, i)
      else 0) x := by
  classical
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  rw [hFr, hFe]
  have hbar : barField Gp (rotRaw (cmat Q) (rawOf D)).1 (rotFld (cmat Q) φ) =
      DecEquiv.rotSite (cmat Q) (barField Gp D.Ψ φ) := by
    funext x i
    exact barField_rot_raw (cmat Q) D.Ψ φ x i
  have hsq := Fluctuation.decCovSqrt_rot_cover hR hfam hφ hδ hsm hU
  simp only at hbar ⊢
  rw [hbar, hsq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rotLift_mulVec, rotLift_mulVec,
    rotFld_transpose_cast]
  funext x i
  by_cases h : unitBlock x ∈ unitPts Gp
  · simp only [h, ↓reduceDIte, Pi.smul_apply, smul_eq_mul, rotFld, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring_nf
  · simp [h, Matrix.mulVec, dotProduct]

end HatRot

section HatIntegralRot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*}

/-- The real rotation `ψ̂ ↦ (1 ⊗ Qᵀ) ψ̂` of the hat variables is a measurable embedding (a
homeomorphism, with inverse `(1 ⊗ Q)`). -/
theorem measurableEmbedding_hatRot {I : Type*} [Fintype I] {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Qᵀ * Q = 1) :
    MeasurableEmbedding (fun (ψ : I × Fin N → ℝ) (r : I × Fin N) => ∑ j, Q j r.2 * ψ (r.1, j)) := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQ
  let e : (I × Fin N → ℝ) ≃ₜ (I × Fin N → ℝ) :=
    { toFun := fun ψ r => ∑ j, Q j r.2 * ψ (r.1, j)
      invFun := fun ψ r => ∑ j, Q r.2 j * ψ (r.1, j)
      left_inv := by
        intro ψ
        funext r
        have h := congrFun (Matrix.mulVec_mulVec (fun l => ψ (r.1, l)) Q Qᵀ) r.2
        rw [hQ', Matrix.one_mulVec] at h
        simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h
      right_inv := by
        intro ψ
        funext r
        have h := congrFun (Matrix.mulVec_mulVec (fun l => ψ (r.1, l)) Qᵀ Q) r.2
        rw [hQ, Matrix.one_mulVec] at h
        simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact e.measurableEmbedding

/-- **The `ψ̂`-integral of a local term is `O(N)`-invariant** (rotation step of the clause `rotE` for
the term `E_X(Y)` of the local class, real rotations; cover form).  For a real orthogonal `Q`, a
compact set `K` of hat variables and a measure `γ` that are invariant under `ψ̂ ↦ (1 ⊗ Qᵀ) ψ̂`, and
a functional `Φ` invariant on realizable triples, the integral
`G(Θ, w) = ∫_K Φ(F₁(σ w, Θ), Sol(σ w, …), (Θ, cc C^{1/2}(σ w) ψ̂)) dγ(ψ̂)` satisfies
`G(R Θ, w) = G(Θ, w)` at the data `Θ` of the chart and the parameters `w` of the polydisc.  (`G` is
introduced through its defining equation `hGf`.) -/
theorem localHat_integral_rot_cover (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
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
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ∈
        FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    (hKQ : ∀ ψ : unitPts Gp × Fin N → ℝ,
      (fun r : unitPts Gp × Fin N => ∑ j, Q j r.2 * ψ (r.1, j)) ∈ K ↔ ψ ∈ K)
    (hγQ : Measure.map (fun (ψ : unitPts Gp × Fin N → ℝ) (r : unitPts Gp × Fin N) =>
      ∑ j, Q j r.2 * ψ (r.1, j)) γ = γ)
    (Gf : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGf : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gf Θ w =
      ∫ ψ in K,
        Φ (F₁ (σ w, Θ))
          (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0) ∂γ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {w : ι → ℂ}
    (hw : w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) :
    Gf (rotRaw (cmat Q) (rawOf D)) w = Gf (rawOf D) w := by
  classical
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  have hs : ∀ P, ‖σ w P‖ < Real.exp κ := hσκ w hw
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD
  have hUd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  have hFe : F₁ (σ w, rawOf D) = (φ, α) := hF₁ (σ w) D hs hUd φ α ⟨hI.small, hI.fixed, hI.field⟩
  have hFr : F₁ (σ w, rotRaw (cmat Q) (rawOf D)) = (rotFld (cmat Q) φ, α) := by
    rw [F₁_rot_cover hS S HBp hκ hM heps hsmall hc7 hF₁ hs hD hQ, hFe]
  have hdom := decDom_of_coverBg hS S HBp hκ.le hM heps hsmall hc7 hphi hs hD hI hmarD hαD
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have SX : Dec2.XCover (coverOf Gp) Gp (compWeight L a₁) a₁ ν Cx :=
    ⟨S.toCoverGeom, hk1, ha₁, ha₂⟩
  have hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf Gp) Gp (compWeight L a₁) a₁ ν x α κ
      (Dec2.extS (coverOf Gp) (σ w)) Cx := fun x hx =>
    xData_cover_of_mem (N := N) SX hCx hx hκ.le hMX (e := (σ w, (barField Gp D.Ψ φ, α))) hdom
  have hφc : IsConstraintField Gp δc (barField Gp D.Ψ φ) := hdom.2.1.toIsConstraintField
  have hUL := (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
  have hTK : ∀ ψ ∈ K, (fun r : unitPts Gp × Fin N => ∑ j, Q j r.2 * ψ (r.1, j)) ∈ K :=
    fun ψ hψ => (hKQ ψ).2 hψ
  let lift : (unitPts Gp × Fin N → ℝ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
    fun ψ' (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, rawOf D)).2
          (Dec2.extS (coverOf Gp) (σ w)) (barField Gp D.Ψ (F₁ (σ w, rawOf D)).1)
          (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ' r : ℂ)))) (⟨unitBlock x, h⟩, i)
      else 0
  let Hm' : (unitPts Gp × Fin N → ℝ) → ℂ := fun ψ' =>
    Φ (F₁ (σ w, rawOf D)) (Sol (σ w, flEdat Gp Hm (F₁ (σ w, rawOf D)) D.Ψ (lift ψ'))).1
      (rawOf D, lift ψ')
  have e2 : Gf (rawOf D) w = ∫ ψ in K, Hm' ψ ∂γ := hGf _ _
  have e1 : Gf (rotRaw (cmat Q) (rawOf D)) w =
      ∫ ψ in K, Hm' (fun r : unitPts Gp × Fin N => ∑ j, Q j r.2 * ψ (r.1, j)) ∂γ := by
    rw [hGf]
    refine setIntegral_congr_fun hKc.isClosed.measurableSet fun ψ hψ => ?_
    have hlift := localHatLift_rot_cover (Gp := Gp) (a₁ := a₁) (ν := ν) hQ (D := D) (s := σ w)
      (F₁ := F₁) hFe hFr hfam hφc hδc hsm hUL cc ψ
    have hψ' : lift (fun r : unitPts Gp × Fin N => ∑ j, Q j r.2 * ψ (r.1, j)) ∈
        FlBallLC Hm δ₁ := by
      refine localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS S HBp hκ.le hM hMX hCx hF₁ heps
        hsmall hc7 hphi hmarD hαD hsm hs hD cc hcψ hδ₁0 hδ₁
        (ψh := fun r => ((∑ j, Q j r.2 * ψ (r.1, j) : ℝ) : ℂ)) fun r => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hKb _ (hTK ψ hψ) r
    show _ = Hm' _
    rw [hlift]
    exact fanLC_rot_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁0 hPmp hF₁ hSol hQ hΦ hs
      (hσ1 w) hD hψ'
  rw [e1, e2]
  have hemb := measurableEmbedding_hatRot (I := unitPts Gp) hQ
  have h3 := hemb.setIntegral_map (μ := γ) Hm' K
  rw [hγQ] at h3
  have hpre : (fun (ψ : unitPts Gp × Fin N → ℝ) (r : unitPts Gp × Fin N) =>
      ∑ j, Q j r.2 * ψ (r.1, j)) ⁻¹' K = K := Set.ext fun ψ => hKQ ψ
  rw [hpre] at h3
  exact h3.symm

end HatIntegralRot

end Balaban.Localization
