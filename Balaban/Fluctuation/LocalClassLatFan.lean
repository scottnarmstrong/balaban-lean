/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassLatCore

/-!
# Lattice covariance of the local terms: the fan composite and the old-term functional

The two-set forms of `fanLC_rot_cover` and `eTermFun_rot_cover` (`LocalClassRot.lean`):

* `fanLC_sym_cover_pair`: the fan composite `Φ(F₁(s, Θ), Sol(s, …), (Θ, ψ'))` of the generating set
  `𝔹` and its transport `Φ'(F₁'(s', σ Θ), Sol'(s', …), (σ Θ, σ ψ'))` on `𝔹'` agree, for a
  functional `Φ'` that is the transport of `Φ` on the realizable triples;
* `eTermFun_sym_cover_pair`: the old-term functional `Φ_E` of `(𝔹, 𝔹_k, 𝔹_j, H⁻)` is transported
  to that of `(𝔹', 𝔹'_k, 𝔹'_j, H'⁻)` on the realizable triples, for old terms with
  `E'(σ r) = E(r)` on the chart of `𝔹_j(X)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.Localization.DecEquiv Finset Matrix

section FanPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp Gp₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable {τ τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}

/-- A field of the fluctuation ball is carried to the fluctuation ball of the image set. -/
theorem symSite_mem_flBallLC (Sm : LatSymm Hm Hm₂ σ) {δ₁ : ℝ}
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    symSite σ ψ' ∈ FlBallLC Hm₂ δ₁ := by
  refine ⟨fun x hx => ?_, isLayerConstant_sym Sm hψ.2⟩
  obtain ⟨z, rfl⟩ := σ.surjective x
  show vn (ψ' (σ.symm (σ z))) < δ₁
  rw [Equiv.symm_apply_apply]
  exact hψ.1 z ((Sm.mem_dataSites z).1 hx)

/-- **The fan composite of the cover of `𝔹_{k+1}` is transported between two generating sets**
(two-set form of `fanLC_rot_cover`): if `Φ'` is the transport of `Φ` on the realizable triples
whose transport is realizable, then
`Φ'(F₁'(s', σ Θ), Sol'(s', …), (σ Θ, σ ψ')) = Φ(F₁(s, Θ), Sol(s, …), (Θ, ψ'))` for `s' ∘ τ = s`. -/
theorem fanLC_sym_cover_pair {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sc : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (Sc₂ : Dec2.CoverBase (coverOf Gp₂) Gp₂ (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp) (hPmp₂ : Precedes Hm₂ Gp₂)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {F₁' : Dec2.DecParams (coverOf Gp₂) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp₂.Ω 1 × Fin N → ℂ) × (Gp₂.Ω 1 → ℂ)}
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gp₂)) (D : BgData Gp₂ N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp₂ (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp₂.Ω 1 × Fin N → ℂ)
        (α : Gp₂.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp₂) Gp₂ (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
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
    {Sol' : Dec2.DecParams (coverOf Gp₂) × Edat Hm₂ N → (Hm₂.Ω 1 × Fin N → ℂ) × (Hm₂.Ω 1 → ℂ)}
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gp₂) × Edat Hm₂ N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi Hm₂ (Dec2.decG (coverOf Gp₂) Hm₂ (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gp₂) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hm₂ (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm₂ (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm₂ (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm₂.Ω 1 → ℂ, Small Hm₂ δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp₂) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {X₁f X₁f₂ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (S : LatSymm Gp Gp₂ σ) (Sm : LatSymm Hm Hm₂ σ)
    (hidx : ∀ q, τ q ∈ (coverOf Gp₂).cubeIdx ↔ q ∈ (coverOf Gp).cubeIdx)
    (hchi : ∀ q x, (coverOf Gp₂).chi (τ q) (σ x) = (coverOf Gp).chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ (coverOf Gp₂).Qset (τ q) ↔ q' ∈ (coverOf Gp).Qset q)
    (hbidx : ∀ q, τb q ∈ blockIdx Gp₂ ↔ q ∈ blockIdx Gp) (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx Gp, jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 (σ.symm (τb q).2) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 q.2)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gp₂.Ω 1 × Fin N → ℂ) × (Gp₂.Ω 1 → ℂ)) → (Hm₂.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((S.fld bg.1, S.mul bg.2), Sm.fld δφ, symU σ u) ∈
        FlRealLC Gp₂ Hm₂ a₁ ν BG κ eps X₁f₂ BG₂ δ₁ →
      Φ' (S.fld bg.1, S.mul bg.2) (Sm.fld δφ) (symU σ u) = Φ bg δφ u)
    {s : Dec2.DecParams (coverOf Gp)} {s' : Dec2.DecParams (coverOf Gp₂)}
    (hss : ∀ P, Dec2.extS (coverOf Gp₂) s' (τ P) = Dec2.extS (coverOf Gp) s P)
    (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    (hs1' : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp₂).cubeIdx),
      P ∉ (coverOf Gp₂).parCubes X₁f₂ → s' ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    Φ' (F₁' (s', symRaw σ (rawOf D)))
      (Sol' (s', flEdat Gp₂ Hm₂ (F₁' (s', symRaw σ (rawOf D))) (symRaw σ (rawOf D)).1
        (symSite σ ψ'))).1 (symRaw σ (rawOf D), symSite σ ψ') =
    Φ (F₁ (s, rawOf D)) (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1 (rawOf D, ψ') := by
  have hs' := norm_lt_of_extS_pair hidx hss hs
  have hD' := xiCData_sym_pair S hD
  have hψ' := symSite_mem_flBallLC Sm hψ
  obtain ⟨φ, α, δφ, δα, hI, hF, hstr, hS1, hmem⟩ :=
    point_facts_core_cover hS Sc HBp hκ hM heps hsmall hc7 hphi hδ₁ hPmp hF₁ hSol hs hs1 hD hψ.1
  obtain ⟨φ', α', δφ', δα', hI', hF', hstr', hS1', hmem'⟩ :=
    point_facts_core_cover hS Sc₂ HBp hκ hM heps hsmall hc7 hphi hδ₁ hPmp₂ hF₁' hSol' hs' hs1'
      hD' hψ'.1
  have hF'' : F₁' (s', symRaw σ (rawOf D)) = (S.fld φ, S.mul α) := by
    rw [← rawOf_sym_pair S D, F₁_sym_cover_pair hS Sc HBp hκ hM heps hsmall hc7 hF₁ hF₁' S hidx
      hchi hbox hqset hbidx hblayer hbump hbbase hss hs hD, hF]
  have hF3 : F₁' (s', rawOf (S.sym D)) = (φ', α') := hF'
  have hpa : (φ', α') = (S.fld φ, S.mul α) := by rw [← hF3]; exact hF''
  obtain ⟨h1, h2⟩ := Prod.mk.inj hpa
  subst φ'
  subst α'
  have hE := flEdat_sym_pair S Sm (φ, α) D.Ψ ψ'
  have hSolr := Sol_sym_pair hSol hSol' Sm hidx hchi hbox hqset hss hs
    (φ₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').1) (α₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1)
    (δΨ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1) (f₁ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)
    hstr (by rw [← hE]; exact hstr')
  have hSa : (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := by rw [hS1]
  have hSb : (Sol' (s', flEdat Gp₂ Hm₂ (S.fld φ, S.mul α) (symSite σ D.Ψ)
      (symSite σ ψ'))).1 = Sm.fld δφ := by
    rw [hE, hSolr, hSa]
  rw [hF'', hF]
  show Φ' (S.fld φ, S.mul α) (Sol' (s', flEdat Gp₂ Hm₂ (S.fld φ, S.mul α)
      (symSite σ D.Ψ) (symSite σ ψ'))).1 (symU σ (rawOf D, ψ')) = _
  rw [hSb, hS1]
  show Φ' (S.fld (φ, α).1, S.mul (φ, α).2) (Sm.fld δφ) (symU σ (rawOf D, ψ')) = _
  have hm1 : ((φ, α), δφ, (rawOf D, ψ')) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ :=
    ⟨hmem, hψ.2⟩
  have hm2 : ((S.fld (φ, α).1, S.mul (φ, α).2), Sm.fld δφ, symU σ (rawOf D, ψ')) ∈
      FlRealLC Gp₂ Hm₂ a₁ ν BG κ eps X₁f₂ BG₂ δ₁ := by
    have hδ' : δφ' = Sm.fld δφ := by
      have h0 := congrArg Prod.fst hS1'
      exact h0.symm.trans hSb
    have h3 : ((S.fld φ, S.mul α), δφ', rawOf (S.sym D), symSite σ ψ') ∈
        FlRealLC Gp₂ Hm₂ a₁ ν BG κ eps X₁f₂ BG₂ δ₁ := ⟨hmem', hψ'.2⟩
    rw [hδ'] at h3
    exact h3
  exact hΦ (φ, α) δφ (rawOf D, ψ') hm1 hm2

end FanPair

section ETermPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp Gp₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk Gk₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj Gj₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- **The old-term functional is transported on the realizable triples between two families of
generating sets** (two-set form of `eTermFun_rot_cover`): for an old term with `E'(σ r) = E(r)` on
the chart of `𝔹_j(X)`, `Φ'_E(σ φ, σ α; σ δφ; σ u) = Φ_E(φ, α; δφ; u)` for a realizable triple whose
transport is realizable.  The composed datum of `𝔹_k` of the transported triple is the transported
datum (`d1Triple_sym_pair`), the old background and the composition are transported
(`LatSymm.bgFieldC_sym`, `composeData_sym_pair`). -/
theorem eTermFun_sym_cover_pair {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sc : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁)
    (Sc₂ : Dec2.CoverBase (coverOf Gp₂) Gp₂ (compWeight L a₁) ν Kc Cx) (hG₂ : CubeAligned Gp₂ m₁)
    (hSS₂ : SupSep Gp₂ m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    (hP₂ : Precedes Gk₂ Gp₂) (hq₂ : Precedes Gj₂ Gk₂)
    (colk₂ : ∀ z ∈ collar Gk₂, z ∈ Gp₂.Ω 1) (colj₂ : ∀ z ∈ collar Gj₂, z ∈ Gk₂.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f X₀₂ X₁f₂ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (dsX₀₂ : ∀ x ∈ dataSites Gk₂, x ∈ X₀₂)
    (hN₂ : ∀ x ∈ X₀₂, x ∈ Gp₂.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp₂.spacing x →
        y ∈ X₁f₂)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ k + 1)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hF₂ : FlSetting N Gp₂ Gk₂ Hm₂ a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f₂)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Fk₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk₂.Ω 1 × Fin N → ℂ) × (Gk₂.Ω 1 → ℂ)}
    (hFk₂ : ∀ D : BgData Gk₂ N, InUnionDomainC Gk₂ (bgC0 d L N) (bgC1 d L N) ν D →
      Fk₂ (rawOf D) = (bgFieldC Gk₂ (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk₂ (compWeight L a₁) ν (bgC0 d L N) D))
    {E E₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (S : LatSymm Gp Gp₂ σ) (Sk : LatSymm Gk Gk₂ σ) (Sj : LatSymm Gj Gj₂ σ)
    (Sm : LatSymm Hm Hm₂ σ)
    (hEr : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), E₂ (symRaw σ r) = E r)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (ht' : ((S.fld t.1.1, S.mul t.1.2), Sm.fld t.2.1, symU σ t.2.2) ∈
      FlRealLC Gp₂ Hm₂ a₁ ν BG κ eps X₁f₂ BG₂ δ₁) :
    eTermFun Gp₂ Gk₂ Gj₂ Hm₂ (compWeight L a₁) Fk₂ E₂ (S.fld t.1.1, S.mul t.1.2)
        (Sm.fld t.2.1) (symU σ t.2.2) =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 := by
  obtain ⟨D, ψ', hlc, -, -, hd1, hD2, hXj⟩ :=
    eTerm_chain_cover_of_one_le hb₁ hbC hS Sc hG hSS hMM ha₁ HBp HBk HBj hP hq colk colj hκ hM
      hnum dsX₀ hN hT hr₀ hj hF hFk ht
  obtain ⟨D2, ψ2, hlc2, -, -, hd1', hD2', -⟩ :=
    eTerm_chain_cover_of_one_le hb₁ hbC hS Sc₂ hG₂ hSS₂ hMM ha₁ HBp HBk HBj hP₂ hq₂ colk₂ colj₂
      hκ hM hnum dsX₀₂ hN₂ hT hr₀ hj hF₂ hFk₂ ht'
  set F := flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc with hFdef
  set F2 := flDatum Gk₂ hP₂ hF₂.hPm (compWeight L a₁)
    (((S.fld t.1.1, S.mul t.1.2), Sm.fld t.2.1, symU σ t.2.2) :
      ((Gp₂.Ω 1 × Fin N → ℂ) × (Gp₂.Ω 1 → ℂ)) × (Hm₂.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))).1.1
    (((S.fld t.1.1, S.mul t.1.2), Sm.fld t.2.1, symU σ t.2.2) :
      ((Gp₂.Ω 1 × Fin N → ℂ) × (Gp₂.Ω 1 → ℂ)) × (Hm₂.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))).2.1
    D2 ψ2 hlc2 with hF2def
  have hrawF2 : rawOf F2 = rawOf (Sk.sym F) := by
    rw [← hd1']
    show d1Triple Gp₂ Gk₂ Hm₂ (compWeight L a₁) (S.fld t.1.1) (Sm.fld t.2.1)
      (symU σ t.2.2) = _
    rw [d1Triple_sym_pair S Sk Sm hP hF.hPm, hd1]
    rfl
  have hF2 : F2 = Sk.sym F :=
    Background.BgData.ext' (congrArg Prod.fst hrawF2) (congrArg Prod.snd hrawF2)
  have e1 : eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      E (rawOf (composeData hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) F) F)) := by
    show E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1
      t.2.2)) = _
    rw [hd1, hD2]
  have e2 : eTermFun Gp₂ Gk₂ Gj₂ Hm₂ (compWeight L a₁) Fk₂ E₂ (S.fld t.1.1, S.mul t.1.2)
      (Sm.fld t.2.1) (symU σ t.2.2) =
      E₂ (rawOf (composeData hq₂ (compWeight L a₁)
        (bgFieldC Gk₂ (compWeight L a₁) ν (bgC0 d L N) F2) F2)) := by
    show E₂ (D2raw Gk₂ Gj₂ (compWeight L a₁) Fk₂ (d1Triple Gp₂ Gk₂ Hm₂ (compWeight L a₁)
      (S.fld t.1.1) (Sm.fld t.2.1) (symU σ t.2.2))) = _
    rw [hd1', hD2']
  rw [e1, e2, hF2, (Sk.bgFieldC_sym (compWeight L a₁) ν (bgC0 d L N) F).1,
    composeData_sym_pair Sj Sk hq hq₂, rawOf_sym_pair]
  exact hEr _ ⟨_, hXj, rfl⟩

end ETermPair

end Balaban.Localization
