/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystemCanon
public import Balaban.Fluctuation.NewLevelCoeffLoc
public import Balaban.Inhabited.StepTowerThetaDetG

/-!
# The coefficient of the system recomputed from the labels inside the polymer (`NewLevelSystemLoc`)

The recomputed family of route R-LOC is the local formula `NewLevelSystem.coeffLoc` on a local
generating set `Gl` (P3 pp. 78-79): the determinant part plus the interpolation coefficient of the
activities of the labels inside the polymer `T` and the marks of the anchors inside `T`, recomputed
on `Gl` (`actBg`, `markBg`, gate radius `ε′`), each at the configuration restricted to the blocks of
its label.  This file reduces the clauses of the recomputed family to its parts.

* `xiCRaw_mono_radius`: the raw chart grows with the radius;
* `actBg_gate`, `markBg_gate`, `coeffLoc_gate`: on the chart of radius `ε ≤ ε′` the objects and the
  coefficient gated at `ε′` are those gated at `ε`; `actBg_root₁`, `actBg_root₂`: the activities
  vanish on the root-union labels;
* `coeffLoc_congr_of_parts`: the coefficients at two parameters agree when the determinant parts,
  the zero-source and old activities of the labels inside `T`, the bridge marks and the old marks of
  the anchors inside `T` agree (the form of (A3));
* `coeff_eq_coeffLoc_of_agree`: the coefficient of the system equals the local formula at a
  parameter of `Gl` when the determinant parts agree and the activities and marks agree label by
  label inside `T` (the form of (A5), with `agree_canon`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset MeasureTheory
  Balaban.Inhabited.MarkBudgetAudit

section Mono

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The raw chart grows with the radius**: `Ξ^c_n(G; 1, ε) ⊆ Ξ^c_n(G; 1, ε′)` for `ε ≤ ε′`. -/
theorem xiCRaw_mono_radius {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {n : ℕ} {ε ε' : ℝ} (hle : ε ≤ ε') {p : RawData d L (N₁ * L ^ m₁) K N}
    (hp : p ∈ XiCRaw G a ν n 1 ε) : p ∈ XiCRaw G a ν n 1 ε' := by
  obtain ⟨D, hD, rfl⟩ := hp
  exact ⟨D, xiCData_mono_radius zero_le_one hle hD, rfl⟩

end Mono

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl ϱl' : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr) {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
  (F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (F₁L' : NS.O.ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (SolL' : NS.O.ι → Dec2.DecParams (coverOf Gl) × Edat Gd N →
    (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))

/-- **On the chart of radius `ε ≤ ε′` the activities gated at `ε′` are those gated at `ε`.** -/
theorem actBg_gate {eps eps' : ℝ} (hle : eps ≤ eps') {θb : physParamBg N Gl}
    (hθ : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps) :
    NS.actBg F₂' Sol₂' F₁L' SolL' eps' θb = NS.actBg F₂' Sol₂' F₁L' SolL' eps θb := by
  have hθ' := xiCRaw_mono_radius hle hθ
  funext u y Φ
  rcases y with (Y | Y | r) | r
  · simp only [actBg, classActFun, Sum.elim_inl, zeroActBg, hθ, hθ', true_and]
  · simp only [actBg, classActFun, Sum.elim_inl, Sum.elim_inr, oldActBg, hθ, hθ', true_and]
  · rfl
  · rfl

/-- **On the chart of radius `ε ≤ ε′` the marks gated at `ε′` are those gated at `ε`.** -/
theorem markBg_gate {eps eps' : ℝ} (hle : eps ≤ eps') {θb : physParamBg N Gl}
    (hθ : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps) :
    NS.markBg F₁L' SolL' F₁b' Solb' eps' θb = NS.markBg F₁L' SolL' F₁b' Solb' eps θb := by
  have hθ' := xiCRaw_mono_radius hle hθ
  funext i u Φ
  rcases i with i | q
  · simp only [markBg, Sum.elim_inl, e1MarkGParamGBgOn, hθ, hθ', true_and]
  · simp only [markBg, Sum.elim_inr, oldMarkGBg, hθ, hθ', true_and]

/-- The recomputed activities vanish on the root-union labels of the old domains. -/
theorem actBg_root₁ (eps' : ℝ) (θb : physParamBg N Gl) (u : ℂ)
    (r : RootUnionLb 1 (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) :
    NS.actBg F₂' Sol₂' F₁L' SolL' eps' θb u (Sum.inl (Sum.inr (Sum.inr r))) Φ = 0 := rfl

/-- The recomputed activities vanish on the root-union labels of the bridges. -/
theorem actBg_root₂ (eps' : ℝ) (θb : physParamBg N Gl) (u : ℂ)
    (r : RootUnionLb 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) :
    NS.actBg F₂' Sol₂' F₁L' SolL' eps' θb u (Sum.inr r) Φ = 0 := rfl

/-- **On the chart of radius `ε ≤ ε′` the coefficient gated at `ε′` is that gated at `ε`.** -/
theorem coeffLoc_gate {eps eps' : ℝ} (hle : eps ≤ eps') (Zb : Finset (unitPts Gl))
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) {θb : physParamBg N Gl}
    (hθ : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T =
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps Zb Φ₀ θb T := by
  unfold coeffLoc
  exact newLevelCoeffLoc_congr Gl _ _ _ _ _ Zb NS.Lab Φ₀ _ _ NS.y0 _ _ θb θb T rfl
    (fun s _ y _ Φ => congrFun (congrFun (congrFun
      (NS.actBg_gate F₂' Sol₂' F₁L' SolL' hle hθ) (s : ℂ)) y) Φ)
    (fun s _ i _ Φ => congrFun (congrFun (congrFun
      (NS.markBg_gate F₁L' SolL' F₁b' Solb' hle hθ) i) (s : ℂ)) Φ)

/-- **The coefficient of the system recomputed from the labels inside `T` reads its parts on `T`
only** (the form of (A3)): at two parameters `θ_b`, `θ_b'` of `Gl`, if the determinant parts agree,
the zero-source activities and the old activities of the labels inside `T` agree, and the bridge
marks and the old marks of the anchors inside `T` agree (for `s ∈ [0, 1]`, at every configuration),
the coefficients agree. -/
theorem coeffLoc_congr_of_parts (eps' : ℝ) (Zb : Finset (unitPts Gl))
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) {θb θb' : physParamBg N Gl}
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hdet : newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T =
      newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb' T)
    (h0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ NS.Z.I.𝒴}, InPoly T Y.1 → ∀ Φ,
      zeroActBg S Gl (BgTransport.canon S.G' Gl N)
        (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁
        NS.hp eps' θb (s : ℂ) Y.1 Φ =
      zeroActBg S Gl (BgTransport.canon S.G' Gl N)
        (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁
        NS.hp eps' θb' (s : ℂ) Y.1 Φ)
    (h1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ NS.𝒴C}, InPoly T Y.1 → ∀ Φ,
      oldActBg S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps' NS.𝒴C θb Y (s : ℂ) Φ =
      oldActBg S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps' NS.𝒴C θb' Y (s : ℂ) Φ)
    (hb : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z}, InPoly T i.1 → ∀ Φ,
      e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' NS.p₁ NS.hp z Gl eps' θb i (s : ℂ) Φ =
      e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' NS.p₁ NS.hp z Gl eps' θb' i (s : ℂ) Φ)
    (hq : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z},
      InPoly T (bridge 1 z q.1.2) → ∀ Φ,
      oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f
        NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps' z θb q (s : ℂ) Φ =
      oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f
        NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps' z θb' q (s : ℂ) Φ) :
    NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T =
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T := by
  unfold coeffLoc
  refine newLevelCoeffLoc_congr Gl _ _ _ _ _ Zb NS.Lab Φ₀ _ _ NS.y0 _ _ θb θb' T hdet
    (fun s hs y hy Φ => ?_) (fun s hs i hi Φ => ?_)
  · rcases y with (Y | Y | r) | r
    · exact h0 s hs Y hy Φ
    · exact h1 s hs Y hy Φ
    · exact (NS.actBg_root₁ F₂' Sol₂' F₁L' SolL' eps' θb _ r Φ).trans
        (NS.actBg_root₁ F₂' Sol₂' F₁L' SolL' eps' θb' _ r Φ).symm
    · exact (NS.actBg_root₂ F₂' Sol₂' F₁L' SolL' eps' θb _ r Φ).trans
        (NS.actBg_root₂ F₂' Sol₂' F₁L' SolL' eps' θb' _ r Φ).symm
  · rcases i with i | q
    · exact hb s hs i hi Φ
    · exact hq s hs q hi Φ

/-- **The replacement identity with the local formula for the system** (the form of (A5)): the
coefficient of the system at the step's parameter `θ` equals the local formula on `Gl` at `θ_b` when
the determinant parts agree and the activities and marks of the system agree with the recomputed
ones on the labels and anchors inside `T` (the conclusion of `agree_canon`). -/
theorem coeff_eq_coeffLoc_of_agree (eps' : ℝ) (Zb : Finset (unitPts Gl))
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (θ : physParam N S) (θb : physParamBg N Gl)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hdet : newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) (S.blockU z) θ T =
      newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite y) ⊆ T →
      (NS.A θ (s : ℂ)).H y = NS.actBg F₂' Sol₂' F₁L' SolL' eps' θb (s : ℂ) y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i)) ⊆ T →
      NS.G θ i (s : ℂ) = NS.markBg F₁L' SolL' F₁b' Solb' eps' θb i (s : ℂ)) :
    NS.coeff θ T = NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T :=
  newLevelCoeffBg_eq_loc_of_agree Gl (S.blockSplit 1 NS.hp).μ S.G' (compWeight L 1) 1 S.ν
    (rho4 d L N NS.BG NS.κ) (S.blockU z) Zb NS.Lab (NS.A θ) NS.y0 (NS.G θ) θ Φ₀
    (NS.actBg F₂' Sol₂' F₁L' SolL' eps') (NS.markBg F₁L' SolL' F₁b' Solb' eps') θb T hdet
    (NS.G_dep θ) hA hG

open Classical in
/-- **Analyticity and bound of the coefficient recomputed from the labels inside `T`, from its
parts** (the form of (A1), (A2)).  Let `V` be the parameters of the chart of `Gl` of radius
`ε ≤ ε′` (`physVBg`), and let the parts gated at `ε` have, for the labels and anchors inside `T`, the
fields of a `ParamMarkFamily` over `V × 𝒰`: the zero-source and old activities are measurable,
bounded by `ε_H e^{-κ_H d^{cov,1}(Y)}`, analytic in `(θ, u)` at every configuration and continuous in
the configuration; the bridge marks and the old marks are measurable, bounded by
`F₀ᵢ e^{-κ_G 𝗱(y0 i)}`, analytic and continuous.  Under the numerical conditions of Theorem 3.4, if
the determinant part is analytic on `V`, the coefficient gated at `ε′` is analytic on `V` and differs
there from its determinant part by at most `CPE · ∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(y0 i)} · e^{-κ' d_ext(T)}`. -/
theorem coeffLoc_analytic_bound_of_parts {eps eps' : ℝ} (hle : eps ≤ eps')
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (Zb : Finset (unitPts Gl))
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    {εH κH κG κ' : ℝ}
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    {𝒰 : Set ℂ} (hU : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    {Q : Set (∀ b, (S.blockSplit 1 NS.hp).Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hcar : ∀ᵐ Φ ∂(Measure.pi (S.blockSplit 1 NS.hp).μ), Φ ∈ Q)
    -- the zero-source activities of the labels inside `T`
    (h0meas : ∀ θb u (Y : {Y // Y ∈ NS.Z.I.𝒴}), InPoly T Y.1 → Measurable (zeroActBg S Gl
      (BgTransport.canon S.G' Gl N) (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
      (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂'
      taylorWeight NS.p₁ NS.hp eps θb u Y.1))
    (h0bd : ∀ θb u (Y : {Y // Y ∈ NS.Z.I.𝒴}) Φ, InPoly T Y.1 → ‖zeroActBg S Gl
      (BgTransport.canon S.G' Gl N) (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
      (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂'
      taylorWeight NS.p₁ NS.hp eps θb u Y.1 Φ‖ ≤
        εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y.1))
    (h0hol : ∀ Y : {Y // Y ∈ NS.Z.I.𝒴}, InPoly T Y.1 → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gl × ℂ => zeroActBg S Gl
        (BgTransport.canon S.G' Gl N) (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
        (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂'
        taylorWeight NS.p₁ NS.hp eps p.1 p.2 Y.1 Φ)
        (physVBg N Gl S.a₁ S.ν eps ×ˢ 𝒰))
    (h0cont : ∀ Y : {Y // Y ∈ NS.Z.I.𝒴}, InPoly T Y.1 → ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
      ∀ u ∈ 𝒰, Continuous (zeroActBg S Gl
        (BgTransport.canon S.G' Gl N) (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
        (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂'
        taylorWeight NS.p₁ NS.hp eps θb u Y.1))
    -- the old activities of the labels inside `T`
    (h1meas : ∀ θb u (Y : {Y // Y ∈ NS.𝒴C}), InPoly T Y.1 → Measurable (oldActBg S Gl
      (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL
      NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C θb Y u))
    (h1bd : ∀ θb u (Y : {Y // Y ∈ NS.𝒴C}) Φ, InPoly T Y.1 → ‖oldActBg S Gl
      (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL
      NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C θb Y u Φ‖ ≤
        εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y.1))
    (h1hol : ∀ Y : {Y // Y ∈ NS.𝒴C}, InPoly T Y.1 → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gl × ℂ => oldActBg S Gl
        (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL
        NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C p.1 Y p.2 Φ)
        (physVBg N Gl S.a₁ S.ν eps ×ˢ 𝒰))
    (h1cont : ∀ Y : {Y // Y ∈ NS.𝒴C}, InPoly T Y.1 → ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
      ∀ u ∈ 𝒰, Continuous (oldActBg S Gl
        (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL
        NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C θb Y u))
    -- the marks of the anchors inside `T`
    (hGmeas : ∀ θb i u, InPoly T (NS.Lab.ysite (NS.y0 i)) →
      Measurable (NS.markBg F₁L' SolL' F₁b' Solb' eps θb i u))
    (hGbd : ∀ θb i u Φ, InPoly T (NS.Lab.ysite (NS.y0 i)) →
      ‖NS.markBg F₁L' SolL' F₁b' Solb' eps θb i u Φ‖ ≤
        F0 i * Real.exp (-κG * NS.Lab.dl (NS.y0 i)))
    (hGhol : ∀ i, InPoly T (NS.Lab.ysite (NS.y0 i)) → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gl × ℂ =>
        NS.markBg F₁L' SolL' F₁b' Solb' eps p.1 i p.2 Φ) (physVBg N Gl S.a₁ S.ν eps ×ˢ 𝒰))
    (hGcont : ∀ i, InPoly T (NS.Lab.ysite (NS.y0 i)) → ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
      ∀ u ∈ 𝒰, Continuous (NS.markBg F₁L' SolL' F₁b' Solb' eps θb i u))
    -- the numerical conditions of Theorem 3.4
    (hκ0 : aEnt d L + 1 ≤ NS.Z.κ0)
    (hKc : K0 d L NS.Z.κ0 + 1 ≤
      2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 + rootUnionK d L 1 m₁ NS.Z.κ0) +
        rootUnionK d L 1 m₁ NS.Z.κ0)
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hdet : AnalyticOnNhd ℂ
      (fun θb => newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T)
      (physVBg N Gl S.a₁ S.ν eps)) :
    AnalyticOnNhd ℂ (fun θb => NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T)
        (physVBg N Gl S.a₁ S.ν eps) ∧
      ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
        ‖NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T‖ ≤
          ‖newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T‖ +
            CPE d L (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 + rootUnionK d L 1 m₁ NS.Z.κ0) +
              rootUnionK d L 1 m₁ NS.Z.κ0) κH NS.Z.κ0 κ' *
            (∑ i, F0 i * Real.exp (-NS.Z.κ0 * NS.Lab.dl (NS.y0 i))) * Real.exp (-κ' * dExt T) := by
  have hV : IsOpen (physVBg N Gl S.a₁ S.ν eps) := isOpen_physVBg Gl S.a₁ S.ν eps HB'
  have hent := (NS.A 0 0).entropy
  have key := newLevelCoeffLoc_analytic_bound Gl (S.blockSplit 1 NS.hp).μ NS.Z.hN (compWeight L 1)
    1 S.ν (rho4 d L N NS.BG NS.κ) Zb NS.Lab Φ₀ (NS.actBg F₂' Sol₂' F₁L' SolL' eps) NS.y0
    (NS.markBg F₁L' SolL' F₁b' Solb' eps) T (εH := εH) (κH := κH)
    (fun θb u y hy => ?_) (fun θb u y Φ hy => ?_) hent hV hU hseg hQ hQm hcar
    (fun y hy Φ => ?_) (fun y hy θb hθb u hu => ?_) hGmeas hGbd hGhol hGcont hκ0 hKc hεpos hι hF0
    hκ' hκG hκ hε hdet
  · -- the gate: on the chart of radius `ε` the coefficient gated at `ε′` is the one gated at `ε`
    have heq : ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T =
          newLevelCoeffLoc Gl (S.blockSplit 1 NS.hp).μ (compWeight L 1) 1 S.ν
            (rho4 d L N NS.BG NS.κ) Zb NS.Lab Φ₀ (NS.actBg F₂' Sol₂' F₁L' SolL' eps) NS.y0
            (NS.markBg F₁L' SolL' F₁b' Solb' eps) θb T :=
      fun θb hθb => NS.coeffLoc_gate F₂' Sol₂' F₁L' SolL' F₁b' Solb' hle Zb Φ₀ hθb.1 T
    refine ⟨fun θb hθb => (key.1 θb hθb).congr ?_, fun θb hθb => ?_⟩
    · filter_upwards [hV.mem_nhds hθb] with θb' hθb'
      exact (heq θb' hθb').symm
    · rw [heq θb hθb]
      exact key.2 θb hθb
  · rcases y with (Y | Y | r) | r
    · exact h0meas θb u Y hy
    · exact h1meas θb u Y hy
    · exact measurable_const
    · exact measurable_const
  · rcases y with (Y | Y | r) | r
    · exact h0bd θb u Y Φ hy
    · exact h1bd θb u Y Φ hy
    · show ‖(0 : ℂ)‖ ≤ _
      rw [norm_zero]
      exact mul_nonneg hεpos.le (Real.exp_pos _).le
    · show ‖(0 : ℂ)‖ ≤ _
      rw [norm_zero]
      exact mul_nonneg hεpos.le (Real.exp_pos _).le
  · rcases y with (Y | Y | r) | r
    · exact h0hol Y hy Φ
    · exact h1hol Y hy Φ
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
  · rcases y with (Y | Y | r) | r
    · exact h0cont Y hy θb hθb u hu
    · exact h1cont Y hy θb hθb u hu
    · exact continuous_const
    · exact continuous_const

open Classical in
/-- **Covariance of the coefficient recomputed from the labels inside `T`, from its parts** (the
form of (A4)).  Let `A` be a bundled family of the activities gated at `ε ≤ ε′` with the local
activities (`locAct`, as produced by `paramMarkFamily_trunc`), `E` a blockwise measure-preserving
equivalence of the block variables fixing `Φ₀`, and `Q` an almost sure set of configurations closed
under the restriction to sets of blocks.  At two parameters `θ_b`, `θ_b'` of the chart of radius `ε`,
if the determinant parts agree and the zero-source and old activities of the labels inside `T` and
the bridge and old marks of the anchors inside `T` satisfy `part θ_b' s (E Φ) = part θ_b s Φ` on
`Q`, the coefficients gated at `ε′` agree. -/
theorem coeffLoc_rot_of_parts {eps eps' : ℝ} (hle : eps ≤ eps') (Zb : Finset (unitPts Gl))
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    {εH κH κ0 Kc : ℝ}
    (A : physParamBg N Gl → ℂ → LabelAct NS.Lab (S.blockSplit 1 NS.hp).Ωb εH κH κ0 Kc)
    (hAH : ∀ θb u y Φ, (A θb u).H y Φ =
      locAct NS.Lab T Φ₀ (NS.actBg F₂' Sol₂' F₁L' SolL' eps) θb u y Φ)
    (E : ∀ b, (S.blockSplit 1 NS.hp).Ωb b ≃ᵐ (S.blockSplit 1 NS.hp).Ωb b)
    (hE : ∀ b, MeasurePreserving (E b) ((S.blockSplit 1 NS.hp).μ b) ((S.blockSplit 1 NS.hp).μ b))
    (hE₀ : ∀ b, E b (Φ₀ b) = Φ₀ b) {Q : Set (∀ b, (S.blockSplit 1 NS.hp).Ωb b)}
    (hQ : ∀ᵐ Φ ∂(Measure.pi (S.blockSplit 1 NS.hp).μ), Φ ∈ Q)
    (hQr : ∀ Φ ∈ Q, ∀ S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ), restrConf S' Φ₀ Φ ∈ Q)
    {θb θb' : physParamBg N Gl}
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hθb' : (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hdet : newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb' T =
      newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T)
    (h0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ NS.Z.I.𝒴}, InPoly T Y.1 → ∀ Φ ∈ Q,
      zeroActBg S Gl (BgTransport.canon S.G' Gl N)
        (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁
        NS.hp eps θb' (s : ℂ) Y.1 (fun b => E b (Φ b)) =
      zeroActBg S Gl (BgTransport.canon S.G' Gl N)
        (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁
        NS.hp eps θb (s : ℂ) Y.1 Φ)
    (h1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ NS.𝒴C}, InPoly T Y.1 → ∀ Φ ∈ Q,
      oldActBg S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C θb' Y (s : ℂ)
          (fun b => E b (Φ b)) =
      oldActBg S Gl (BgTransport.canon S.G' Gl N)
        (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
        (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C θb Y (s : ℂ) Φ)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, InPoly T (NS.Lab.ysite (NS.y0 i)) → ∀ Φ ∈ Q,
      NS.markBg F₁L' SolL' F₁b' Solb' eps θb' i (s : ℂ) (fun b => E b (Φ b)) =
        NS.markBg F₁L' SolL' F₁b' Solb' eps θb i (s : ℂ) Φ) :
    NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T =
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T := by
  rw [NS.coeffLoc_gate F₂' Sol₂' F₁L' SolL' F₁b' Solb' hle Zb Φ₀ hθb' T,
    NS.coeffLoc_gate F₂' Sol₂' F₁L' SolL' F₁b' Solb' hle Zb Φ₀ hθb T]
  unfold coeffLoc
  refine newLevelCoeffLoc_rot Gl (S.blockSplit 1 NS.hp).μ _ _ _ _ Zb NS.Lab Φ₀ _ NS.y0 _ T A hAH
    E hE hE₀ hQ hQr hdet (fun s hs y hy Φ hΦ => ?_) hG
  rcases y with (Y | Y | r) | r
  · exact h0 s hs Y hy Φ hΦ
  · exact h1 s hs Y hy Φ hΦ
  · rfl
  · rfl

end NewLevelSystem

end Balaban.Inhabited
