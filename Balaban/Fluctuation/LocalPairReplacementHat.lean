/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairCollar
public import Balaban.Fluctuation.LocalPairHatLift

/-!
# The replacement identity at the local generating set with the local hat variable

P3 pp. 78-79 recomputes every term of (4.45) on `𝔹_{k+1}(Y)`, with the fluctuation variable of
(4.46), `ψ' = β^{-1/2} C^{1/2}(s) ψ` (4.22)-(4.24), formed with the square root of the generating set
on which the term is computed.  Here the ambient term (decoupled background and fluctuation fields
of the level set `𝔹_{k+1}`, parameters `σ w = extParams 𝔹_{k+1} X₁ w`, ambient hat lift `hatPsiF`)
and the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` (restricted datum, transported parameters `τ w`,
local hat lift: the square root of the cover of `𝔹_{k+1}(Y⁺)` at the local background applied to the
restriction of `ψ̂` to its unit lattice) have the same coefficient at `𝒞` in Lemma AE.  `Y⁺` is the
collar of the expansion domain `Y` (`LocalPairCollar.lean`) and the read region lies in `Y`.

* `hatPsiF_eq_dite`: for a level set the ambient hat lift is the local-lift expression (every unit
  block is a unit point);
* `localHatLift_mem_flBallLC_of_spec`: the local hat lift of a cover pair, at the decoupled
  background of a datum of the chart, lies in the fluctuation ball of every generating set without
  layer `k + 1` (from `localHatLift_mem_flBallLC_cover`);
* `coef_eTermFun_replacement_localB_hat`: the assembled coefficient equality.  Proof: the ambient
  term reads its fluctuation variable only within `L^{k+1}` of the read region
  (`eTermFun_level_hat_congr`), where the two hat lifts agree (`localHatLift_eq_hatPsiF_localB`);
  then `coef_eTermFun_replacement_localB_collar` with the local hat lift as `ψ'(w)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Ball

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a₁ ν : ℝ}

/-- **The ambient hat lift as a local lift**: for a level set every unit block is a unit point, so
`hatPsiF = liftC (cc • C^{1/2}(s) ψ̂)` is the lift `x ↦ (cc • C^{1/2}(s) ψ̂)(unitBlock x)` written as
the local lift (extension by zero off the unit points). -/
theorem hatPsiF_eq_dite (hG' : IsLevel G (k + 1)) (cc : ℂ)
    (F₁ : DecParams G × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (s : DecParams G) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts G × Fin N → ℂ) :
    hatPsiF G a₁ ν hG' cc F₁ s Θ ψh = fun x i =>
      if h : unitBlock x ∈ unitPts G then
        (cc • (decCovSqrt G (compWeight L a₁) a₁ ν (F₁ (s, Θ)).2 (extS G s)
          (barField G Θ.1 (F₁ (s, Θ)).1) (unitQ G) (unitP G) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
      else 0 := by
  funext x i
  rw [dite_eq_left ((mem_unitPts G).2 ⟨x, hG'.mem_layer x, rfl⟩)]
  rfl

/-- **The local hat lift lies in the fluctuation ball** (from the specification of the background
map): for a cover base of `(coverOf G, G)`, parameters `|s_P| < e^κ`, a datum `D` of the chart
`Ξ^c(G; 1, ε)` and `F₁` the decoupled background map, the local hat lift
`cc C^{1/2}(s) ψ̂` at the background `F₁(s, D)` (extended by zero off the unit points of `G`) lies in
`FlBallLC Hl δ₁` for every `Hl` without layer `k + 1`, when `|ψ̂| ≤ c_ψ` and
`√N ‖cc‖ K c_ψ < δ₁` (`localHatLift_mem_flBallLC_cover` at the point of `DecDom` given by
`decDom_of_coverBg`). -/
theorem localHatLift_mem_flBallLC_of_spec {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    (hHl : Hl.Ω (k + 1) = ∅) (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf G) G (compWeight L a₁) ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    {F₁ : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ (s, rawOf D) = (φ, α))
    {eps δc : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {s : Dec2.DecParams (coverOf G)} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData G N}
    (hD : XiCData G (compWeight L a₁) ν (k + 1) 1 eps D) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {ψh : unitPts G × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then
        (cc • (decCovSqrt G (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2 (Dec2.extS (coverOf G) s)
          (barField G D.Ψ (F₁ (s, rawOf D)).1) (unitQ G) (unitP G) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
      else 0) ∈ FlBallLC Hl δ₁ := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS S HB hκ hMc heps hsmall hc7 hs hD
  have hDd : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB hδ0 (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7
      (xiCData_inDomainC HB hsmall hD)
  have hFe : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hDd φ α ⟨hI.small, hI.fixed, hI.field⟩
  have hdom := decDom_of_coverBg hS S HB hκ hMc heps hsmall hc7 hphi hs hD hI hmarD hαD
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have SX : Dec2.XCover (coverOf G) G (compWeight L a₁) a₁ ν Cx := ⟨S.toCoverGeom, hk1, ha₁, ha₂⟩
  rw [hFe]
  exact localHatLift_mem_flBallLC_cover SX hCx hκ hMX hδc hsm hdom cc hcψ hδ₁0 hδ₁ hψh hHl

end Ball

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {ν : ℝ}

/-- **The replacement identity at the local generating set with the local hat variable (P3
pp. 78-79, (4.46)).**  Let `𝔹_{k+1} = levelGS (k + 1)`, `𝔹_k` a level set (`k ≥ 1`), `Y` the
expansion domain and `Y⁺ = Yp` its collar (`hYp`: the `𝒞_{k+1}`-cubes meeting the closed
`2 M₁ L^{k+1}`-neighbourhood of `Y`), `𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺`,
`𝔹_k(Y⁺) = localB k … Ω_k(𝔹_{k+1}(Y⁺))`, and `R ⊆ Y` a read region (the cubes of `𝒞`, the cubes
meeting `X₁`, the data sites of `𝔹_k(X)`).  The coefficient `coef (·) 𝒞` of Lemma AE of the ambient
term, with the parameters `σ w = extParams 𝔹_{k+1} X₁ w` and the ambient hat lift
`ψ'(w) = hatPsiF … (σ w) Θ ψ̂`, equals that of the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` with
the restricted datum `D' = localBRestrict D`, the transported parameters `τ w` and the local hat lift
`cc C'^{1/2}(τ w) ψ̂'` (the square root of the cover of `𝔹_{k+1}(Y⁺)` at the local background of
`D'`, `ψ̂'` the restriction of `ψ̂` to the unit lattice of `𝔹_{k+1}(Y⁺)`).  The hypotheses are the
constants (those of `coef_eTermFun_replacement_localB_restrict`, `1/2 ≤ a₁ ≤ 2`, the `DecDom`
margin `δc` at `ε'`, the sup bound `√N ‖cc‖ K c_ψ < δ₁` with `|ψ̂| ≤ c_ψ`), the
specifications of the solution maps and the chart of `D`. -/
theorem coef_eTermFun_replacement_localB_hat (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {D : BgData (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) N} (hD : XiCData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps D)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      rawOf D))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, rawOf D)) D.Ψ
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh))).1
        (rawOf D, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh))) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
              (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D)))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D)))
            (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D).Ψ
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D).Ψ
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (rawOf (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D),
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D).Ψ
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))) C := by
  classical
  have hG' : IsLevel (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) (k + 1) := isLevel_levelGS (Nat.le_add_left 1 k) hk
  obtain ⟨Sb, Sb', Sf, -⟩ := localB_replacement_coverBases hG' Hm hk Yp hN hm₁ hM HB hag hagm hagl
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have heps' : 0 < eps' := by nlinarith
  have hle : eps ≤ eps' := by nlinarith
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hS.fam.2.1 hd0).le
  have hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀ := by
    have : K4 d L N BG κ * (xiC1 d * eps) ≤ K4 d L N BG κ * (xiC1 d * eps') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by linarith)) hK4
    linarith
  have hxle : xiC1 d * eps ≤ xiC1 d * eps' := mul_le_mul_of_nonneg_left hle (by linarith)
  have hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxle hK4) hαD'
  have hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc := by
    refine lt_of_le_of_lt ?_ hmarD'
    unfold decDomMargin
    gcongr
  have hDom := xiCData_inDomainC HB hsmall hD
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
  have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hD'x := localB_xiCData_restrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
    (Nat.le_add_left 1 k) HB' HB.mass hδ0 le_rfl hc0 hc1 hνε hεb D hDom
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams _ X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hmar := localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp hRY
  have hHm : Hm.Ω (k + 1) = ∅ :=
    Finset.eq_empty_of_forall_notMem fun x => isLevel_not_mem_Ω hG le_rfl (by omega) x
  have hψh' : ∀ p : unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N,
      ‖(fun p : unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N =>
        if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2) else 0) p‖ ≤ cψ := by
    intro p
    dsimp only
    split_ifs
    · exact hψh _
    · simpa using hcψ
  refine (coef_congr_near hR' fun w hw => ?_).trans
    (coef_eTermFun_replacement_localB_collar hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB HB'
      hκ hMc hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall hc7 hphi hεb
      hsmall' hc7' hphi' hδ₀e hD _ (fun w hw => (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂
        hS Sb' HB' hκ.le hMc hMX (Cchi_nonneg d L) hF₁' heps' hsmall' hc7' hphi' hmarD' hαD' hsm
        (localB_tau_norm_lt hk Yp _ (hsσ w hw) hE1) hD'x cc hcψ h1 hδ₁c hψh').1)
      hRC hRX hRk hRY)
  have hψa : hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (ϱ := ϱ) (k + 1) hk) a₁ ν hG' cc F₁ (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    rw [hatPsiF_eq_dite (a₁ := a₁) (ν := ν) hG' cc F₁ (extParams _ X₁ w) (rawOf D) ψh]
    exact (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb HB hκ.le hMc hMX
      (Cchi_nonneg d L) hF₁ heps hsmall hc7 hphi hmarD hαD hsm (hsσ w hw) hD cc hcψ h1 hδ₁c
      hψh).1
  have hψl := (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb' HB' hκ.le hMc hMX
    (Cchi_nonneg d L) hF₁' heps' hsmall' hc7' hphi' hmarD' hαD' hsm
    (localB_tau_norm_lt hk Yp _ (hsσ w hw) hE1) hD'x cc hcψ h1 hδ₁c hψh').1
  exact eTermFun_level_hat_congr hG' hm₁ hF₂ Sf hκ.le hM₂ h0 h1.le hδ₀ hδ₁ hSol ac Fk E hRC hRX
    hRk hw.1 (hsσ w hw) _ (rawOf D)
    (strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD hψa)
    (strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD hψl)
    (fun x hx y hy => funext fun i => (localHatLift_eq_hatPsiF_localB hG' hk1 hk Yp hN hm₁ hM hag
      hagl hS HB HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' heps hsmall hc7 hphi heps' hsmall' hc7' hphi'
      hmarD hαD hmarD' hαD' hsm hD hD'x
      (fun x hx => localBRestrict_eq_of_mem_top (Nat.le_add_left 1 k) D hx) hRC hRX hmar hw.1
      (hsσ w hw) cc ψh ⟨x, hx, hy⟩ i).symm)

end Assembly

end Balaban.Localization
