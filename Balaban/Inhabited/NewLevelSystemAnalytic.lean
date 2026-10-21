/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystemLoc
public import Balaban.Inhabited.NewLevelBridgeMarksBgFields
public import Balaban.Fluctuation.NewLevelOldTermsBgFields
public import Balaban.Fluctuation.NewLevelDetBgClauses

/-!
# Analyticity and bound of the coefficient recomputed from the labels inside the polymer

Route R-LOC, L5, the clauses (A1), (A2) of `newLabels_castInputs_of_localFamily` (P3 (4.46),
(4.47) and Lemma 4.2 at `Gl`): the coefficient of the system recomputed on a local generating set
`Gl` from the labels inside the polymer `T` (`NewLevelSystem.coeffLoc`, gate radius `ε′`) is
analytic on the parameters of the chart of `Gl` of the analyticity radius `ε ≤ ε′` and bounded
there by the determinant bound plus the bound of the cluster expansion.

The fields of the activities and marks of the labels inside `T` (whose sites lie in the top layer of
`Gl` by the label margin) are those of L4-3: `zeroActBg_canon_fields`, `oldActBg_canon_fields`,
`e1MarkGParamGBgOn_canon_fields`, `oldMarkGBg_canon_fields`; their bounds are put in the class form
`ε_H e^{-(2κ_dec - 1) d^{cov,1}(Y)}`, `F₀ e^{-(2κ_dec - 1) d(y0)}` by the numerical premises `hεz`,
`hεo`, `hFb`, `hFo` (the step's bounds, of the same form as those of the chain).  The determinant part
is analytic and bounded by `newLevelDetBg_analyticOnNhd`, `norm_newLevelDetBg_le_of_avoid`.

* `NewLevelSystem.dl_y0_bridge`, `NewLevelSystem.dl_y0_old`, `NewLevelSystem.ysite_y0_bridge`,
  `NewLevelSystem.ysite_y0_old`: the sizes and the site sets of the anchor labels;
* `NewLevelSystem.zeroAct_fields_of`, `oldAct_fields_of`, `marks_fields_of`: the fields of the
  activities and marks of the labels and anchors inside `T` in the forms of
  `coeffLoc_analytic_bound_of_parts`;
* `NewLevelSystem.coeffLoc_analytic_bound_of`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset MeasureTheory Metric
  Balaban.Inhabited.MarkBudgetAudit

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl ϱl' : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr)

/-- The size of the anchor label of a bridge mark is the covering length of the bridge. -/
theorem dl_y0_bridge (i : {Y' // Y' ∈ bridgeFamily 1
    (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z}) :
    NS.Lab.dl (NS.y0 (Sum.inl i)) = treeLenCovOne 1 (k + 1) i.1 := rfl

/-- The size of the anchor label of an old mark is the covering length of its bridge. -/
theorem dl_y0_old (q : {q // q ∈ markedIdx
    (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) :
    NS.Lab.dl (NS.y0 (Sum.inr q)) = treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2) := rfl

/-- The anchor label of a bridge mark is the bridge. -/
theorem ysite_y0_bridge (i : {Y' // Y' ∈ bridgeFamily 1
    (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z}) :
    NS.Lab.ysite (NS.y0 (Sum.inl i)) = i.1 := rfl

/-- The anchor label of an old mark is its bridge. -/
theorem ysite_y0_old (q : {q // q ∈ markedIdx
    (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) :
    NS.Lab.ysite (NS.y0 (Sum.inr q)) = bridge 1 z q.1.2 := rfl

variable {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
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

open Classical in
/-- **The fields of the zero-source activities of the labels inside `T`** (L4-3 at `Gl`): for the
labels inside a polymer `T` with the label margin in `Gl`, the zero-source activities recomputed on
`Gl` are measurable, bounded by `ε_H e^{-(2κ_dec - 1) d^{cov,1}(Y)}` (`hεz`), analytic in `(θ, u)` on
`physVBg Gl ε × {‖u‖ < 17/16}` and continuous in the configuration (`zeroActBg_canon_fields`). -/
theorem zeroAct_fields_of (hS1 : S.a₁ = 1) {eps : ℝ}
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    {c c₂ Kc Cx : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kc Cx c₂ NS.BG₂ t)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    {δc : ℝ} (hmarD : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hBG₂ : 0 ≤ NS.BG₂) (hdk : Gd.Ω k = Gl.Ω k) (hHm : Gd.Ω (k + 1) = ∅)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    (hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    {R₁ r : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    (hF₂an : ∀ b, AnalyticOnNhd ℂ (F₂' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂an : ∀ b, AnalyticOnNhd ℂ (Sol₂' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    {εH : ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) :
    (∀ θb u (Y : {Y // Y ∈ NS.Z.I.𝒴}), InPoly T Y.1 → Measurable (zeroActBg S Gl (BgTransport.canon S.G' Gl N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁ NS.hp eps
      θb u Y.1)) ∧
    (∀ θb u (Y : {Y // Y ∈ NS.Z.I.𝒴}) Φ, InPoly T Y.1 → ‖zeroActBg S Gl (BgTransport.canon S.G' Gl N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁ NS.hp eps
      θb u Y.1 Φ‖ ≤ εH * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) Y.1)) ∧
    (∀ Y : {Y // Y ∈ NS.Z.I.𝒴}, InPoly T Y.1 → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gl × ℂ => zeroActBg S Gl (BgTransport.canon S.G' Gl N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁ NS.hp eps
        p.1 p.2 Y.1 Φ) (physVBg N Gl S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
    (∀ Y : {Y // Y ∈ NS.Z.I.𝒴}, InPoly T Y.1 → ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
      ∀ u ∈ Metric.ball (0 : ℂ) corrU, Continuous (zeroActBg S Gl (BgTransport.canon S.G' Gl N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁ NS.hp eps
        θb u Y.1)) := by
  have ha₁ : 1 / 2 ≤ S.a₁ := by rw [hS1]; norm_num
  have ha₂ : S.a₁ ≤ 2 := by rw [hS1]; norm_num
  have hp₁ : 0 < NS.p₁ := NS.Z.hp₁
  have hcovB := fun b => LocalCover.covSetup S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  have hX₁B := fun b => LocalCover.coe_nbhdF_eq_X1 S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  have hoptB := fun b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    LocalCover.hopt 1 (Nat.le_succ k) (LocalCover.blockSite k b)
  have hΔB := fun b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    LocalCover.treeLen_eq_zero 1 (Nat.le_succ k) (LocalCover.blockSite k b)
  have hzXB : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k b,
        x ∈ X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) := fun b x hx => by
    rw [← hX₁B b]
    exact LocalCover.blockSites_subset_nbhdF 1 le_rfl b (Finset.mem_coe.2 hx)
  have hrays' : ∀ Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b,
      (S.hatOf 1 NS.p₁ NS.hp Φ, S.hatOf 1 NS.p₁ NS.hp Φ) ∈ HatRays (N := N) S.G' cψ R₁ 2 r := by
    intro Φ σ hσ t' ht' τ hτ p
    have hψ : ‖S.hatOf 1 NS.p₁ NS.hp Φ p‖ ≤ NS.p₁ := S.hatOf_mem 1 hp₁ NS.hp Φ p
    have h2 : ‖σ * t' + τ‖ ≤ 2 * R₁ + r := by
      refine (norm_add_le _ _).trans (add_le_add ?_ hτ)
      rw [norm_mul]
      exact mul_le_mul hσ.le ht'.le (norm_nonneg _) (by norm_num)
    calc ‖((σ * t') • S.hatOf 1 NS.p₁ NS.hp Φ + τ • S.hatOf 1 NS.p₁ NS.hp Φ) p‖ =
        ‖(σ * t' + τ) * S.hatOf 1 NS.p₁ NS.hp Φ p‖ := by simp [add_mul]
      _ ≤ (2 * R₁ + r) * NS.p₁ := by
        rw [norm_mul]
        exact mul_le_mul h2 hψ (norm_nonneg _) (by linarith)
      _ ≤ cψ := hrays
  have hzero := fun (Y : {Y // Y ∈ NS.Z.I.𝒴}) (hY : InPoly T Y.1) =>
    zeroActBg_canon_fields S ha₁ ha₂ hS Sb HB' hC.hκ hC.hM hMX hCx hC.eps_pos hC.small1 hC.c7le
      hC.phi_lt hmarD hαD hsm hcψ hC.δ₁_pos hBG₂ hC.hPmp hdk hHm hδ₁c hF₂an hF₂s' hSol₂an hSol₂'
      hcovB hX₁B hoptB hΔB hzXB hκ₀ hκdec hκκ h1 hlog Y.1
      (labelMargin_of_subset (ysite_subset_sitesOf NS.Z.hN NS.Lab (Sum.inl (Sum.inl Y)) hY)
        hTm).subset taylorWeight NS.hp hR₁ continuous_taylorWeight (analyticOnNhd_taylorWeight _)
      (by norm_num) norm_taylorWeight_le hr hrays'
  have hU0 : (Metric.ball (0 : ℂ) corrU) ⊆ Metric.ball (0 : ℂ) 2 :=
    Metric.ball_subset_ball (by norm_num [corrU])
  refine ⟨fun θb u Y hY => (hzero Y hY).2.2.2 θb u, fun θb u Y Φ hY => ?_,
    fun Y hY Φ => ((hzero Y hY).2.1 Φ).mono (Set.prod_mono le_rfl hU0),
    fun Y hY θb hθb u hu => (hzero Y hY).2.2.1 θb hθb.1 u (mem_ball_zero_iff.1 (hU0 hu))⟩
  refine ((hzero Y hY).1 θb u Φ).trans ?_
  have e : ∀ X e' : ℝ, 8 * (|S.β| * (X * e')) = 8 * (|S.β| * X) * e' := fun X e' => by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hεz (Real.exp_pos _).le

open Classical in
/-- **The fields of the old activities of the labels inside `T`** (L4-3 at `Gl`): for the labels
inside a polymer `T` with the label margin in `Gl`, the old activities recomputed on `Gl` are
measurable, bounded by `ε_H e^{-(2κ_dec - 1) d^{cov,1}(Y)}` (`hεo`), analytic in `(θ, u)` on
`physVBg Gl ε × {‖u‖ < 17/16}` and continuous in the configuration (`oldActBg_canon_fields`). -/
theorem oldAct_fields_of (hS1 : S.a₁ = 1) {eps : ℝ}
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (hHm : Gd.Ω (k + 1) = ∅)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    -- the old terms
    {cL c₂L KcL CxL : ℝ} (hSL : Dec2.DecSpecs d L KcL CxL cL NS.O.BG)
    (SbL : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν KcL CxL)
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps KcL CxL c₂L NS.O.BG₂ NS.O.δ₁)
    (hMXL : Dec2.cstarX d L CxL * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) (hCxL : 0 ≤ CxL)
    {δcL : ℝ} (hmarDL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps) < δcL)
    (hαDL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    (hF₁Lan : ∀ τ, AnalyticOnNhd ℂ (F₁L' τ) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.O.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolLan : ∀ τ, AnalyticOnNhd ℂ (SolL' τ) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2})
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ)
    (hΦ : ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      AnalyticOnNhd ℂ (fun t' => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁)
          (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2)
        (FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁))
    (hΦbd : ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      ∀ t' ∈ FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁,
        ‖eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2‖ ≤
          Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    {εH : ℝ}
    (hεo : ∀ Y ∈ NS.𝒴C, |S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ)
        (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0) ≤
      εH * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) Y))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) :
    (∀ θb u (Y : {Y // Y ∈ NS.𝒴C}), InPoly T Y.1 → Measurable (oldActBg S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C
      θb Y u)) ∧
    (∀ θb u (Y : {Y // Y ∈ NS.𝒴C}) Φ, InPoly T Y.1 → ‖oldActBg S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C
      θb Y u Φ‖ ≤ εH * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) Y.1)) ∧
    (∀ Y : {Y // Y ∈ NS.𝒴C}, InPoly T Y.1 → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gl × ℂ => oldActBg S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C
        p.1 Y p.2 Φ) (physVBg N Gl S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
    (∀ Y : {Y // Y ∈ NS.𝒴C}, InPoly T Y.1 → ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
      ∀ u ∈ Metric.ball (0 : ℂ) corrU, Continuous (oldActBg S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps NS.𝒴C
        θb Y u)) := by
  have ha₁ : 1 / 2 ≤ S.a₁ := by rw [hS1]; norm_num
  have ha₂ : S.a₁ ≤ 2 := by rw [hS1]; norm_num
  have htopτ : ∀ τ {Y : Set (CTorus d L N₁ m₁ (k + 1))},
      Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) →
      (∀ x ∈ Y, x ∈ Gl.Ω (k + 1)) → ∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1) := fun τ _ hY hYt x hx =>
    hYt x (subset_polyDom hY (by rw [← hX₁L τ]; exact hx))
  have hold := fun (Y : {Y // Y ∈ NS.𝒴C}) (hY : InPoly T Y.1) =>
    have hYtop := (labelMargin_of_subset (ysite_subset_sitesOf NS.Z.hN NS.Lab
      (Sum.inl (Sum.inr (Sum.inl Y))) hY) hTm).subset
    oldActBg_canon_fields S (maskPre S.hG' Gl (S.blockU z)) NS.𝒴C (X₁f := NS.O.X₁f)
      (m₀ := NS.O.m₀) (jL := NS.O.jL) (𝒦X := NS.O.𝒦X) (F₁ := F₁L') (Sol := SolL')
      (Φ := fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) (ρ := NS.O.ρ) (hp := NS.hp) (Ru := corrU)
      (eps := eps) ha₁ ha₂ hSL SbL HB' hCL.hκ hCL.hM hMXL hCxL hCL.eps_pos hCL.small1 hCL.c7le
      hCL.phi_lt hmarDL hαDL hsmL hcψL hCL.δ₁_pos hCL.hPmp hHm hRuL hF₁Lan hF₁L' hSolLan hSolL'
      hcovL hX₁L hoptL hκ₀ hκdec hκκL h1L hlogL hEb hρL hρcL Y hYtop
      (fun τ hYτ => hΦ τ (htopτ τ hYτ hYtop)) (fun τ hYτ => hΦbd τ (htopτ τ hYτ hYtop))
  exact ⟨fun θb u Y hY => (hold Y hY).2.2.2 θb u,
    fun θb u Y Φ hY => ((hold Y hY).1 θb u Φ).trans (hεo Y.1 Y.2),
    fun Y hY Φ => (hold Y hY).2.1 Φ,
    fun Y hY θb hθb u hu => (hold Y hY).2.2.1 θb hθb.1 u (mem_ball_zero_iff.1 hu)⟩

open Classical in
/-- **The fields of the marks of the anchors inside `T`** (L4-3 at `Gl`): for the anchors inside a
polymer `T` with the label margin in `Gl`, the bridge marks and the old marks recomputed on `Gl` are
measurable, bounded by `F₀ᵢ e^{-(2κ_dec - 1) 𝗱(y0 i)}` (`hFb`, `hFo`), analytic in `(θ, u)` on
`physVBg Gl ε × {‖u‖ < 17/16}` and continuous in the configuration
(`e1MarkGParamGBgOn_canon_fields`, `oldMarkGBg_canon_fields`). -/
theorem marks_fields_of (hS1 : S.a₁ = 1) {eps : ℝ}
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (hd : 3 ≤ d)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    {c c₂ Kc Cx : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kc Cx c₂ NS.BG₂ t)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (hMX' : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ} (hmarD : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hBG₂ : 0 ≤ NS.BG₂) (hdk : Gd.Ω k = Gl.Ω k) (hHm : Gd.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gl.Ω (k + 1), y ∈ Gd.Ω 1)
    (hrow : RowInHat (coverOf Gl) Gd (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    (hρc : NS.p₁ ≤ cψ)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    (hF₁ban : ∀ b, AnalyticOnNhd ℂ (F₁b' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolban : ∀ b, AnalyticOnNhd ℂ (Solb' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the old terms
    {cL c₂L KcL CxL : ℝ} (hSL : Dec2.DecSpecs d L KcL CxL cL NS.O.BG)
    (SbL : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν KcL CxL)
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps KcL CxL c₂L NS.O.BG₂ NS.O.δ₁)
    (hMXL : Dec2.cstarX d L CxL * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) (hCxL : 0 ≤ CxL)
    {δcL : ℝ} (hmarDL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps) < δcL)
    (hαDL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hF₁Lan : ∀ τ, AnalyticOnNhd ℂ (F₁L' τ) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.O.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolLan : ∀ τ, AnalyticOnNhd ℂ (SolL' τ) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2})
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ)
    (hΦ : ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      AnalyticOnNhd ℂ (fun t' => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁)
          (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2)
        (FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁))
    (hΦbd : ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      ∀ t' ∈ FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁,
        ‖eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2‖ ≤
          Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) :
    (∀ θb i u, InPoly T (NS.Lab.ysite (NS.y0 i)) → Measurable (NS.markBg F₁L' SolL' F₁b' Solb' eps θb i u)) ∧
    (∀ θb i u Φ, InPoly T (NS.Lab.ysite (NS.y0 i)) →
      ‖NS.markBg F₁L' SolL' F₁b' Solb' eps θb i u Φ‖ ≤ F0 i * Real.exp (-(2 * κdec - 1) * NS.Lab.dl (NS.y0 i))) ∧
    (∀ i, InPoly T (NS.Lab.ysite (NS.y0 i)) → ∀ Φ,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gl × ℂ => NS.markBg F₁L' SolL' F₁b' Solb' eps p.1 i p.2 Φ)
        (physVBg N Gl S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
    (∀ i, InPoly T (NS.Lab.ysite (NS.y0 i)) → ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
      ∀ u ∈ Metric.ball (0 : ℂ) corrU, Continuous (NS.markBg F₁L' SolL' F₁b' Solb' eps θb i u)) := by
  have ha₁ : 1 / 2 ≤ S.a₁ := by rw [hS1]; norm_num
  have ha₂ : S.a₁ ≤ 2 := by rw [hS1]; norm_num
  have hL2 : 2 ≤ L := NS.hL
  have hp₁ : 0 < NS.p₁ := NS.Z.hp₁
  have hcovB := fun b => LocalCover.covSetup S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  have hX₁B := fun b => LocalCover.coe_nbhdF_eq_X1 S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  have hoptB := fun b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    LocalCover.hopt 1 (Nat.le_succ k) (LocalCover.blockSite k b)
  have hΔB := fun b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    LocalCover.treeLen_eq_zero 1 (Nat.le_succ k) (LocalCover.blockSite k b)
  have hZB : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      readSites Gd k b ⊆ ↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)) := fun b =>
    LocalCover.readSites_subset_nbhdF Gd hL2 1 le_rfl b
  have hBMB : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      BlockMargin S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b))
        (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))) := fun b =>
    LocalCover.blockMargin SpG S.hG' le_rfl _ (LocalCover.blockSites_subset_cell 1 le_rfl b)
  have hzXB : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k b, x ∈ LocalCover.nbhdF 1 (LocalCover.blockSite k b) :=
    fun b x hx => LocalCover.blockSites_subset_nbhdF 1 le_rfl b (Finset.mem_coe.2 hx)
  have htopτ : ∀ τ {Y : Set (CTorus d L N₁ m₁ (k + 1))},
      Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) →
      (∀ x ∈ Y, x ∈ Gl.Ω (k + 1)) → ∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1) := fun τ _ hY hYt x hx =>
    hYt x (subset_polyDom hY (by rw [← hX₁L τ]; exact hx))
  -- the anchors inside `T` lie in the top layer of `Gl`
  have hTi : ∀ i : {Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z},
      InPoly T (NS.Lab.ysite (NS.y0 (Sum.inl i))) → LabelMargin Gl i.1 := fun i hi => by
    have h := ysite_subset_sitesOf NS.Z.hN NS.Lab (NS.y0 (Sum.inl i)) hi
    rw [NS.ysite_y0_bridge i] at h
    exact labelMargin_of_subset h hTm
  have hTq : ∀ q : {q // q ∈ markedIdx
      (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z},
      InPoly T (NS.Lab.ysite (NS.y0 (Sum.inr q))) → ∀ x ∈ q.1.2, x ∈ Gl.Ω (k + 1) := fun q hq => by
    have h := ysite_subset_sitesOf NS.Z.hN NS.Lab (NS.y0 (Sum.inr q)) hq
    rw [NS.ysite_y0_old q] at h
    exact (labelMargin_of_subset ((subset_bridge z q.1.2).trans h) hTm).subset
  have hbrM := fun (i : {Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z})
      (hi : InPoly T (NS.Lab.ysite (NS.y0 (Sum.inl i)))) =>
    e1MarkGParamGBgOn_canon_fields S ha₁ ha₂ hS Sb HB' hC.hκ hC.hM hMX hCx hC.eps_pos
      hC.small1 hC.c7le hC.phi_lt hmarD hαD hsm hcψ hC.δ₁_pos hBG₂ hC.hPmp hHm hC hdk hHmtop
      hrow hMX' hd NS.Z.hN hcovB hX₁B hoptB hΔB hZB hBMB hzXB hκ₀ hκdec hκκ h1 hlog
      (by linarith) hF₁ban hF₁b' hSolban hSolb' (maskPre S.hG' Gl (S.blockU z)) hp₁ hρc NS.hp
      hR hRR hUR hU z i (hTi i hi)
  have holdM := fun (q : {q // q ∈ markedIdx
      (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z})
      (hq : InPoly T (NS.Lab.ysite (NS.y0 (Sum.inr q)))) =>
    oldMarkGBg_canon_fields S (maskPre S.hG' Gl (S.blockU z)) (X₁f := NS.O.X₁f)
      (m₀ := NS.O.m₀) (jL := NS.O.jL) (𝒦X := NS.O.𝒦X) (F₁ := F₁L') (Sol := SolL')
      (Φ := fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) (ρ := NS.O.ρ) (hp := NS.hp) (Ru := corrU)
      (eps := eps) ha₁ ha₂ hSL SbL HB' hCL.hκ hCL.hM hMXL hCxL hCL.eps_pos hCL.small1 hCL.c7le
      hCL.phi_lt hmarDL hαDL hsmL hcψL hCL.δ₁_pos hCL.hPmp hHm ht₀ (by norm_num [corrU]) hRt
      hF₁Lan hF₁L' hSolLan hSolL' hcovL hX₁L hoptL hκ₀ hκdec hκκL h1L hlogL hEb hρL hρcL z q
      (hTq q hq) (hΦ q.1.1 (htopτ q.1.1 (mem_markedIdx.1 q.2).1 (hTq q hq)))
      (hΦbd q.1.1 (htopτ q.1.1 (mem_markedIdx.1 q.2).1 (hTq q hq)))
  have hball : Metric.ball (0 : ℂ) corrU = Metric.ball (0 : ℂ) (17 / 16 : ℝ) := rfl
  refine ⟨fun θb i u hi => ?_, fun θb i u Φ hi => ?_, fun i hi Φ => ?_,
    fun i hi θb hθb u hu => ?_⟩
  · rcases i with i | q
    · exact (hbrM i hi).1 θb u
    · exact (holdM q hi).2.2.2 θb u
  · rcases i with i | q
    · refine ((hbrM i hi).2.2.1 θb u Φ).trans ?_
      rw [NS.dl_y0_bridge i]
      exact mul_le_mul_of_nonneg_right (hFb i) (Real.exp_pos _).le
    · refine ((holdM q hi).1 θb u Φ).trans ?_
      rw [NS.dl_y0_old q]
      exact hFo q
  · rcases i with i | q
    · rw [hball]
      exact (hbrM i hi).2.2.2.1 Φ
    · exact (holdM q hi).2.1 Φ
  · rcases i with i | q
    · rw [hball] at hu
      exact (hbrM i hi).2.2.2.2 θb hθb u hu
    · exact (holdM q hi).2.2.1 θb hθb.1 u (mem_ball_zero_iff.1 hu)

open Classical in
/-- **Analyticity and bound of the coefficient recomputed from the labels inside `T`** (P3 (4.46),
(4.47) and Lemma 4.2 at `Gl`; the form of (A1), (A2)).  Let `(Gl, Gd)` have a cover base and the
fluctuation core at the analyticity radius `ε ≤ ε′` with the constants of the system (zero-source
and bridge pairs, determinant) and with those of the old terms, the decoupling pairs of `(Gl, Gd)`
pinned and analytic, the functionals of the old terms analytic and bounded on the realizable
triples of `Gl` when their frozen region lies in the top layer of `Gl` (`hΦ`, `hΦbd`), and the
sites of `T` with the label margin in `Gl`.  If the bounds of the recomputed activities and marks
are of the class form (`hεz`, `hεo`, `hFb`, `hFo`) and the numerical conditions of Theorem 3.4
hold, then the coefficient gated at `ε′` is analytic on `physVBg Gl ε` and bounded there by
`|Zb| · (½ N covBLog / (1 - z)) e^{-λ dExt T / (2 d L)} + CPE · ∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(y0 i)} · e^{-κ' dExt T}`. -/
theorem coeffLoc_analytic_bound_of (hS1 : S.a₁ = 1) {eps eps' : ℝ} (hle : eps ≤ eps')
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (hd : 3 ≤ d)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    -- the zero-source and bridge pairs, and the determinant part
    {c c₂ Kc Cx : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kc Cx c₂ NS.BG₂ t)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (hMX' : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hmarD : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hBG₂ : 0 ≤ NS.BG₂) (hdk : Gd.Ω k = Gl.Ω k) (hHm : Gd.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gl.Ω (k + 1), y ∈ Gd.Ω 1)
    (hrow : RowInHat (coverOf Gl) Gd (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    (hρc : NS.p₁ ≤ cψ)
    (hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    {R₁ r : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    (hF₂an : ∀ b, AnalyticOnNhd ℂ (F₂' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂an : ∀ b, AnalyticOnNhd ℂ (Sol₂' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁ban : ∀ b, AnalyticOnNhd ℂ (F₁b' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolban : ∀ b, AnalyticOnNhd ℂ (Solb' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the old terms
    {cL c₂L KcL CxL : ℝ} (hSL : Dec2.DecSpecs d L KcL CxL cL NS.O.BG)
    (SbL : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν KcL CxL)
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps KcL CxL c₂L NS.O.BG₂ NS.O.δ₁)
    (hMXL : Dec2.cstarX d L CxL * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) (hCxL : 0 ≤ CxL)
    {δcL : ℝ} (hmarDL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps) < δcL)
    (hαDL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hF₁Lan : ∀ τ, AnalyticOnNhd ℂ (F₁L' τ) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.O.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolLan : ∀ τ, AnalyticOnNhd ℂ (SolL' τ) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2})
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ)
    (hΦ : ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      AnalyticOnNhd ℂ (fun t' => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁)
          (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2)
        (FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁))
    (hΦbd : ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      ∀ t' ∈ FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁,
        ‖eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2‖ ≤
          Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    -- the bounds in the class form
    {εH κ' : ℝ}
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, |S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ)
        (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0) ≤
      εH * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    -- the numerical conditions of Theorem 3.4
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    -- the determinant part
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    -- the polymer
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) :
    AnalyticOnNhd ℂ (fun θb => NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T)
        (physVBg N Gl S.a₁ S.ν eps) ∧
      ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
        ‖NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T‖ ≤
          Zb.card * ((1 / 2 : ℝ) * N * covBLog d L (compWeight L S.a₁ k) (S.a₁ / (L : ℝ) ^ 2)
            NS.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ)) *
            Real.exp (-((NS.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt T)) +
          CPE d L (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 + rootUnionK d L 1 m₁ NS.Z.κ0) +
              rootUnionK d L 1 m₁ NS.Z.κ0) (2 * κdec - 1) NS.Z.κ0 κ' *
            (∑ i, F0 i * Real.exp (-NS.Z.κ0 * NS.Lab.dl (NS.y0 i))) * Real.exp (-κ' * dExt T) := by
  obtain ⟨h0meas, h0bd, h0hol, h0cont⟩ := NS.zeroAct_fields_of F₂' Sol₂' hS1 HB' hS Sb hC hMX
    hCx hmarD hαD hsm hcψ hBG₂ hdk hHm hκ₀ hκdec hκκ h1 hlog hδ₁c hR₁ hr hrays hF₂an hF₂s'
    hSol₂an hSol₂' hεz T hTm
  obtain ⟨h1meas, h1bd, h1hol, h1cont⟩ := NS.oldAct_fields_of F₁L' SolL' hS1 HB' hHm hκ₀ hκdec
    hSL SbL hCL hMXL hCxL hmarDL hαDL hsmL hcψL hκκL h1L hlogL hρL hρcL hRuL hF₁Lan hF₁L'
    hSolLan hSolL' hcovL hX₁L hoptL hEb hΦ hΦbd hεo T hTm
  obtain ⟨hGmeas, hGbd, hGhol, hGcont⟩ := NS.marks_fields_of F₁L' SolL' F₁b' Solb' hS1 HB' hd SpG
    hS Sb hC hMX hCx hMX' hmarD hαD hsm hcψ hBG₂ hdk hHm hHmtop hrow hκ₀ hκdec hκκ h1 hlog hρc hR
    hRR hUR hU hF₁ban hF₁b' hSolban hSolb' hSL SbL hCL hMXL hCxL hmarDL hαDL hsmL hcψL hκκL h1L
    hlogL hρL hρcL ht₀ hRt hF₁Lan hF₁L' hSolLan hSolL' hcovL hX₁L hoptL hEb hΦ hΦbd hFb hFo T hTm
  have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) corrU := by
    intro s hs
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    norm_num [corrU]
    linarith [hs.2]
  have hdetE : (fun θb : physParamBg N Gl =>
        newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T) =
      fun θb => newLevelDetBg Gl (compWeight L S.a₁) S.a₁ S.ν (rho4 d L N NS.BG NS.κ) Zb θb T := by
    rw [hS1]
  have hdetA : AnalyticOnNhd ℂ
      (fun θb : physParamBg N Gl =>
        newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T)
      (physVBg N Gl S.a₁ S.ν eps) := by
    rw [hdetE]
    exact newLevelDetBg_analyticOnNhd hC S.hk1 hδc hMX' hsm hmarD hαD HB' Zb T
  have hκ0 : aEnt d L + 1 ≤ NS.Z.κ0 := by linarith [NS.hκ02]
  have hKc : K0 d L NS.Z.κ0 + 1 ≤ 2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0 := by
    have h0 := K0_pos d L NS.Z.κ0
    have h1' := rootUnionK_nonneg (d := d) (L := L) (m₁ := m₁) 1 NS.Z.κ0
    linarith
  have key := NS.coeffLoc_analytic_bound_of_parts F₂' Sol₂' F₁L' SolL' F₁b' Solb' hle HB' Zb Φ₀ T
    Metric.isOpen_ball hseg (isCompact_physCarrier S 1 NS.hp) (measurableSet_physCarrier S 1 NS.hp)
    (ae_mem_physCarrier S 1 NS.hp) h0meas h0bd h0hol h0cont h1meas h1bd h1hol h1cont hGmeas hGbd
    hGhol hGcont hκ0 hKc hεpos hι hF0 hκ' le_rfl hκ hε hdetA
  refine ⟨key.1, fun θb hθb => (key.2 θb hθb).trans (add_le_add ?_ le_rfl)⟩
  -- the determinant part at the datum of the parameter
  obtain ⟨D, hD, hθD⟩ := hθb.1
  have hTav : ∀ x ∈ sitesOf T, x ∉ Gl.layer 1 := fun x hx hl => by
    have hk1 := S.hk1
    have h2 : x ∈ Gl.Ω 2 :=
      Gl.Ω_antitone (i := 2) (j := k + 1) (by norm_num) (by omega) (by omega) (hTm.subset x hx)
    exact (Gl.mem_layer.1 hl).2 h2
  have e1 : newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T =
      newLevelDetBg Gl (compWeight L S.a₁) S.a₁ S.ν (rho4 d L N NS.BG NS.κ) Zb
        (⟨rawOf D, rawOf_mem_rawSub D⟩, θb.2) T := by
    rw [newLevelDetBg_of_eq Gl _ _ _ _ Zb hθD T, hS1]
    rfl
  rw [e1]
  exact norm_newLevelDetBg_le_of_avoid hC S.hk1 hδc hMX' hsm hmarD hαD hD NS.Z.hN hz Zb θb.2 T
    hTav

end NewLevelSystem

end Balaban.Inhabited
