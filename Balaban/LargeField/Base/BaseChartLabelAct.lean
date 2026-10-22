/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartTerms
public import Balaban.LargeField.Base.BaseLabelSum
public import Balaban.LargeField.Base.BaseLabelAct
import Mathlib.Tactic.Linarith

/-!
# The chart exponents as a `LabelAct`

The activity `chartTerm` of a label `Y` is the sum, over the sites `x` of `Ω₁` and the families `Cs`
of cells of the decoupling cover whose label is `Y`, of the coefficients `coef_{Cs}` of
`s ↦ V_x(F(s, e); ψ')`; the label of `(x, Cs)` is the hull of the root cube of `x` and of the patches
of the family (`labelSet`).  Under the hypotheses of `chartCoef_spec`, with the field `ψ' = fld Φ`
assembled from block variables `Φ`:

* `chartTerm_norm_le`: `‖chartTerm Y‖ ≤ labelAmp · e^{-labelRate · d^cov(Y)}` (`norm_labelSum_le`);
* `chartTerm_depOn`: it depends on the blocks of `Y` only (`chartFe_psi_congr`);
* `chartTerm_analytic`, `chartTerm_measurable`: analytic in the data `e`, measurable in `Φ`;
* `chartTerm_sum`: `∑_Y chartTerm Y = ∑_x V_x(F(1, e); ψ')`;
* `chartActivity_LabelAct`: the family `e ↦ A e` of `LabelAct` on the labels `chartLabels`
  (`baseActivity_LabelAct`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Final

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- The activity of the label `Y` in the chart exponents: the sum, over the sites `x` and the
families `Cs` of cells whose label is `Y`, of the coefficients of `s ↦ V_x(F(s,e); ψ)`. -/
noncomputable def chartTerm (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (m₀ ρs : ℕ) (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (e : RawData d L (N₁ * L ^ m₁) 1 N) (ψ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x : G.Ω 1, ∑ Cs ∈ Finset.univ.filter (fun Cs : Finset ↥(coverOf G).cubeIdx =>
      labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ρs Cs = Y),
    coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs

section Meas

/-- A function continuous on a set `A` that contains the range of a measurable map composes to a
measurable function. -/
theorem measurable_comp_of_continuousOn {α β γ : Type*} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    {f : α → β} {g : β → γ} {A : Set β} (hf : Measurable f) (hg : ContinuousOn g A)
    (hA : ∀ a, f a ∈ A) : Measurable (g ∘ f) := by
  have h1 : Measurable (A.domRestrict g) := hg.domRestrict.measurable
  have h2 : Measurable (Set.codRestrict f A hA) := hf.subtype_mk
  exact h1.comp h2

end Meas

section Blocks

variable {K m₀ j : ℕ}

open Classical in
/-- **A site of a domain lies in a block contained in it.** -/
theorem exists_block_of_mem (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Y : Set (Balaban.Localization.CTorus d L N₁ m₁ K)} (hY : IsDj m₀ j Y)
    {y : Balaban.Localization.CTorus d L N₁ m₁ K} (hy : y ∈ Y) :
    ∃ b ∈ blocksOf m₀ j Set.univ Y, y ∈ Localization.box b.1 (cellSide L m₀ m₁ j) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  obtain ⟨c, hc1, hc2, hc3⟩ := hY.2.1 y hy
  have hcell : Localization.box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆ Y :=
    (cell_subset_cube hdvd ha0 hc1 hc2).trans hc3
  exact ⟨⟨cbase (cellSide L m₀ m₁ j) y, aligned_cbase y, Set.subset_univ _⟩, mem_blocksOf.2 hcell,
    mem_box_cbase ha0 y⟩

end Blocks

section Spec

variable {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
  (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ) (hβ : 0 < β)
  (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
  (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
    (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
  (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
  (hΩ : ∀ z, z ∈ G.Ω 1) {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr)
  (g : G.Ω 1 × Fin N → ℂ) (ρ : ℕ)
  (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
  (hWloc : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r)
  {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
  (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα Gg : ℝ} (hE : 0 ≤ Ee)
  (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
  (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ∀ x, ‖u.2 x‖ ≤ Aα)
  (hg : ∀ x, ∑ i, ‖g (x, i)‖ ≤ Gg)
  (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
  (hmemAll : ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
    ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) → F (s, (D.Ψ, D.h)) ∈ U)

include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ in
open Classical in
/-- **The coefficients at a datum of the union domain** (`chartCoef_spec` for every site). -/
theorem chartSpec_of_mem {e : RawData d L (N₁ * L ^ m₁) 1 N}
    (he : e ∈ dataSet G N BG κ ν) {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    (x : G.Ω 1) :
    (∀ Cs : Finset ↥(coverOf G).cubeIdx, ¬ IsRootedFamily (cellPatch (coverOf G) Dr)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs →
        coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs = 0) ∧
    (∀ Cs : Finset ↥(coverOf G).cubeIdx,
        ‖coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs‖ ≤
          2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg * Real.exp (-(κ - 1) * Cs.card)) ∧
    chartFe G a ν β g ψ W x (F (fun _ => 1, e)) =
      ∑ Cs ∈ Finset.univ.filter (fun Cs : Finset ↥(coverOf G).cubeIdx => IsRootedFamily
          (cellPatch (coverOf G) Dr)
          (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs),
        coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs := by
  obtain ⟨Dd, hDu, rfl⟩ := he
  exact chartCoef_spec hS G a ν β hβ Sb HB hκ hM hF hDu hFan hΩ hDD g ψ x ρ W hWloc hWan hE hBW hp
    (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1, (hU u hu).2.2 x⟩) hψ (hg x) hsmall (hmemAll Dd hDu)

end Spec


section Final2

set_option linter.unusedSectionVars false

variable {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
  (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ) (hβ : 0 < β)
  (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
  (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
    (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
  (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
  (hΩ : ∀ z, z ∈ G.Ω 1) {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr) (hDr : Dr ≤ L ^ (1 + m₁))
  (hm4 : 4 * L ^ 2 ≤ L ^ m₁) (hd : 0 < d) (hL2 : 2 ≤ L)
  (g : G.Ω 1 × Fin N → ℂ) (ρ : ℕ)
  (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
  (hWloc : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r)
  (hWr : ∀ u p r, W u p r ≠ 0 → supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1)
      (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ ρ)
  {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
  (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα Gg : ℝ} (hE : 0 ≤ Ee)
  (hBW : 0 ≤ BW) (hp : 0 ≤ p₁) (hA : 0 ≤ Aα) (hG : 0 ≤ Gg)
  (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ∀ x, ‖u.2 x‖ ≤ Aα)
  (hg : ∀ x, ∑ i, ‖g (x, i)‖ ≤ Gg)
  (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
  (hmemAll : ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
    ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) → F (s, (D.Ψ, D.h)) ∈ U)
  {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)] (fld : (∀ b, Ωb b) → G.Ω 1 × Fin N → ℂ)
  (hfld_meas : Measurable fld) (hfld_bd : ∀ Φ r, ‖fld Φ r‖ ≤ p₁)
  (hfld_loc : ∀ (B : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ))
    (Φ Φ' : ∀ b, Ωb b), (∀ b ∈ B, Φ b = Φ' b) → ∀ r : G.Ω 1 × Fin N,
    (∃ b ∈ B, (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
      Localization.box b.1 (cellSide L m₀ m₁ 1)) → fld Φ r = fld Φ' r)
  {V : Set (RawData d L (N₁ * L ^ m₁) 1 N)} (hV : IsOpen V) (hVS : V ⊆ dataSet G N BG κ ν)

open Classical in
include hL2 hN hDr hm4 in
/-- The facts about the label of a rooted family. -/
theorem chart_label_facts (x : G.Ω 1) (Cs : Finset ↥(coverOf G).cubeIdx)
    (h : IsRootedFamily (cellPatch (coverOf G) Dr)
      (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs) :
    IsPolyDom m₀ (0 + 1) (labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs) ∧
    (∀ y, supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ ρ + L →
      y ∈ labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs) := by
  have hlay : ∀ q ∈ (coverOf G).cubeIdx, q.1 ≤ 0 + 1 := fun q hq => ((mem_cubeIdx G).1 hq).1.2
  have hseed : ∀ y ∈ ((seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) :
      Finset _) : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)),
      supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ ρ + L :=
    fun y hy => mem_seedBall.1 (Finset.mem_coe.1 hy)
  have := labelHull_spec (C := coverOf G) (m₀ := m₀) hN hL2 (hDr : Dr ≤ L ^ (0 + 1 + m₁)) hm4 hlay
    (x : Balaban.Localization.CTorus d L N₁ m₁ 1) hseed h
  exact ⟨this.1, this.2.1⟩

open Classical in
/-- **The size of the activity of a label from the coefficients of its pairs.** -/
theorem chartTerm_norm_le_of_spec (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hL2 : 2 ≤ L) {Dr : ℕ} (hDr : Dr ≤ L ^ (1 + m₁))
    (hm4 : 4 * L ^ 2 ≤ L ^ m₁) (hd : 0 < d) (ρ : ℕ) {κ B : ℝ} (hB : 0 ≤ B)
    (hz : labelZ d L 0 (ρ + L) κ < 1) (e : RawData d L (N₁ * L ^ m₁) 1 N)
    (ψ : G.Ω 1 × Fin N → ℂ) (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hspec : ∀ (x : G.Ω 1) (Cs : Finset ↥(coverOf G).cubeIdx),
      labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs = Y →
      (¬ IsRootedFamily (cellPatch (coverOf G) Dr)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs →
        coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs = 0) ∧
      ‖coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs‖ ≤ B * Real.exp (-(κ - 1)) ^ Cs.card) :
    ‖chartTerm G a ν β g W F m₀ (ρ + L) Y e ψ‖ ≤
      labelAmp d L m₀ m₁ 0 (ρ + L) κ B *
        Real.exp (-(labelRate d L 0 (ρ + L) κ) * treeLenCovOne m₀ (0 + 1) Y) := by
  have hlay : ∀ q ∈ (coverOf G).cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ 0 + 1 :=
    fun q hq => ((mem_cubeIdx G).1 hq).1
  have hal : ∀ q ∈ (coverOf G).cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2 :=
    fun q hq => ((mem_cubeIdx G).1 hq).2.2
  have hDr' : Dr ≤ L ^ (0 + 1 + m₁) := hDr
  have hseed : ∀ x : G.Ω 1, ∀ y ∈ ((seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) :
      Finset _) : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)),
      supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ ρ + L :=
    fun x y hy => mem_seedBall.1 (Finset.mem_coe.1 hy)
  have key := norm_labelSum_le (coverOf G) hd (fun x : G.Ω 1 => (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
    Subtype.val_injective hN hL2 hDr' hm4 hlay hal
    (fun x => (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _)) hseed
    (fun x Cs => if labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs = Y
      then coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs else 0) hB hz
    (fun x Cs hne => by
      by_contra hnr
      by_cases hl : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs = Y
      · exact hne (by simp only [hl, ↓reduceIte]; exact (hspec x Cs hl).1 hnr)
      · exact hne (by simp only [hl, ↓reduceIte]))
    (fun x Cs => by
      by_cases hl : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs = Y
      · simp only [hl, ↓reduceIte]; exact (hspec x Cs hl).2
      · simp only [hl, ↓reduceIte, norm_zero]; positivity) Y
  convert key using 3
  unfold chartTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Cs hCs => ?_
  simp only [(Finset.mem_filter.1 hCs).2, ↓reduceIte]

open Classical in
/-- **The activity of a label depends only on the blocks of the label, from the vanishing of the non-rooted
coefficients with that label.** -/
theorem chartTerm_depOn_of_spec (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hL2 : 2 ≤ L) {Dr : ℕ} (hDr : Dr ≤ L ^ (1 + m₁))
    (hm4 : 4 * L ^ 2 ≤ L ^ m₁) (ρ : ℕ) (e : RawData d L (N₁ * L ^ m₁) 1 N)
    (hWr : ∀ u p r, W u p r ≠ 0 → supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1)
      (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ ρ)
    {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (fld : (∀ b, Ωb b) → G.Ω 1 × Fin N → ℂ) {p₁ : ℝ}
    (hfld_bd : ∀ Φ r, ‖fld Φ r‖ ≤ p₁)
    (hfld_loc : ∀ (B : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ))
      (Φ Φ' : ∀ b, Ωb b), (∀ b ∈ B, Φ b = Φ' b) → ∀ r : G.Ω 1 × Fin N,
      (∃ b ∈ B, (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
        Localization.box b.1 (cellSide L m₀ m₁ 1)) → fld Φ r = fld Φ' r)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hvan : ∀ ψ : G.Ω 1 × Fin N → ℂ, (∀ r, ‖ψ r‖ ≤ p₁) →
      ∀ (x : G.Ω 1) (Cs : Finset ↥(coverOf G).cubeIdx),
      labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs = Y →
      ¬ IsRootedFamily (cellPatch (coverOf G) Dr)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs →
        coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs = 0) :
    DepOn (blocksOf m₀ 1 Set.univ Y) (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) := by
  intro Φ Φ' hΦ
  unfold chartTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Cs hCs => ?_
  have hlab := (Finset.mem_filter.1 hCs).2
  by_cases hr : IsRootedFamily (cellPatch (coverOf G) Dr)
      (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs
  · have hfacts := chart_label_facts (G := G) (hL2 := hL2) (hN := hN) (hDr := hDr) (hm4 := hm4)
      (ρ := ρ) (x := x) (Cs := Cs) hr
    have hYDj : IsDj m₀ 1 Y := by
      rw [← hlab]; exact isDj_of_isPolyDom hfacts.1
    have hpsi : ∀ r : G.Ω 1 × Fin N, supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1)
        (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ ρ + L → fld Φ r = fld Φ' r := by
      intro r hrr
      have hrY : (r.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y := by
        rw [← hlab]; exact hfacts.2 _ hrr
      obtain ⟨b, hb, hbx⟩ := exists_block_of_mem hN (le_refl 1) hYDj hrY
      exact hfld_loc (blocksOf m₀ 1 Set.univ Y) Φ Φ' hΦ r ⟨b, hb, hbx⟩
    exact congrArg (fun f => coef f Cs)
      (funext fun s => chartFe_psi_congr G a ν β g (fld Φ) (fld Φ') x ρ W hWr hpsi (F (s, e)))
  · rw [hvan (fld Φ) (hfld_bd Φ) x Cs hlab hr, hvan (fld Φ') (hfld_bd Φ') x Cs hlab hr]

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd hVS hA hG in
/-- **The size of the activity of a label.** -/
theorem chartTerm_norm_le (hz : labelZ d L 0 (ρ + L) κ < 1)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) {e : RawData d L (N₁ * L ^ m₁) 1 N}
    (he : e ∈ V) {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁) :
    ‖chartTerm G a ν β g W F m₀ (ρ + L) Y e ψ‖ ≤
      labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) *
        Real.exp (-(labelRate d L 0 (ρ + L) κ) * treeLenCovOne m₀ (0 + 1) Y) := by
  have hB0 : 0 ≤ 2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg := by
    have := chartBound_nonneg d L N (a 1) ν β Aα Ee BW p₁ Gg hβ hA hE hBW hp hG
    linarith
  have hsp := fun x => chartSpec_of_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc hWan hE
    hBW hp hU hg hsmall hmemAll (hVS he) hψ x
  exact chartTerm_norm_le_of_spec G a ν β g W F hN hL2 hDr hm4 hd ρ hB0 hz e ψ Y
    (fun x Cs _ => ⟨(hsp x).1 Cs, by
      refine ((hsp x).2.1 Cs).trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul]; congr 2; ring⟩)

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hVS hWr hfld_bd hfld_loc in
/-- **The activity of a label depends only on the blocks of the label.** -/
theorem chartTerm_depOn (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V) :
    DepOn (blocksOf m₀ 1 Set.univ Y) (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) := by
  exact chartTerm_depOn_of_spec G a ν β g W F hN hL2 hDr hm4 ρ e hWr fld hfld_bd hfld_loc Y
    (fun ψ hψ x Cs _ hr => (chartSpec_of_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc
      hWan hE hBW hp hU hg hsmall hmemAll (hVS he) hψ x).1 Cs hr)

open Classical in
include hFan hWan hE hU hsmall hmemAll hβ hκ hVS hfld_bd in
/-- **The activity of a label is analytic in the data.** -/
theorem chartTerm_analytic (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ (fun e => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) V := by
  intro e he
  unfold chartTerm
  refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun Cs _ => ?_
  have h1 := chartCoef_analyticOnNhd (BG := BG) G a ν β hβ (by linarith) hFan g x W hWan hE
    (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1⟩) hsmall hmemAll Cs (e, fld Φ) ⟨hVS he, hfld_bd Φ⟩
  have h2 : AnalyticAt ℂ (fun e' : RawData d L (N₁ * L ^ m₁) 1 N => (e', fld Φ)) e :=
    analyticAt_id.prod analyticAt_const
  have h3 := h1.comp_of_eq h2 rfl
  exact h3.congr (Filter.Eventually.of_forall fun p => rfl)

open Classical in
include hFan hWan hE hU hsmall hmemAll hβ hκ hVS hfld_bd hfld_meas hp in
/-- **The activity of a label is measurable in the block variables.** -/
theorem chartTerm_measurable (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V) :
    Measurable (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) := by
  have hcont : ∀ (x : G.Ω 1) (Cs : Finset ↥(coverOf G).cubeIdx), ContinuousOn
      (fun ψ : G.Ω 1 × Fin N → ℂ => coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs)
      {ψ | ∀ r, ‖ψ r‖ ≤ p₁} := by
    intro x Cs
    have h1 := (chartCoef_analyticOnNhd (BG := BG) G a ν β hβ (by linarith) hFan g x W hWan hE
      (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1⟩) hsmall hmemAll Cs).continuousOn
    have h2 : ContinuousOn (fun ψ : G.Ω 1 × Fin N → ℂ => (e, ψ)) {ψ | ∀ r, ‖ψ r‖ ≤ p₁} :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h3 := h1.comp h2 (fun ψ hψ => ⟨hVS he, hψ⟩)
    exact h3.congr (fun ψ _ => rfl)
  unfold chartTerm
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun Cs _ => ?_
  have key := measurable_comp_of_continuousOn (f := fld) (g := fun ψ : G.Ω 1 × Fin N → ℂ =>
    coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs)
    (A := {ψ : G.Ω 1 × Fin N → ℂ | ∀ r, ‖ψ r‖ ≤ p₁}) hfld_meas (hcont x Cs) hfld_bd
  exact key

open Classical in
/-- **The labels of the chart activities**: the hulls of the rooted families of cells about the sites
of `Ω₁`. -/
noncomputable def chartLabels (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (Dr m₀ ρs : ℕ) :
    Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) :=
  ((Finset.univ : Finset (G.Ω 1 × Finset ↥(coverOf G).cubeIdx)).filter fun p =>
    IsRootedFamily (cellPatch (coverOf G) Dr)
      (seedBall (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ρs : Set _) p.2).image
    fun p => labelSet (coverOf G) m₀ (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ρs p.2

open Classical in
include hL2 hN hDr hm4 in
theorem chartLabels_isDj : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L), IsDj m₀ 1 Y := by
  intro Y hY
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hY
  exact isDj_of_isPolyDom (chart_label_facts (G := G) (hL2 := hL2) (hN := hN) (hDr := hDr)
    (hm4 := hm4) (ρ := ρ) (x := p.1) (Cs := p.2) (Finset.mem_filter.1 hp).2).1

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hVS in
/-- **The activities of the labels sum to the chart exponents.** -/
theorem chartTerm_sum {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V)
    {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁) :
    ∑ Y ∈ chartLabels G Dr m₀ (ρ + L), chartTerm G a ν β g W F m₀ (ρ + L) Y e ψ =
      ∑ x : G.Ω 1, chartFe G a ν β g ψ W x (F (fun _ => 1, e)) := by
  unfold chartTerm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hsp := chartSpec_of_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc hWan hE
    hBW hp hU hg hsmall hmemAll (hVS he) hψ x
  rw [(hsp).2.2]
  set lab : Finset ↥(coverOf G).cubeIdx → Set (Balaban.Localization.CTorus d L N₁ m₁ 1) :=
    fun Cs => labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs with hlab
  set cc : Finset ↥(coverOf G).cubeIdx → ℂ :=
    fun Cs => coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs with hcc
  have hroot : ∀ Cs, IsRootedFamily (cellPatch (coverOf G) Dr)
      (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs →
      lab Cs ∈ chartLabels G Dr m₀ (ρ + L) := fun Cs h =>
    Finset.mem_image.2 ⟨(x, Cs), Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩
  have h1 : ∑ Y ∈ chartLabels G Dr m₀ (ρ + L), ∑ Cs ∈ Finset.univ.filter (fun Cs => lab Cs = Y), cc Cs =
      ∑ Cs ∈ Finset.univ.filter (fun Cs => lab Cs ∈ chartLabels G Dr m₀ (ρ + L)), cc Cs := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun Cs => lab Cs ∈ chartLabels G Dr m₀ (ρ + L))) (t := chartLabels G Dr m₀ (ρ + L)) (g := lab)
      (fun Cs hCs => (Finset.mem_filter.1 hCs).2)]
    refine Finset.sum_congr rfl fun Y hY => Finset.sum_congr ?_ fun _ _ => rfl
    ext Cs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hY, h⟩
    · rintro ⟨_, h⟩; exact h
  rw [h1, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun Cs _ => ?_
  by_cases hr : IsRootedFamily (cellPatch (coverOf G) Dr)
      (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs
  · simp [hroot Cs hr, hr, hcc]
  · have h0 : coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs = 0 := hsp.1 Cs hr
    simp [hcc, h0, hr]

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd
  hVS hA hG hWr hfld_meas hfld_bd hfld_loc hV in
/-- **The chart exponents as a `LabelAct`.**  Let `ψ' = fld Φ` be the field assembled from the block
variables `Φ` (bounded by `p₁`, the field at a site depending only on the block of the site).  The
activities `chartTerm` of the labels `chartLabels` (hulls of the rooted families of cells, in `𝒟_1`)
are the activities of a family `e ↦ A e` of `LabelAct` of amplitude `labelAmp` and rate `labelRate`
(entropy bound `K₀(d, L, κ₀)`), analytic in the data `e` on an open subset `V` of the union domain,
and they sum to `∑_x V_x(F(1, e); ψ')`. -/
theorem chartActivity_LabelAct {κ0 Kent : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKent : K0 d L κ0 ≤ Kent)
    (hz : labelZ d L 0 (ρ + L) κ < 1) :
    ∃ (hdom : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L), IsDj m₀ 1 Y)
      (A : RawData d L (N₁ * L ^ m₁) 1 N → LabelAct
        (thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L)) hdom) Ωb
        (labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg))
        (labelRate d L 0 (ρ + L) κ) κ0 Kent),
      (∀ e ∈ V, ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L)}) Φ,
        (A e).H y Φ = chartTerm G a ν β g W F m₀ (ρ + L) y.1 e (fld Φ)) ∧
      (∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L)}) Φ,
        AnalyticOnNhd ℂ (fun e => (A e).H y Φ) V) ∧
      (∀ e ∈ V, ∀ Φ, ∑ Y ∈ chartLabels G Dr m₀ (ρ + L),
          chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) =
        ∑ x : G.Ω 1, chartFe G a ν β g (fld Φ) W x (F (fun _ => 1, e))) := by
  have hdom := chartLabels_isDj G hDr hm4 hL2 hN (ρ := ρ)
  have hB0 : 0 ≤ 2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg := by
    have := chartBound_nonneg d L N (a 1) ν β Aα Ee BW p₁ Gg hβ hA hE hBW hp hG
    linarith
  have hε := labelAmp_nonneg d L m₀ m₁ 0 (ρ + L) κ hB0 hz
  have hmeas : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L), ∀ e ∈ V,
      Measurable (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) :=
    fun Y _ e he => chartTerm_measurable (G := G) (a := a) (ν := ν) (β := β) (g := g) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd)
      (hfld_meas := hfld_meas) (hp := hp) (fld := fld) (m₀ := m₀) (V := V) (Y := Y) (he := he)
  have hdep : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L), ∀ e ∈ V, DepOn (blocksOf m₀ 1 Set.univ Y)
      (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) :=
    fun Y _ e he => chartTerm_depOn hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD hDr hm4 hL2 g ρ W hWloc
      hWr hWan hE hBW hp hU hg hsmall hmemAll hN fld hfld_bd hfld_loc hVS Y he
  have hbd : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L), ∀ e ∈ V, ∀ Φ,
      ‖chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)‖ ≤
        labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) *
          Real.exp (-(labelRate d L 0 (ρ + L) κ) * treeLenCovOne m₀ 1 Y) :=
    fun Y _ e he Φ => chartTerm_norm_le hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD hDr hm4 hd hL2 g ρ W
      hWloc hWan hE hBW hp hA hG hU hg hsmall hmemAll hN hVS hz Y he (hfld_bd Φ)
  have han : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L), ∀ Φ, AnalyticOnNhd ℂ
      (fun e => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) V :=
    fun Y _ Φ => chartTerm_analytic (G := G) (a := a) (ν := ν) (β := β) (g := g) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd) (fld := fld) (m₀ := m₀) (V := V) (Y := Y) (Φ := Φ)
  obtain ⟨A, hA1, hA2⟩ := baseActivity_LabelAct (K := 1) (m₀ := m₀) (j := 1) hV hN (le_refl 1)
    (chartLabels G Dr m₀ (ρ + L)) hdom
    (fun Y e Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ))
    (εH := labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg))
    (κH := labelRate d L 0 (ρ + L) κ) hε hκ0 hKent hmeas hdep hbd han
  exact ⟨hdom, A, hA1, hA2, fun e he Φ => chartTerm_sum hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W
    hWloc hWan hE hBW hp hU hg hsmall hmemAll hVS he (hfld_bd Φ)⟩

end Final2

end Final

end Balaban.LargeField.Base
