/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartLocalSpec
public import Balaban.LargeField.Base.BaseChartDefectAct
public import Balaban.LargeField.Base.BaseChartEG

/-!
# The activities of the labels inside a deep region, for a generating set

For a generating set `G` of the first step and a set `R` whose `8 L^{1+m₁}`-neighbourhood lies in `Ω₁`, the
masked activity `maskedTerm` of a label `Y`: `chartTerm + defTerm` if `Y ⊆ R`, `0` otherwise.  Without any
assumption on `Ω₁` outside `R`, the activities `maskedTerm` of all sets `Y` are measurable and jointly analytic
in the datum and the source, depend on the blocks of `Y` only and satisfy the bound of `LabelAct`
(`maskedTerm_norm_le`, `maskedTerm_depOn`, `maskedTerm_measurable`, `maskedTerm_analytic`), so that they form a
family of `LabelAct` on any finite set of labels (`masked_labelAct_eps`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Masked

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- The activity of the label `Y` of the chart exponent and the defect, masked to the labels inside `R`. -/
noncomputable def maskedTerm (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) (m₀ ρs rD : ℕ)
    (R : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (e : RawData d L (N₁ * L ^ m₁) 1 N)
    (ψ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  if Y ⊆ R then chartTerm G a ν β g W F m₀ ρs Y e ψ + defTerm G Dm m₀ rD Y ψ else 0

end Masked

section Props

set_option linter.unusedSectionVars false

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The chart activity is jointly analytic in the datum and the source.** -/
theorem chartTerm_analytic_eg {BG : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (ν β : ℝ) (hβ : 0 < β) {κ : ℝ} (hκ : 0 < κ)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα : ℝ} (hE : 0 ≤ Ee)
    (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ∀ x, ‖u.2 x‖ ≤ Aα)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
    (hmemAll : ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
      ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) → F (s, (D.Ψ, D.h)) ∈ U)
    {m₀ ρs : ℕ} (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (ψ : G.Ω 1 × Fin N → ℂ)
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁) :
    AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ) =>
      chartTerm G a ν β q.2 W F m₀ ρs Y q.1 ψ) (dataSet G N BG κ ν ×ˢ Set.univ) := by
  intro q hq
  unfold chartTerm
  refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun Cs _ => ?_
  exact chartCoef_analyticOnNhd_eg (BG := BG) G a ν β hβ hκ hFan ψ x W hWan hE hBW hp
    (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1, (hU u hu).2.2 x⟩) hψ hsmall hmemAll Cs q hq

section Masked2

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
  {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr) (hDr : Dr ≤ L ^ (1 + m₁))
  (hm4 : 4 * L ^ 2 ≤ L ^ m₁) (hd : 0 < d) (hL2 : 2 ≤ L) (ρ : ℕ)
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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (dat : E →L[ℂ] RawData d L (N₁ * L ^ m₁) 1 N) (sr : E →L[ℂ] (G.Ω 1 × Fin N → ℂ))
  {V : Set E} (hV : IsOpen V) (hVS : ∀ p ∈ V, dat p ∈ dataSet G N BG κ ν)
  (hg : ∀ p ∈ V, ∀ x, ∑ i, ‖sr p (x, i)‖ ≤ Gg)
  (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {DB : ℝ} (rD : ℕ) (hDB : 0 ≤ DB)
  (hDrow : ∀ p, ∑ q, ‖Dm p q‖ ≤ DB)
  (hDrange : ∀ p q, Dm p q ≠ 0 → supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1)
    (q.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ rD)
  (R : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
  (hRdeep : ∀ w : Balaban.Localization.CTorus d L N₁ m₁ 1,
    (∃ t ∈ R, supDist w t ≤ 8 * L ^ (0 + 1 + m₁)) → w ∈ G.Ω 1)
  (hρ : ρ + 4 * L ≤ 8 * L ^ (0 + 1 + m₁))

open Classical in
include hRdeep hρ hN in
/-- The hypothesis `hdeep` of the locality theorems at a pair with a label inside `R`. -/
theorem hdeep_of_label (x : G.Ω 1) (Cs : Finset ↥(coverOf G).cubeIdx)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (hYR : Y ⊆ R)
    (hlab : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) Cs = Y) :
    ∀ s ∈ supportedOn Cs, ∀ y ∈ seedHull (coverOf G) Dr (Dec2.extS _ s)
        (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L)),
      ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (0 + 1), supDist y z ≤ 2 * L ^ (0 + 1) → z ∈ G.Ω 1 := by
  have hLP : L ^ 1 ≤ L ^ (0 + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  refine hdeep_of_cells G Cs _ (fun i hi w hw => ?_) (fun z hz w hw => ?_)
  · have hb : (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2 ∈ Y := by
      have := ball_subset_labelSet (m₀ := m₀) (x := (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
        (ρs := ρ + L) hN hi (y := (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2)
        (by rw [supDist_self]; exact Nat.zero_le _)
      rwa [hlab] at this
    exact hRdeep w ⟨_, hYR hb, by rw [supDist_comm]; simp only [zero_add, pow_one] at hw hLP ⊢; omega⟩
  · have hx : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y := by
      rw [← hlab]; exact seed_subset_labelSet hN (by rw [supDist_self]; exact Nat.zero_le _)
    have hz' := mem_seedBall.1 hz
    have := supDist_triangle (x : Balaban.Localization.CTorus d L N₁ m₁ 1) z w
    exact hRdeep w ⟨_, hYR hx, by rw [supDist_comm]; simp only [zero_add, pow_one] at hw hLP hρ this ⊢; omega⟩

open Classical in
include hS Sb HB hκ hM hF hFan hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd hVS hA hG
  hRdeep hρ hDB hDrow in
/-- **The size of the masked activity of a label.** -/
theorem maskedTerm_norm_le (hz : labelZ d L 0 (ρ + L) κ < 1)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) {q : E} (hq : q ∈ V)
    {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁) :
    ‖maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R Y (dat q) ψ‖ ≤
      (labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
        defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ)) *
        Real.exp (-(labelRate d L 0 (ρ + L) κ) * treeLenCovOne m₀ 1 Y) := by
  have hB0 : 0 ≤ 2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg := by
    have := chartBound_nonneg d L N (a 1) ν β Aα Ee BW p₁ Gg hβ hA hE hBW hp hG
    linarith
  have hε1 := labelAmp_nonneg d L m₀ m₁ 0 (ρ + L) κ hB0 hz
  have hκH : 0 ≤ labelRate d L 0 (ρ + L) κ := by
    have hz0 := labelZ_pos d L 0 (ρ + L) κ
    have hlam : 0 < -Real.log (labelZ d L 0 (ρ + L) κ) := by
      have := Real.log_neg hz0 hz; linarith
    unfold labelRate; positivity
  have hε2 : 0 ≤ defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) := by
    unfold defAmp
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  unfold maskedTerm
  by_cases hYR : Y ⊆ R
  · simp only [hYR, ↓reduceIte]
    obtain ⟨Dd, hDu, hDd⟩ := hVS q hq
    rw [hDd]
    have h1 := chartTerm_norm_le_of_spec G a ν β (sr q) W F hN hL2 hDr hm4 hd ρ hB0 hz (Dd.Ψ, Dd.h) ψ Y
      (fun x Cs hlab => by
        obtain ⟨h1, h2⟩ := chartPair_spec_deep hS G a ν β hβ Sb HB hκ hM hF hDu hFan hDD (sr q) ψ x ρ W
          hWloc hWan hE hBW hp (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1, (hU u hu).2.2 x⟩) hψ (hg q hq x)
          hsmall (hmemAll Dd hDu) Cs
          (hdeep_of_label (G := G) (ρ := ρ) (hN := hN) (R := R) (hRdeep := hRdeep) (hρ := hρ) x Cs Y hYR hlab)
        exact ⟨h1, h2.trans (le_of_eq (by rw [← Real.exp_nat_mul]; congr 2; ring))⟩)
    have h2 := defTerm_norm_le G Dm hN hL2 hm4 hp hDB hκH hDrow rD Y hψ
    calc _ ≤ ‖chartTerm G a ν β (sr q) W F m₀ (ρ + L) Y (Dd.Ψ, Dd.h) ψ‖ + ‖defTerm G Dm m₀ rD Y ψ‖ :=
          norm_add_le _ _
      _ ≤ _ := by
          have := add_le_add h1 h2
          rw [add_mul]; exact this
  · simp only [hYR, ↓reduceIte, norm_zero]
    positivity

open Classical in
include hS Sb HB hκ hM hF hFan hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hVS hWr
  hfld_bd hfld_loc hRdeep hρ hDrange in
/-- **The masked activity of a label depends only on the blocks of the label.** -/
theorem maskedTerm_depOn (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) {q : E} (hq : q ∈ V) :
    DepOn (blocksOf m₀ 1 Set.univ Y)
      (fun Φ => maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R Y (dat q) (fld Φ)) := by
  intro Φ Φ' hΦ
  unfold maskedTerm
  by_cases hYR : Y ⊆ R
  · simp only [hYR, ↓reduceIte]
    obtain ⟨Dd, hDu, hDd⟩ := hVS q hq
    rw [hDd]
    have h1 := chartTerm_depOn_of_spec G a ν β (sr q) W F hN hL2 hDr hm4 ρ (Dd.Ψ, Dd.h) hWr fld hfld_bd
      hfld_loc Y (fun ψ hψ x Cs hlab hr =>
        (chartPair_spec_deep hS G a ν β hβ Sb HB hκ hM hF hDu hFan hDD (sr q) ψ x ρ W hWloc hWan
          hE hBW hp (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1, (hU u hu).2.2 x⟩) hψ (hg q hq x) hsmall
          (hmemAll Dd hDu) Cs (hdeep_of_label (G := G) (ρ := ρ) (hN := hN) (R := R) (hRdeep := hRdeep)
            (hρ := hρ) x Cs Y hYR hlab)).1 hr) Φ Φ' hΦ
    have h2 := defTerm_depOn (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD) (hL2 := hL2)
      (hN := hN) (hm4 := hm4) (hDrange := hDrange) (hfld_loc := hfld_loc) Y Φ Φ' hΦ
    simp only [] at h1 h2 ⊢
    rw [h1, h2]
  · simp only [hYR, ↓reduceIte]

open Classical in
include hFan hWan hE hU hsmall hmemAll hβ hκ hVS hfld_bd hfld_meas hp in
/-- **The masked activity of a label is measurable in the block variables.** -/
theorem maskedTerm_measurable (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) {q : E} (hq : q ∈ V) :
    Measurable (fun Φ => maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R Y (dat q) (fld Φ)) := by
  unfold maskedTerm
  by_cases hYR : Y ⊆ R
  · simp only [hYR, ↓reduceIte]
    exact (chartTerm_measurable (G := G) (a := a) (ν := ν) (β := β) (g := sr q) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := fun e he => by
        rw [Set.mem_singleton_iff.1 he]; exact hVS q hq) (hfld_bd := hfld_bd)
      (hfld_meas := hfld_meas) (hp := hp) (fld := fld) (m₀ := m₀) (V := {dat q}) (Y := Y)
      (he := Set.mem_singleton _)).add
      (defTerm_measurable (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD)
        (hfld_meas := hfld_meas) Y)
  · simp only [hYR, ↓reduceIte]
    exact measurable_const

open Classical in
include hFan hWan hE hBW hp hU hsmall hmemAll hβ hκ hVS hfld_bd in
/-- **The masked activity of a label is jointly analytic in the datum and the source.** -/
theorem maskedTerm_analytic (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ
      (fun q => maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R Y (dat q) (fld Φ)) V := by
  unfold maskedTerm
  by_cases hYR : Y ⊆ R
  · simp only [hYR, ↓reduceIte]
    have h1 := chartTerm_analytic_eg (BG := BG) G a ν β hβ (by linarith) hFan W hWan hE hBW hp hU hsmall
      hmemAll (m₀ := m₀) (ρs := ρ + L) Y (fld Φ) (hfld_bd Φ)
    have h2 : AnalyticOnNhd ℂ (fun q : E => (dat q, sr q)) V := fun q _ =>
      ((dat.analyticAt q).prod (sr.analyticAt q))
    have h3 := h1.comp h2 (fun q hq => ⟨hVS q hq, Set.mem_univ _⟩)
    exact h3.add analyticOnNhd_const
  · simp only [hYR, ↓reduceIte]
    exact analyticOnNhd_const

open Classical in
include hFan hWan hE hBW hp hU hsmall hmemAll hβ hκ hVS hfld_bd in
/-- **The masked activity of a label is continuous in the block variables** when the assembled field is. -/
theorem maskedTerm_continuous [∀ b, TopologicalSpace (Ωb b)] (hfld_cont : Continuous fld)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) {q : E} (hq : q ∈ V) :
    Continuous (fun Φ => maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R Y (dat q) (fld Φ)) := by
  unfold maskedTerm
  by_cases hYR : Y ⊆ R
  · simp only [hYR, ↓reduceIte]
    exact (chartTerm_continuous (G := G) (a := a) (ν := ν) (β := β) (g := sr q) (W := W) (F := F)
      (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := fun e he => by
        rw [Set.mem_singleton_iff.1 he]; exact hVS q hq) (hfld_bd := hfld_bd) (fld := fld)
      (m₀ := m₀) (V := {dat q}) hfld_cont Y (Set.mem_singleton _)).add
      (defTerm_continuous (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD) hfld_cont Y)
  · simp only [hYR, ↓reduceIte]
    exact continuous_const

open Classical in
include hS Sb HB hκ hM hF hFan hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd hVS hA hG
  hRdeep hρ hDB hDrow hWr hfld_meas hfld_bd hfld_loc hV hDrange in
/-- **The masked activities as a `LabelAct`, with a common amplitude `ε*`.**  For `κ` large and
`ε*` with `chart amplitude + defect amplitude ≤ ε* ≤ ε_max`, `0 < ε*`: on any finite set `𝒴` of labels
the family of masked activities is a family of `LabelAct` of amplitude `ε*`, rate `labelRate`,
`κ0 = a_ent + 1` and `Kc = K₀ + 1` (the constants of the hypotheses of `marked_cubes_explicit`),
jointly analytic in the datum and the source on `V`. -/
theorem masked_labelAct_eps (𝒴 : Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1)))
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ 1 Y) {κ' εs : ℝ} (hκ'0 : 0 ≤ κ')
    (hκlarge : 1 + 2 * Real.log (labelDelta d L 0 (ρ + L) : ℕ) +
      4 * d * L * 20 ^ d * (κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2) ≤ κ)
    (hεpos : 0 < εs)
    (hεs : εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ')
    (hεtot : labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) ≤ εs) :
    0 < εs ∧ εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ' ∧
    ∃ A : E → LabelAct (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Ωb
        εs (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1),
      (∀ q ∈ V, ∀ (y : {Y // Y ∈ 𝒴}) Φ,
        (A q).H y Φ = maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R y.1 (dat q) (fld Φ)) ∧
      (∀ (y : {Y // Y ∈ 𝒴}) Φ, AnalyticOnNhd ℂ (fun q => (A q).H y Φ) V) := by
  have hc1 := one_le_c1 d L
  have haent := aEnt_nonneg d L
  have hT : 0 < κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 := by linarith
  obtain ⟨hz, -⟩ := labelRate_ge d L 0 (ρ + L) hd hT hκlarge
  have hB0 : 0 ≤ 2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg := by
    have := chartBound_nonneg d L N (a 1) ν β Aα Ee BW p₁ Gg hβ hA hE hBW hp hG
    linarith
  have hε1 := labelAmp_nonneg d L m₀ m₁ 0 (ρ + L) κ hB0 hz
  have hκH : 0 ≤ labelRate d L 0 (ρ + L) κ := by
    have hz0 := labelZ_pos d L 0 (ρ + L) κ
    have hlam : 0 < -Real.log (labelZ d L 0 (ρ + L) κ) := by
      have := Real.log_neg hz0 hz; linarith
    unfold labelRate; positivity
  have hε2 : 0 ≤ defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) := by
    unfold defAmp
    have hc1' : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  obtain ⟨A, hA1, hA2⟩ := baseActivity_LabelAct (K := 1) (m₀ := m₀) (j := 1) hV hN (le_refl 1) 𝒴 hdom
    (fun Y q Φ => maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R Y (dat q) (fld Φ))
    (εH := labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ))
    (κH := labelRate d L 0 (ρ + L) κ) (κ0 := aEnt d L + 1) (Kc := K0 d L (aEnt d L + 1) + 1)
    (add_nonneg hε1 hε2) (le_refl _) (by linarith)
    (fun Y _ q hq => maskedTerm_measurable (G := G) (a := a) (ν := ν) (β := β) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd)
      (hfld_meas := hfld_meas) (hp := hp) (fld := fld) (m₀ := m₀) (V := V) (Dm := Dm) (rD := rD) (R := R)
      (dat := dat) (sr := sr) (Y := Y) (hq := hq))
    (fun Y _ q hq => maskedTerm_depOn (hS := hS) (G := G) (a := a) (ν := ν) (β := β) (hβ := hβ)
      (Sb := Sb) (HB := HB) (hκ := hκ) (hM := hM) (hF := hF) (hFan := hFan) (hDD := hDD) (hDr := hDr)
      (hm4 := hm4) (hL2 := hL2) (ρ := ρ) (W := W) (hWloc := hWloc) (hWr := hWr) (hWan := hWan)
      (hE := hE) (hBW := hBW) (hp := hp) (hU := hU) (hg := hg) (hsmall := hsmall) (hmemAll := hmemAll)
      (hN := hN) (fld := fld) (hfld_bd := hfld_bd) (hfld_loc := hfld_loc) (hVS := hVS) (Dm := Dm)
      (rD := rD) (hDrange := hDrange) (R := R) (hRdeep := hRdeep) (hρ := hρ) (dat := dat) (sr := sr)
      (Y := Y) (hq := hq))
    (fun Y _ q hq Φ => maskedTerm_norm_le (hS := hS) (G := G) (a := a) (ν := ν) (β := β) (hβ := hβ)
      (Sb := Sb) (HB := HB) (hκ := hκ) (hM := hM) (hF := hF) (hFan := hFan) (hDD := hDD) (hDr := hDr)
      (hm4 := hm4) (hd := hd) (hL2 := hL2) (ρ := ρ) (W := W) (hWloc := hWloc) (hWan := hWan)
      (hE := hE) (hBW := hBW) (hp := hp) (hA := hA) (hG := hG) (hU := hU) (hg := hg) (hsmall := hsmall)
      (hmemAll := hmemAll) (hN := hN) (hVS := hVS) (Dm := Dm) (rD := rD) (hDB := hDB) (hDrow := hDrow)
      (R := R) (hRdeep := hRdeep) (hρ := hρ) (dat := dat) (sr := sr) hz Y hq (hfld_bd Φ))
    (fun Y _ Φ => maskedTerm_analytic (G := G) (a := a) (ν := ν) (β := β) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hBW := hBW) (hp := hp) (hU := hU)
      (hsmall := hsmall) (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd)
      (fld := fld) (m₀ := m₀) (V := V) (Dm := Dm) (rD := rD) (R := R) (dat := dat) (sr := sr)
      (Y := Y) (Φ := Φ))
  exact ⟨hεpos, hεs, fun q => (A q).mono (add_nonneg hε1 hε2) hεtot le_rfl le_rfl le_rfl, hA1, hA2⟩

open Classical in
include hS Sb HB hκ hM hF hFan hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd hVS hA hG
  hRdeep hρ hDB hDrow hWr hfld_meas hfld_bd hfld_loc hV hDrange in
/-- **The cluster-expansion coefficients of the masked activities are jointly analytic in the datum and
the source.**  For every product probability measure `μ` carried by a compact set `Q` on which the assembled
field is continuous, `q ↦ Pst μ Lab (A q).H T` is analytic on `V` for the family of `masked_labelAct_eps`. -/
theorem masked_Pst_analyticOnNhd [FiniteDimensional ℂ E] [∀ b, TopologicalSpace (Ωb b)]
    [∀ b, OpensMeasurableSpace (Ωb b)] [∀ b, SecondCountableTopology (Ωb b)] (hfld_cont : Continuous fld)
    (μ : ∀ b, MeasureTheory.Measure (Ωb b)) [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(MeasureTheory.Measure.pi μ), Φ ∈ Q)
    (𝒴 : Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1)))
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ 1 Y) {κ' εs : ℝ} (hκ'0 : 0 ≤ κ')
    (hκlarge : 1 + 2 * Real.log (labelDelta d L 0 (ρ + L) : ℕ) +
      4 * d * L * 20 ^ d * (κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2) ≤ κ)
    (hεpos : 0 < εs)
    (hεs : εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ')
    (hεtot : labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) ≤ εs)
    (Y0 : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (hY0 : Y0 ∈ 𝒴)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)) :
    ∃ A : E → LabelAct (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Ωb
        εs (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1),
      (∀ q ∈ V, ∀ (y : {Y // Y ∈ 𝒴}) Φ,
        (A q).H y Φ = maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R y.1 (dat q) (fld Φ)) ∧
      AnalyticOnNhd ℂ (fun q => Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) (A q).H T) V := by
  have hc1 := one_le_c1 d L
  have haent := aEnt_nonneg d L
  have hT : 0 < κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 := by linarith
  obtain ⟨-, hrate⟩ := labelRate_ge d L 0 (ρ + L) hd hT hκlarge
  obtain ⟨-, -, A, hA1, hA2⟩ := masked_labelAct_eps hS G a ν β hβ Sb HB hκ hM hF hFan hDD hDr hm4 hd hL2 ρ W
    hWloc hWr hWan hE hBW hp hA hG hU hsmall hmemAll hN fld hfld_meas hfld_bd hfld_loc dat sr hV hVS hg Dm
    rD hDB hDrow hDrange R hRdeep hρ 𝒴 hdom hκ'0 hκlarge hεpos hεs hεtot
  refine ⟨A, hA1, ?_⟩
  have hcont : ∀ y, ∀ q ∈ V, ContinuousOn ((A q).H y) Q := by
    intro y q hq
    have h1 : (A q).H y = fun Φ => maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R y.1 (dat q) (fld Φ) :=
      funext fun Φ => hA1 q hq y Φ
    rw [h1]
    exact (maskedTerm_continuous (G := G) (a := a) (ν := ν) (β := β) (W := W) (F := F) (ρ := ρ)
      (hFan := hFan) (hWan := hWan) (hE := hE) (hBW := hBW) (hp := hp) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd) (fld := fld)
      (m₀ := m₀) (V := V) (Dm := Dm) (rD := rD) (R := R) (dat := dat) (sr := sr) hfld_cont y.1 hq).continuousOn
  exact labelAct_Pst_analyticOnNhd μ hN hV hQ hQm hμQ A ⟨Y0, hY0⟩ hA2 hcont hκ'0 hεpos hrate hεs T

end Masked2
end Props

end Balaban.LargeField.Base
