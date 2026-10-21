/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartDefectAct
public import Balaban.LargeField.Base.BaseSourcePst
import Mathlib.Tactic.Linarith

/-!
# The source dependence of the chart and defect activities

The chart exponent is affine in the source (`chartSite_affine_g`, `chartFe_affine_g`), so the
coefficients of `s ↦ V_x(F(s, e); ψ, g)` are analytic in `g` (`chartCoef_analytic_g`, by
`analyticOnNhd_coef_of_analyticOnNhd`), the activity of a label is analytic in `g`
(`chartTerm_analytic_g`) and depends on `g` only on the sites of the label (`chartTerm_g_local`).
`chartPst_src_increment` feeds the union family, for the sources in the `ℓ¹` ball, into
`Pst_src_increment`: `Pst(g) = Pst(0) + ⟨g, ℳ(g)⟩₁` with the Cauchy bound for `ℳ` and its locality.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Affine

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **`chartSite` is affine in the source.** -/
theorem chartSite_affine_g (β : ℝ) (e : ι → Fin N → ℂ) (H : Matrix ι ι ℂ) (g w : ι × Fin N → ℂ)
    (x : ι) :
    chartSite β e H g w x = chartSite β e H 0 w x +
      ∑ i, g (x, i) * (chartSite β e H (Pi.single (x, i) 1) w x - chartSite β e H 0 w x) := by
  have hδ : ∀ (i0 : Fin N) (q : Fin N → ℂ),
      ∑ j, (Pi.single (x, i0) (1 : ℂ) : ι × Fin N → ℂ) (x, j) * q j = q i0 := by
    intro i0 q
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb
      have : (x, b) ≠ (x, i0) := fun h => hb (Prod.mk.inj h).2
      simp [this]
    · simp
  unfold chartSite
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero, hδ]
  have hs : ∀ (A c : ℂ) (q : Fin N → ℂ), ∑ i, g (x, i) * (A - c * q i - A) = -(c * ∑ i, g (x, i) * q i) := by
    intro A c q
    simp only [sub_sub_cancel_left, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs _ _ (fun i => chartTangent e w (x, i) + chartZ β e (chartTangent e w) (x, i))]
  ring

end Affine

section ChartG

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem chartFe_affine_g (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g ψ : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (x : G.Ω 1) (u : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    chartFe G a ν β g ψ W x u = chartFe G a ν β 0 ψ W x u +
      ∑ i, g (x, i) * (chartFe G a ν β (Pi.single (x, i) 1) ψ W x u - chartFe G a ν β 0 ψ W x u) :=
  chartSite_affine_g β _ _ g _ x

theorem chartFe_g_congr (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    {g g' : G.Ω 1 × Fin N → ℂ} (ψ : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (x : G.Ω 1) (hgg : ∀ i, g (x, i) = g' (x, i)) (u : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    chartFe G a ν β g ψ W x u = chartFe G a ν β g' ψ W x u := by
  unfold chartFe chartSite
  simp only [hgg]

end ChartG

section ChartG2

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The coefficients of the chart exponent are analytic in the source.**  For a datum `e` of the
union domain, a bounded field `ψ` and a site `x`, `g ↦ coef_C (s ↦ V_x(F(s, e); ψ, g))` is analytic
on all sources (the chart exponent is affine in `g`); the unit sources at `x` and the source `0` satisfy the bound
`Gg ≥ 1` of `chartFunctional_bound`. -/
theorem chartCoef_analytic_g {BG : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (ν β : ℝ) (hβ : 0 < β) {κ : ℝ} (hκ : 0 < κ)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hFan : AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    {U : Set ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))}
    (hWan : ∀ p r, AnalyticOnNhd ℂ (fun u => W u p r) U) {Ee BW p₁ Aα : ℝ} (hE : 0 ≤ Ee)
    (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hU : ∀ u ∈ U, (∀ y i, ‖u.1 (y, i)‖ ≤ Ee) ∧ (∀ p, ∑ r, ‖W u p r‖ ≤ BW) ∧ ‖u.2 x‖ ≤ Aα)
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    (hsmall : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 4)
    (hmemAll : ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D →
      ∀ s : Dec2.DecParams (coverOf G), (∀ P, ‖s P‖ < Real.exp κ) → F (s, (D.Ψ, D.h)) ∈ U)
    {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ dataSet G N BG κ ν)
    (Cs : Finset ↥(coverOf G).cubeIdx) :
    AnalyticOnNhd ℂ (fun g : G.Ω 1 × Fin N → ℂ =>
      coef (fun s => chartFe G a ν β g ψ W x (F (s, e))) Cs) Set.univ := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  obtain ⟨D, hD, rfl⟩ := he
  -- the pieces `s ↦ V_x(F(s, e); ψ, src)` for a source of `ℓ¹` size `≤ 1`
  have hpiece : ∀ src : G.Ω 1 × Fin N → ℂ, ∑ i, ‖src (x, i)‖ ≤ 1 → ∀ s : Dec2.DecParams (coverOf G),
      (∀ P, ‖s P‖ < Real.exp κ) →
      AnalyticAt ℂ (fun s' : Dec2.DecParams (coverOf G) =>
        chartFe G a ν β src ψ W x (F (s', (D.Ψ, D.h)))) s := by
    intro src hsrc s hs
    have hF1 : AnalyticAt ℂ F (s, (D.Ψ, D.h)) := hFan _ ⟨hs, D, hD, rfl⟩
    have hq : AnalyticAt ℂ (fun s' : Dec2.DecParams (coverOf G) => (s', (D.Ψ, D.h))) s := by
      fun_prop
    have hFe := (chartFunctional_bound G a ν β hβ src ψ x W hWan hE hBW hp hU hψ hsrc hsmall).1
      (F (s, (D.Ψ, D.h))) (hmemAll D hD s hs)
    have h1 := hFe.comp_of_eq (hF1.comp_of_eq hq rfl) rfl
    exact h1.congr (Filter.Eventually.of_forall fun p => rfl)
  have hδ : ∀ i : Fin N, ∑ i', ‖(Pi.single (x, i) (1 : ℂ) : G.Ω 1 × Fin N → ℂ) (x, i')‖ ≤ 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : (x, b) ≠ (x, i) := fun h => hb (Prod.mk.inj h).2
      simp [this]
    · simp
  have h0 : ∑ i', ‖(0 : G.Ω 1 × Fin N → ℂ) (x, i')‖ ≤ 1 := by simp
  refine analyticOnNhd_coef_of_analyticOnNhd (R := Real.exp κ) hR
    (Φ := fun p : (G.Ω 1 × Fin N → ℂ) × Dec2.DecParams (coverOf G) =>
      chartFe G a ν β p.1 ψ W x (F (p.2, (D.Ψ, D.h)))) ?_ Cs
  rintro ⟨g, s⟩ ⟨-, hs⟩
  have hsb : ∀ P, ‖s P‖ < Real.exp κ := fun P => by simpa using hs P
  have hf0 := (hpiece 0 h0 s hsb).comp (analyticAt_snd (𝕜 := ℂ) (p := (g, s)))
  have hfi := fun i : Fin N => (hpiece (Pi.single (x, i) 1) (hδ i) s hsb).comp
    (analyticAt_snd (𝕜 := ℂ) (p := (g, s)))
  have hexp : AnalyticAt ℂ (fun p : (G.Ω 1 × Fin N → ℂ) × Dec2.DecParams (coverOf G) =>
      chartFe G a ν β 0 ψ W x (F (p.2, (D.Ψ, D.h))) +
        ∑ i, p.1 (x, i) * (chartFe G a ν β (Pi.single (x, i) 1) ψ W x (F (p.2, (D.Ψ, D.h))) -
          chartFe G a ν β 0 ψ W x (F (p.2, (D.Ψ, D.h))))) (g, s) := by
    refine hf0.add (Finset.analyticAt_fun_sum _ fun i _ => ?_)
    have hc : AnalyticAt ℂ (fun p : (G.Ω 1 × Fin N → ℂ) × Dec2.DecParams (coverOf G) => p.1 (x, i)) (g, s) := by
      fun_prop
    exact hc.mul ((hfi i).sub hf0)
  exact hexp.congr (Filter.Eventually.of_forall fun p => (chartFe_affine_g G a ν β p.1 ψ W x _).symm)

end ChartG2

section ChartSrc

set_option linter.unusedSectionVars false

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

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
  (ρ : ℕ)
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
  {V : Set (RawData d L (N₁ * L ^ m₁) 1 N)} (hV : IsOpen V) (hVS : V ⊆ dataSet G N BG κ ν)
  (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {DB : ℝ} (rD : ℕ) (hDB : 0 ≤ DB)
  (hDrow : ∀ p, ∑ q, ‖Dm p q‖ ≤ DB)
  (hDrange : ∀ p q, Dm p q ≠ 0 → supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1)
    (q.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ rD)


open Classical in
include hFan hWan hE hBW hp hU hsmall hmemAll hβ hκ hVS in
/-- **The activity of a label is analytic in the source.** -/
theorem chartTerm_analytic_g (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V) {ψ : G.Ω 1 × Fin N → ℂ}
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁) :
    AnalyticOnNhd ℂ (fun g : G.Ω 1 × Fin N → ℂ =>
      chartTerm G a ν β g W F m₀ (ρ + L) Y e ψ) Set.univ := by
  intro g hg
  unfold chartTerm
  refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun Cs _ => ?_
  exact chartCoef_analytic_g (BG := BG) G a ν β hβ (by linarith) hFan ψ x W hWan hE hBW hp
    (fun u hu => ⟨(hU u hu).1, (hU u hu).2.1, (hU u hu).2.2 x⟩) hψ hsmall hmemAll (hVS he) Cs g
    (Set.mem_univ g)

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hsmall hmemAll hβ hL2 hN hDr hm4 hVS in
/-- **The activity of a label depends on the source only on the sites of the label.** -/
theorem chartTerm_g_local {g g' : G.Ω 1 × Fin N → ℂ} (hg : ∀ x, ∑ i, ‖g (x, i)‖ ≤ Gg)
    (hg' : ∀ x, ∑ i, ‖g' (x, i)‖ ≤ Gg) (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V) {ψ : G.Ω 1 × Fin N → ℂ}
    (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    (hagree : ∀ x : G.Ω 1, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y → ∀ i, g (x, i) = g' (x, i)) :
    chartTerm G a ν β g W F m₀ (ρ + L) Y e ψ = chartTerm G a ν β g' W F m₀ (ρ + L) Y e ψ := by
  unfold chartTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Cs hCs => ?_
  have hlab := (Finset.mem_filter.1 hCs).2
  by_cases hr : IsRootedFamily (cellPatch (coverOf G) Dr)
      (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L) : Set _) Cs
  · have hfacts := chart_label_facts (G := G) (hL2 := hL2) (hN := hN) (hDr := hDr) (hm4 := hm4)
      (ρ := ρ) (x := x) (Cs := Cs) hr
    have hxY : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y := by
      rw [← hlab]; exact hfacts.2 _ (by simp only [supDist_self]; exact Nat.zero_le _)
    exact congrArg (fun f => coef f Cs)
      (funext fun s => chartFe_g_congr G a ν β ψ W x (hagree x hxY) (F (s, e)))
  · rw [(chartSpec_of_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc hWan hE hBW hp hU hg
      hsmall hmemAll (hVS he) hψ x).1 Cs hr,
      (chartSpec_of_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g' ρ W hWloc hWan hE hBW hp hU hg'
      hsmall hmemAll (hVS he) hψ x).1 Cs hr]

/-- The source on the sites of `Ω₁` of a source on the torus. -/
def srcOf (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (gc : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  fun p => gc p.1 p.2

theorem sum_srcOf_le (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (gc : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) (x : G.Ω 1) :
    ∑ i, ‖srcOf G gc (x, i)‖ ≤ l1src gc := by
  unfold l1src srcOf
  exact Finset.single_le_sum (f := fun z => ∑ i, ‖gc z i‖) (fun z _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.mem_univ (x : Balaban.Localization.CTorus d L N₁ m₁ 1))

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hsmall hmemAll hβ hL2 hN hDr hm4 hd
  hVS hA hG hWr hfld_meas hfld_bd hfld_loc hV hDB hDrow hDrange in
/-- **The source increment of the cluster coefficients of the chart and defect activities.**  Fix a datum
`e ∈ V`.  The union activities for the source `g` (on the sites of `Ω₁`) form a family `A g` of `LabelAct`
of amplitude `εs`, rate `labelRate`, `κ0 = a_ent + 1`, `Kc = K₀ + 1`, over the `ℓ¹` ball of radius `Gs > 1`
of sources, with `(A g).H y = chartTerm + defTerm`.  For `‖g‖₁ < 1` and `Y ≠ ∅`, `P(g) = Pst μ Lab (A g).H Y`
satisfies `P g = P 0 + ∑_{x,i} g_{x,i} ℳ_{x,i}(g)`, `|ℳ_{x,i}(g)| ≤ ε_s Kc C_PE e^{-κ' d(Y)} / (Gs - 1)` and
`ℳ_{x,i} = 0` for the sites `x ∉ Ŷ(Y)`. -/
theorem chartPst_src_increment [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)] (hfld_cont : Continuous fld)
    (μ : ∀ b, MeasureTheory.Measure (Ωb b)) [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(MeasureTheory.Measure.pi μ), Φ ∈ Q)
    {Gs : ℝ} (hGs : 1 < Gs) (hGg : Gs ≤ Gg)
    {κ' εs : ℝ} (hκ'0 : 0 ≤ κ')
    (hκlarge : 1 + 2 * Real.log (labelDelta d L 0 (ρ + L) : ℕ) +
      4 * d * L * 20 ^ d * (κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2) ≤ κ)
    (hεpos : 0 < εs)
    (hεs : εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ')
    (hεtot : labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) ≤ εs)
    (Y0 : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hY0 : Y0 ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD)
    {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V) :
    ∃ (hdom : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, IsDj m₀ 1 Y)
      (A : (Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) → LabelAct
        (thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) Ωb
        εs (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1)),
      (∀ gc, l1src gc < Gs → ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
        (A gc).H y Φ = chartTerm G a ν β (srcOf G gc) W F m₀ (ρ + L) y.1 e (fld Φ) +
          defTerm G Dm m₀ rD y.1 (fld Φ)) ∧
      ∀ (Y : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)), Y.Nonempty →
        ∀ gc, l1src gc < 1 →
        (Pst μ (thickLabels (m₀ := m₀) (j := 1)
            (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) (A gc).H Y =
          Pst μ (thickLabels (m₀ := m₀) (j := 1)
            (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) (A 0).H Y +
          ∑ z, ∑ i, gc z i * srcM (fun h => Pst μ (thickLabels (m₀ := m₀) (j := 1)
            (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) (A h).H Y) gc z i) ∧
        (∀ z i, ‖srcM (fun h => Pst μ (thickLabels (m₀ := m₀) (j := 1)
            (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) (A h).H Y) gc z i‖ ≤
          εs * (K0 d L (aEnt d L + 1) + 1) *
            CPE d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ' *
            Real.exp (-κ' * dExt Y) / (Gs - 1)) ∧
        (∀ z, z ∉ Yhat Set.univ (sitesOf Y) → ∀ i, srcM (fun h => Pst μ (thickLabels (m₀ := m₀) (j := 1)
            (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) (A h).H Y) gc z i = 0) := by
  have hc1 := one_le_c1 d L
  have haent := aEnt_nonneg d L
  have hT : 0 < κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 := by linarith
  obtain ⟨-, hrate⟩ := labelRate_ge d L 0 (ρ + L) hd hT hκlarge
  have hGg0 : 0 ≤ Gg := by linarith
  -- the family of `LabelAct` over the sources
  have hsrc : ∀ gc : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ, l1src gc < Gs → ∀ x : G.Ω 1, ∑ i, ‖srcOf G gc (x, i)‖ ≤ Gg := fun gc hb x =>
    (sum_srcOf_le G gc x).trans (hb.le.trans hGg)
  have hex0 := union_labelAct_eps hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD hDr hm4 hd hL2 0 ρ W hWloc hWr
    hWan hE hBW hp hA hGg0 hU (fun x => by simp; exact hGg0) hsmall hmemAll hN fld hfld_meas hfld_bd
    hfld_loc hV hVS Dm rD hDB hDrow hDrange hκ'0 hκlarge hεpos hεs hεtot
  obtain ⟨-, -, hdom, A0, -⟩ := hex0
  have hex : ∀ gc : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ,
      ∃ A : RawData d L (N₁ * L ^ m₁) 1 N → LabelAct
        (thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) Ωb
        εs (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1),
        l1src gc < Gs → ∀ e' ∈ V, ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
          (A e').H y Φ = chartTerm G a ν β (srcOf G gc) W F m₀ (ρ + L) y.1 e' (fld Φ) +
            defTerm G Dm m₀ rD y.1 (fld Φ) := by
    intro gc
    by_cases hb : l1src gc < Gs
    · obtain ⟨-, -, _, A, hA1, -⟩ := union_labelAct_eps hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD hDr hm4
        hd hL2 (srcOf G gc) ρ W hWloc hWr hWan hE hBW hp hA hGg0 hU (hsrc gc hb) hsmall hmemAll hN fld
        hfld_meas hfld_bd hfld_loc hV hVS Dm rD hDB hDrow hDrange hκ'0 hκlarge hεpos hεs hεtot
      exact ⟨A, fun _ => hA1⟩
    · exact ⟨A0, fun h => absurd h hb⟩
  choose Afam hAfam using hex
  refine ⟨hdom, fun gc => Afam gc e, fun gc hb y Φ => hAfam gc hb e he y Φ, ?_⟩
  intro Y hY gc hgc
  have hopen : IsOpen {g : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ | l1src g < Gs} :=
    isOpen_lt continuous_l1src continuous_const
  have hform : ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) (Φ : ∀ b, Ωb b),
      ∀ gc0, l1src gc0 < Gs → AnalyticAt ℂ (fun gc' : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ =>
        chartTerm G a ν β (srcOf G gc') W F m₀ (ρ + L) y.1 e (fld Φ) +
          defTerm G Dm m₀ rD y.1 (fld Φ)) gc0 := by
    intro y Φ gc0 _
    have h1 := chartTerm_analytic_g (hFan := hFan) (hWan := hWan) (hE := hE) (hBW := hBW) (hp := hp)
      (hU := hU) (hsmall := hsmall) (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS)
      (G := G) (a := a) (ν := ν) (β := β) (W := W) (F := F) (ρ := ρ) (m₀ := m₀) (V := V)
      y.1 he (hfld_bd Φ) (srcOf G gc0) (Set.mem_univ _)
    have h2 : AnalyticAt ℂ (fun gc' : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ =>
        srcOf G gc') gc0 := by
      exact analyticAt_pi_iff.2 fun p => by
        show AnalyticAt ℂ (fun gc' : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ => gc' p.1 p.2) gc0
        fun_prop
    have h3 := h1.comp_of_eq h2 rfl
    exact (h3.congr (Filter.Eventually.of_forall fun p => rfl)).add analyticAt_const
  have key := Pst_src_increment (μ := μ) (hN := hN) (hj := le_refl 1) (hΩ := isPiUnion_univ_K)
    (Lab := thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom)
    (εH := εs) (κH := labelRate d L 0 (ρ + L) κ) (κ0 := aEnt d L + 1) (κ' := κ')
    (Kc := K0 d L (aEnt d L + 1) + 1) (hQ := hQ) (hQm := hQm) (hμQ := hμQ) (hGs := hGs)
    (A := fun gc' => Afam gc' e) (y0 := ⟨Y0, hY0⟩)
    (hAhol := fun y Φ _ gc0 hgc0 => by
      have hev : ∀ᶠ gc' in nhds gc0, (Afam gc' e).H y Φ =
          chartTerm G a ν β (srcOf G gc') W F m₀ (ρ + L) y.1 e (fld Φ) + defTerm G Dm m₀ rD y.1 (fld Φ) := by
        filter_upwards [hopen.mem_nhds hgc0] with gc' hb' using hAfam gc' hb' e he y Φ
      exact (hform y Φ gc0 hgc0).congr (hev.mono fun p hp => hp.symm))
    (hAcont := fun y gc' hb' => by
      have h1 : (Afam gc' e).H y = fun Φ => chartTerm G a ν β (srcOf G gc') W F m₀ (ρ + L) y.1 e (fld Φ) +
          defTerm G Dm m₀ rD y.1 (fld Φ) := funext fun Φ => hAfam gc' hb' e he y Φ
      rw [h1]
      exact ((chartTerm_continuous (G := G) (a := a) (ν := ν) (β := β) (g := srcOf G gc') (W := W)
        (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
        (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd) (fld := fld)
        (m₀ := m₀) (V := V) hfld_cont y.1 he).add
        (defTerm_continuous (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD) hfld_cont y.1)).continuousOn)
    (hdep := fun y gc1 gc2 h1 h2 hag => by
      funext Φ
      rw [hAfam gc1 h1 e he y Φ, hAfam gc2 h2 e he y Φ]
      congr 1
      exact chartTerm_g_local (hS := hS) (G := G) (a := a) (ν := ν) (β := β) (hβ := hβ) (Sb := Sb)
        (HB := HB) (hκ := hκ) (hM := hM) (hF := hF) (hFan := hFan) (hΩ := hΩ) (hDD := hDD) (ρ := ρ)
        (W := W) (hWloc := hWloc) (hWan := hWan) (hE := hE) (hBW := hBW) (hp := hp) (hU := hU)
        (hsmall := hsmall) (hmemAll := hmemAll) (hL2 := hL2) (hN := hN) (hDr := hDr) (hm4 := hm4)
        (hVS := hVS) (hg := hsrc gc1 h1) (hg' := hsrc gc2 h2) (Y := y.1) (he := he) (hψ := hfld_bd Φ)
        (hagree := fun x hx i => by simp only [srcOf]; rw [hag _ hx]))
    (hκ0 := le_rfl) (hKc := le_rfl) (hεpos := hεpos) (hκ' := hκ'0) (hκ := hrate) (hε := hεs)
    (Y := Y) (hY := hY) (hg := hgc)
  exact key

end ChartSrc

end Balaban.LargeField.Base
