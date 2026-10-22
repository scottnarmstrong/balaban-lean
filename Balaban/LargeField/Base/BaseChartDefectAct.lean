/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartLabelAct
public import Balaban.LargeField.Base.BaseUnionNumerics
public import Balaban.LargeField.Base.BasePstAnalytic
import Mathlib.Tactic.Linarith

/-!
# The quadratic defect as a `LabelAct`, and its union with the chart exponents

For an abstract finite-range matrix `D` (row sums `≤ ‖D‖`, `D_{pq} ≠ 0 → |p - q| ≤ r`), the defect
`q_D(ψ) = ∑_x defPt D ψ x` has the activity `defTerm Y`: the sum of `defPt` over the sites whose label
is `Y`, the label of `x` being the hull of the root cube of `x` and of the patches meeting the ball of
radius `r` (`labelSet … r ∅`, of size at most `2 d L (2r/L^{1+m₁}+2)^d`).  It is bounded by
`defAmp · e^{-κ d(Y)}` for every `κ ≥ 0` (`defTerm_norm_le`, `ncard_le_of_isDj`), depends on the blocks
of `Y` only (`defTerm_depOn`), and is measurable.  `chartDefectActivity_LabelAct` puts the chart
and the defect activities into one `LabelAct` on the union of the two label sets, of amplitude the sum
of the amplitudes.  The activities are continuous in the block variables when the assembled field is
(`chartTerm_continuous`, `defTerm_continuous`), which feeds `Pst_Gst_analyticOnNhd`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Defect

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The quadratic defect at the site `x`: `∑_{i,y,j} ψ_{x i} D_{(x,i),(y,j)} ψ_{y j}`. -/
noncomputable def defPt (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) (ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) : ℂ :=
  ∑ i : Fin N, ∑ q : G.Ω 1 × Fin N, ψ (x, i) * D (x, i) q * ψ q

theorem norm_defPt_le (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {Dr0 p₁ : ℝ} (hp : 0 ≤ p₁)
    (hD : ∀ p, ∑ q, ‖D p q‖ ≤ Dr0) {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁) (x : G.Ω 1) :
    ‖defPt G D ψ x‖ ≤ N * (p₁ * (Dr0 * p₁)) := by
  unfold defPt
  refine (norm_sum_le _ _).trans ?_
  have hi : ∀ i : Fin N, ‖∑ q : G.Ω 1 × Fin N, ψ (x, i) * D (x, i) q * ψ q‖ ≤ p₁ * (Dr0 * p₁) := by
    intro i
    refine (norm_sum_le _ _).trans ?_
    calc ∑ q : G.Ω 1 × Fin N, ‖ψ (x, i) * D (x, i) q * ψ q‖
        ≤ ∑ q : G.Ω 1 × Fin N, p₁ * (‖D (x, i) q‖ * p₁) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [norm_mul, norm_mul]
          have h1 := hψ (x, i)
          have h2 := hψ q
          have h3 := norm_nonneg (D (x, i) q)
          calc ‖ψ (x, i)‖ * ‖D (x, i) q‖ * ‖ψ q‖ ≤ p₁ * ‖D (x, i) q‖ * p₁ := by gcongr
            _ = p₁ * (‖D (x, i) q‖ * p₁) := by ring
      _ = p₁ * ((∑ q, ‖D (x, i) q‖) * p₁) := by rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ p₁ * (Dr0 * p₁) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hD _) hp) hp
  calc ∑ i : Fin N, ‖∑ q : G.Ω 1 × Fin N, ψ (x, i) * D (x, i) q * ψ q‖
      ≤ ∑ _i : Fin N, p₁ * (Dr0 * p₁) := Finset.sum_le_sum fun i _ => hi i
    _ = N * (p₁ * (Dr0 * p₁)) := by simp

theorem defPt_congr (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {r : ℕ}
    (hDr : ∀ p q, D p q ≠ 0 → supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1)
      (q.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ r)
    {ψ ψ' : G.Ω 1 × Fin N → ℂ} (x : G.Ω 1)
    (h : ∀ q : G.Ω 1 × Fin N, supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1)
      (q.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ r → ψ q = ψ' q) :
    defPt G D ψ x = defPt G D ψ' x := by
  unfold defPt
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases h0 : D (x, i) q = 0
  · rw [h0]; simp
  · have hq := hDr _ _ h0
    have hx : supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1)
        ((x, i).1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ r := by
      simp only [supDist_self]; exact Nat.zero_le _
    rw [h (x, i) hx, h q hq]

open Classical in
/-- The activity of the label `Y` in the quadratic defect: the defect at the sites `x` whose label
(the hull of the root cube of `x` and of the patches meeting the ball of radius `r`) is `Y`. -/
noncomputable def defTerm (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) (m₀ r : ℕ)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (ψ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x : G.Ω 1, if labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅ = Y
    then defPt G D ψ x else 0

open Classical in
theorem defect_label_facts (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (hL2 : 2 ≤ L) (hm4 : 4 * L ^ 2 ≤ L ^ m₁) (x : G.Ω 1) (r : ℕ) :
    IsPolyDom m₀ (0 + 1) (labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅) ∧
    (∀ y, supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ r →
      y ∈ labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅) ∧
    sizeJ m₀ (0 + 1) (labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅) ≤
      (2 * d * L : ℝ) * (((2 * r / L ^ (0 + 1 + m₁) + 2) ^ d : ℕ) : ℝ) := by
  have hlay : ∀ q ∈ (coverOf G).cubeIdx, q.1 ≤ 0 + 1 := fun q hq => ((mem_cubeIdx G).1 hq).1.2
  have hD0 : (0 : ℕ) ≤ L ^ (0 + 1 + m₁) := Nat.zero_le _
  have := labelHull_spec (C := coverOf G) (m₀ := m₀) (D := 0) (S := (∅ : Set _)) hN hL2 hD0 hm4 hlay
    (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρs := r) (fun y hy => absurd hy (Set.notMem_empty y))
    (Cs := ∅) (fun i hi => absurd hi (Finset.notMem_empty i))
  refine ⟨this.1, this.2.1, ?_⟩
  simpa [labelSet] using this.2.2

/-- The amplitude of the activity of the defect labels. -/
noncomputable def defAmp (d L m₀ m₁ N r : ℕ) (Dr0 p₁ κH : ℝ) : ℝ :=
  (((L ^ (0 + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d * c1 d L * (N * (p₁ * (Dr0 * p₁))) *
    (1 + (2 * d * L : ℝ) * (((2 * r / L ^ (0 + 1 + m₁) + 2) ^ d : ℕ) : ℝ)) *
    Real.exp (κH * ((2 * d * L : ℝ) * (((2 * r / L ^ (0 + 1 + m₁) + 2) ^ d : ℕ) : ℝ)))

open Classical in
/-- **The size of the activity of a defect label.** -/
theorem defTerm_norm_le (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {Dr0 p₁ κH : ℝ} {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (hL2 : 2 ≤ L) (hm4 : 4 * L ^ 2 ≤ L ^ m₁) (hp : 0 ≤ p₁) (hDr0 : 0 ≤ Dr0) (hκH : 0 ≤ κH)
    (hD : ∀ p, ∑ q, ‖D p q‖ ≤ Dr0) (r : ℕ) (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁) :
    ‖defTerm G D m₀ r Y ψ‖ ≤ defAmp d L m₀ m₁ N r Dr0 p₁ κH *
      Real.exp (-κH * treeLenCovOne m₀ (0 + 1) Y) := by
  set BD : ℝ := N * (p₁ * (Dr0 * p₁)) with hBD
  have hBD0 : 0 ≤ BD := by positivity
  set σm : ℝ := (2 * d * L : ℝ) * (((2 * r / L ^ (0 + 1 + m₁) + 2) ^ d : ℕ) : ℝ) with hσm
  have hσm0 : 0 ≤ σm := by positivity
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hamp : 0 ≤ defAmp d L m₀ m₁ N r Dr0 p₁ κH := by unfold defAmp; positivity
  by_cases hex : ∃ x : G.Ω 1, labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅ = Y
  swap
  · have h0 : defTerm G D m₀ r Y ψ = 0 := Finset.sum_eq_zero fun x _ => by
      have hneg : ¬ labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅ = Y :=
        fun h => hex ⟨x, h⟩
      simp [hneg]
    rw [h0, norm_zero]; positivity
  obtain ⟨x0, hx0⟩ := hex
  have hf0 := defect_label_facts G hN hL2 hm4 x0 r
  have hY : IsPolyDom m₀ (0 + 1) Y := by rw [← hx0]; exact hf0.1
  have hYDj : IsDj m₀ 1 Y := isDj_of_isPolyDom hY
  set σ : ℝ := treeLenCovOne m₀ (0 + 1) Y with hσ
  have hσ0 : 0 ≤ σ := treeLenCovOne_nonneg m₀ (0 + 1) Y
  have hσle : σ ≤ σm := by rw [← hx0] at hσ; exact hσ ▸ hf0.2.2
  -- the sum over the sites with label `Y`
  have hnorm : ‖defTerm G D m₀ r Y ψ‖ ≤ ∑ x : G.Ω 1, if (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y then BD else 0 := by
    unfold defTerm
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    by_cases hl : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅ = Y
    · have hxY : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y := by
        rw [← hl]
        exact (defect_label_facts G hN hL2 hm4 x r).2.1 _ (by simp only [supDist_self]; exact Nat.zero_le _)
      simp only [hl, hxY, ite_true]
      exact norm_defPt_le G D hp hD hψ x
    · simp only [hl, ite_false, norm_zero]
      split_ifs
      · exact hBD0
      · exact le_rfl
  have hcard : (∑ x : G.Ω 1, if (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y then BD else 0) ≤
      (Y.ncard : ℝ) * BD := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hBD0
    have h1 : (Finset.univ.filter fun x : G.Ω 1 => (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y).card =
        ((Finset.univ.filter fun x : G.Ω 1 => (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y).image
          (fun x : G.Ω 1 => (x : Balaban.Localization.CTorus d L N₁ m₁ 1))).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    have h2 : (((Finset.univ.filter fun x : G.Ω 1 => (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y).image
          (fun x : G.Ω 1 => (x : Balaban.Localization.CTorus d L N₁ m₁ 1)) : Finset _) :
          Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) ⊆ Y := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact (Finset.mem_filter.1 hx).2
    have h3 := Set.ncard_le_ncard h2 (Set.toFinite Y)
    rw [Set.ncard_coe_finset] at h3
    rw [h1]; exact_mod_cast h3
  have hYn := ncard_le_of_isDj hN (le_refl 1) hYDj
  have hcs : ((cellSide L m₀ m₁ 1 : ℕ) : ℝ) = (((L ^ (0 + 1 + m₀ + m₁) : ℕ) : ℝ)) := by
    unfold cellSide; rfl
  rw [hcs] at hYn
  have hexp : (1 + σ) ≤ (1 + σm) * Real.exp (κH * σm) * Real.exp (-κH * σ) := by
    have h1 : 1 ≤ Real.exp (κH * σm) * Real.exp (-κH * σ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 + σm)]
  have ha0 : 0 ≤ (((L ^ (0 + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d := by positivity
  calc ‖defTerm G D m₀ r Y ψ‖ ≤ (Y.ncard : ℝ) * BD := hnorm.trans hcard
    _ ≤ ((((L ^ (0 + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d * (c1 d L * (1 + σ))) * BD :=
        mul_le_mul_of_nonneg_right hYn hBD0
    _ = ((((L ^ (0 + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d * c1 d L * BD) * (1 + σ) := by ring
    _ ≤ ((((L ^ (0 + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d * c1 d L * BD) *
          ((1 + σm) * Real.exp (κH * σm) * Real.exp (-κH * σ)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by unfold defAmp; ring

end Defect


section Union

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
  (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {DB : ℝ} (rD : ℕ) (hDB : 0 ≤ DB)
  (hDrow : ∀ p, ∑ q, ‖Dm p q‖ ≤ DB)
  (hDrange : ∀ p q, Dm p q ≠ 0 → supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1)
    (q.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ≤ rD)

open Classical in
/-- **The labels of the defect activities**: the hulls attached to the sites of `Ω₁`. -/
noncomputable def defLabels (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (m₀ r : ℕ) :
    Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) :=
  Finset.univ.image fun x : G.Ω 1 =>
    labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) r ∅

open Classical in
include hL2 hN hm4 in
theorem defLabels_isDj : ∀ Y ∈ defLabels G m₀ rD, IsDj m₀ 1 Y := by
  intro Y hY
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hY
  exact isDj_of_isPolyDom (defect_label_facts G hN hL2 hm4 x rD).1

open Classical in
theorem defTerm_eq_zero_of_not_mem {Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hY : Y ∉ defLabels G m₀ rD) (ψ : G.Ω 1 × Fin N → ℂ) : defTerm G Dm m₀ rD Y ψ = 0 := by
  unfold defTerm
  refine Finset.sum_eq_zero fun x _ => ?_
  have hneg : ¬ labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) rD ∅ = Y :=
    fun h => hY (Finset.mem_image.2 ⟨x, Finset.mem_univ _, h⟩)
  simp [hneg]

open Classical in
include hL2 hN hm4 hDrange hfld_loc in
/-- The defect activity of a label depends on the blocks of the label only. -/
theorem defTerm_depOn (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) :
    DepOn (blocksOf m₀ 1 Set.univ Y) (fun Φ => defTerm G Dm m₀ rD Y (fld Φ)) := by
  intro Φ Φ' hΦ
  unfold defTerm
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hl : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) rD ∅ = Y
  · simp only [hl, ite_true]
    have hfacts := defect_label_facts G hN hL2 hm4 x rD
    have hYDj : IsDj m₀ 1 Y := by
      rw [← hl]; exact isDj_of_isPolyDom hfacts.1
    refine defPt_congr G Dm hDrange x fun q hq => ?_
    have hqY : (q.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y := by
      rw [← hl]; exact hfacts.2.1 _ hq
    obtain ⟨b, hb, hbx⟩ := exists_block_of_mem hN (le_refl 1) hYDj hqY
    exact hfld_loc (blocksOf m₀ 1 Set.univ Y) Φ Φ' hΦ q ⟨b, hb, hbx⟩
  · simp [hl]

open Classical in
include hfld_meas in
theorem defTerm_measurable (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) :
    Measurable (fun Φ => defTerm G Dm m₀ rD Y (fld Φ)) := by
  have hco : ∀ q : G.Ω 1 × Fin N, Measurable (fun Φ => fld Φ q) := fun q =>
    (measurable_pi_apply q).comp hfld_meas
  unfold defTerm
  refine Finset.measurable_sum _ fun x _ => ?_
  by_cases hl : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) rD ∅ = Y
  · simp only [hl, ite_true]
    unfold defPt
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun q _ => ?_
    exact ((hco (x, i)).mul_const _).mul (hco q)
  · simp [hl]

open Classical in
theorem defTerm_sum (ψ : G.Ω 1 × Fin N → ℂ) :
    ∑ Y ∈ defLabels G m₀ rD, defTerm G Dm m₀ rD Y ψ = ∑ x : G.Ω 1, defPt G Dm ψ x := by
  unfold defTerm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) rD ∅)]
  · simp
  · intro Y _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd (Finset.mem_image.2 ⟨x, Finset.mem_univ _, rfl⟩) h

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hVS in
theorem chartTerm_eq_zero_of_not_mem {e : RawData d L (N₁ * L ^ m₁) 1 N} (he : e ∈ V)
    {ψ : G.Ω 1 × Fin N → ℂ} (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    {Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)} (hY : Y ∉ chartLabels G Dr m₀ (ρ + L)) :
    chartTerm G a ν β g W F m₀ (ρ + L) Y e ψ = 0 := by
  unfold chartTerm
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun Cs hCs => ?_
  have hsp := chartSpec_of_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc hWan hE
    hBW hp hU hg hsmall hmemAll (hVS he) hψ x
  refine hsp.1 Cs fun hr => hY ?_
  rw [← (Finset.mem_filter.1 hCs).2]
  exact Finset.mem_image.2 ⟨(x, Cs), Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩, rfl⟩

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd
  hVS hA hG hWr hfld_meas hfld_bd hfld_loc hV hDB hDrow hDrange in
/-- **The chart exponents and the quadratic defect as one `LabelAct`.**  On the labels
`chartLabels ∪ defLabels` the activity is `chartTerm + defTerm`; the amplitude is the sum of the
amplitudes and the rate is that of the chart activities. -/
theorem chartDefectActivity_LabelAct {κ0 Kent : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    (hKent : K0 d L κ0 ≤ Kent) (hz : labelZ d L 0 (ρ + L) κ < 1) :
    ∃ (hdom : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, IsDj m₀ 1 Y)
      (A : RawData d L (N₁ * L ^ m₁) 1 N → LabelAct
        (thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) Ωb
        (labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
          defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ))
        (labelRate d L 0 (ρ + L) κ) κ0 Kent),
      (∀ e ∈ V, ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
        (A e).H y Φ = chartTerm G a ν β g W F m₀ (ρ + L) y.1 e (fld Φ) +
          defTerm G Dm m₀ rD y.1 (fld Φ)) ∧
      (∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
        AnalyticOnNhd ℂ (fun e => (A e).H y Φ) V) ∧
      (∀ e ∈ V, ∀ Φ, ∑ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD,
          (chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) + defTerm G Dm m₀ rD Y (fld Φ)) =
        ∑ x : G.Ω 1, (chartFe G a ν β g (fld Φ) W x (F (fun _ => 1, e)) +
          defPt G Dm (fld Φ) x)) := by
  have hdom : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, IsDj m₀ 1 Y := by
    intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact chartLabels_isDj G hDr hm4 hL2 hN (ρ := ρ) Y h
    · exact defLabels_isDj G hm4 hL2 hN (rD := rD) Y h
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
  have hmeas : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, ∀ e ∈ V,
      Measurable (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) +
        defTerm G Dm m₀ rD Y (fld Φ)) :=
    fun Y _ e he => (chartTerm_measurable (G := G) (a := a) (ν := ν) (β := β) (g := g) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd)
      (hfld_meas := hfld_meas) (hp := hp) (fld := fld) (m₀ := m₀) (V := V) (Y := Y) (he := he)).add
      (defTerm_measurable (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD)
        (hfld_meas := hfld_meas) Y)
  have hdep : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, ∀ e ∈ V,
      DepOn (blocksOf m₀ 1 Set.univ Y) (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) +
        defTerm G Dm m₀ rD Y (fld Φ)) := by
    intro Y _ e he Φ Φ' hΦ
    have h1 := chartTerm_depOn hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD hDr hm4 hL2 g ρ W hWloc
      hWr hWan hE hBW hp hU hg hsmall hmemAll hN fld hfld_bd hfld_loc hVS Y he Φ Φ' hΦ
    have h2 := defTerm_depOn (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD) (hL2 := hL2)
      (hN := hN) (hm4 := hm4) (hDrange := hDrange) (hfld_loc := hfld_loc) Y Φ Φ' hΦ
    simp only [] at h1 h2 ⊢
    rw [h1, h2]
  have hbd : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, ∀ e ∈ V, ∀ Φ,
      ‖chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) + defTerm G Dm m₀ rD Y (fld Φ)‖ ≤
        (labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
          defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ)) *
          Real.exp (-(labelRate d L 0 (ρ + L) κ) * treeLenCovOne m₀ 1 Y) := by
    intro Y _ e he Φ
    have h1 := chartTerm_norm_le hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD hDr hm4 hd hL2 g ρ W
      hWloc hWan hE hBW hp hA hG hU hg hsmall hmemAll hN hVS hz Y he (hfld_bd Φ)
    have h2 := defTerm_norm_le G Dm hN hL2 hm4 hp hDB hκH hDrow rD Y (hfld_bd Φ)
    calc _ ≤ ‖chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)‖ + ‖defTerm G Dm m₀ rD Y (fld Φ)‖ :=
          norm_add_le _ _
      _ ≤ _ := by
          have := add_le_add h1 h2
          rw [add_mul]; exact this
  have han : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, ∀ Φ, AnalyticOnNhd ℂ
      (fun e => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) + defTerm G Dm m₀ rD Y (fld Φ)) V :=
    fun Y _ Φ => (chartTerm_analytic (G := G) (a := a) (ν := ν) (β := β) (g := g) (W := W)
      (F := F) (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd) (fld := fld)
      (m₀ := m₀) (V := V) (Y := Y) (Φ := Φ)).add analyticOnNhd_const
  obtain ⟨A, hA1, hA2⟩ := baseActivity_LabelAct (K := 1) (m₀ := m₀) (j := 1) hV hN (le_refl 1)
    (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom
    (fun Y e Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) + defTerm G Dm m₀ rD Y (fld Φ))
    (εH := labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ))
    (κH := labelRate d L 0 (ρ + L) κ) (add_nonneg hε1 hε2) hκ0 hKent hmeas hdep hbd han
  refine ⟨hdom, A, hA1, hA2, fun e he Φ => ?_⟩
  rw [Finset.sum_add_distrib]
  have hc : ∑ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD,
      chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) =
      ∑ Y ∈ chartLabels G Dr m₀ (ρ + L), chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) :=
    (Finset.sum_subset Finset.subset_union_left fun Y _ hY =>
      chartTerm_eq_zero_of_not_mem hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc hWan hE hBW hp
        hU hg hsmall hmemAll hVS he (hfld_bd Φ) hY).symm
  have hd2 : ∑ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, defTerm G Dm m₀ rD Y (fld Φ) =
      ∑ Y ∈ defLabels G m₀ rD, defTerm G Dm m₀ rD Y (fld Φ) :=
    (Finset.sum_subset Finset.subset_union_right fun Y _ hY =>
      defTerm_eq_zero_of_not_mem (G := G) (Dm := Dm) (m₀ := m₀) (rD := rD) hY _).symm
  rw [hc, hd2, chartTerm_sum hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD g ρ W hWloc hWan hE hBW hp hU hg
    hsmall hmemAll hVS he (hfld_bd Φ), defTerm_sum, Finset.sum_add_distrib]

open Classical in
include hFan hWan hE hU hsmall hmemAll hβ hκ hVS hfld_bd in
/-- **The chart activity is continuous in the block variables** when the assembled field is. -/
theorem chartTerm_continuous [∀ b, TopologicalSpace (Ωb b)] (hfld_cont : Continuous fld)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) {e : RawData d L (N₁ * L ^ m₁) 1 N}
    (he : e ∈ V) : Continuous (fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ)) := by
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
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun Cs _ => ?_
  exact (hcont x Cs).comp_continuous hfld_cont hfld_bd

open Classical in
theorem defTerm_continuous [∀ b, TopologicalSpace (Ωb b)] (hfld_cont : Continuous fld)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) :
    Continuous (fun Φ => defTerm G Dm m₀ rD Y (fld Φ)) := by
  have hco : ∀ q : G.Ω 1 × Fin N, Continuous (fun Φ => fld Φ q) := fun q =>
    (continuous_apply q).comp hfld_cont
  unfold defTerm
  refine continuous_finsetSum _ fun x _ => ?_
  by_cases hl : labelSet (coverOf G) m₀ (x : Balaban.Localization.CTorus d L N₁ m₁ 1) rD ∅ = Y
  · simp only [hl, ite_true]
    unfold defPt
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun q _ => ?_
    exact ((hco (x, i)).mul continuous_const).mul (hco q)
  · simp only [hl, ite_false]
    exact continuous_const

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd
  hVS hA hG hWr hfld_meas hfld_bd hfld_loc hV hDB hDrow hDrange in
/-- **The union `LabelAct`, relaxed to a common amplitude `ε*`.**  For `κ` large (`labelRate_ge`) and
`ε*` with `chart amplitude + defect amplitude ≤ ε* ≤ ε_max`, `0 < ε*`: the family of
`chartDefectActivity_LabelAct` is a family of `LabelAct` of amplitude `ε*`, rate `labelRate`, `κ0 = a_ent + 1`
and `Kc = K₀ + 1`, i.e. with exactly the constants of the hypotheses of `marked_cubes_explicit`. -/
theorem union_labelAct_eps {κ' εs : ℝ} (hκ'0 : 0 ≤ κ')
    (hκlarge : 1 + 2 * Real.log (labelDelta d L 0 (ρ + L) : ℕ) +
      4 * d * L * 20 ^ d * (κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2) ≤ κ)
    (hεpos : 0 < εs)
    (hεs : εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ')
    (hεtot : labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) ≤ εs) :
    0 < εs ∧ εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ' ∧
    ∃ (hdom : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, IsDj m₀ 1 Y)
      (A : RawData d L (N₁ * L ^ m₁) 1 N → LabelAct
        (thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) Ωb
        εs (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1)),
      (∀ e ∈ V, ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
        (A e).H y Φ = chartTerm G a ν β g W F m₀ (ρ + L) y.1 e (fld Φ) +
          defTerm G Dm m₀ rD y.1 (fld Φ)) ∧
      (∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
        AnalyticOnNhd ℂ (fun e => (A e).H y Φ) V) ∧
      (∀ e ∈ V, ∀ Φ, ∑ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD,
          (chartTerm G a ν β g W F m₀ (ρ + L) Y e (fld Φ) + defTerm G Dm m₀ rD Y (fld Φ)) =
        ∑ x : G.Ω 1, (chartFe G a ν β g (fld Φ) W x (F (fun _ => 1, e)) +
          defPt G Dm (fld Φ) x)) := by
  have hc1 := one_le_c1 d L
  have haent := aEnt_nonneg d L
  have hT : 0 < κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 := by linarith
  obtain ⟨hz, -⟩ := labelRate_ge d L 0 (ρ + L) hd hT hκlarge
  obtain ⟨hdom, A, hA1, hA2, hA3⟩ := chartDefectActivity_LabelAct hS G a ν β hβ Sb HB hκ hM hF hFan hΩ
    hDD hDr hm4 hd hL2 g ρ W hWloc hWr hWan hE hBW hp hA hG hU hg hsmall hmemAll hN fld hfld_meas
    hfld_bd hfld_loc hV hVS Dm rD hDB hDrow hDrange (κ0 := aEnt d L + 1)
    (Kent := K0 d L (aEnt d L + 1) + 1) (le_refl (aEnt d L + 1)) (by linarith) hz
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
  exact ⟨hεpos, hεs, hdom, fun e => (A e).mono (add_nonneg hε1 hε2) hεtot le_rfl le_rfl le_rfl, hA1, hA2, hA3⟩

open Classical in
include hS Sb HB hκ hM hF hFan hΩ hDD hWloc hWan hE hBW hp hU hg hsmall hmemAll hβ hL2 hN hDr hm4 hd
  hVS hA hG hWr hfld_meas hfld_bd hfld_loc hV hDB hDrow hDrange in
/-- **The coefficients of the cluster expansion of the union family are analytic in the data.**
For every product probability measure `μ` carried by a compact set `Q` on which the assembled field
is continuous, `e ↦ Pst μ Lab (A e).H Y` is analytic on `V` (`Pst_Gst_analyticOnNhd` with the mark
`G = 1`, `F0 = e^{κG d(y0)}`), for the union family of `union_labelAct_eps`. -/
theorem union_Pst_analyticOnNhd [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)] (hfld_cont : Continuous fld)
    (μ : ∀ b, MeasureTheory.Measure (Ωb b)) [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(MeasureTheory.Measure.pi μ), Φ ∈ Q)
    {κ' εs : ℝ} (hκ'0 : 0 ≤ κ')
    (hκlarge : 1 + 2 * Real.log (labelDelta d L 0 (ρ + L) : ℕ) +
      4 * d * L * 20 ^ d * (κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2) ≤ κ)
    (hεpos : 0 < εs)
    (hεs : εs ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) κ')
    (hεtot : labelAmp d L m₀ m₁ 0 (ρ + L) κ (2 * chartBound d L N (a 1) ν β Aα Ee BW p₁ Gg) +
      defAmp d L m₀ m₁ N rD DB p₁ (labelRate d L 0 (ρ + L) κ) ≤ εs)
    (Y0 : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hY0 : Y0 ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD)
    (Y : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)) :
    ∃ (hdom : ∀ Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD, IsDj m₀ 1 Y)
      (A : RawData d L (N₁ * L ^ m₁) 1 N → LabelAct
        (thickLabels (m₀ := m₀) (j := 1) (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) Ωb
        εs (labelRate d L 0 (ρ + L) κ) (aEnt d L + 1) (K0 d L (aEnt d L + 1) + 1)),
      (∀ e ∈ V, ∀ (y : {Y // Y ∈ chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD}) Φ,
        (A e).H y Φ = chartTerm G a ν β g W F m₀ (ρ + L) y.1 e (fld Φ) +
          defTerm G Dm m₀ rD y.1 (fld Φ)) ∧
      AnalyticOnNhd ℂ (fun e => Pst μ (thickLabels (m₀ := m₀) (j := 1)
        (chartLabels G Dr m₀ (ρ + L) ∪ defLabels G m₀ rD) hdom) (A e).H Y) V := by
  have hc1 := one_le_c1 d L
  have haent := aEnt_nonneg d L
  have hT : 0 < κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 := by linarith
  obtain ⟨-, hrate⟩ := labelRate_ge d L 0 (ρ + L) hd hT hκlarge
  obtain ⟨-, -, hdom, A, hA1, hA2, hA3⟩ := union_labelAct_eps hS G a ν β hβ Sb HB hκ hM hF hFan hΩ hDD
    hDr hm4 hd hL2 g ρ W hWloc hWr hWan hE hBW hp hA hG hU hg hsmall hmemAll hN fld hfld_meas hfld_bd
    hfld_loc hV hVS Dm rD hDB hDrow hDrange hκ'0 hκlarge hεpos hεs hεtot
  refine ⟨hdom, A, hA1, ?_⟩
  have hcont : ∀ y, ∀ e ∈ V, ContinuousOn ((A e).H y) Q := by
    intro y e he
    have h1 : (A e).H y = fun Φ => chartTerm G a ν β g W F m₀ (ρ + L) y.1 e (fld Φ) +
        defTerm G Dm m₀ rD y.1 (fld Φ) := funext fun Φ => hA1 e he y Φ
    rw [h1]
    exact ((chartTerm_continuous (G := G) (a := a) (ν := ν) (β := β) (g := g) (W := W) (F := F)
      (ρ := ρ) (hFan := hFan) (hWan := hWan) (hE := hE) (hU := hU) (hsmall := hsmall)
      (hmemAll := hmemAll) (hβ := hβ) (hκ := hκ) (hVS := hVS) (hfld_bd := hfld_bd) (fld := fld)
      (m₀ := m₀) (V := V) hfld_cont y.1 he).add
      (defTerm_continuous (G := G) (Dm := Dm) (fld := fld) (m₀ := m₀) (rD := rD) hfld_cont y.1)).continuousOn
  exact labelAct_Pst_analyticOnNhd μ hN hV hQ hQm hμQ A ⟨Y0, hY0⟩ hA2 hcont hκ'0 hεpos hrate hεs Y

end Union

end Balaban.LargeField.Base
