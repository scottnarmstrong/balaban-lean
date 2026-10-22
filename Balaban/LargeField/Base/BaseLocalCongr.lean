/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLocalActivity

/-!
# The chart activity of a deep label is local in the data

For a generating set `G` of the first step and a label `Y` inside a deep set `R`: two data of the union
domain that agree (field and multiplier) within `3 L^{1+m₁} + 5 L` of `Y` give the same activity
`chartTerm` of the label (`chartTerm_data_congr`), by `bgFunctional_coef_data_congr_deep` for each pair
`(x, Cs)` of label `Y`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Congr

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The region read by the coefficient of a family: the `L^{k+1}`-neighbourhood of the seed hull of the
indicator vector of the rooted component is within `3 L^{1+m₁} + 3 L` of the seed or of the bases of the cells. -/
theorem hdat_region (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {Dr : ℕ}
    (Cs : Finset ↥(coverOf G).cubeIdx)
    (seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hseedY : ∀ z ∈ seed, z ∈ Y)
    (hbaseY : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2 ∈ Y)
    {y : Balaban.Localization.CTorus d L N₁ m₁ 1}
    (hy : y ∈ nbhdSup (L ^ (0 + 1)) (seedHull (coverOf G) Dr (Dec2.extS _
      (indVec G (rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs))) seed)) :
    ∃ t ∈ Y, supDist t y ≤ 3 * L ^ (0 + 1 + m₁) + 3 * L ^ (0 + 1) := by
  classical
  obtain ⟨h, hh, hhy⟩ := mem_nbhdSup.1 hy
  have hsupp : indVec G (rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs) ∈
      supportedOn (rootComp (cellPatch (coverOf G) Dr) (seed : Set _) Cs) := by
    intro i hi
    simp [indVec, hi]
  rcases seedHull_near (fun q hq => ((mem_cubeIdx G).1 hq).1.2) hsupp hh with ⟨z, hz, hzh⟩ | ⟨i, hi, hih⟩
  · refine ⟨z, hseedY z hz, ?_⟩
    have := supDist_triangle z h y
    have hP : L ^ (0 + 1) ≤ 3 * L ^ (0 + 1 + m₁) + 3 * L ^ (0 + 1) := by omega
    omega
  · refine ⟨(i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2,
      hbaseY i (rootComp_subset _ _ _ hi), ?_⟩
    have := supDist_triangle (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2 h y
    omega

open Classical in
/-- **The chart activity of a deep label is local in the data.**  Let `Y ⊆ R`, with the `8 L^{1+m₁}`-neighbourhood
of `R` in `Ω₁(G)`.  Two data of the union domain that agree (field and multiplier) within
`3 L^{1+m₁} + 5 L` of `Y` give the same activity `chartTerm` of the label `Y`. -/
theorem chartTerm_data_congr {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
    (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {Dd Dd' : BgData G N} (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd)
    (hDu' : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd')
    {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr) (g ψ : G.Ω 1 × Fin N → ℂ) (ρ : ℕ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hWloc : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r)
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (R : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hRdeep : ∀ w : Balaban.Localization.CTorus d L N₁ m₁ 1,
      (∃ t ∈ R, supDist w t ≤ 8 * L ^ (0 + 1 + m₁)) → w ∈ G.Ω 1)
    (hρ : ρ + 4 * L ≤ 8 * L ^ (0 + 1 + m₁))
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (hYR : Y ⊆ R)
    (hagree : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ 1,
      (∃ t ∈ Y, supDist t z ≤ 3 * L ^ (0 + 1 + m₁) + 5 * L ^ (0 + 1)) →
        Dd.Ψ z = Dd'.Ψ z ∧ Dd.h z = Dd'.h z) :
    chartTerm G a ν β g W F m₀ (ρ + L) Y (Dd.Ψ, Dd.h) ψ =
      chartTerm G a ν β g W F m₀ (ρ + L) Y (Dd'.Ψ, Dd'.h) ψ := by
  unfold chartTerm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun Cs hCs => ?_
  have hlab := (Finset.mem_filter.1 hCs).2
  have hdeep := hdeep_of_label (G := G) (Dr := Dr) (ρ := ρ) (hN := hN) (R := R) (hRdeep := hRdeep) (hρ := hρ) x Cs Y
    hYR hlab
  refine bgFunctional_coef_data_congr_deep G a ν hS Sb HB hκ hM hF hDu hDu' hDD
    (chartSite_readsSeed G a ν β g ψ x ρ W hWloc) Cs hdeep ?_
  intro y hy _ z hz
  have hseedY : ∀ z' ∈ seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L), z' ∈ Y := fun z' hz' => by
    rw [← hlab]; exact seed_subset_labelSet hN (mem_seedBall.1 hz')
  have hbaseY : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2 ∈ Y := fun i hi => by
    have := ball_subset_labelSet (m₀ := m₀) (x := (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
      (ρs := ρ + L) hN hi (y := (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1).2)
      (by rw [supDist_self]; exact Nat.zero_le _)
    rwa [hlab] at this
  obtain ⟨t, ht, hty⟩ := hdat_region G Cs _ Y hseedY hbaseY hy
  refine hagree z ⟨t, ht, ?_⟩
  have h1 := supDist_le_of_mem_approxDep hz
  have h2 := supDist_triangle t y z
  simp only [zero_add, pow_one] at *
  omega

open Classical in
/-- **The masked activity of a label is local in the data.** -/
theorem maskedTerm_data_congr {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
    (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
    {Dd Dd' : BgData G N} (hDu : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd)
    (hDu' : InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν Dd')
    {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr) (g ψ : G.Ω 1 × Fin N → ℂ) (ρ : ℕ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hWloc : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r)
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (R : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hRdeep : ∀ w : Balaban.Localization.CTorus d L N₁ m₁ 1,
      (∃ t ∈ R, supDist w t ≤ 8 * L ^ (0 + 1 + m₁)) → w ∈ G.Ω 1)
    (hρ : ρ + 4 * L ≤ 8 * L ^ (0 + 1 + m₁))
    (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) (rD : ℕ)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (hagree : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ 1,
      (∃ t ∈ Y, supDist t z ≤ 3 * L ^ (0 + 1 + m₁) + 5 * L ^ (0 + 1)) →
        Dd.Ψ z = Dd'.Ψ z ∧ Dd.h z = Dd'.h z) :
    maskedTerm G a ν β g W F Dm m₀ (ρ + L) rD R Y (Dd.Ψ, Dd.h) ψ =
      maskedTerm G a ν β g W F Dm m₀ (ρ + L) rD R Y (Dd'.Ψ, Dd'.h) ψ := by
  unfold maskedTerm
  by_cases hYR : Y ⊆ R
  · simp only [hYR, ↓reduceIte]
    rw [chartTerm_data_congr hS G a ν β Sb HB hκ hM hF hDu hDu' hDD g ψ ρ W hWloc hN R hRdeep hρ Y hYR hagree]
  · simp only [hYR, ↓reduceIte]

end Congr

section PstCongr

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

variable {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
  (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
  (Sb : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (HB : BgHyp d L 1 ϱ a ν) {κ : ℝ}
  (hκ : 1 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  {F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
    (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  (hF : ∀ (s : Dec2.DecParams (coverOf G)) (D : BgData G N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC G (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : G.Ω 1 × Fin N → ℂ)
        (α : G.Ω 1 → ℂ), Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α →
          F (s, (D.Ψ, D.h)) = (φ, α))
  {Dr : ℕ} (hDD : L ^ 1 + 2 * L ^ 1 ≤ Dr) (ρ : ℕ)
  (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
  (hWloc : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r)
  {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)] (fld : (∀ b, Ωb b) → G.Ω 1 × Fin N → ℂ)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (dat : E →L[ℂ] RawData d L (N₁ * L ^ m₁) 1 N) (sr : E →L[ℂ] (G.Ω 1 × Fin N → ℂ))
  {V : Set E} (hVS : ∀ p ∈ V, dat p ∈ dataSet G N BG κ ν)
  (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) (rD : ℕ)
  (R : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
  (hRdeep : ∀ w : Balaban.Localization.CTorus d L N₁ m₁ 1,
    (∃ t ∈ R, supDist w t ≤ 8 * L ^ (0 + 1 + m₁)) → w ∈ G.Ω 1)
  (hρ : ρ + 4 * L ≤ 8 * L ^ (0 + 1 + m₁))

open Classical in
include hS Sb HB hκ hM hF hDD hWloc hN hVS hRdeep hρ in
/-- **Locality of the cluster-expansion coefficient of the masked activities in the data** (the clause (A3)
of the local family).  If the labels of the family with blocks in `T` lie in `R` and the data of two
parameters with the same source agree within `3 L^{1+m₁} + 5 L` of the sites of `T`, then
`P(T)` is the same. -/
theorem masked_Pst_data_congr (μ : ∀ b, MeasureTheory.Measure (Ωb b))
    [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    (𝒴 : Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1)))
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ 1 Y) {εH κH κ0 Kc' : ℝ}
    (A : E → LabelAct (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Ωb εH κH κ0 Kc')
    (hA1 : ∀ q ∈ V, ∀ (y : {Y // Y ∈ 𝒴}) Φ,
      (A q).H y Φ = maskedTerm G a ν β (sr q) W F Dm m₀ (ρ + L) rD R y.1 (dat q) (fld Φ))
    {q q' : E} (hq : q ∈ V) (hq' : q' ∈ V) (hsr : sr q = sr q')
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ))
    (hlabR : ∀ y : {Y // Y ∈ 𝒴}, blocksOf m₀ 1 Set.univ y.1 ⊆ T → y.1 ⊆ R)
    (hagree : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ 1,
      (∃ t ∈ sitesOf T, supDist t z ≤ 3 * L ^ (0 + 1 + m₁) + 5 * L ^ (0 + 1)) →
        (dat q).1 z = (dat q').1 z ∧ (dat q).2 z = (dat q').2 z) :
    Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) (A q).H T =
      Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) (A q').H T := by
  obtain ⟨Dd, hDu, hDd⟩ := hVS q hq
  obtain ⟨Dd', hDu', hDd'⟩ := hVS q' hq'
  refine Pst_congr μ μ (A q) (A q').H T (fun _ _ => rfl) (fun y hy => ?_)
  funext Φ
  rw [hA1 q hq y Φ, hA1 q' hq' y Φ, hsr, hDd, hDd']
  have hYT : y.1 ⊆ sitesOf T := by
    have hs := sitesOf_blocksOf hN (le_refl 1) isPiUnion_univ_K
      ((thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom).isDj y).2.1
    intro z hz
    have hz' : z ∈ sitesOf (blocksOf m₀ 1 Set.univ y.1) := by
      rw [show (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom).ysite y = y.1 from rfl] at hs
      rw [hs]; exact ⟨hz, Set.mem_univ _⟩
    exact sitesOf_mono hy hz'
  have hlabR' := hlabR y hy
  exact maskedTerm_data_congr hS G a ν β Sb HB hκ hM hF hDu hDu' hDD _ _ ρ W hWloc hN R hRdeep hρ Dm rD y.1
    (fun z ⟨t, ht, hd⟩ => by
      have := hagree z ⟨t, hYT ht, hd⟩
      rw [hDd, hDd'] at this
      exact this)

end PstCongr

end Balaban.LargeField.Base
