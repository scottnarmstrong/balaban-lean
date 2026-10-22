/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLabelCross
public import Balaban.LargeField.Base.BaseChartCross
public import Balaban.LargeField.Base.BaseChartLabelAct

/-!
# The activity of a deep label for a level set and for a local generating set

For a level set `Gp` and a generating set `Gl` of the first step, a label `Y` whose `8 L^{1+m₁}`-neighbourhood
lies in `Ω₁(Gl)` has the same chart activity `chartTerm` for the two systems, when the data agree near `Y`:
the pairs `(x, Cs)` with label `Y` correspond (`crossCubeMap`), and the coefficients agree
(`bgFunctional_coef_relabel_cross`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix

section Pairs

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ} {m₀ : ℕ}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱl} {Gp : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}

local notation "𝕋₁" => Balaban.Localization.CTorus d L N₁ m₁ 1

/-- **The cells of a pair with a deep label are deep.**  If `(x, Cs)` has label `Y` then the ball of radius
`9 L^{1+m₁}` about each base of `Cs` lies in `Y`, in particular the interaction cube of each cell. -/
theorem pair_ball_subset (hN : L ^ m₀ ∣ N₁) {x : 𝕋₁} {ρs : ℕ} {Cs : Finset ↥(coverOf Gl).cubeIdx}
    {Y : Set 𝕋₁} (hY : labelSet (coverOf Gl) m₀ x ρs Cs = Y) {i : ↥(coverOf Gl).cubeIdx} (hi : i ∈ Cs)
    {y : 𝕋₁} (hy : supDist (i : ℕ × 𝕋₁).2 y ≤ 9 * L ^ (0 + 1 + m₁)) : y ∈ Y := by
  rw [← hY]; exact ball_subset_labelSet hN hi hy

variable {a : ℕ → ℝ} {ν β : ℝ}

open Classical in
/-- **The coefficient of a pair with a deep label agrees on the two systems.** -/
theorem chartCoef_pair_cross (hG' : IsLevel Gp 1) (hm₁ : 2 ≤ m₁) (hN : L ^ m₀ ∣ N₁)
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L 1 ϱl a ν) (HBp : BgHyp d L 1 ϱ a ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {Fl : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    {Fp : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hFl : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          Fl (s, (D.Ψ, D.h)) = (φ, α))
    (hFp : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          Fp (s, (D.Ψ, D.h)) = (φ, α))
    {D : BgData Gl N} {D' : BgData Gp N}
    (hDu : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDu' : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D')
    (gl ψl : Gl.Ω 1 × Fin N → ℂ) (gp ψp : Gp.Ω 1 × Fin N → ℂ)
    (Wl : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ)
    (Wp : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (ρs : ℕ) (Y : Set 𝕋₁)
    (hdepth : ∀ z : 𝕋₁, (∃ t ∈ Y, supDist z t ≤ 8 * L ^ (0 + 1 + m₁)) → z ∈ Gl.Ω (0 + 1))
    (hdat0 : ∀ z : 𝕋₁, (∃ t ∈ Y, supDist z t ≤ 4 * L ^ (0 + 1)) →
      D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    (hfl : ∀ x : Gl.Ω 1, AnalyticOnNhd ℂ
      (fun s => chartFe Gl a ν β gl ψl Wl x (Fl (s, (D.Ψ, D.h))))
      (polydisc (0 : Dec2.DecParams (coverOf Gl)) (fun _ => Real.exp κ)))
    (hreads : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (x : 𝕋₁) ∈ Y →
      ReadsSeedCross Gl Gp (seedBall (x : 𝕋₁) ρs) (chartFe Gl a ν β gl ψl Wl x)
        (chartFe Gp a ν β gp ψp Wp x'))
    (d0 : ↥(coverOf Gp).cubeIdx) (x : Gl.Ω 1) (Cs : Finset ↥(coverOf Gl).cubeIdx)
    (hlab : labelSet (coverOf Gl) m₀ (x : 𝕋₁) ρs Cs = Y) :
    coef (fun s' => chartFe Gp a ν β gp ψp Wp ⟨(x : 𝕋₁), (hG' (x : 𝕋₁)).1⟩ (Fp (s', (D'.Ψ, D'.h))))
        (Cs.image (crossCubeMap Gl Gp d0)) =
      coef (fun s => chartFe Gl a ν β gl ψl Wl x (Fl (s, (D.Ψ, D.h)))) Cs := by
  classical
  set T : Finset 𝕋₁ := Finset.univ.filter (· ∈ Y) with hT
  set Yn : Finset 𝕋₁ := Finset.univ.filter
    (fun y => ∃ t ∈ T, supDist y t ≤ 2 * L ^ (0 + 1)) with hYn
  have hTmem : ∀ y, y ∈ T ↔ y ∈ Y := by intro y; simp [hT]
  have hYnmem : ∀ y, y ∈ Yn ↔ ∃ t ∈ T, supDist y t ≤ 2 * L ^ (0 + 1) := by intro y; simp [hYn]
  have hxY : (x : 𝕋₁) ∈ Y := by
    rw [← hlab]; exact seed_subset_labelSet hN (by rw [supDist_self]; exact Nat.zero_le _)
  have hCT : ∀ i ∈ Cs, ∀ y ∈ intBox (i : ℕ × 𝕋₁), y ∈ T := by
    intro i hi y hy
    rw [hTmem]
    have hi1 : (i : ℕ × 𝕋₁).1 ≤ 0 + 1 := ((mem_cubeIdx Gl).1 i.2).1.2
    have h3 := supDist_intBox_le' hy
    have h4 := crossPow_le (L := L) (m₁ := m₁) (k := 0) hi1
    refine pair_ball_subset hN hlab hi ?_
    rw [supDist_comm]
    omega
  refine bgFunctional_coef_relabel_cross Gl Gp hG' hm₁ hS Sl Sp HBl HBp hκ hM hFl hFp hDu hDu'
    (Fel := chartFe Gl a ν β gl ψl Wl x) (Fep := chartFe Gp a ν β gp ψp Wp ⟨(x : 𝕋₁), (hG' (x : 𝕋₁)).1⟩)
    (hfl x) Cs d0 (T := T) (Y := Yn) (seed := seedBall (x : 𝕋₁) ρs) ?_ ?_ ?_ ?_ hCT ?_ ?_
    (hreads x _ rfl hxY)
  · intro t ht
    exact (hYnmem t).2 ⟨t, ht, by rw [supDist_self]; exact Nat.zero_le _⟩
  · intro z hz
    obtain ⟨t, ht, hd⟩ := hz
    exact hdepth z ⟨t, (hTmem t).1 ht, hd⟩
  · intro y hy
    exact (hYnmem y).1 hy
  · intro u hu y hy
    exact (hYnmem y).2 ⟨u, hu, by rw [supDist_comm]; omega⟩
  · intro y hy _ z hz
    obtain ⟨t, ht, hd⟩ := (hYnmem y).1 hy
    have h1 := supDist_le_of_mem_approxDep hz
    have h2 := supDist_triangle z y t
    rw [supDist_comm z y] at h2
    refine hdat0 z ⟨t, (hTmem t).1 ht, ?_⟩
    omega
  · intro z hz
    rw [hTmem, ← hlab]
    exact seed_subset_labelSet hN (mem_seedBall.1 hz)


open Classical in
/-- **The chart activity of a deep label agrees on a level set and on a local generating set.**  If the
`8 L^{1+m₁}`-neighbourhood of the label `Y` lies in the top layer of `Gl`, the two systems have the same
data within `4 L` of `Y`, and the chart exponents of the two systems read the same seeds, the activity
`chartTerm` of the label `Y` is the same: the pairs `(x, Cs)` of label `Y` correspond through `crossCubeMap`. -/
theorem chartTerm_cross (hG' : IsLevel Gp 1) (hm₁ : 2 ≤ m₁) (hN : L ^ m₀ ∣ N₁)
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L 1 ϱl a ν) (HBp : BgHyp d L 1 ϱ a ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {Fl : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    {Fp : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) 1 N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hFl : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          Fl (s, (D.Ψ, D.h)) = (φ, α))
    (hFp : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          Fp (s, (D.Ψ, D.h)) = (φ, α))
    {D : BgData Gl N} {D' : BgData Gp N}
    (hDu : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDu' : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D')
    (gl ψl : Gl.Ω 1 × Fin N → ℂ) (gp ψp : Gp.Ω 1 × Fin N → ℂ)
    (Wl : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ)
    (Wp : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (ρs : ℕ) (Y : Set 𝕋₁)
    (hdepth : ∀ z : 𝕋₁, (∃ t ∈ Y, supDist z t ≤ 8 * L ^ (0 + 1 + m₁)) → z ∈ Gl.Ω (0 + 1))
    (hdat0 : ∀ z : 𝕋₁, (∃ t ∈ Y, supDist z t ≤ 4 * L ^ (0 + 1)) →
      D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    (hfl : ∀ x : Gl.Ω 1, AnalyticOnNhd ℂ
      (fun s => chartFe Gl a ν β gl ψl Wl x (Fl (s, (D.Ψ, D.h))))
      (polydisc (0 : Dec2.DecParams (coverOf Gl)) (fun _ => Real.exp κ)))
    (hreads : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋₁) = x' → (x : 𝕋₁) ∈ Y →
      ReadsSeedCross Gl Gp (seedBall (x : 𝕋₁) ρs) (chartFe Gl a ν β gl ψl Wl x)
        (chartFe Gp a ν β gp ψp Wp x'))
    (d0 : ↥(coverOf Gp).cubeIdx) (d0l : ↥(coverOf Gl).cubeIdx) :
    chartTerm Gp a ν β gp Wp Fp m₀ ρs Y (D'.Ψ, D'.h) ψp =
      chartTerm Gl a ν β gl Wl Fl m₀ ρs Y (D.Ψ, D.h) ψl := by
  classical
  have hΩp : ∀ z, z ∈ Gp.Ω 1 := fun z => (hG' z).1
  have hself : ∀ z : 𝕋₁, supDist z z ≤ 0 := fun z => by rw [supDist_self]
  -- the base of a cell of a pair with label `Y` lies in `Y`, hence in the top layer of `Gl`
  have hbaseY : ∀ {C : DecCover d L N₁ m₁ 1} {x : 𝕋₁} {Cs : Finset ↥C.cubeIdx},
      labelSet C m₀ x ρs Cs = Y → ∀ i ∈ Cs, (i : ℕ × 𝕋₁).2 ∈ Y := by
    intro C x Cs hlab i hi
    have := ball_subset_labelSet (m₀ := m₀) (x := x) (ρs := ρs) hN hi (y := (i : ℕ × 𝕋₁).2)
      (by rw [supDist_self]; exact Nat.zero_le _)
    rwa [hlab] at this
  have hdeep : ∀ z ∈ Y, z ∈ Gl.Ω (0 + 1) := fun z hz =>
    hdepth z ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
  have hmemL : ∀ (x : Gl.Ω 1) (Cs : Finset ↥(coverOf Gl).cubeIdx), labelSet (coverOf Gl) m₀ (x : 𝕋₁) ρs Cs = Y →
      ∀ i ∈ Cs, (i : ℕ × 𝕋₁) ∈ (coverOf Gp).cubeIdx := fun x Cs hlab i hi =>
    (level_mem_cubeIdx_iff_of_mem_top hG' (hdeep _ (hbaseY hlab i hi))).2 i.2
  have hmemP : ∀ (x : Gp.Ω 1) (Cs : Finset ↥(coverOf Gp).cubeIdx), labelSet (coverOf Gp) m₀ (x : 𝕋₁) ρs Cs = Y →
      ∀ i ∈ Cs, (i : ℕ × 𝕋₁) ∈ (coverOf Gl).cubeIdx := fun x Cs hlab i hi =>
    (level_mem_cubeIdx_iff_of_mem_top hG' (hdeep _ (hbaseY hlab i hi))).1 i.2
  have hxP : ∀ (x : Gp.Ω 1) (Cs : Finset ↥(coverOf Gp).cubeIdx), labelSet (coverOf Gp) m₀ (x : 𝕋₁) ρs Cs = Y →
      (x : 𝕋₁) ∈ Gl.Ω 1 := fun x Cs hlab =>
    hdeep _ (by rw [← hlab]; exact seed_subset_labelSet hN (by rw [supDist_self]; exact Nat.zero_le _))
  unfold chartTerm
  rw [Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij'
    (fun a _ => (⟨⟨(a.1 : 𝕋₁), hΩp a.1⟩, a.2.image (crossCubeMap Gl Gp d0)⟩ :
      Σ _ : Gp.Ω 1, Finset ↥(coverOf Gp).cubeIdx))
    (fun b hb => (⟨⟨(b.1 : 𝕋₁), hxP b.1 b.2 (Finset.mem_filter.1 (Finset.mem_sigma.1 hb).2).2⟩,
      b.2.image (crossCubeMap Gp Gl d0l)⟩ : Σ _ : Gl.Ω 1, Finset ↥(coverOf Gl).cubeIdx))
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have hlab := (Finset.mem_filter.1 (Finset.mem_sigma.1 ha).2).2
    refine Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    show labelSet (coverOf Gp) m₀ (a.1 : 𝕋₁) ρs (a.2.image (crossCubeMap Gl Gp d0)) = Y
    rw [labelSet_cubeMap d0 _ _ _ (hmemL a.1 a.2 hlab), hlab]
  · intro b hb
    have hlab := (Finset.mem_filter.1 (Finset.mem_sigma.1 hb).2).2
    refine Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    show labelSet (coverOf Gl) m₀ (b.1 : 𝕋₁) ρs (b.2.image (crossCubeMap Gp Gl d0l)) = Y
    rw [labelSet_cubeMap d0l _ _ _ (hmemP b.1 b.2 hlab), hlab]
  · intro a ha
    have hlab := (Finset.mem_filter.1 (Finset.mem_sigma.1 ha).2).2
    obtain ⟨x, Cs⟩ := a
    refine Sigma.ext rfl (heq_of_eq ?_)
    simp only []
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := Cs)]
    refine Finset.image_congr fun i hi => ?_
    exact crossCubeMap_cubeMap Gl Gp d0 d0l (hmemL x Cs hlab i hi)
  · intro b hb
    have hlab := (Finset.mem_filter.1 (Finset.mem_sigma.1 hb).2).2
    obtain ⟨x, Cs⟩ := b
    refine Sigma.ext rfl (heq_of_eq ?_)
    simp only []
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := Cs)]
    refine Finset.image_congr fun i hi => ?_
    exact crossCubeMap_cubeMap Gp Gl d0l d0 (hmemP x Cs hlab i hi)
  · intro a ha
    have hlab := (Finset.mem_filter.1 (Finset.mem_sigma.1 ha).2).2
    exact (chartCoef_pair_cross hG' hm₁ hN hS Sl Sp HBl HBp hκ hM hFl hFp hDu hDu' gl ψl gp ψp Wl Wp ρs Y
      hdepth hdat0 hfl hreads d0 a.1 a.2 hlab).symm


end Pairs

end Balaban.LargeField.Base
