/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRemainderClamp
public import Balaban.Fluctuation.ParamActivitySubspace

/-!
# The remainder marks as the marks of a parameter family

* `obsGrFam`: the marks `obsGrRawC` of the raw datum of a parameter `θ` of the physical parameter
  space, and `0` when the raw datum of `θ` is outside the set `A` on which the marks are
  controlled.  The marks do not depend on the source component of `θ`.
* The mark hypotheses of `paramMarkFamilyOn_of_marks` in their exact shapes: measurability and the
  bound for every parameter, analyticity and continuity on `physV`; block locality and parameter
  locality on `physV`.
* `gsumCoeff_congr_ae`: the remainder coefficients `gsumCoeff` are unchanged when the marks are
  replaced by marks that agree almost everywhere for the block product measure.
* `gsumCoeff_obsGr_eq_obsGrFam`: at a chart datum, the coefficients of the landed marks `obsGr`
  and of the family `obsGrFam` agree.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

/-! ### Almost-everywhere congruence of the coefficients -/

section Congr

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- The local term `G*(Y₀, S)` depends on the mark only through its class modulo null sets of the
block product measure. -/
theorem Gst_congr_ae {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ S : Finset 𝔅) {G G' : (∀ b, Ωb b) → ℂ}
    (hG : ∀ᵐ Φ ∂(Measure.pi μ), G Φ = G' Φ) :
    Gst μ Lab H S₀ G S = Gst μ Lab H S₀ G' S := by
  unfold Gst
  have hK : marksK μ Subtype.val (presum Lab H) (gMark S₀ G) =
      marksK μ Subtype.val (presum Lab H) (gMark S₀ G') := by
    funext Z l
    unfold marksK mayerK
    refine integral_congr_ae ?_
    filter_upwards [hG] with Φ h
    have hH : ∀ t, Hlam (presum Lab H) (gMark S₀ G) l t Φ =
        Hlam (presum Lab H) (gMark S₀ G') l t Φ := by
      intro t
      simp [Hlam, gMark, h]
    unfold mayerAct
    simp only [hH]
  rw [hK]

/-- **Almost-everywhere congruence of `gsumCoeff` in the marks**: with the same activities, the
coefficient is unchanged when each mark `Gᵢ(s)`, `s ∈ [0,1]`, is replaced by a mark that is equal
to it for almost every block configuration (for the block product measure). -/
theorem gsumCoeff_congr_ae {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G G' : ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset 𝔅)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      ∀ᵐ Φ ∂(Measure.pi μ), G i (s : ℂ) Φ = G' i (s : ℂ) Φ) :
    gsumCoeff μ Lab A y0 G T = gsumCoeff μ Lab A y0 G' T := by
  unfold gsumCoeff
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold Gsum
  exact Finset.sum_congr rfl fun i _ => Gst_congr_ae μ Lab _ _ T (hG s hs i)

end Congr

/-! ### The family of remainder marks over the physical parameter space -/

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
  (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
  (A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N))

open Classical in
/-- **The remainder marks as the marks of a parameter family**: at the parameter `θ`, the marks
`obsGrRawC` of the raw datum of `θ` when it lies in `A`, and `0` otherwise.  They do not depend on
the source component of `θ`. -/
noncomputable def obsGrFam (θ : physParam N S) :
    RemIdx 𝒴 → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ :=
  if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A then
    obsGrRawC S m₀ hp Ev 𝒴 (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
  else fun _ _ _ => 0

variable {S m₀ hp Ev 𝒴 A}

theorem obsGrFam_of_mem {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A) :
    obsGrFam S m₀ hp Ev 𝒴 A θ = obsGrRawC S m₀ hp Ev 𝒴 (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
  by simp [obsGrFam, hθ]

theorem obsGrFam_of_not_mem {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∉ A) :
    obsGrFam S m₀ hp Ev 𝒴 A θ = fun _ _ _ => 0 :=
  by simp [obsGrFam, hθ]

/-- The marks do not depend on the source component of the parameter. -/
theorem obsGrFam_eq_of_fst_eq {θ θ' : physParam N S} (h : θ.1 = θ'.1) :
    obsGrFam S m₀ hp Ev 𝒴 A θ = obsGrFam S m₀ hp Ev 𝒴 A θ' := by
  rw [obsGrFam, obsGrFam, h]

/-- The raw datum of a parameter of `physV` lies in the chart `XiCRaw`. -/
theorem physV_fst_mem_xiCRaw {a₁ ν eps : ℝ} {θ : physParam N S} (hθ : θ ∈ physV S a₁ ν eps) :
    (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps :=
  hθ.1

variable {cψ : ℝ}

/-- **Measurability** in the configuration, for every parameter. -/
theorem measurable_obsGrFam (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (θ : physParam N S) (idx : RemIdx 𝒴) (u : ℂ) :
    Measurable (obsGrFam S m₀ hp Ev 𝒴 A θ idx u) := by
  by_cases hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A
  · rw [obsGrFam_of_mem hθ]; exact measurable_obsGrRawC hcψ hq ha hθ idx u
  · rw [obsGrFam_of_not_mem hθ]; exact measurable_const

/-- **The bound** `8 C0 q² e^{-κG 𝗱(y_idx)}`, for every parameter, index, `u` and configuration. -/
theorem norm_obsGrFam_le (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {C0 κd : ℝ} (hC0 : 0 < C0)
    (hb : ∀ Y ∈ 𝒴, ∀ x ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ‖Ev Y x‖ ≤ C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y))
    {Lb : Type*} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb)
    (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb)
    (hdl : ∀ Y, Lab.dl (lab Y) = treeLenCovOne m₀ (k + 1) Y.1) {κG : ℝ} (hκG : κG ≤ κd)
    (θ : physParam N S) (idx : RemIdx 𝒴) (u : ℂ) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖obsGrFam S m₀ hp Ev 𝒴 A θ idx u Φ‖ ≤
      8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κG * Lab.dl (obsRemLab 𝒴 lab y₀ idx)) := by
  by_cases hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A
  · rw [obsGrFam_of_mem hθ]; exact norm_obsGrRawC_le hcψ hq ha hC0 hb Lab lab y₀ hdl hκG hθ idx u Φ
  · rw [obsGrFam_of_not_mem hθ]
    have hpc : 0 < S.p₁ / cψ := div_pos hp hcψ
    simp only [norm_zero]; positivity

/-- **Joint analyticity** in `(θ, u)` on `physV ×ˢ ball 0 (3/2)`, for every configuration. -/
theorem analyticOnNhd_obsGrFam {a₁ ν eps : ℝ} (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (hAV : XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ⊆ A)
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (idx : RemIdx 𝒴) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => obsGrFam S m₀ hp Ev 𝒴 A p.1 idx p.2 Φ)
      (physV S a₁ ν eps ×ˢ ball (0 : ℂ) (3 / 2)) := by
  have hlin : AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
      (((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.2) :
        RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ)) Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        ((physIncl N S p.1).1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) Set.univ :=
      ((ContinuousLinearMap.fst ℂ _ _).comp ((physIncl N S).comp
        (ContinuousLinearMap.fst ℂ _ ℂ))).analyticOnNhd _
    exact fun x hx => (h1 x hx).prod analyticAt_snd
  have hcomp := (analyticOnNhd_obsGrRawC (S := S) (m₀ := m₀) (hp := hp) (Ev := Ev)
    (𝒴 := 𝒴) hcψ hq ha idx Φ).comp
    (hlin.mono (Set.subset_univ (physV S a₁ ν eps ×ˢ ball (0 : ℂ) (3 / 2))))
    (fun p hp' => ⟨hAV hp'.1.1, hp'.2⟩)
  refine hcomp.congr ((isOpen_physV S a₁ ν eps H).prod isOpen_ball) fun p hp' => ?_
  simp only [Function.comp]
  rw [obsGrFam_of_mem (hAV hp'.1.1)]

/-- **Continuity in the configuration** on all block configurations, for `θ ∈ physV`. -/
theorem continuous_obsGrFam {a₁ ν eps : ℝ}
    (hAV : XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ⊆ A)
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {θ : physParam N S} (hθ : θ ∈ physV S a₁ ν eps) (idx : RemIdx 𝒴) (u : ℂ) :
    Continuous (obsGrFam S m₀ hp Ev 𝒴 A θ idx u) := by
  have hm := hAV hθ.1
  rw [obsGrFam_of_mem hm]
  exact continuous_obsGrRawC hcψ hq ha hm idx u

/-- **Block locality** on `physV`: the mark of the domain `Y` depends on the configuration only
through the blocks of the cube label of `Y`; the dummy index gives the zero mark. -/
theorem depOn_obsGrFam {a₁ ν eps : ℝ}
    (hAV : XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ⊆ A)
    (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    {θ : physParam N S} (hθ : θ ∈ physV S a₁ ν eps) (Y : {Y // Y ∈ 𝒴}) (u : ℂ) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ Y.1) (obsGrFam S m₀ hp Ev 𝒴 A θ (some Y) u) := by
  have hm := hAV hθ.1
  rw [obsGrFam_of_mem hm]
  exact depOn_obsGrRawC hN hcψ hq hdj hd hm Y u

/-- **Parameter locality** on `physV`: two parameters of `physV` whose raw data agree on the
thickening of `Y` give the same mark of `Y`. -/
theorem obsGrFam_local {a₁ ν eps : ℝ}
    (hAV : XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ⊆ A)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    {θ θ' : physParam N S} (hθ : θ ∈ physV S a₁ ν eps) (hθ' : θ' ∈ physV S a₁ ν eps)
    (Y : {Y // Y ∈ 𝒴})
    (hag : agreeOn (thickSet S.G' Y.1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ'.1)
    (u : ℂ) :
    obsGrFam S m₀ hp Ev 𝒴 A θ (some Y) u = obsGrFam S m₀ hp Ev 𝒴 A θ' (some Y) u := by
  rw [obsGrFam_of_mem (hAV hθ.1), obsGrFam_of_mem (hAV hθ'.1)]
  funext Φ
  exact obsGrRawC_local hd hcψ hq (hAV hθ.1) (hAV hθ'.1) Y hag u Φ

/-- **At a chart datum** `D` (a parameter `θ` with raw datum `rawOf D ∈ A`), the family agrees with
the landed marks `obsGr` almost everywhere. -/
theorem ae_obsGrFam_eq_obsGr (D : BgData S.G' N) {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) (hD : rawOf D ∈ A) :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), ∀ (idx : RemIdx 𝒴) (u : ℂ),
      obsGrFam S m₀ hp Ev 𝒴 A θ idx u Φ = obsGr S m₀ hp Ev D 𝒴 idx u Φ := by
  have hm : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A := hθ ▸ hD
  rw [obsGrFam_of_mem hm, hθ]
  exact ae_obsGrRawC_rawOf_eq_obsGr D

/-- **The coefficients from the landed marks equal those from the family**, at a chart datum:
for any activities, labels and indices, `gsumCoeff` computed with `obsGr S m₀ hp Ev D 𝒴` equals
`gsumCoeff` computed with `obsGrFam` at a parameter `θ` with raw datum `rawOf D`. -/
theorem gsumCoeff_obsGr_eq_obsGrFam {Lb : Type*} [Fintype Lb] {m₀ : ℕ}
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb}
    {εH κH κ0 Kc : ℝ} (Act : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (y0 : RemIdx 𝒴 → Lb)
    (D : BgData S.G' N) {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) (hD : rawOf D ∈ A)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    gsumCoeff (S.blockSplit m₀ hp).μ Lab Act y0 (obsGr S m₀ hp Ev D 𝒴) T =
      gsumCoeff (S.blockSplit m₀ hp).μ Lab Act y0 (obsGrFam S m₀ hp Ev 𝒴 A θ) T := by
  refine gsumCoeff_congr_ae _ Act y0 _ _ T fun s _ i => ?_
  filter_upwards [ae_obsGrFam_eq_obsGr (hp := hp) D hθ hD] with Φ h
  exact (h i (s : ℂ)).symm

end Family

end Balaban.Fluctuation
