/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRemainderParam
public import Balaban.Fluctuation.ParamActivityPhysical

/-!
# The remainder marks with the continuous clamp

`obsGrRawC` is `obsGrRaw` with the clipped hat field `obsHat` replaced by the continuous clamp
`StepSetting.hatOf` at radius `p₁`.  Since the clamp is continuous on all block configurations,
the marks are continuous on the whole carrier (not only on `{‖Φ b w‖ < p₁}`); the other fields are
those of `obsGrRaw`.  The two families agree for almost every block configuration.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
  (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))

/-- **The remainder marks with the continuous clamp**: `obsGrRaw` with the clipped hat field
replaced by `S.hatOf m₀ S.p₁ hp Φ`, the radial projection onto the disk of radius `p₁`. -/
noncomputable def obsGrRawC (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    RemIdx 𝒴 → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ
  | none, _, _ => 0
  | some Y, u, Φ => remExt (fun ζ : ℂ => Ev Y.1 (r, ζ • S.hatOf m₀ S.p₁ hp Φ)) u

variable {S m₀ hp Ev 𝒴}
variable {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {cψ : ℝ}

theorem norm_hatOf_p₁_le (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (q : S.U × Fin N) :
    ‖S.hatOf m₀ S.p₁ hp Φ q‖ ≤ S.p₁ := S.hatOf_mem m₀ hp hp Φ q

/-- Joint analyticity in the datum and the ray variable, for every configuration. -/
theorem analyticOnNhd_obsGrRawC (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (idx : RemIdx 𝒴) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    AnalyticOnNhd ℂ (fun x : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ =>
      obsGrRawC S m₀ hp Ev 𝒴 x.1 idx x.2 Φ) (A ×ˢ ball (0 : ℂ) (3 / 2)) := by
  cases idx with
  | none => exact analyticOnNhd_const
  | some Y =>
    exact analyticOnNhd_remExt_ray_param hcψ hp hq (ha Y.1 Y.2) (norm_hatOf_p₁_le Φ)

/-- The bound `8 C0 q² e^{-κG 𝗱(y_idx)}`, for `r ∈ A`, all `u` and all `Φ`. -/
theorem norm_obsGrRawC_le (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {C0 κd : ℝ} (hC0 : 0 < C0)
    (hb : ∀ Y ∈ 𝒴, ∀ x ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ‖Ev Y x‖ ≤ C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y))
    {Lb : Type*} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb)
    (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb)
    (hdl : ∀ Y, Lab.dl (lab Y) = treeLenCovOne m₀ (k + 1) Y.1) {κG : ℝ} (hκG : κG ≤ κd)
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (idx : RemIdx 𝒴) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖obsGrRawC S m₀ hp Ev 𝒴 r idx u Φ‖ ≤
      8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κG * Lab.dl (obsRemLab 𝒴 lab y₀ idx)) := by
  have hpc : 0 < S.p₁ / cψ := div_pos hp hcψ
  have hc0 : 0 < 8 * C0 * (S.p₁ / cψ) ^ 2 := by positivity
  cases idx with
  | none => simp only [obsGrRawC, norm_zero]; positivity
  | some Y =>
    simp only [obsGrRawC, obsRemLab]
    have htl : 0 ≤ treeLenCovOne m₀ (k + 1) Y.1 := by rw [← hdl Y]; exact Lab.dl_nonneg _
    refine (norm_remExt_ray_le hcψ hp hq hr (ha Y.1 Y.2) (hb Y.1 Y.2) (norm_hatOf_p₁_le Φ)
      u).trans ?_
    rw [hdl Y, show 8 * (C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y.1)) * (S.p₁ / cψ) ^ 2 =
      8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y.1) by ring]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0.le
    nlinarith [htl]

/-- **Continuity in the configuration** on the whole space of block configurations, for `r ∈ A`. -/
theorem continuous_obsGrRawC (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (idx : RemIdx 𝒴) (u : ℂ) :
    Continuous (obsGrRawC S m₀ hp Ev 𝒴 r idx u) := by
  cases idx with
  | none => exact continuous_const
  | some Y =>
    by_cases hu : ‖u‖ < 3 / 2
    · have hc := continuousOn_ray_rem hcψ hp hq hr (ha Y.1 Y.2) hu
      exact hc.comp_continuous (S.continuous_hatOf m₀ S.p₁ hp) (fun Φ p => norm_hatOf_p₁_le Φ p)
    · have : obsGrRawC S m₀ hp Ev 𝒴 r (some Y) u = fun _ => 0 := by
        funext Φ; exact remExt_eq_zero_of_le _ (not_lt.1 hu)
      rw [this]; exact continuous_const

/-- **Measurability** in the block configuration, for `r ∈ A`. -/
theorem measurable_obsGrRawC (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (idx : RemIdx 𝒴) (u : ℂ) :
    Measurable (obsGrRawC S m₀ hp Ev 𝒴 r idx u) :=
  (continuous_obsGrRawC hcψ hq ha hr idx u).measurable

/-- **Block locality**: for `r ∈ A`, the mark of the domain `Y` depends on `Φ` only through the
blocks of the cube label of `Y`. -/
theorem depOn_obsGrRawC (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (Y : {Y // Y ∈ 𝒴}) (u : ℂ) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ Y.1) (obsGrRawC S m₀ hp Ev 𝒴 r (some Y) u) := by
  intro Φ Φ' h
  refine remExt_ray_congr hcψ hp hq (fun ζ hζ => ?_) u
  refine hd Y.1 Y.2 (r, ζ • S.hatOf m₀ S.p₁ hp Φ)
    ⟨hr, smul_mem_ball_p hp (norm_hatOf_p₁_le Φ) (by simpa using hζ)⟩
    (r, ζ • S.hatOf m₀ S.p₁ hp Φ')
    ⟨hr, smul_mem_ball_p hp (norm_hatOf_p₁_le Φ') (by simpa using hζ)⟩
    ⟨agreeOn_refl _ _, fun y' hy' i => ?_⟩
  have hT := cellOf_mem_obsRowLabel S hN (hdj Y.1 Y.2) hy'
    (rfl : unitPt S.hG' y' = unitPt S.hG' y')
  have := h _ hT
  simp only [Pi.smul_apply, smul_eq_mul, StepSetting.hatOf]
  rw [this]

/-- **Parameter locality for any agreement relation** `Ag` on pairs (raw datum, hat variable): if
`Ev Y` takes equal values at `Ag`-related points of the ball and `(r, h)`, `(r', h)` are
`Ag`-related for every hat variable `h`, the marks of `Y` at `r` and `r'` are equal.
`obsGrRawC_local` (thickening) and `obsGrRawC_local_rawY` (exact) are its instances. -/
theorem obsGrRawC_local_rel
    (Ag : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → Prop)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        Ag Y u u' → Ev Y u = Ev Y u')
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    {r r' : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (hr' : r' ∈ A)
    (Y : {Y // Y ∈ 𝒴}) (hag : ∀ h, Ag Y.1 (r, h) (r', h)) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    obsGrRawC S m₀ hp Ev 𝒴 r (some Y) u Φ = obsGrRawC S m₀ hp Ev 𝒴 r' (some Y) u Φ := by
  have h4 := four_le_of hcψ hp hq
  simp only [obsGrRawC]
  have hloc : ∀ ζ : ℂ, ‖ζ‖ < cψ / S.p₁ →
      Ev Y.1 (r, ζ • S.hatOf m₀ S.p₁ hp Φ) = Ev Y.1 (r', ζ • S.hatOf m₀ S.p₁ hp Φ) :=
    fun ζ hζ =>
    hd Y.1 Y.2 (r, ζ • S.hatOf m₀ S.p₁ hp Φ)
      ⟨hr, smul_mem_ball_p hp (norm_hatOf_p₁_le Φ) hζ⟩ (r', ζ • S.hatOf m₀ S.p₁ hp Φ)
      ⟨hr', smul_mem_ball_p hp (norm_hatOf_p₁_le Φ) hζ⟩ (hag _)
  by_cases hu : ‖u‖ < 3 / 2
  · have hq' : ∀ v : ℂ, ‖v‖ < 3 / 2 →
        deriv (fun ζ : ℂ => Ev Y.1 (r, ζ • S.hatOf m₀ S.p₁ hp Φ)) v =
          deriv (fun ζ : ℂ => Ev Y.1 (r', ζ • S.hatOf m₀ S.p₁ hp Φ)) v := by
      intro v hv
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(isOpen_ball (x := (0 : ℂ)) (ε := cψ / S.p₁)).mem_nhds
        (show v ∈ ball (0 : ℂ) (cψ / S.p₁) by rw [mem_ball_zero_iff]; linarith)] with ζ hζ
      exact hloc ζ (by simpa using hζ)
    rw [remExt_eq_of_lt _ hu, remExt_eq_of_lt _ hu, hq' u hu, hq' 0 (by simp)]
  · rw [remExt_eq_zero_of_le _ (not_lt.1 hu), remExt_eq_zero_of_le _ (not_lt.1 hu)]


/-- **Parameter locality**: for `r, r' ∈ A` that agree on the thickening of `Y`, the marks of `Y`
are equal. -/
theorem obsGrRawC_local
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    {r r' : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (hr' : r' ∈ A)
    (Y : {Y // Y ∈ 𝒴}) (hag : agreeOn (thickSet S.G' Y.1) r r') (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    obsGrRawC S m₀ hp Ev 𝒴 r (some Y) u Φ = obsGrRawC S m₀ hp Ev 𝒴 r' (some Y) u Φ := by
  exact obsGrRawC_local_rel (fun Y u u' => AgHatDir S.hG' Y u u') hd hcψ hq hr hr' Y
    (fun h => ⟨hag, fun _ _ _ => rfl⟩) u Φ

/-- **Parameter locality, exact form**: for `r, r' ∈ A` that agree on `Y` itself, the marks of `Y`
are equal, for terms `Ev Y` local for raw data on `Y` and hat variables at the unit points of `Y`. -/
theorem obsGrRawC_local_rawY
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u')
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    {r r' : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (hr' : r' ∈ A)
    (Y : {Y // Y ∈ 𝒴}) (hag : agreeOn Y.1 r r') (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    obsGrRawC S m₀ hp Ev 𝒴 r (some Y) u Φ = obsGrRawC S m₀ hp Ev 𝒴 r' (some Y) u Φ := by
  exact obsGrRawC_local_rel (fun Y u u' => agreeOn Y u.1 u'.1 ∧
    ∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i))
    (fun Y hY u hu u' hu' h => hd Y hY u hu u' hu' h.1 h.2) hcψ hq hr hr' Y
    (fun h => ⟨hag, fun _ _ _ => rfl⟩) u Φ

/-- **The clamp is the clipped hat field almost everywhere**: for the block product measure, the
marks with the clamp equal the marks with the clipping, for every datum, index and `u`. -/
theorem ae_obsGrRawC_eq_obsGrRaw :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (idx : RemIdx 𝒴) (u : ℂ),
      obsGrRawC S m₀ hp Ev 𝒴 r idx u Φ = obsGrRaw S m₀ hp Ev 𝒴 r idx u Φ := by
  filter_upwards [ae_obsHat_eq_true S m₀ hp] with Φ hΦ r idx u
  have hh : S.hatOf m₀ S.p₁ hp Φ = obsHat S m₀ hp Φ := by
    funext q
    have hn : ‖obsHatTrue S m₀ hp Φ q‖ ≤ S.p₁ := by
      rw [← congrFun hΦ q]; exact norm_obsHat_le S m₀ hp Φ q
    exact (clampC_of_le hp hn).trans (congrFun hΦ q).symm
  cases idx with
  | none => rfl
  | some Y => simp only [obsGrRawC, obsGrRaw, hh]

/-- The clamped marks at `rawOf D` equal the landed marks `obsGr` almost everywhere. -/
theorem ae_obsGrRawC_rawOf_eq_obsGr (D : BgData S.G' N) :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), ∀ (idx : RemIdx 𝒴) (u : ℂ),
      obsGrRawC S m₀ hp Ev 𝒴 (rawOf D) idx u Φ = obsGr S m₀ hp Ev D 𝒴 idx u Φ := by
  filter_upwards [ae_obsGrRawC_eq_obsGrRaw (S := S) (m₀ := m₀) (hp := hp) (Ev := Ev) (𝒴 := 𝒴)]
    with Φ h idx u
  rw [h, obsGrRaw_rawOf]

end Marks

end Balaban.Fluctuation
