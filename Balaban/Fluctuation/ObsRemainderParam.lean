/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRemainderMarks
public import Balaban.Fluctuation.ParamCarrierLocal

/-!
# The remainder marks as a function of the raw datum

`obsGrRaw` is the family of remainder marks `obsGr` of `ObsRemainderMarks` with the datum `D`
replaced by its raw datum `r = rawOf D` (the marks read the datum only through `rawOf D`).
From the three clauses of the sharp hat expansion `Ev` (analyticity of each `Ev Y` on
`A ×ˢ {‖ψ̂ p‖ ≤ cψ}`, the locality `AgHatDir`, the decay bound) we prove:

* `analyticOnNhd_obsGrRaw`: joint analyticity of `(r, u) ↦ obsGrRaw r idx u Φ` on
  `A ×ˢ ball 0 (3/2)`, for every block configuration `Φ`;
* `norm_obsGrRaw_le`: the bound `8 C0 q² e^{-κG 𝗱(y_idx)}`, the same for all `r ∈ A`;
* `measurable_obsGrRaw`, `depOn_obsGrRaw`;
* `continuousOn_obsGrRaw`: continuity in `Φ` on the open set of configurations with all site
  components of norm `< p₁` (not on the closed carrier: the clipping is discontinuous at norm `p₁`);
* `obsGrRaw_local`: parameter locality, two raw data that agree on the thickening of the domain
  give the same mark.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

/-! ### Joint analyticity of the ray remainder -/

section Ray

variable {R P : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P] [DecidableEq P]
  {A : Set R} {cψ p₁ : ℝ}

omit [DecidableEq P] in
/-- **Joint analyticity** of `(r, u) ↦ remExt (ζ ↦ E (r, ζ • ψ)) u` on `A ×ˢ ball 0 (3/2)`. -/
theorem analyticOnNhd_remExt_ray_param {E : R × (P → ℂ) → ℂ} (hcψ : 0 < cψ) (hp : 0 < p₁)
    (hq : p₁ / cψ ≤ 1 / 4)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {ψ : P → ℂ}
    (hψ : ∀ p, ‖ψ p‖ ≤ p₁) :
    AnalyticOnNhd ℂ (fun x : R × ℂ => remExt (fun ζ : ℂ => E (x.1, ζ • ψ)) x.2)
      (A ×ˢ ball (0 : ℂ) (3 / 2)) := by
  have h4 := four_le_of hcψ hp hq
  set g : R × ℂ → ℂ := fun x => E (x.1, x.2 • ψ) with hg
  have hga : ∀ x : R × ℂ, x.1 ∈ A → ‖x.2‖ < cψ / p₁ → AnalyticAt ℂ g x := by
    intro x hx1 hx2
    have := (hE (x.1, x.2 • ψ) ⟨hx1, smul_mem_ball_p hp hψ hx2⟩).comp_of_eq
      (f := fun x : R × ℂ => (x.1, x.2 • ψ))
      (analyticAt_fst.prod (analyticAt_snd.smul analyticAt_const)) rfl
    exact this
  have hder : ∀ x : R × ℂ, AnalyticAt ℂ g x →
      deriv (fun ζ : ℂ => E (x.1, ζ • ψ)) x.2 = fderiv ℂ g x (0, 1) := by
    intro x hx
    have h1 : HasDerivAt (fun ζ : ℂ => (x.1, ζ)) ((0 : R), (1 : ℂ)) x.2 :=
      (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    have h2 : HasFDerivAt g (fderiv ℂ g x) ((fun ζ : ℂ => (x.1, ζ)) x.2) :=
      hx.differentiableAt.hasFDerivAt
    exact (h2.comp_hasDerivAt x.2 h1).deriv
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hx2' : ‖x.2‖ < 3 / 2 := by simpa using hx2
  have hlt : ‖x.2‖ < cψ / p₁ := by linarith
  have hgx : AnalyticAt ℂ g x := hga x hx1 hlt
  have hz : AnalyticAt ℂ g (x.1, 0) := hga (x.1, 0) hx1 (by simp; linarith)
  have a1 : AnalyticAt ℂ (fun y : R × ℂ => fderiv ℂ g y (0, 1)) x :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : R), (1 : ℂ))).analyticAt _).comp hgx.fderiv
  have hc0 : Continuous (fun y : R × ℂ => (y.1, (0 : ℂ))) :=
    continuous_fst.prodMk continuous_const
  have a0 : AnalyticAt ℂ (fun y : R × ℂ => fderiv ℂ g (y.1, 0) (0, 1)) x := by
    have := hz.fderiv.comp_of_eq (f := fun y : R × ℂ => (y.1, (0 : ℂ)))
      (analyticAt_fst.prod analyticAt_const) rfl
    exact ((ContinuousLinearMap.apply ℂ ℂ ((0 : R), (1 : ℂ))).analyticAt _).comp this
  refine (a1.sub a0).congr ?_
  have hopen : ∀ᶠ y : R × ℂ in nhds x, ‖y.2‖ < 3 / 2 := by
    have : IsOpen {y : R × ℂ | ‖y.2‖ < 3 / 2} :=
      isOpen_lt (continuous_snd.norm) continuous_const
    exact this.mem_nhds hx2'
  have e1 : ∀ᶠ y : R × ℂ in nhds x, AnalyticAt ℂ g y := hgx.eventually_analyticAt
  have e0 : ∀ᶠ y : R × ℂ in nhds x, AnalyticAt ℂ g (y.1, 0) :=
    hc0.continuousAt.eventually (hz.eventually_analyticAt)
  filter_upwards [hopen, e1, e0] with y hy hy1 hy0
  rw [remExt_eq_of_lt _ hy, hder y hy1]
  have := hder (y.1, 0) hy0
  simp only at this
  rw [this]
  simp [g]

end Ray

/-! ### The remainder marks of the raw datum -/

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
  (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))

/-- **The remainder marks as a function of the raw datum**: `obsGr` with `rawOf D` replaced by a
raw datum `r`. -/
noncomputable def obsGrRaw (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    RemIdx 𝒴 → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ
  | none, _, _ => 0
  | some Y, u, Φ => remExt (fun ζ : ℂ => Ev Y.1 (r, ζ • obsHat S m₀ hp Φ)) u

/-- The raw-datum marks at `rawOf D` are the marks `obsGr` of the datum `D`. -/
theorem obsGrRaw_rawOf (D : BgData S.G' N) :
    obsGrRaw S m₀ hp Ev 𝒴 (rawOf D) = obsGr S m₀ hp Ev D 𝒴 := by
  funext r u Φ
  cases r <;> rfl

variable {S m₀ hp Ev 𝒴}
variable {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {cψ : ℝ}

/-- **Joint analyticity** of `(r, u) ↦ obsGrRaw r idx u Φ` on `A ×ˢ ball 0 (3/2)`, for every block
configuration `Φ`. -/
theorem analyticOnNhd_obsGrRaw (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (idx : RemIdx 𝒴) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    AnalyticOnNhd ℂ (fun x : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ =>
      obsGrRaw S m₀ hp Ev 𝒴 x.1 idx x.2 Φ) (A ×ˢ ball (0 : ℂ) (3 / 2)) := by
  cases idx with
  | none => exact analyticOnNhd_const
  | some Y =>
    exact analyticOnNhd_remExt_ray_param hcψ hp hq (ha Y.1 Y.2) (norm_obsHat_le S m₀ hp Φ)

/-- **Bound uniform in the datum**: for `r ∈ A`, all `u` and `Φ`,
`‖G_idx(r, u, Φ)‖ ≤ 8 C0 q² e^{-κG 𝗱(y_idx)}`, `q = p₁ / cψ`. -/
theorem norm_obsGrRaw_le (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
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
    ‖obsGrRaw S m₀ hp Ev 𝒴 r idx u Φ‖ ≤
      8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κG * Lab.dl (obsRemLab 𝒴 lab y₀ idx)) := by
  have hpc : 0 < S.p₁ / cψ := div_pos hp hcψ
  have hc0 : 0 < 8 * C0 * (S.p₁ / cψ) ^ 2 := by positivity
  cases idx with
  | none => simp only [obsGrRaw, norm_zero]; positivity
  | some Y =>
    simp only [obsGrRaw, obsRemLab]
    have htl : 0 ≤ treeLenCovOne m₀ (k + 1) Y.1 := by rw [← hdl Y]; exact Lab.dl_nonneg _
    refine (norm_remExt_ray_le hcψ hp hq hr (ha Y.1 Y.2) (hb Y.1 Y.2) (norm_obsHat_le S m₀ hp Φ)
      u).trans ?_
    rw [hdl Y, show 8 * (C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y.1)) * (S.p₁ / cψ) ^ 2 =
      8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y.1) by ring]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0.le
    nlinarith [htl]

/-- **Measurability** in the block configuration, for `r ∈ A`. -/
theorem measurable_obsGrRaw (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (idx : RemIdx 𝒴) (u : ℂ) :
    Measurable (obsGrRaw S m₀ hp Ev 𝒴 r idx u) := by
  cases idx with
  | none => exact measurable_const
  | some Y =>
    exact measurable_ray_rem hcψ hp hq hr (ha Y.1 Y.2) (measurable_obsHat S m₀ hp)
      (norm_obsHat_le S m₀ hp) u

/-- **Block locality**: for `r ∈ A`, the mark of the domain `Y` depends on `Φ` only through the
blocks of the cube label of `Y` (the locality `AgHatDir` of the term). -/
theorem depOn_obsGrRaw (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (Y : {Y // Y ∈ 𝒴}) (u : ℂ) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ Y.1) (obsGrRaw S m₀ hp Ev 𝒴 r (some Y) u) := by
  intro Φ Φ' h
  refine remExt_ray_congr hcψ hp hq (fun ζ hζ => ?_) u
  refine hd Y.1 Y.2 (r, ζ • obsHat S m₀ hp Φ)
    ⟨hr, smul_mem_ball_p hp (norm_obsHat_le S m₀ hp Φ) (by simpa using hζ)⟩
    (r, ζ • obsHat S m₀ hp Φ')
    ⟨hr, smul_mem_ball_p hp (norm_obsHat_le S m₀ hp Φ') (by simpa using hζ)⟩
    ⟨agreeOn_refl _ _, fun y' hy' i => ?_⟩
  have hT := cellOf_mem_obsRowLabel S hN (hdj Y.1 Y.2) hy'
    (rfl : unitPt S.hG' y' = unitPt S.hG' y')
  have := depOn_blockMark S m₀ hp (unitPt S.hG' y') i hT Φ Φ' h
  simp only [Pi.smul_apply, smul_eq_mul]
  show ζ * blockMark S m₀ hp _ i Φ = ζ * blockMark S m₀ hp _ i Φ'
  rw [this]

/-- **Parameter locality**: for `r, r' ∈ A` that agree on the thickening of the domain `Y`, the
marks of `Y` are equal (for all `u` and `Φ`). -/
theorem obsGrRaw_local
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    {r r' : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (hr' : r' ∈ A)
    (Y : {Y // Y ∈ 𝒴}) (hag : agreeOn (thickSet S.G' Y.1) r r') (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    obsGrRaw S m₀ hp Ev 𝒴 r (some Y) u Φ = obsGrRaw S m₀ hp Ev 𝒴 r' (some Y) u Φ := by
  have h4 := four_le_of hcψ hp hq
  simp only [obsGrRaw]
  have hloc : ∀ ζ : ℂ, ‖ζ‖ < cψ / S.p₁ →
      Ev Y.1 (r, ζ • obsHat S m₀ hp Φ) = Ev Y.1 (r', ζ • obsHat S m₀ hp Φ) := fun ζ hζ =>
    hd Y.1 Y.2 (r, ζ • obsHat S m₀ hp Φ)
      ⟨hr, smul_mem_ball_p hp (norm_obsHat_le S m₀ hp Φ) hζ⟩ (r', ζ • obsHat S m₀ hp Φ)
      ⟨hr', smul_mem_ball_p hp (norm_obsHat_le S m₀ hp Φ) hζ⟩ ⟨hag, fun _ _ _ => rfl⟩
  by_cases hu : ‖u‖ < 3 / 2
  · have hq' : ∀ v : ℂ, ‖v‖ < 3 / 2 →
        deriv (fun ζ : ℂ => Ev Y.1 (r, ζ • obsHat S m₀ hp Φ)) v =
          deriv (fun ζ : ℂ => Ev Y.1 (r', ζ • obsHat S m₀ hp Φ)) v := by
      intro v hv
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(isOpen_ball (x := (0 : ℂ)) (ε := cψ / S.p₁)).mem_nhds
        (show v ∈ ball (0 : ℂ) (cψ / S.p₁) by rw [mem_ball_zero_iff]; linarith)] with ζ hζ
      exact hloc ζ (by simpa using hζ)
    rw [remExt_eq_of_lt _ hu, remExt_eq_of_lt _ hu, hq' u hu, hq' 0 (by simp)]
  · rw [remExt_eq_zero_of_le _ (not_lt.1 hu), remExt_eq_zero_of_le _ (not_lt.1 hu)]

/-- **Continuity in the configuration** on the open set of block configurations all of whose site
components have norm `< p₁`, for `r ∈ A`.  (On the closed carrier `‖Φ b w‖ ≤ p₁` the clipping
makes `obsHat` discontinuous at norm `p₁`.) -/
theorem continuousOn_obsGrRaw (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {r : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (idx : RemIdx 𝒴) (u : ℂ) :
    ContinuousOn (obsGrRaw S m₀ hp Ev 𝒴 r idx u)
      {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b | ∀ b w, ‖Φ b w‖ < S.p₁} := by
  cases idx with
  | none => exact continuousOn_const
  | some Y =>
    by_cases hu : ‖u‖ < 3 / 2
    · have hc := continuousOn_ray_rem hcψ hp hq hr (ha Y.1 Y.2) hu
      have ht : Continuous (obsHatTrue S m₀ hp) := by
        refine continuous_pi fun q => ?_
        exact Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj q.2).continuous.comp
            ((continuous_apply _).comp (continuous_apply _)))
      have hco : ContinuousOn (obsHat S m₀ hp)
          {Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b | ∀ b w, ‖Φ b w‖ < S.p₁} := by
        refine ht.continuousOn.congr fun Φ hΦ => ?_
        funext q
        exact clippedCoord_of_lt q.2 (hΦ _ _)
      exact hc.comp hco (fun Φ _ p => norm_obsHat_le S m₀ hp Φ p)
    · have : obsGrRaw S m₀ hp Ev 𝒴 r (some Y) u = fun _ => 0 := by
        funext Φ; exact remExt_eq_zero_of_le _ (not_lt.1 hu)
      rw [this]; exact continuousOn_const

end Marks

end Balaban.Fluctuation
