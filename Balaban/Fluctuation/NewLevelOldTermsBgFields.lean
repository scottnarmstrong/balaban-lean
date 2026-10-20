/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelOldTermsBg
public import Balaban.Fluctuation.NewLevelTermsBgAnalytic
public import Balaban.Fluctuation.MarkedEvJoint

/-!
# The fields of the old activities and marks recomputed on a background generating set

P3 pp. 78-79 and Lemma 4.2 at `Gb`, (AE1), for the activities `oldActBg` and the marks `oldMarkGBg`
of the old labels of the new level recomputed on a background generating set `Gb` with the
canonical transport (route R-LOC, L4-3).  For functionals `Φ τ` of the old terms analytic and
bounded on the realizable triples of `Gb` (for the old terms `eTermFun` on `Gb`:
`eTermFun_analytic_bound_of_top`) and a label `Y` inside the top layer of `Gb`, the terms
`evDecBg` of `Y` are bounded and jointly analytic on the chart of `Gb`
(`evDecBg_canon_bound_analytic`, `evDecBg_canon_fields`), hence:

* `oldActBg_canon_of_mem`, `oldActBg_canon_of_not`: the gate of the activities;
* `oldActBg_canon_fields`: the activity of `Y` is bounded by
  `|β| ∑_{τ : Y ∈ polyDom τ} 2 E_τ e^{-κ₀ d(X_τ) - 2 κ_dec d̃(Y)}`, analytic in `(θ, u)` on
  `physVBg Gb × {‖u‖ < R_u}`, continuous in the configuration on the chart and measurable;
* `oldMarkGBg_canon_fields`: the mark of an anchor `q = (τ, Y)` is bounded by
  `|β| E_τ e^{-κ₀ d(X_τ) - 2 κ_dec d̃(Y)} / t₀`, analytic in `(θ, u)` on `physVBg Gb × {‖u‖ < R_u}`,
  continuous in the configuration on the chart and measurable.

No locality is used.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Finset Metric

section OldFields

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱd : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱd} (Zb : Finset (unitPts Gb))
  {ι : Type*} [Fintype ι]
  (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ : ℕ) (jL : ι → ℕ)
  (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
  (F₁ : ι → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
  (Sol : ι → Dec2.DecParams (coverOf Gb) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (Φ : ι → ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Gd.Ω 1 × Fin N → ℂ) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
  (ρ : ℝ) (hp : 0 < S.p₁) (Ru eps : ℝ) (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))

open Classical in
/-- The old activity on `Gb` on the chart and the disc. -/
theorem oldActBg_canon_of_mem {θ : physParamBg N Gb} {u : ℂ}
    (h1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps) (h2 : ‖u‖ < Ru) (Y : {Y // Y ∈ 𝒴C})
    (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps 𝒴C θ Y u Ψ =
      ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        (S.β : ℂ) * (evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb S.a₁ S.ν
            (BgTransport.canon S.G' Gb N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (Φ τ) Zb u 0 Y.1 ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
              (BgTransport.canon S.G' Gb N).res (S.hatOf 1 ρ hp Ψ)) -
          evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ) (Φ τ) Zb 0 0 Y.1
            ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
              (BgTransport.canon S.G' Gb N).res (S.hatOf 1 ρ hp Ψ)))
      else 0 := by
  simp only [oldActBg, h1, h2, and_self, ↓reduceIte]

/-- The old activity on `Gb` vanishes off the chart or off the disc. -/
theorem oldActBg_canon_of_not {θ : physParamBg N Gb} {u : ℂ}
    (h : ¬ ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru)) (Y : {Y // Y ∈ 𝒴C})
    (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps 𝒴C θ Y u Ψ =
      0 := by
  simp only [oldActBg, h, ↓reduceIte]

open Classical in
/-- The old mark on `Gb` on the chart and the disc. -/
theorem oldMarkGBg_canon_of_mem (z : RootIdx d L N₁ m₁ (k + 1)) {θ : physParamBg N Gb} {u : ℂ}
    (h1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps) (h2 : ‖u‖ < Ru)
    (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z})
    (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z θ q u Ψ =
      (S.β : ℂ) * deriv (fun t : ℂ => evDecBg S.G' (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) Gb S.a₁
        S.ν (BgTransport.canon S.G' Gb N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1)
        (Sol q.1.1) (Φ q.1.1) Zb u t q.1.2 ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          (BgTransport.canon S.G' Gb N).res (S.hatOf 1 ρ hp Ψ))) 0 := by
  simp only [oldMarkGBg, h1, h2, and_self, ↓reduceIte]

open Classical in
/-- The old mark on `Gb` vanishes off the chart or off the disc. -/
theorem oldMarkGBg_canon_of_not (z : RootIdx d L N₁ m₁ (k + 1)) {θ : physParamBg N Gb} {u : ℂ}
    (h : ¬ ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru))
    (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z})
    (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z θ q u Ψ =
      0 := by
  simp only [oldMarkGBg, h, ↓reduceIte]

/-- The marks `(u, 0)`, `‖u‖ ≤ R_u`, lie in the radius set when `R_u m_R < δ₁`, `δ₁ > 0`. -/
theorem mem_markedRad_of_le {mR δ₁ Ru : ℝ} (hδ₁ : 0 < δ₁) (hRu : Ru * mR < δ₁) {u : ℂ}
    (hu : ‖u‖ ≤ Ru) : (‖u‖ + ‖(0 : ℂ)‖) * mR < δ₁ := by
  rw [norm_zero, add_zero]
  rcases le_or_gt 0 mR with h | h
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu h) hRu
  · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg u) h.le) hδ₁

open Classical in
/-- **The fields of a gated sum of mark differences of analytic terms**: for terms `T τ` of the
datum, the hat variable and the marks, analytic and bounded by `B τ` on the chart of `Gb` times the
box `|ψ̂| ≤ c_ψ` times a set `W` of marks containing `(u, 0)` for `‖u‖ < R_u` and `(0, 0)`, the
activity `A θ u Ψ = β ∑_{τ : C τ} (T τ ((θ.raw, ψ̂(Ψ)), (u, 0)) - T τ ((θ.raw, ψ̂(Ψ)), (0, 0)))` on the
chart and the disc `‖u‖ < R_u` (`0` off them) is bounded by `|β| ∑_{τ : C τ} 2 B τ`, analytic in
`(θ, u)` on `physVBg Gb × {‖u‖ < R_u}`, continuous in the configuration on the chart and the disc,
and measurable in the configuration. -/
theorem gatedMarkDiff_fields (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν)
    {ρ cψ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (Ru eps : ℝ)
    (C : ι → Prop) [DecidablePred C]
    (T : ι → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) → ℂ)
    (W : Set (ℂ × ℂ)) (hW : ∀ u : ℂ, ‖u‖ < Ru → (u, (0 : ℂ)) ∈ W)
    (hW0 : ((0 : ℂ), (0 : ℂ)) ∈ W) (B : ι → ℝ) (hB : ∀ τ, 0 ≤ B τ)
    (hT : ∀ τ, C τ → AnalyticOnNhd ℂ (T τ)
      ((XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ W))
    (hTb : ∀ τ, C τ → ∀ p ∈ (XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ W, ‖T τ p‖ ≤ B τ)
    (A : physParamBg N Gb → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hA : ∀ θ u Ψ, A θ u Ψ = if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru then
      ∑ τ, if C τ then (S.β : ℂ) *
        (T τ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Ψ), (u, 0)) -
          T τ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Ψ), (0, 0)))
      else 0 else 0) :
    (∀ θ u Ψ, ‖A θ u Ψ‖ ≤ |S.β| * ∑ τ, if C τ then 2 * B τ else 0) ∧
    (∀ Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b, AnalyticOnNhd ℂ
      (fun p : physParamBg N Gb × ℂ => A p.1 p.2 Ψ)
      (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) Ru)) ∧
    (∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < Ru →
      Continuous (A θ u)) ∧
    (∀ θ u, Measurable (A θ u)) := by
  have hbox : ∀ Ψ : (∀ b, (S.blockSplit 1 hp).Ωb b), ∀ q, ‖S.hatOf 1 ρ hp Ψ q‖ ≤ cψ :=
    fun Ψ q => (S.hatOf_mem 1 hρ hp Ψ q).trans hρc
  -- continuity in the configuration on the chart
  have hcont : ∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < Ru →
      Continuous (A θ u) := by
    intro θ hθ u hu
    have hc : ∀ τ, C τ → ∀ w ∈ W, Continuous (fun Ψ : (∀ b, (S.blockSplit 1 hp).Ωb b) =>
        T τ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Ψ), w)) := by
      intro τ hτ w hw
      have hcon := (hT τ hτ).continuousOn.comp
        (f := fun ψ : unitPts S.G' × Fin N → ℂ =>
          (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψ), w))
        (s := {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) (by fun_prop)
        (fun ψ hψ => ⟨⟨hθ, hψ⟩, hw⟩)
      exact hcon.comp_continuous (S.continuous_hatOf 1 ρ hp) hbox
    have e : A θ u = fun Ψ => ∑ τ, if C τ then (S.β : ℂ) *
        (T τ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Ψ), (u, 0)) -
          T τ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Ψ), (0, 0)))
        else 0 := funext fun Ψ => by rw [hA, ite_eq_left ⟨hθ, hu⟩]
    rw [e]
    refine continuous_finsetSum _ fun τ _ => ?_
    by_cases hτ : C τ
    · simp only [hτ, ↓reduceIte]
      exact continuous_const.mul ((hc τ hτ _ (hW u hu)).sub (hc τ hτ _ hW0))
    · simp only [hτ, ↓reduceIte]
      exact continuous_const
  refine ⟨fun θ u Ψ => ?_, fun Ψ => ?_, hcont, fun θ u => ?_⟩
  · -- the bound
    have hsum0 : 0 ≤ ∑ τ, (if C τ then 2 * B τ else 0) :=
      Finset.sum_nonneg fun τ _ => by
        split_ifs
        · have := hB τ
          positivity
        · exact le_rfl
    rw [hA]
    split_ifs with hc
    · rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
      by_cases hτ : C τ
      · simp only [hτ, ↓reduceIte]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have e1 := hTb τ hτ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          S.hatOf 1 ρ hp Ψ), (u, 0)) ⟨⟨hc.1, hbox Ψ⟩, hW u hc.2⟩
        have e0 := hTb τ hτ (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          S.hatOf 1 ρ hp Ψ), (0, 0)) ⟨⟨hc.1, hbox Ψ⟩, hW0⟩
        refine (norm_sub_le _ _).trans ((add_le_add e1 e0).trans_eq ?_)
        ring
      · simp only [hτ, ↓reduceIte, norm_zero, mul_zero, le_refl]
    · rw [norm_zero]
      exact mul_nonneg (abs_nonneg _) hsum0
  · -- analyticity in `(θ, u)`
    let g : physParamBg N Gb × ℂ →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ :=
      ((rawSub N Gb).subtypeL.comp (ContinuousLinearMap.fst ℂ _ _)).prodMap
        (ContinuousLinearMap.id ℂ ℂ)
    intro p hp'
    have hp1 : (g p).1 ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps := hp'.1.1
    have hp2 : ‖(g p).2‖ < Ru := mem_ball_zero_iff.1 hp'.2
    have hg := g.analyticAt p
    have hA' : AnalyticAt ℂ (fun q : physParamBg N Gb × ℂ =>
        ∑ τ, if C τ then (S.β : ℂ) *
          (T τ (((g q).1, S.hatOf 1 ρ hp Ψ), ((g q).2, 0)) -
            T τ (((g q).1, S.hatOf 1 ρ hp Ψ), (0, 0)))
        else 0) p := by
      refine Finset.analyticAt_fun_sum _ fun τ _ => ?_
      by_cases hτ : C τ
      · simp only [hτ, ↓reduceIte]
        have m1 : AnalyticAt ℂ (fun q : physParamBg N Gb × ℂ =>
            ((((g q).1, S.hatOf 1 ρ hp Ψ), ((g q).2, (0 : ℂ))) :
              (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ))) p :=
          ((analyticAt_fst.comp hg).prod analyticAt_const).prod
            ((analyticAt_snd.comp hg).prod analyticAt_const)
        have m0 : AnalyticAt ℂ (fun q : physParamBg N Gb × ℂ =>
            ((((g q).1, S.hatOf 1 ρ hp Ψ), ((0 : ℂ), (0 : ℂ))) :
              (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ))) p :=
          ((analyticAt_fst.comp hg).prod analyticAt_const).prod analyticAt_const
        have e1 := (hT τ hτ ((((g p).1, S.hatOf 1 ρ hp Ψ), ((g p).2, (0 : ℂ))))
          ⟨⟨hp1, hbox Ψ⟩, hW _ hp2⟩).comp_of_eq m1 rfl
        have e0 := (hT τ hτ ((((g p).1, S.hatOf 1 ρ hp Ψ), ((0 : ℂ), (0 : ℂ))))
          ⟨⟨hp1, hbox Ψ⟩, hW0⟩).comp_of_eq m0 rfl
        exact analyticAt_const.mul (e1.sub e0)
      · simp only [hτ, ↓reduceIte]
        exact analyticAt_const
    have hopen : IsOpen (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) Ru) :=
      (isOpen_physVBg Gb S.a₁ S.ν eps HBb).prod isOpen_ball
    refine hA'.congr (Filter.eventually_of_mem (hopen.mem_nhds hp') fun q hq => ?_)
    dsimp only
    rw [hA, ite_eq_left ⟨hq.1.1, mem_ball_zero_iff.1 hq.2⟩]
    rfl
  · -- measurability
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru
    · exact (hcont θ hc.1 u hc.2).measurable
    · have e : A θ u = fun _ => 0 := funext fun Ψ => by rw [hA, ite_eq_right hc]
      rw [e]
      exact measurable_const

variable {X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps}
variable {Kc Cx : ℝ} {XL : ι → Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **The fields of the old activities recomputed on `Gb` with the canonical transport** (P3
pp. 78-79 and Lemma 4.2 at `Gb`, (AE1)).  Let the functionals `Φ τ` of the old terms whose
expansion has the domain `Y` be analytic and bounded by `E_τ e^{-(κ_dec - 1) d^{cov,1}(X_τ)}` on
the realizable triples of `Gb`, `Y` inside the top layer of `Gb`, the decoupling pairs `F₁`, `Sol`
of `Gb` pinned and analytic, and `R_u m_R < δ₁`.  Then the activity `oldActBg … θ Y u Ψ`:

1. is bounded by `|β| ∑_{τ : Y ∈ polyDom τ} 2 E_τ e^{-κ₀ d(X_τ) - 2 κ_dec d̃(Y)}`;
2. is analytic in `(θ, u)` on `physVBg Gb × {‖u‖ < R_u}` for every configuration;
3. is continuous in the configuration at the parameters of the chart and `‖u‖ < R_u`;
4. is measurable in the configuration. -/
theorem oldActBg_canon_fields (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hPmp : Precedes Gd Gb) (hHm : Gd.Ω (k + 1) = ∅)
    (hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData Gb N, InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf Gb) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Gd (Dec2.decG (coverOf Gb) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf Gb) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Gd (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {Eb : ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (Y : {Y // Y ∈ 𝒴C}) (hYtop : ∀ x ∈ Y.1, x ∈ Gb.Ω (k + 1))
    (hΦ : ∀ τ, Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) →
      AnalyticOnNhd ℂ (fun t => Φ τ t.1 t.2.1 t.2.2)
        (FlRealLC Gb Gd S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁))
    (hΦbd : ∀ τ, Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) →
      ∀ t ∈ FlRealLC Gb Gd S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁,
        ‖Φ τ t.1 t.2.1 t.2.2‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ))) :
    (∀ θ u Ψ, ‖oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps
        𝒴C θ Y u Ψ‖ ≤
      |S.β| * ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y.1)) else 0) ∧
    (∀ Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b, AnalyticOnNhd ℂ
      (fun p : physParamBg N Gb × ℂ => oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL
        𝒦X F₁ Sol Φ ρ hp Ru eps 𝒴C p.1 Y p.2 Ψ)
      (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) Ru)) ∧
    (∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < Ru →
      Continuous (oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru
        eps 𝒴C θ Y u)) ∧
    (∀ θ u, Measurable (oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ
      hp Ru eps 𝒴C θ Y u)) := by
  have hW0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rw [norm_zero, add_zero, zero_mul]
    exact hδ₁0
  -- (AE1) of the terms of the old terms whose expansion has the domain `Y`
  have hτ := fun τ (hY : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) =>
    evDecBg_canon_bound_analytic S S.hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps hsmall hc7 hphi
      hmarD hαD hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hδ₁0 hPmp hHm (hF₁an τ) (hF₁ τ)
      (hSolan τ) (hSol τ) (hcov τ) (hX₁ τ) (hopt τ) hκ₀ hκdec hκκ h1 hlog (hEb τ)
      (X₁g := X₁f τ) (fun x hx => hx)
      (fun x hx => hYtop x (subset_polyDom hY (by rw [← hX₁ τ]; exact hx))) (hΦ τ hY)
      (hΦbd τ hY) Zb
  exact gatedMarkDiff_fields S HBb hρ hρc hp Ru eps
    (fun τ => Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (fun τ p => evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ) (Φ τ) Zb p.2.1 p.2.2 Y.1
      (p.1.1, (BgTransport.canon S.G' Gb N).res p.1.2))
    {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁}
    (fun u hu => mem_markedRad_of_le hδ₁0 hRu hu.le) hW0
    (fun τ => Eb τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
      2 * κdec * treeLenCov S.G' m₀ Y.1))
    (fun τ => mul_nonneg (hEb τ) (Real.exp_pos _).le) (fun τ hY => (hτ τ hY).2 Y.1)
    (fun τ hY => (hτ τ hY).1 Y.1)
    (fun θ u Ψ => oldActBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru
      eps 𝒴C θ Y u Ψ) (fun θ u Ψ => by simp only [oldActBg])

open Classical in
/-- **The fields of the old marks recomputed on `Gb` with the canonical transport** (P3
pp. 78-79 and Lemma 4.2 at `Gb`, (AE1), with the Cauchy estimate of the derivative in the second
mark).  Under the hypotheses of `oldActBg_canon_fields` for the old term `τ = q.1` of an anchor
`q = (τ, Y)` with `Y` inside the top layer of `Gb`, and `(R_u + t₀) m_R < δ₁`, `0 < t₀`,
`0 ≤ R_u`, the mark `oldMarkGBg … θ q u Ψ`:

1. is bounded by `|β| E_τ e^{-κ₀ d(X_τ) - 2 κ_dec d̃(Y)} / t₀`;
2. is analytic in `(θ, u)` on `physVBg Gb × {‖u‖ < R_u}` for every configuration;
3. is continuous in the configuration at the parameters of the chart and `‖u‖ < R_u`;
4. is measurable in the configuration. -/
theorem oldMarkGBg_canon_fields (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hPmp : Precedes Gd Gb) (hHm : Gd.Ω (k + 1) = ∅)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hRu0 : 0 ≤ Ru)
    (hRt : (Ru + t₀) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData Gb N, InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf Gb) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Gd (Dec2.decG (coverOf Gb) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf Gb) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Gd (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {Eb : ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (z : RootIdx d L N₁ m₁ (k + 1))
    (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z})
    (hYtop : ∀ x ∈ q.1.2, x ∈ Gb.Ω (k + 1))
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ q.1.1 t.1 t.2.1 t.2.2)
        (FlRealLC Gb Gd S.a₁ S.ν BG κ eps (X₁f q.1.1) BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlRealLC Gb Gd S.a₁ S.ν BG κ eps (X₁f q.1.1) BG₂ δ₁,
        ‖Φ q.1.1 t.1 t.2.1 t.2.2‖ ≤
          Eb q.1.1 * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL q.1.1) (XL q.1.1))) :
    (∀ θ u Ψ, ‖oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps
        z θ q u Ψ‖ ≤
      |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) -
          2 * κdec * treeLenCov S.G' m₀ q.1.2) / t₀)) ∧
    (∀ Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b, AnalyticOnNhd ℂ
      (fun p : physParamBg N Gb × ℂ => oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀
        jL 𝒦X F₁ Sol Φ ρ hp Ru eps z p.1 q p.2 Ψ)
      (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) Ru)) ∧
    (∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < Ru →
      Continuous (oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru
        eps z θ q u)) ∧
    (∀ θ u, Measurable (oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ
      hp Ru eps z θ q u)) := by
  have hbox : ∀ Ψ : (∀ b, (S.blockSplit 1 hp).Ωb b), ∀ q', ‖S.hatOf 1 ρ hp Ψ q'‖ ≤ cψ :=
    fun Ψ q' => (S.hatOf_mem 1 hρ hp Ψ q').trans hρc
  have hYq : q.1.2 ∈ polyDom S.G' (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) :=
    (mem_markedIdx.1 q.2).1
  obtain ⟨hcau, hJ2, hJ4⟩ := evDecBg_canon_fields S S.hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps
    hsmall hc7 hphi hmarD hαD hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hδ₁0 hPmp hHm
    (hF₁an q.1.1) (hF₁ q.1.1) (hSolan q.1.1) (hSol q.1.1) (hcov q.1.1) (hX₁ q.1.1) (hopt q.1.1)
    hκ₀ hκdec hκκ h1 hlog (hEb q.1.1) (X₁g := X₁f q.1.1) (fun x hx => hx)
    (fun x hx => hYtop x (subset_polyDom hYq (by rw [← hX₁ q.1.1]; exact hx))) hΦ hΦbd Zb
  have hRu : Ru * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rcases le_or_gt 0 (markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      with h0 | h0
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) h0) hRt
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos hRu0 h0.le) hδ₁0
  have hW : ∀ u : ℂ, ‖u‖ < Ru → (‖u‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := fun u hu =>
    mem_markedRad_of_le hδ₁0 hRu hu.le
  -- continuity in the configuration on the chart
  have hcont : ∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < Ru →
      Continuous (oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru
        eps z θ q u) := by
    intro θ hθ u hu
    refine Continuous.congr ?_ fun Ψ =>
      (oldMarkGBg_canon_of_mem S Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z hθ hu q Ψ).symm
    have hana := analyticOnNhd_deriv_mark (hJ2 q.1.2)
    have hcon : ContinuousOn (fun ψ : unitPts S.G' × Fin N → ℂ => deriv (fun t : ℂ =>
        evDecBg S.G' (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) Gb S.a₁ S.ν
          (BgTransport.canon S.G' Gb N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1)
          (Sol q.1.1) (Φ q.1.1) Zb u t q.1.2 ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
            (BgTransport.canon S.G' Gb N).res ψ)) 0)
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q', ‖ψh q'‖ ≤ cψ} :=
      hana.continuousOn.comp (f := fun ψ : unitPts S.G' × Fin N → ℂ =>
        (((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψ), u)) (by fun_prop)
        (fun ψ hψ => ⟨⟨hθ, hψ⟩, hW u hu⟩)
    exact continuous_const.mul (hcon.comp_continuous (S.continuous_hatOf 1 ρ hp) hbox)
  refine ⟨fun θ u Ψ => ?_, fun Ψ => ?_, hcont, fun θ u => ?_⟩
  · -- the bound
    have hB0 : 0 ≤ Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) -
        2 * κdec * treeLenCov S.G' m₀ q.1.2) / t₀ := by
      have := hEb q.1.1
      positivity
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru
    · rw [oldMarkGBg_canon_of_mem S Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z hc.1 hc.2 q Ψ,
        norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc' := hcau Ru t₀ t₀ hRu0 ht₀.le ht₀ le_rfl hRt u hc.2.le q.1.2
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Ψ) ⟨hc.1, hbox Ψ⟩
      dsimp only at hc'
      exact mul_le_mul_of_nonneg_left hc' (abs_nonneg _)
    · rw [oldMarkGBg_canon_of_not S Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z hc q Ψ, norm_zero]
      exact mul_nonneg (abs_nonneg _) hB0
  · -- analyticity in `(θ, u)`
    intro p hp'
    have hA := (analyticAt_const (v := (S.β : ℂ))).mul
      (hJ4 q.1.2 (S.hatOf 1 ρ hp Ψ) (hbox Ψ) Ru t₀ hRu0 ht₀ hRt p hp')
    have hopen : IsOpen (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) Ru) :=
      (isOpen_physVBg Gb S.a₁ S.ν eps HBb).prod isOpen_ball
    refine hA.congr (Filter.eventually_of_mem (hopen.mem_nhds hp') fun r hr => ?_)
    exact (oldMarkGBg_canon_of_mem S Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z hr.1.1
      (mem_ball_zero_iff.1 hr.2) q Ψ).symm
  · -- measurability
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru
    · exact (hcont θ hc.1 u hc.2).measurable
    · have e : oldMarkGBg S Gb (BgTransport.canon S.G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru
          eps z θ q u = fun _ => 0 :=
        funext fun Ψ => oldMarkGBg_canon_of_not S Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z hc q Ψ
      rw [e]
      exact measurable_const

end OldFields

end Balaban.Fluctuation
