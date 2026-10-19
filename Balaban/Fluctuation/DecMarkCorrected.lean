/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkBlocks
public import Balaban.Fluctuation.RenormExpCauchy

/-!
# The corrected decoupled marks (first-order Taylor remainder in the first mark)

The decoupled mark `decMarkG … um Φ` is a holomorphic function of the first mark `um`, bounded by
`E_* e^{-2 κ_dec d^cov(Y)} / R` on a disc `‖um‖ < R` whose radius is large.  The corrected mark is
its first-order Taylor remainder at `um = 0`, which is of size `(‖um‖ / R)²` times that bound.

* `norm_taylor1_remainder_le_of_mem_ball`, `norm_taylor1_remainder_le`: for `f` holomorphic and
  bounded by `B` on the disc of radius `R`, `‖f u − f 0 − u f′(0)‖ ≤ 4 B (‖u‖ / R)²`
  (two applications of the Schwarz lemma to the difference quotients).
* `analyticOnNhd_deriv_snd`: the derivative at `0` in the last variable of a jointly analytic
  function is analytic in the other variable.
* `decMarkCorr`: the corrected block-level mark `f(um) − f(0) − um · f′(0)`, `f = decMarkG … · Φ`.
* `decMarkCorr_dep`, `decMarkCorr_fields`: block locality, continuity, measurability, the cubic
  bound with the exponential decay, and analyticity in `(e, um)`.
* `decMarkCorrBg`, `decMarkCorrBg_dep`, `decMarkCorrBg_fields_of`: the corrected mark on a background
  generating set `Gb` (ruling R8) and its fields from the clauses of the terms on `Gb`;
  `decMarkCorr` is the instance `Gb = S.G'`, `BgTransport.self` (definitionally,
  `decMarkCorr_eq_decMarkG`), and the field theorems at `S.G'` are instances.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.Analysis Balaban.Polymer Metric

section Taylor

/-- **The first-order Taylor remainder on a disc.**  If `f` is holomorphic on the disc of radius
`R` and bounded by `B` there, then for `‖u‖ < R`,
`‖f u − f 0 − u f′(0)‖ ≤ 4 B (‖u‖ / R)²`. -/
theorem norm_taylor1_remainder_le_of_mem_ball {f : ℂ → ℂ} {R B : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 R)) (hB : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ B)
    {u : ℂ} (hu : u ∈ ball (0 : ℂ) R) :
    ‖f u - f 0 - u * deriv f 0‖ ≤ 4 * B * (‖u‖ / R) ^ 2 := by
  have hR : 0 < R := pos_of_mem_ball hu
  have hs : DifferentiableOn ℂ (dslope f 0) (ball 0 R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 hR)).2 hd
  have hsb : ∀ z ∈ ball (0 : ℂ) R, ‖dslope f 0 z‖ ≤ 2 * B / R := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have hev : ∀ᶠ w in nhdsWithin (0 : ℂ) {0}ᶜ, ‖dslope f 0 w‖ ≤ 2 * B / R := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hR)]
          with w hw hwb
        have hw0 : w ≠ 0 := hw
        have h1 := norm_sub_le_two_mul_of_ball hd hB hwb
        rw [dslope_of_ne _ hw0, slope_def_field, sub_zero, norm_div]
        rw [div_le_iff₀ (norm_pos_iff.2 hw0)]
        calc ‖f w - f 0‖ ≤ 2 * B / R * ‖w‖ := h1
          _ = _ := by ring
      have hne : (nhdsWithin (0 : ℂ) {0}ᶜ).NeBot := inferInstance
      have hct : Filter.Tendsto (fun w => ‖dslope f 0 w‖) (nhdsWithin (0 : ℂ) {0}ᶜ)
          (nhds ‖dslope f 0 0‖) :=
        ((hs.continuousOn.continuousAt (ball_mem_nhds (0 : ℂ) hR)).norm).tendsto.mono_left
          nhdsWithin_le_nhds
      exact le_of_tendsto hct hev
    · have h1 := norm_sub_le_two_mul_of_ball hd hB hz
      rw [dslope_of_ne _ hz0, slope_def_field, sub_zero, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.2 hz0)]
      calc ‖f z - f 0‖ ≤ 2 * B / R * ‖z‖ := h1
        _ = _ := by ring
  have h2 := norm_sub_le_two_mul_of_ball hs hsb hu
  have e1 : f u - f 0 = u * dslope f 0 u := by
    have := sub_smul_dslope f 0 u
    simp only [sub_zero, smul_eq_mul] at this
    exact this.symm
  have e2 : dslope f 0 0 = deriv f 0 := dslope_same f 0
  have e3 : f u - f 0 - u * deriv f 0 = u * (dslope f 0 u - dslope f 0 0) := by
    rw [e2, mul_sub, ← e1]
  rw [e3, norm_mul]
  calc ‖u‖ * ‖dslope f 0 u - dslope f 0 0‖ ≤ ‖u‖ * (2 * (2 * B / R) / R * ‖u‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 4 * B * (‖u‖ / R) ^ 2 := by field_simp; ring

/-- **The first-order Taylor remainder, in the form with a radius `U`.**  Same hypotheses, with
`‖u‖ ≤ U`, `2 U ≤ R`: `‖f u − f 0 − u f′(0)‖ ≤ 4 B (U / R)²`.  (The condition `2 U ≤ R` is only
used to place `u` in the disc.) -/
theorem norm_taylor1_remainder_le {f : ℂ → ℂ} {R B U : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball 0 R)) (hB : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ B)
    {u : ℂ} (hu : ‖u‖ ≤ U) (hUR : 2 * U ≤ R) :
    ‖f u - f 0 - u * deriv f 0‖ ≤ 4 * B * (U / R) ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_ball_self hR))
  have hmem : u ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  refine (norm_taylor1_remainder_le_of_mem_ball hd hB hmem).trans ?_
  have : ‖u‖ / R ≤ U / R := div_le_div_of_nonneg_right hu hR.le
  gcongr

end Taylor

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The derivative in the last variable.**  If `g (x, v)` is analytic on `A × S` and `0 ∈ S`, then
`x ↦ ∂_v g (x, v)|_{v=0}` is analytic on `A`. -/
theorem analyticOnNhd_deriv_snd {A : Set E} {S : Set ℂ} {g : E × ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (A ×ˢ S)) (h0 : (0 : ℂ) ∈ S) :
    AnalyticOnNhd ℂ (fun x : E => deriv (fun v : ℂ => g (x, v)) 0) A := by
  have hf : AnalyticOnNhd ℂ (fun p : E × (ℂ × ℂ) => g (p.1, p.2.2))
      (A ×ˢ ((Set.univ : Set ℂ) ×ˢ S)) :=
    hg.comp (f := fun p : E × (ℂ × ℂ) => (p.1, p.2.2))
      (fun _ _ => analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd))
      (fun p hp => ⟨hp.1, hp.2.2⟩)
  have h := analyticOnNhd_deriv_mark hf
  refine (h.comp (f := fun x : E => (x, (0 : ℂ))) (fun _ _ => analyticAt_id.prod analyticAt_const)
    ?_)
  intro x hx
  exact ⟨hx, Set.mem_univ _, h0⟩

end Generic

section BlocksBg

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {T : BgTransport S.G' Gb N}
variable {a₁ ν κ eps δ₁ cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts Gb)}
variable {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **The corrected decoupled mark on a background generating set `Gb`.**  The first-order Taylor
remainder, in the first mark `um`, of the mark `decMarkGBg … um Φ` computed on `Gb` with the
transport `T`: `f(um) − f(0) − um · f′(0)` with `f = fun v => decMarkGBg … v Φ`. -/
noncomputable def decMarkCorrBg (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (T : BgTransport S.G' Gb N) (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gb)) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ -
    decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ 0 Φ -
    um * deriv (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ) 0

/-- **Block locality of the corrected mark on a background generating set.**  From the locality
`hloc` of the terms `evDecBg` in the step's hat variable: each of the three summands depends only on
the blocks inside a cell-union `Y′ ⊇ Y` (for the derivative, the family in `v` agrees near
`v = 0`). -/
theorem decMarkCorrBg_dep
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u.1, T.res u.2) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u'.1, T.res u'.2))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y) (hYY : Y ⊆ Y')
    (hY' : ∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') :
    DepOn (blocksOf m₀ (k + 1) Set.univ Y')
      (decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um) := by
  intro Φ Φ' h
  have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
  have e1 := decMarkGBg_dep S hloc hρ hρc hp hΘ hum hYm hYY hY' Φ Φ' h
  have e2 := decMarkGBg_dep S hloc hρ hρc hp hΘ h0 hYm hYY hY' Φ Φ' h
  have hopen : IsOpen {t : ℂ | (‖t‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have e3 : deriv (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ) 0 =
      deriv (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ') 0 := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hopen.mem_nhds h0] with v hv
    exact decMarkGBg_dep S hloc hρ hρc hp hΘ hv hYm hYY hY' Φ Φ' h
  unfold decMarkCorrBg
  rw [e1, e2, e3]

/-- **The cubic bound of the corrected mark on a background generating set.**  From the Cauchy
estimate `hcau` with a bound `B` and the joint analyticity `hJ2` of the terms on the chart of the step (the datum read on `Gb` is `T.dat` of it):
for `0 < R`, `(R + R) · markedRad < δ₁`, `2 U ≤ R` and `‖um‖ ≤ U`,
`‖decMarkCorrBg … um Φ‖ ≤ 4 (B Y / R) (U / R)²` (`norm_taylor1_remainder_le`). -/
theorem norm_decMarkCorrBg_le
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (u.1, T.res u.2)) 0‖ ≤ B Y / t₀)
    (hJ2 : ∀ Y, LabelMargin Gb Y → AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2.1 p.2.2 Y (p.1.1, T.res p.1.2))
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hYm : LabelMargin Gb Y)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps) {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k a₁ κ cψ cc < δ₁) (hUR : 2 * U ≤ R) {um : ℂ}
    (hum : ‖um‖ ≤ U) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ‖ ≤
      4 * (B Y / R) * (U / R) ^ 2 := by
  have hana := analyticOnNhd_deriv_mark (hJ2 Y hYm)
  have hdiff : DifferentiableOn ℂ
      (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ)
      (ball 0 R) := by
    have hc := hana.comp (f := fun v : ℂ => ((Θ, S.hatOf m₀ ρ hp Φ), v))
      (fun _ _ => analyticAt_const.prod analyticAt_id)
      (fun v hv => ⟨⟨hΘ, fun q => (S.hatOf_mem m₀ hρ hp Φ q).trans hρc⟩,
        mem_markedRadiusSet_of_pos hδ hRR (mem_ball_zero_iff.1 hv).le
          (by simpa using hR.le)⟩)
    exact hc.differentiableOn
  have hB : ∀ w ∈ ball (0 : ℂ) R,
      ‖decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ w Φ‖ ≤ B Y / R :=
    fun w hw => norm_decMarkGBg_le S hcau hρ hρc hp hΘ hR.le hR.le hR le_rfl hRR
      (mem_ball_zero_iff.1 hw).le Y hYm Φ
  exact norm_taylor1_remainder_le hR hdiff hB hum hUR

/-- **The fields of the corrected marks on a background generating set.**  From the locality
`hloc`, the Cauchy estimate `hcau` with a bound `B`, the joint analyticity `hJ2` of the terms on
the chart of the step (the datum read on `Gb` is `T.dat` of it) and the analyticity `hJ4` of the derivative marks on `physV`, for `0 < δ₁`:
block locality on the blocks inside every cell-union `Y′ ⊇ Y`; continuity and measurability in the
block configuration; the cubic bound `4 (B Y / R) (U / R)²` for `‖um‖ ≤ U`, `2 U ≤ R`,
`(R + R) · markedRad < δ₁`; analyticity in `(e, um)` on `physV × {‖um‖ < a}`. -/
theorem decMarkCorrBg_fields_of
    {En : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u.1, T.res u.2) =
        evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um tm Y (u'.1, T.res u'.2))
    (hcau : ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm um t Y
          (u.1, T.res u.2)) 0‖ ≤ B Y / t₀)
    (hJ2 : ∀ Y, LabelMargin Gb Y → AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2.1 p.2.2 Y (p.1.1, T.res p.1.2))
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ Y, LabelMargin Gb Y → ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), T.res ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) :
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), LabelMargin Gb Y → Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um)) ∧
      (∀ Y, LabelMargin Gb Y → ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um) ∧
        Measurable (decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um)) ∧
      (∀ Y, LabelMargin Gb Y → ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ R U : ℝ, 0 < R →
        (R + R) * markedRad d L N k a₁ κ cψ cc < δ₁ → 2 * U ≤ R → ∀ um : ℂ, ‖um‖ ≤ U →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ‖ ≤
          4 * (B Y / R) * (U / R) ^ 2) ∧
      (∀ Y, LabelMargin Gb Y → ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 < a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp
            (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y Y' hYm hYY hY' Θ hΘ um hum
    exact decMarkCorrBg_dep S hloc hρ hρc hp hδ hΘ hum hYm hYY hY'
  · intro Y hYm Θ hΘ um hum
    have hW0 : ((0 : ℂ), (0 : ℂ)) ∈ {w : ℂ × ℂ |
        (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} := by
      show (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * _ < δ₁
      simpa using hδ
    have hana := analyticOnNhd_deriv_mark (hJ2 Y hYm)
    have hanaD := analyticOnNhd_deriv_snd hana hW0
    have hmem : ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), (Θ, S.hatOf m₀ ρ hp Φ) ∈
        XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ} :=
      fun Φ => ⟨hΘ, fun q => (S.hatOf_mem m₀ hρ hp Φ q).trans hρc⟩
    have hcm : ∀ w : ℂ, (‖w‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ w) := by
      intro w hw
      have hc := hana.continuousOn.comp
        (f := fun ψ : unitPts S.G' × Fin N → ℂ => ((Θ, ψ), w))
        (by fun_prop) (fun ψ hψ => ⟨⟨hΘ, hψ⟩, hw⟩)
      exact hc.comp_continuous (S.continuous_hatOf m₀ ρ hp)
        (fun Φ q => (S.hatOf_mem m₀ hρ hp Φ q).trans hρc)
    have hD : Continuous (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        deriv (fun v : ℂ => decMarkGBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ)
          0) :=
      hanaD.continuousOn.comp_continuous
        (f := fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) => (Θ, S.hatOf m₀ ρ hp Φ))
        (by have := S.continuous_hatOf m₀ ρ hp; fun_prop) hmem
    have h0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := by simpa using hδ
    have hcont : Continuous
        (decMarkCorrBg S Gb T X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um) := by
      unfold decMarkCorrBg
      exact ((hcm um hum).sub (hcm 0 h0)).sub (continuous_const.mul hD)
    exact ⟨hcont, hcont.measurable⟩
  · intro Y hYm Θ hΘ R U hR hRR hUR um hum Φ
    exact norm_decMarkCorrBg_le S hcau hJ2 hρ hρc hp hδ Y hYm hΘ hR hRR hUR hum Φ
  · intro Y hYm Φ a b ha hb hab
    have hF := hJ4 Y hYm (S.hatOf m₀ ρ hp Φ) (fun q => (S.hatOf_mem m₀ hρ hp Φ q).trans hρc) a b
      ha.le hb hab
    have hD := analyticOnNhd_deriv_snd (A := physV S a₁ ν eps) (S := ball (0 : ℂ) a)
      (g := fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν T cc F₁ Sol En Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), T.res (S.hatOf m₀ ρ hp Φ))) 0)
      hF (mem_ball_self ha)
    have hF0 := hF.comp (f := fun p : physParam N S × ℂ => (p.1, (0 : ℂ)))
      (fun _ _ => analyticAt_fst.prod analyticAt_const)
      (fun p (hp' : p ∈ physV S a₁ ν eps ×ˢ ball (0 : ℂ) a) => ⟨hp'.1, mem_ball_self ha⟩)
    have hDp := hD.comp (f := fun p : physParam N S × ℂ => p.1)
      (fun _ _ => analyticAt_fst)
      (fun p (hp' : p ∈ physV S a₁ ν eps ×ˢ ball (0 : ℂ) a) => hp'.1)
    exact (hF.sub hF0).sub ((show AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => p.2)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a) from fun p _ => analyticAt_snd).mul hDp)

end BlocksBg

section Blocks

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
variable {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
variable {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}

/-- **The corrected decoupled mark.**  The first-order Taylor remainder, in the first mark `um`,
of the block-level decoupled mark `decMarkG … um Φ`:
`f(um) − f(0) − um · f′(0)` with `f = fun v => decMarkG … v Φ` (`decMarkCorrBg` at `Gb = S.G'`
with the transport `BgTransport.self`). -/
noncomputable def decMarkCorr (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts S.G')) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  decMarkCorrBg S S.G' (BgTransport.self S.hG') X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ

/-- The corrected mark is `f(um) − f(0) − um · f′(0)` with `f = fun v => decMarkG … v Φ`. -/
theorem decMarkCorr_eq_decMarkG (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts S.G')) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (ρ : ℝ) (hp : 0 < S.p₁) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ =
      decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ um Φ -
        decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ 0 Φ -
        um * deriv (fun v : ℂ => decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol En Zm Y ρ hp Θ v Φ) 0 :=
  rfl

/-- **Block locality of the corrected mark.**  As `decMarkG_dep`: each of the three summands
depends only on the blocks inside `Y′` (for the derivative, the family in `v` agrees near `v = 0`). -/
theorem decMarkCorr_dep
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hYY : Y ⊆ Y')
    (hY' : ∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') :
    DepOn (blocksOf m₀ (k + 1) Set.univ Y')
      (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
        Zm Y ρ hp Θ um) :=
  decMarkCorrBg_dep S (T := BgTransport.self S.hG') (fun um tm hm Y _ => hP.2.1 um tm hm Y) hρ hρc
    hp hδ hΘ hum (labelMargin_of_isLevel S.hG' Y) hYY hY'

/-- **The fields of the corrected marks, for a given pair.**  The four field conclusions of
`decMarkCorr_fields` for an explicitly given pair `(F₁, Sol)` with its eight clauses `hP`, joint
analyticity on the chart (`hJ2`) and the derivative marks on `physV` (`hJ4`), exactly as
`MarkedEvJointPhysV` provides them. -/
theorem decMarkCorr_fields_of_pair
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
      F₁ Sol)
    (hJ2 : ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) :
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) ∧
        Measurable (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ R U : ℝ, 0 < R →
        (R + R) * markedRad d L N k a₁ κ cψ cc < δ₁ → 2 * U ≤ R → ∀ um : ℂ, ‖um‖ ≤ U →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um Φ‖ ≤
          4 * (energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / R) * (U / R) ^ 2) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 < a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  have h := decMarkCorrBg_fields_of S (T := BgTransport.self S.hG')
    (B := fun Y => energyBdScaled d L N (compWeight L a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
      Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) (fun um tm hm Y _ => hP.2.1 um tm hm Y)
    (fun a b t₀ ha hb ht htb hab um hum Y _ => hP.2.2.2.2.1 a b t₀ ha hb ht htb hab um hum Y)
    (fun Y _ => hJ2 Y) (fun Y _ => hJ4 Y) hρ hρc hp hδ
  exact ⟨fun Y Y' => h.1 Y Y' (labelMargin_of_isLevel S.hG' Y),
    fun Y => h.2.1 Y (labelMargin_of_isLevel S.hG' Y),
    fun Y => h.2.2.1 Y (labelMargin_of_isLevel S.hG' Y),
    fun Y => h.2.2.2 Y (labelMargin_of_isLevel S.hG' Y)⟩

/-- **The fields of the corrected marks.**  For the pair `(F₁, Sol)` of `decMarkG_fields` (from
`MarkedEvJointPhysV`), the clamp radius `0 < ρ ≤ cψ`, and `0 < δ₁`:

* `dep`: block locality on the blocks inside every cell-union `Y′ ⊇ Y`;
* continuity and measurability in the block configuration;
* the cubic bound: for `0 < R` with `(R + R) · markedRad < δ₁`, `‖um‖ ≤ U`, `2 U ≤ R`,
  `‖decMarkCorr … um Φ‖ ≤ 4 (E_* e^{-2 κ_dec d^cov(Y)} / R) (U / R)²` for every `Φ`;
* analyticity in `(e, um)` on `physV × {‖um‖ < a}` (`a, b > 0`, `(a + b) · markedRad < δ₁`). -/
theorem decMarkCorr_fields
    (hM : MarkedEvJointPhysV S Hm cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) :
    ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) ∧
        Measurable (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ R U : ℝ, 0 < R →
        (R + R) * markedRad d L N k a₁ κ cψ cc < δ₁ → 2 * U ≤ R → ∀ um : ℂ, ‖um‖ ≤ U →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um Φ‖ ≤
          4 * (energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / R) * (U / R) ^ 2) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 < a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  obtain ⟨F₁, Sol, hP, hJ2, -, hJ4, -, -⟩ := hM
  exact ⟨F₁, Sol, decMarkCorr_fields_of_pair S F₁ Sol hP hJ2 hJ4 hρ hρc hp hδ⟩

end Blocks
end Balaban.Fluctuation
