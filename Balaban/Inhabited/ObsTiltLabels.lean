/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsTiltFamily
public import Balaban.Inhabited.ObsMarksFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable activity family on the observable label system

`Balaban.Inhabited.ObsTiltFamily` builds the physical activity `physAct A e t` and its tilt
`tiltAct` as one family analytic in the datum, the source and the ray variables, on the labels
`Lab.sum Lab`.  The landed per-source observable record uses the observable labels
`obsLab (Lab.sum Lab) hdj`, reached by two extensions by zero (`LabelAct.extendZero`).  Here the
extension is a function of the parameter.

* `physActObs`, `tiltActObs`: the extension of `physAct A e t` to `obsLab` (two `extendZero`
  steps, then `mono` to a larger entropy constant) and its scalar tilt.
* `physActObs_total`, `physActObs_analyticOnNhd`, `physActObs_differentiableOn`,
  `tiltActObs_analyticOnNhd`, `tiltActObs_fields`: the label sum, the analyticity in `(e, t)` and
  `(e, t, σ)` and the fields of the consumer, for every parameter.
* `tiltActObs_holA`, `tiltActObs_continuous`: the activity fields `holA` and `contA` of a
  parameter family, for the activity `fun θ t => tiltActObs θ t 1`.
* `obsTiltLabels_fromTower`: at the shared tower, one null set outside of which the label sum of
  the extended family is `W₁(1) + W₂(g, t)` for every datum of the fibre and every source, the
  analyticity, the activity fields of a parameter family on the carrier `physCarrier`, and, for a
  fixed source in the ball, the four fields `holt`, `holσ`, `zero`, `hW` of `ObsMarks` for the
  tilt at the radius `obsRg`.
-/

@[expose] public section

namespace Balaban.Inhabited

open MeasureTheory Metric Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer
  Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization.LevelPair
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

section Generic

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {Lb : Type} [Fintype Lb]
variable {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ Lb} {εH κH κ0 Kc : ℝ}
  {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ → Type}
  [∀ b, MeasurableSpace (Ωb b)] {E₁ E₂ : Type*}

/-- **The physical activity of the observable on the observable labels, as a function of the
parameter.**  The extension of `physAct A e t` by zero to the labels of the domains `𝒴obs` and of
the single cubes (the two steps of `exists_obsExtend`), with the entropy constant raised to any
`Kobs ≥ (Kc + Kc) + K₀ + K₀`. -/
noncomputable def physActObs [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (hN : L ^ m₀ ∣ N₁) (hκ0 : aEnt d L + 1 ≤ κ0) (hεH : 0 ≤ εH)
    {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y)
    {Kobs : ℝ} (hK : Kc + Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs) (e : E₁ × E₂) (t : ℂ) :
    LabelAct (obsLab (Lab.sum Lab) hdj) Ωb (max (εH + εH) εH) κH κ0 Kobs :=
  ((((physAct A e t).extendZero (thickLabels 𝒴obs hdj) (le_max_of_le_right hεH) (K0 d L κ0)
    (entropy_thick (m₁ := m₁) (j := k + 1) (m₀ := m₀) hN le_rfl 𝒴obs hdj hκ0)).extendZero
    (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1))
    (le_max_of_le_right hεH) (K0 d L κ0)
    (cubeLabels_entropy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (m₀ := m₀) (j := k + 1) hN le_rfl hκ0)).mono (le_max_of_le_right hεH) le_rfl le_rfl le_rfl
    hK)

/-- **The tilted activity of the observable on the observable labels**: the scalar tilt
`obsScalarTilt` of `physActObs A … e`. -/
noncomputable def tiltActObs [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (hN : L ^ m₀ ∣ N₁) (hκ0 : aEnt d L + 1 ≤ κ0) (hεH : 0 ≤ εH)
    {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y)
    {Kobs : ℝ} (hK : Kc + Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)
    (𝒰 : Set ℂ) (e : E₁ × E₂) (t σ : ℂ) :
    LabelAct (obsLab (Lab.sum Lab) hdj) Ωb (Rg * max (εH + εH) εH) κH κ0 Kobs :=
  obsScalarTilt Rg hR 𝒰 (physActObs A hN hκ0 hεH hdj hK e) t σ

section Values

variable [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
  (hN : L ^ m₀ ∣ N₁) (hκ0 : aEnt d L + 1 ≤ κ0) (hεH : 0 ≤ εH)
  {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs)

/-- On the labels of `Lab.sum Lab` the extended activity is `physAct`. -/
theorem physActObs_H_inl (e : E₁ × E₂) (t : ℂ) (y : Lb ⊕ Lb) (Φ : ∀ b, Ωb b) :
    (physActObs A hN hκ0 hεH hdj hK e t).H (Sum.inl (Sum.inl y)) Φ = (physAct A e t).H y Φ :=
  rfl

/-- On the new labels the extended activity vanishes. -/
theorem physActObs_H_new (e : E₁ × E₂) (t : ℂ) (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs)
    (hy : ∀ z, y ≠ Sum.inl (Sum.inl z)) (Φ : ∀ b, Ωb b) :
    (physActObs A hN hκ0 hεH hdj hK e t).H y Φ = 0 := by
  rcases y with (z | z) | z
  · exact absurd rfl (hy z)
  · rfl
  · rfl

/-- **The label sum is unchanged by the extension to the observable labels.** -/
theorem physActObs_total (e : E₁ × E₂) (t : ℂ) (Φ : ∀ b, Ωb b) :
    ∑ y, (physActObs A hN hκ0 hεH hdj hK e t).H y Φ = ∑ y, (physAct A e t).H y Φ :=
  (LabelAct.extendZero_total _ _ (le_max_of_le_right hεH) _
    (cubeLabels_entropy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (m₀ := m₀) (j := k + 1) hN le_rfl hκ0) Φ).trans
    (LabelAct.extendZero_total _ _ (le_max_of_le_right hεH) _
      (entropy_thick (m₁ := m₁) (j := k + 1) (m₀ := m₀) hN le_rfl 𝒴obs hdj hκ0) Φ)

theorem tiltActObs_H (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ) (e : E₁ × E₂) (t σ : ℂ)
    (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs) (Φ : ∀ b, Ωb b) :
    (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 e t σ).H y Φ =
      obsTiltFactor Rg 𝒰 t σ * (physActObs A hN hκ0 hεH hdj hK e t).H y Φ := rfl

/-- The tilt at `σ = 1` has the same label sum as `physAct`, for `t ∈ 𝒰` and `1 < Rg`. -/
theorem tiltActObs_total_one {Rg : ℝ} (hR : 0 ≤ Rg) (hRg : 1 < Rg) {𝒰 : Set ℂ} {t : ℂ}
    (ht : t ∈ 𝒰) (e : E₁ × E₂) (Φ : ∀ b, Ωb b) :
    ∑ y, (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 e t 1).H y Φ =
      ∑ y, (physAct A e t).H y Φ := by
  rw [← physActObs_total A hN hκ0 hεH hdj hK e t Φ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [tiltActObs_H, obsTiltFactor_of_mem ht (by simpa using hRg), one_mul]

end Values

section Analytic

variable [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  {A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {V : Set (E₁ × E₂)} {R : ℝ}
  {hN : L ^ m₀ ∣ N₁} {hκ0 : aEnt d L + 1 ≤ κ0} {hεH : 0 ≤ εH}
  {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y}
  {Kobs : ℝ} {hK : Kc + Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs}

/-- **Joint analyticity of the extended physical activity** in `(e, t)` on `V × ball 0 R`. -/
theorem physActObs_analyticOnNhd (hR : 1 < R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs) (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ
      (fun r : (E₁ × E₂) × ℂ => (physActObs A hN hκ0 hεH hdj hK r.1 r.2).H y Φ)
      (V ×ˢ ball (0 : ℂ) R) := by
  rcases y with (y | y) | y
  · exact physAct_analyticOnNhd hR hsub h y Φ
  · exact analyticOnNhd_const (v := (0 : ℂ))
  · exact analyticOnNhd_const (v := (0 : ℂ))

/-- Holomorphy in `t` of the extended physical activity at a fixed parameter `e ∈ V`. -/
theorem physActObs_differentiableOn (hR : 1 < R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    {e : E₁ × E₂} (he : e ∈ V) (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs) (Φ : ∀ b, Ωb b) :
    DifferentiableOn ℂ (fun t : ℂ => (physActObs A hN hκ0 hεH hdj hK e t).H y Φ)
      (ball (0 : ℂ) R) := by
  have hι : AnalyticOnNhd ℂ (fun t : ℂ => ((e, t) : (E₁ × E₂) × ℂ)) Set.univ :=
    (analyticOnNhd_const (v := e)).prod analyticOnNhd_id
  exact ((physActObs_analyticOnNhd (hN := hN) (hκ0 := hκ0) (hεH := hεH) (hdj := hdj) (hK := hK)
    hR hsub h y Φ).comp (hι.mono (Set.subset_univ _)) (fun t ht => ⟨he, ht⟩)).differentiableOn

/-- **Joint analyticity of the tilted extended activity** in `(e, t, σ)` on
`V × (𝒰 × ball 0 Rg)`, for an open `V` and an open `𝒰 ⊆ ball 0 R`. -/
theorem tiltActObs_analyticOnNhd {Rg : ℝ} (hRg : 0 ≤ Rg) {𝒰 : Set ℂ} (hR : 1 < R)
    (hV : IsOpen V) (h𝒰 : IsOpen 𝒰) (h𝒰R : 𝒰 ⊆ ball (0 : ℂ) R)
    (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs) (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ × ℂ =>
      (tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 r.1 r.2.1 r.2.2).H y Φ)
      (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg)) := by
  have hM : AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ × ℂ => ((r.1, r.2.1) : (E₁ × E₂) × ℂ))
      Set.univ :=
    ((ContinuousLinearMap.fst ℂ (E₁ × E₂) (ℂ × ℂ)).prod
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (E₁ × E₂) (ℂ × ℂ)))
        ).analyticOnNhd _
  have h1 := (physActObs_analyticOnNhd (hN := hN) (hκ0 := hκ0) (hεH := hεH) (hdj := hdj)
    (hK := hK) hR hsub h y Φ).comp
    (hM.mono (Set.subset_univ (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg))))
    (fun r hr => ⟨hr.1, h𝒰R hr.2.1⟩)
  have hσ : AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ × ℂ => r.2.2)
      (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg)) :=
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ (E₁ × E₂) (ℂ × ℂ))).analyticOnNhd _)
  refine (hσ.mul h1).congr (hV.prod (h𝒰.prod isOpen_ball)) fun r hr => ?_
  have hσn : ‖r.2.2‖ < Rg := by simpa using hr.2.2
  show r.2.2 * (physActObs A hN hκ0 hεH hdj hK r.1 r.2.1).H y Φ = obsTiltFactor Rg 𝒰 r.2.1 r.2.2 * _
  rw [obsTiltFactor_of_mem hr.2.1 hσn]

/-- **The fields of the consumer, uniformly in the parameter**: for every `e ∈ V` the tilted
extended activity is holomorphic in `t ∈ 𝒰` at `σ = 1`, holomorphic in `σ` on the disc, and
vanishes at `σ = 0`. -/
theorem tiltActObs_fields {Rg : ℝ} (hRg : 0 ≤ Rg) (hRg1 : 1 < Rg) {𝒰 : Set ℂ}
    (hR : 1 < R) (h𝒰R : 𝒰 ⊆ ball (0 : ℂ) R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    {e : E₁ × E₂} (he : e ∈ V) :
    (∀ y Φ, DifferentiableOn ℂ
      (fun t => (tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 e t 1).H y Φ) 𝒰) ∧
    (∀ t ∈ 𝒰, ∀ y Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 e t σ).H y Φ) (ball (0 : ℂ) Rg)) ∧
    (∀ t y Φ, (tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 e t 0).H y Φ = 0) :=
  ⟨obsScalarTilt_holt hRg1 fun y Φ =>
      (physActObs_differentiableOn (hN := hN) (hκ0 := hκ0) (hεH := hεH) (hdj := hdj) (hK := hK)
        hR hsub h he y Φ).mono h𝒰R,
    fun _ ht => obsScalarTilt_holσ (Aphys := physActObs A hN hκ0 hεH hdj hK e) ht,
    fun t y Φ => obsScalarTilt_zero (Aphys := physActObs A hN hκ0 hεH hdj hK e) t y Φ⟩

/-! ### The activity fields of a parameter family -/

/-- **`holA` of a parameter family**, for the activity `fun θ t => tiltActObs θ t 1`: the
coefficients are analytic in `(θ, t)` on `V × 𝒰`. -/
theorem tiltActObs_holA {Rg : ℝ} (hRg : 0 ≤ Rg) (hRg1 : 1 < Rg) {𝒰 : Set ℂ} (hR : 1 < R)
    (hV : IsOpen V) (h𝒰 : IsOpen 𝒰) (h𝒰R : 𝒰 ⊆ ball (0 : ℂ) R)
    (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (h : ∀ (y : Lb) (Φ : ∀ b, Ωb b),
      AnalyticOnNhd ℂ (fun r : (E₁ × E₂) × ℂ => (A r.1 r.2).H y Φ) (V ×ˢ ball (0 : ℂ) R))
    (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs) (Φ : ∀ b, Ωb b) :
    AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ =>
      (tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 p.1 p.2 1).H y Φ) (V ×ˢ 𝒰) := by
  have hM1 : AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => p.1) Set.univ :=
    ((ContinuousLinearMap.fst ℂ (E₁ × E₂) ℂ).analyticOnNhd _)
  have hM2 : AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => p.2) Set.univ :=
    ((ContinuousLinearMap.snd ℂ (E₁ × E₂) ℂ).analyticOnNhd _)
  have hM : AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => ((p.1, p.2, (1 : ℂ)) :
      (E₁ × E₂) × ℂ × ℂ)) Set.univ :=
    hM1.prod (hM2.prod analyticOnNhd_const)
  have hmem : ∀ p ∈ V ×ˢ 𝒰, ((p.1, p.2, (1 : ℂ)) : (E₁ × E₂) × ℂ × ℂ) ∈
      V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg) := fun p hp =>
    Set.mk_mem_prod hp.1 (Set.mk_mem_prod hp.2 (by simpa using hRg1))
  have key : ∀ G : (E₁ × E₂) × ℂ × ℂ → ℂ, AnalyticOnNhd ℂ G (V ×ˢ (𝒰 ×ˢ ball (0 : ℂ) Rg)) →
      AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => G (p.1, p.2, (1 : ℂ))) (V ×ˢ 𝒰) :=
    fun G hG => hG.comp (hM.mono (Set.subset_univ _)) hmem
  have hT := tiltActObs_analyticOnNhd (hN := hN) (hκ0 := hκ0) (hεH := hεH) (hdj := hdj)
    (hK := hK) hRg hR hV h𝒰 h𝒰R hsub h y Φ
  exact key (fun r => (tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 r.1 r.2.1 r.2.2).H y Φ) hT

variable [∀ b, TopologicalSpace (Ωb b)]

omit [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedSpace ℂ E₂] in
/-- Continuity in the configuration of the physical activity. -/
theorem physAct_continuous (hR : 1 < R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (hc : ∀ e ∈ V, ∀ u : ℂ, ‖u‖ < R → ∀ y : Lb, Continuous ((A e u).H y))
    {e : E₁ × E₂} (he : e ∈ V) {t : ℂ} (ht : ‖t‖ < R) (y : Lb ⊕ Lb) :
    Continuous ((physAct A e t).H y) := by
  rcases y with y | y
  · have : (physAct A e t).H (Sum.inl y) =
        fun Φ => (A (e.1, 0) 1).H y Φ - (A (e.1, 0) t).H y Φ :=
      funext fun Φ => physAct_H_inl A e t y Φ
    rw [this]
    exact (hc _ (hsub e he) 1 (by simpa using hR) y).sub (hc _ (hsub e he) t ht y)
  · exact hc e he t ht y

omit [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedSpace ℂ E₂] in
/-- **`contA` of a parameter family**: continuity in the block configuration of each coefficient
of the tilted extended activity, for `θ ∈ V` and `t ∈ 𝒰`.  Then continuity on any set, in
particular on the carrier `physCarrier`, follows (`Continuous.continuousOn`). -/
theorem tiltActObs_continuous {Rg : ℝ} (hRg : 0 ≤ Rg) {𝒰 : Set ℂ} (hR : 1 < R)
    (h𝒰R : 𝒰 ⊆ ball (0 : ℂ) R) (hsub : ∀ e ∈ V, (e.1, (0 : E₂)) ∈ V)
    (hc : ∀ e ∈ V, ∀ u : ℂ, ‖u‖ < R → ∀ y : Lb, Continuous ((A e u).H y))
    {e : E₁ × E₂} (he : e ∈ V) {t : ℂ} (ht : t ∈ 𝒰) (σ : ℂ)
    (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs) :
    Continuous ((tiltActObs A hN hκ0 hεH hdj hK Rg hRg 𝒰 e t σ).H y) := by
  have hbase : Continuous ((physActObs A hN hκ0 hεH hdj hK e t).H y) := by
    have ht' : ‖t‖ < R := by simpa using h𝒰R ht
    rcases y with (y | y) | y
    · exact physAct_continuous hR hsub hc he ht' y
    · exact continuous_const
    · exact continuous_const
  exact continuous_const.mul hbase

end Analytic

end Generic

section Tower

open Set

/-- **Locality of the activity family in the datum and the source, with the activity family of
`obsTiltLabels_fromTower`.**  The statement of `obsTiltLabels_fromTower` with two locality
clauses for the same activity `A`: raw agreement on `thickSet S.G' Z`, and raw agreement on `Z`
itself. In both cases source agreement on `Z` gives equality of the activities of labels whose
sites lie in `Z`, at the zero-source parameters and at `e, e'`, for every complex `u`. -/
theorem obsTiltLabels_local_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s Θ : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hΘ : 0 < Θ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 3 3 T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
          ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
          agreeOn (thickSet S.G' Z) (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
            (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
          ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
            (A ((e.1, 0) : physParam 2 S) u).H w = (A ((e'.1, 0) : physParam 2 S) u).H w ∧
            (A e u).H w = (A e' u).H w) ∧
        (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
          ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
          agreeOn Z (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
            (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
          ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
            (A ((e.1, 0) : physParam 2 S) u).H w = (A ((e'.1, 0) : physParam 2 S) u).H w ∧
            (A e u).H w = (A e' u).H w) ∧
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          ∀ {𝒴obs : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))}
            (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y) {Kobs : ℝ}
            (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs),
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (physActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
            Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit 1 hp).restr x)) ∧
        ∀ {𝒴obs : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))}
          (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y) {Kobs : ℝ}
          (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs),
        (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
            (physActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              r.1 r.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ × ℂ =>
            (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVq S S.a₁ S.ν T.t q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
              hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
              hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ) (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
            hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
            (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2))) ∧
          (∀ y, ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
            ContinuousOn ((tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
              hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y)
              (physCarrier S 1 hp))) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q →
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤ Θ ∧
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
            (∀ y Φ, DifferentiableOn ℂ
              (fun t => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) t 1).H y Φ)
              (ball (0 : ℂ) (3 / 2))) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ y Φ, DifferentiableOn ℂ
              (fun σ => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) σ).H y Φ)
              (ball (0 : ℂ) (obsRg CR s (p : ℝ) (β * 3 ^ k)))) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ y Φ,
              (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) 0).H y Φ = 0) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x =
              ∑ y, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) 1).H y
                ((S.blockSplit 1 hp).restr x))) := by
  classical
  obtain ⟨β₁, CE, CF, hβ₁, hCE, hCF, hfam⟩ := activityFamilyAnalytic_fromTower T hA p
  obtain ⟨b₀, hb₀, hb⟩ := obsTilt_of_physAct.{0} (CR := CR) (CU := CE + CF) (s := s)
    (p := (p : ℝ)) (Θ := Θ) hCR (by positivity) hs0 hs hΘ
  refine ⟨max (max β₁ b₀) 3, CE, CF, le_max_right _ _, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp Kc hKc
  have hβ₁' : β₁ ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hβb₀ : b₀ ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hβ3 : 3 ≤ β := le_trans (le_max_right _ _) hβ
  have hH : BgHyp 3 3 (k + 1) (rhoSep T.m₁) (compWeight 3 S.a₁) S.ν := by
    subst hS
    exact bgHyp_lv (k := k) T.m₁ hνpos.le hν
  have hXi : XiCData S.G' S.a S.ν (k + 1) 1 T.t S.D' := by
    subst hS
    exact D.xi
  obtain ⟨Jr, val, 𝒴, Tt, I, -, -, -, -, -, -, hF, hεU, hεpos, hε4, hrest⟩ :=
    hfam k hk N₁ h3N hN ν hνpos hν β hβ₁' p₁ hp0 hp₁ q hq0 hq D S hS hp
  obtain ⟨A, hAeq, hhol, hcont, -, -, -, -, h7, h8, -, -, -, -⟩ := hrest hKc
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hsub : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ((e.1, 0) : physParam 2 S) ∈
      physVq S S.a₁ S.ν T.t q := fun e he =>
    fst_zero_mem_physVq S (physVq_subset S _ _ _ _ he) hq0
  have hV := isOpen_physVq S S.a₁ S.ν T.t q hH
  have h𝒰R : ball (0 : ℂ) (3 / 2) ⊆ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num)
  have hR2 : (1 : ℝ) < 2 := by norm_num
  have hseg : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → (r : ℂ) ∈ ball (0 : ℂ) (3 / 2) := fun r hr => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    linarith [hr.2]
  -- the identity with the physical activity, from the two fibre identities of the family
  have hae : ∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
      (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
        (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
      ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
        ((S.blockSplit 1 hp).restr x) := by
    filter_upwards [h7, h8] with x hx7 hx8
    intro D' hDh hX g hg t ht
    have e7 := hx7 D' hDh hX 1 ⟨zero_le_one, le_rfl⟩
    have e8 := hx8 D' hDh hX g hg t ht
    simp only [Complex.ofReal_one, one_pow, one_mul] at e7
    rw [physAct_total]
    dsimp only
    rw [e7, e8]
    ring
  -- the amplitude
  have hb1 : (1 : ℝ) ≤ β * 3 ^ k := by
    have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hbe : Real.exp 1 ≤ β * 3 ^ k := by
    have := Real.exp_one_lt_three
    have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hbb : b₀ ≤ β * 3 ^ k := by
    have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hlog : 0 ≤ Real.log (β * 3 ^ k) := Real.log_nonneg hb1
  have hsq : 0 ≤ Real.sqrt (β * 3 ^ k) := Real.sqrt_nonneg _
  have hamp : 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
      CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    linarith
  have hεH : 0 < 2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) := by linarith
  have hCFle : q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ≤
      CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    refine div_le_div_of_nonneg_right ?_ hsq
    have h0 : 0 ≤ CF * (Real.log (β * 3 ^ k)) ^ p := mul_nonneg hCF.le (pow_nonneg hlog p)
    calc q * CF * (Real.log (β * 3 ^ k)) ^ p = q * (CF * (Real.log (β * 3 ^ k)) ^ p) := by ring
      _ ≤ 1 * (CF * (Real.log (β * 3 ^ k)) ^ p) := mul_le_mul_of_nonneg_right hq h0
      _ = _ := one_mul _
  have hεb : max (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) + 2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
      (CE + CF) * obsW (p : ℝ) (β * 3 ^ k) ^ 3 / Real.sqrt (β * 3 ^ k) := by
    rw [max_add_self_eq hεH.le]
    exact obs_eps_le_tilt_form hCF.le hbe (hamp.trans (by linarith))
  have hloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
      agreeOn (thickSet S.G' Z) (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : {Y // Y ∈ I.𝒴}), (thickLabels I.𝒴 I.dom).ysite w ⊆ Z →
        (A ((e.1, 0) : physParam 2 S) u).H w = (A ((e'.1, 0) : physParam 2 S) u).H w ∧
        (A e u).H w = (A e' u).H w := by
    intro e he e' he' Z hr hg u w hw
    subst hAeq
    have hag : ∀ (e₁ e₂ : physParam 2 S), agreeOn (thickSet S.G' w.1)
        (e₁.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (e₂.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
        (∀ x ∈ w.1, e₁.2 x = e₂.2 x) → ∀ Y ∈ I.𝒴, Y ⊆ w.1 →
        physAgΘ S Y (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e₁)
          (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e₂) := fun e₁ e₂ h1 h2 Y _ hY =>
      ⟨agreeOn_mono (fun x hx => thickSet_mono hY (Or.inl hx)) h1, fun x hx => by
        simp [physInclScaled_apply, h2 x (hY hx)]⟩
    exact ⟨labelActFamilyOn_local S 1 _ hF hN3 hp0 (by norm_num) hεU T.κ0_ent hKc
        (hsub e he) (hsub e' he') w.1
        (hag _ _ (agreeOn_mono (thickSet_mono hw) hr) (fun _ _ => rfl)) u w subset_rfl,
      labelActFamilyOn_local S 1 _ hF hN3 hp0 (by norm_num) hεU T.κ0_ent hKc he he' w.1
        (hag _ _ (agreeOn_mono (thickSet_mono hw) hr) (fun x hx => hg x (hw hx))) u w subset_rfl⟩
  have hlocExact : ∀ e ∈ physVq S S.a₁ S.ν T.t q,
      ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
      agreeOn Z (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
      (∀ x ∈ Z, e.2 x = e'.2 x) → ∀ (u : ℂ) (w : {Y // Y ∈ I.𝒴}),
      (thickLabels I.𝒴 I.dom).ysite w ⊆ Z →
        (A ((e.1, 0) : physParam 2 S) u).H w =
          (A ((e'.1, 0) : physParam 2 S) u).H w ∧
        (A e u).H w = (A e' u).H w := by
    intro e he e' he' Z hr hg u w hw
    subst hAeq
    have hag : ∀ (e₁ e₂ : physParam 2 S), agreeOn w.1
        (e₁.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e₂.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
        (∀ x ∈ w.1, e₁.2 x = e₂.2 x) → ∀ Y ∈ I.𝒴, Y ⊆ w.1 →
        physAgΘ S Y (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e₁)
          (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e₂) :=
      fun e₁ e₂ h1 h2 Y _ hY =>
        ⟨agreeOn_mono hY h1, fun x hx => by
          simp [physInclScaled_apply, h2 x (hY hx)]⟩
    exact ⟨labelActFamilyOn_local S 1 _ hF hN3 hp0 (by norm_num) hεU T.κ0_ent hKc
        (hsub e he) (hsub e' he') w.1
        (hag _ _ (agreeOn_mono hw hr) (fun _ _ => rfl)) u w subset_rfl,
      labelActFamilyOn_local S 1 _ hF hN3 hp0 (by norm_num) hεU T.κ0_ent hKc
        he he' w.1 (hag _ _ (agreeOn_mono hw hr) (fun x hx => hg x (hw hx)))
        u w subset_rfl⟩
  refine ⟨_, inferInstance, _, _, hεH, A, hloc, hlocExact, hamp, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    intro D' hDh hX g hg t ht 𝒴obs hdj Kobs hK
    have hphys := hx D' hDh hX g hg t ht
    refine ⟨?_, fun Rg hR hRg => ?_⟩
    · rw [physActObs_total]
      exact hphys
    · rw [tiltActObs_total_one A hN3 T.κ0_ent (by linarith) hdj hK hR hRg
        (norm_ofReal_lt_of_mem ht (by norm_num : (1 : ℝ) < 3 / 2) |> fun h => by simpa using h)]
      exact hphys
  · intro 𝒴obs hdj Kobs hK
    refine ⟨fun y Φ => physActObs_analyticOnNhd hR2 hsub hhol y Φ,
      fun Rg hR y Φ => tiltActObs_analyticOnNhd hR hR2 hV isOpen_ball h𝒰R hsub hhol y Φ,
      fun Rg hR hRg e he => tiltActObs_fields hR hRg hR2 h𝒰R hsub hhol he, ?_, ?_⟩
    · intro Rg hR hRg
      exact ⟨fun y Φ _ => tiltActObs_holA hR hRg hR2 hV isOpen_ball h𝒰R hsub hhol y Φ,
        fun y θ hθ u hu => (tiltActObs_continuous hR hR2 h𝒰R hsub
          (fun e he u hu => hcont e he u (by simpa using hu)) hθ hu 1 y).continuousOn⟩
    · intro g hg
      have he0 : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
          physVq S S.a₁ S.ν T.t q :=
        ⟨(mk_mem_physFibre S S.hh₀ hXi (g := g) (lt_of_lt_of_le hg hq)).1, hg⟩
      exact hb (β * 3 ^ k) hbb (S.blockSplit 1 hp) _
        (physActObs A hN3 T.κ0_ent hεH.le hdj hK ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ :
          rawSub 2 S.G'), g)) (ball (0 : ℂ) (3 / 2))
        (fun r x => S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
          S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x)
        hεb hseg
        (fun y Φ => (physActObs_differentiableOn hR2 hsub hhol he0 y Φ).mono h𝒰R)
        (fun r hr => hae.mono fun x hx => by
          rw [physActObs_total]
          exact hx S.D' S.hh₀ hXi g hg r hr)



/-- **The observable activity family on the observable labels, at the shared tower.**  For the
tower `T`, `A₁, p`, `C_R, s` and `Θ > 0` there are `β₀, C_E, C_F` such that at every admissible
scale (`q ≤ 1`, `Kc ≥ K₀`) the family `A` of `obsTiltFamily_fromTower` has the amplitude `εH > 0`
with `2 εH ≤ C_E ℓ^{3p}/√b + q C_F ℓ^p/√b`, and, for every choice of domains `𝒴obs` (with `IsDj`)
and entropy constant `Kobs ≥ 2 Kc + 2 K₀`, the extension `physActObs` to the observable labels and
its tilt `tiltActObs` satisfy:

* one null set outside of which, for every datum `D'` of the fibre `h ≡ h₀`, every source with
  `‖g‖₁ < q` and every `t ∈ [0,1]`, `W₁(1) + W₂(g, t)` of `S.withDatum D'` is the label sum of
  `physActObs … (rawOf D', g) t` and (for `1 < Rg`) of `tiltActObs … (rawOf D', g) t 1`;
* joint analyticity of `physActObs` in `(e, t)` on `physVq × ball 0 2` and of `tiltActObs` in
  `(e, t, σ)` on `physVq × (ball 0 (3/2) × ball 0 Rg)`;
* for every `e` of the chart, `1 < Rg`: holomorphy in `t` at `σ = 1`, holomorphy in `σ`, vanishing
  at `σ = 0`;
* `holA` and `contA` of a parameter family for the activity `fun θ t => tiltActObs θ t 1`, with
  `V = physVq`, `𝒰 = ball 0 (3/2)` and the carrier `physCarrier S 1 hp`;
* for a fixed source `g` with `‖g‖₁ < q` and the datum `S.D'` of the step: with
  `b = β 3^k`, `1 < obsRg CR s p b`, `obsRg CR s p b · 2 εH ≤ Θ`, and the four fields `holt`,
  `holσ`, `zero`, `hW` of `ObsMarks` for the activity `tiltActObs … (obsRg …) … (rawOf S.D', g)`
  and the exponent `S.WoneC C 1 + S.WtwoC C g r`. -/
theorem obsTiltLabels_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s Θ : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hΘ : 0 < Θ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 3 3 T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          ∀ {𝒴obs : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))}
            (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y) {Kobs : ℝ}
            (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs),
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (physActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
            Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit 1 hp).restr x)) ∧
        ∀ {𝒴obs : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))}
          (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y) {Kobs : ℝ}
          (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs),
        (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
            (physActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              r.1 r.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ × ℂ =>
            (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVq S S.a₁ S.ν T.t q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
              hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
              hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ) (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
            hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
            (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2))) ∧
          (∀ y, ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
            ContinuousOn ((tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
              hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y)
              (physCarrier S 1 hp))) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q →
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤ Θ ∧
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
            (∀ y Φ, DifferentiableOn ℂ
              (fun t => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) t 1).H y Φ)
              (ball (0 : ℂ) (3 / 2))) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ y Φ, DifferentiableOn ℂ
              (fun σ => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) σ).H y Φ)
              (ball (0 : ℂ) (obsRg CR s (p : ℝ) (β * 3 ^ k)))) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ y Φ,
              (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) 0).H y Φ = 0) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x =
              ∑ y, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) 1).H y
                ((S.blockSplit 1 hp).restr x))) := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsTiltLabels_local_fromTower T hA p hCR hs0 hs hΘ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    D S hS hp Kc hKc => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, -, -, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0
    hp₁ q hq0 hq1 D S hS hp hKc
  exact ⟨Lb, instLb, Lab, εH, hεH, A, hrest⟩

end Tower

end Balaban.Inhabited
