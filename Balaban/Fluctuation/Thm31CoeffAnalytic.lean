/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesHolo
public import Balaban.Polymer.MarkedHoloParam
public import Balaban.Fluctuation.Thm31CoeffA
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analyticity in a finite-dimensional parameter of `P(S)`, `G*(Y₀, S)` and `gsumCoeff`

Several-parameter form of `Pst_Gst_differentiableOn`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Holo

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- **Analyticity of `P(S)` and `G*(Y₀, S)` in a finite-dimensional parameter `u ∈ V`**
(several-parameter form of `Pst_Gst_differentiableOn`).  The label activities `(A u).H` and the
mark `G u` are analytic in `u ∈ V` for each configuration `Φ` of a compact set `Q` carrying the
product measure, and continuous on `Q` for each `u`; the hypotheses of `marked_cubes` hold for
every `u` with the same constants. -/
theorem Pst_Gst_analyticOnNhd {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    {V : Set E} (hV : IsOpen V) {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (A : E → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : E → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ u, Measurable (G u))
    (hG : ∀ u Φ, ‖G u Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hAhol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun u => (A u).H y Φ) V)
    (hGhol : ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun u => G u Φ) V)
    (hAcont : ∀ y, ∀ u ∈ V, ContinuousOn ((A u).H y) Q)
    (hGcont : ∀ u ∈ V, ContinuousOn (G u) Q)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (Y : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun u => Pst μ Lab (A u).H Y) V ∧
      AnalyticOnNhd ℂ (fun u => Gst μ Lab (A u).H (blocksOf m₀ j Ω (Lab.ysite y0)) (G u) Y) V := by
  set S0 := blocksOf m₀ j Ω (Lab.ysite y0) with hS0
  set r0 := εH * Kc * Real.exp (κ0 * Lab.dl y0) / F0 with hr0
  have hKgeo : 0 < K0 d L κ0 := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hKc1 : 1 ≤ Kc := by linarith
  have hKc0 : 0 ≤ Kc := by linarith
  have hc1 := one_le_c1 d L
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have haent := aEnt_nonneg d L
  have hκ0nn : 0 ≤ κ0 := by linarith
  have hκHge : κ0 ≤ κH := by linarith
  have hκ1nn : 0 ≤ κH - 2 * κ0 := by linarith
  have hκGnn : 0 ≤ κG := by linarith
  have hr0pos : 0 < r0 := by positivity
  obtain ⟨hα1, hq, hH0log⟩ := numerics_PE hεpos hKc1 hc1 hcG hκ' hκ1nn hε
  have hexp_le : ∀ (κ x : ℝ), 0 ≤ κ → 0 ≤ x → Real.exp (-κ * x) ≤ 1 := fun κ x hκ hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  have hGC : ∀ u Φ, ‖G u Φ‖ ≤ F0 := fun u Φ => (hG u Φ).trans (by
    have := hexp_le κG (Lab.dl y0) hκGnn (Lab.dl_nonneg y0)
    nlinarith)
  have hG2c := fun b : 𝔅 => (sum_exp_dExt_le hN hj b hκ0).trans hKc
  have hG3T : ∀ C : Finset (NePoly 𝔅), ConnSet (Subtype.val : NePoly 𝔅 → Finset 𝔅) C →
      dExt (unionCs (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) ≤
        ∑ t ∈ C, dExt t.1 + cG d L * ((C.card : ℝ) - 1) := fun C hC => dExt_unionCs_le C hC
  have hG1 : ∀ Y : NePoly 𝔅, (Y.1.card : ℝ) ≤ c1 d L * (1 + dExt Y.1) :=
    fun Y => card_le_dExt hN hj Y.1
  have hκ1 : κ' + κ0 + c1 d L ≤ (κH - 2 * κ0) - 3 / 2 := by linarith
  have hH0 : 0 ≤ 2 * εH * Kc := by positivity
  have hKP := marked_kp (B := 𝔅) (d := dExt) (c1 := c1 d L) (κ' := κ') (κ0P := κ0) (K0P := Kc)
    (cP := cG d L) (κ1 := κH - 2 * κ0)
    (ε := 2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L)
    (by positivity) (fun Y => dExt_nonneg Y) hG1 (fun b => by convert hG2c b) hκ1 hα1
  -- the per-`u` data
  have hdat : ∀ u, (∀ Z : NePoly 𝔅, AnalyticOnNhd ℂ
        (marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z)
        (Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ => r0))) ∧
      (∀ (Z : NePoly 𝔅), ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ => r0),
        ‖marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z l‖ ≤
          sizeW (Subtype.val : NePoly 𝔅 → Finset 𝔅) dExt
            (2 * (2 * (2 * εH * Kc) * Kc * Real.exp ((κH - 2 * κ0) * cG d L)) * c1 d L)
            (κH - 2 * κ0 - 3 / 2) κ' (cG d L) Z) := by
    intro u
    have hab : ∀ t, Bdd ((presum Lab (A u).H) t) := fun t => ⟨εH * Kc, fun Φ =>
      ((A u).presum_bound hN hj hΩ hεpos.le hκHge t Φ).trans (by
        have := hexp_le (κH - κ0) (dExt t.1) (by linarith) (dExt_nonneg t.1)
        have h0 : 0 ≤ εH * Kc := by positivity
        nlinarith)⟩
    have hHb : ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ : Unit => r0),
        ∀ (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
        ‖Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ‖ ≤
          (2 * εH * Kc) * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) :=
      fun l hl t Φ => hHlam_bound hN hj hΩ (A u) y0 (G u) (hG u) hεpos hF0 (by linarith) hκHge hκG l
        (by simpa using hl ()) t Φ
    have hmb := marked_bounds μ (Subtype.val : NePoly 𝔅 → Finset 𝔅) (fun t => t.2)
      (fun t => (A u).presum_meas t) hab (fun _ t => gMark_measurable S0 (hGm u) t)
      (fun _ t => gMark_bdd S0 hF0.le (hGC u) t) hH0 hH0log hκ0nn hκ1nn hcG
      (fun Y => dExt_nonneg Y) hHb (fun b => by rw [Finset.sum_filter]; convert hG2c b) hG3T
      (by linarith) hq hG1 hKc0 hκ' hcG
    exact ⟨hmb.1, hmb.2.2⟩
  -- analyticity in `u` of the activities, for fixed marks
  have hKu : ∀ (Z : NePoly 𝔅), ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ : Unit => r0),
      AnalyticOnNhd ℂ (fun u => marksK μ Subtype.val (presum Lab (A u).H)
        (gMark S0 (G u)) Z l) V := by
    intro Z l hl
    have hHb : ∀ u (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
        ‖Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ‖ ≤ 2 * εH * Kc := fun u t Φ => by
      refine (hHlam_bound hN hj hΩ (A u) y0 (G u) (hG u) hεpos hF0 (by linarith) hκHge hκG l
        (by simpa using hl ()) t Φ).trans ?_
      have := hexp_le (κ0 + (κH - 2 * κ0)) (dExt t.1) (by linarith) (dExt_nonneg t.1)
      nlinarith [mul_nonneg hKc0 hεpos.le]
    have hanal : ∀ t : NePoly 𝔅, ∀ Φ ∈ Q,
        AnalyticOnNhd ℂ (fun u => Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ) V := by
      intro t Φ hΦ
      have h1 : AnalyticOnNhd ℂ (fun u => presum Lab (A u).H t Φ) V := by
        unfold presum
        exact Finset.analyticOnNhd_fun_sum _ (fun y _ => hAhol y Φ hΦ)
      have h2 : AnalyticOnNhd ℂ (fun u => gMark S0 (G u) () t Φ) V := by
        by_cases ht : t.1 = S0
        · simp only [gMark, ht, ite_true]; exact hGhol Φ hΦ
        · simp only [gMark, ht, ite_false]; exact analyticOnNhd_const
      unfold Hlam
      exact h1.add (Finset.analyticOnNhd_fun_sum _ (fun j _ => analyticOnNhd_const.mul h2))
    have hcontΦ : ∀ t : NePoly 𝔅, ∀ u ∈ V,
        ContinuousOn (Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t) Q := by
      intro t u hu
      have h1 : ContinuousOn (presum Lab (A u).H t) Q := by
        unfold presum
        exact continuousOn_finsetSum _ (fun y _ => hAcont y u hu)
      have h2 : ContinuousOn (gMark S0 (G u) () t) Q := by
        by_cases ht : t.1 = S0
        · have : gMark S0 (G u) () t = G u := by funext Φ; simp [gMark, ht]
          rw [this]; exact hGcont u hu
        · have : gMark S0 (G u) () t = fun _ => 0 := by funext Φ; simp [gMark, ht]
          rw [this]; exact continuousOn_const
      unfold Hlam
      exact h1.add (continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul h2))
    exact analyticOnNhd_mayerK_param (sup := (Subtype.val : NePoly 𝔅 → Finset 𝔅)) μ hV hQ hQm
      hμQ (H := fun u => Hlam (presum Lab (A u).H) (gMark S0 (G u)) l) hanal
      (fun t => continuousOn_prod_of_analytic_bdd hV (fun Φ hΦ => hanal t Φ hΦ)
        (fun u hu => hcontΦ t u hu) (fun u _ Φ _ => hHb u t Φ)) Z
  have hmain := holo_of_KP_param (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val hKP
    (fun _ => hr0pos) hV
    (fun u Z l => marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z l)
    (fun u _ Z => (hdat u).1 Z) hKu (fun u _ Z l hl => (hdat u).2 Z l hl) Y
  refine ⟨?_, hmain.2 ()⟩
  have heq : (fun u => Pst μ Lab (A u).H Y) = fun u => PY (shareBlock
      (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (fun Z => marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z 0) Y := by
    funext u
    exact (Ff_zero_eq_Pst μ Lab (A u).H S0 (G u) Y).symm
  rw [heq]
  exact hmain.1

end Holo

end Balaban.Fluctuation
