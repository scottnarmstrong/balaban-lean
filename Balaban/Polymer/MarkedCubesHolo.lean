/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesLocal
public import Balaban.Polymer.MarkedHolo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 3.4: holomorphy in the parameter `u` (FLUCTUATION.md §3.4)

If the label activities `H(Y; Φ, u)` and the mark `G(Φ, u)` are holomorphic in `u ∈ 𝒰` (open) with
the bounds of `marked_cubes` uniform in `u`, then `P(S)` and `G*(Y₀, S)` are holomorphic in `u`
(PE (d), MY (ii)).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Holo

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- **Holomorphy of `P(S)` and `G*(Y₀, S)` in `u`.**  The label activities `(A u).H` and the mark
`G u` are holomorphic in `u ∈ 𝒰` for each configuration `Φ`; the hypotheses of `marked_cubes` hold
for every `u` (with the same constants). -/
theorem Pst_Gst_differentiableOn {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    {𝒰 : Set ℂ} (h𝒰 : IsOpen 𝒰)
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ u, Measurable (G u))
    (hG : ∀ u Φ, ‖G u Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hAhol : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰)
    (hGhol : ∀ Φ, DifferentiableOn ℂ (fun u => G u Φ) 𝒰)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (Y : Finset 𝔅) :
    DifferentiableOn ℂ (fun u => Pst μ Lab (A u).H Y) 𝒰 ∧
      DifferentiableOn ℂ (fun u => Gst μ Lab (A u).H (blocksOf m₀ j Ω (Lab.ysite y0)) (G u) Y) 𝒰 := by
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
  -- holomorphy in `u` of the activities, for fixed marks
  have hKu : ∀ (Z : NePoly 𝔅), ∀ l ∈ Balaban.Analysis.polydisc (0 : Unit → ℂ) (fun _ : Unit => r0),
      DifferentiableOn ℂ (fun u => marksK μ Subtype.val (presum Lab (A u).H)
        (gMark S0 (G u)) Z l) 𝒰 := by
    intro Z l hl
    have hHb : ∀ u (t : NePoly 𝔅) (Φ : ∀ b, Ωb b),
        ‖Hlam (presum Lab (A u).H) (gMark S0 (G u)) l t Φ‖ ≤
          (2 * εH * Kc) * Real.exp (-(κ0 + (κH - 2 * κ0)) * dExt t.1) :=
      fun u t Φ => hHlam_bound hN hj hΩ (A u) y0 (G u) (hG u) hεpos hF0 (by linarith) hκHge hκG l
        (by simpa using hl ()) t Φ
    refine differentiableOn_mayerK (sup := (Subtype.val : NePoly 𝔅 → Finset 𝔅)) μ h𝒰
      (H := fun u => Hlam (presum Lab (A u).H) (gMark S0 (G u)) l)
      (fun u t => measurable_Hlam (fun t => (A u).presum_meas t)
        (fun _ t => gMark_measurable S0 (hGm u) t) l t) (fun t Φ => ?_) (fun t => ⟨2 * εH * Kc, fun u _ Φ => ?_⟩) Z
    · have h1 : DifferentiableOn ℂ (fun u => presum Lab (A u).H t Φ) 𝒰 := by
        unfold presum
        exact DifferentiableOn.fun_sum (fun y _ => hAhol y Φ)
      have h2 : DifferentiableOn ℂ (fun u => gMark S0 (G u) () t Φ) 𝒰 := by
        by_cases ht : t.1 = S0
        · simp only [gMark, ht, ite_true]; exact hGhol Φ
        · simp only [gMark, ht, ite_false]; exact differentiableOn_const _
      unfold Hlam
      exact h1.add (DifferentiableOn.fun_sum (fun j _ => (differentiableOn_const _).mul h2))
    · refine (hHb u t Φ).trans ?_
      have := hexp_le (κ0 + (κH - 2 * κ0)) (dExt t.1) (by linarith) (dExt_nonneg t.1)
      nlinarith [mul_nonneg hKc0 hεpos.le]
  have hmain := holo_of_KP (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val hKP
    (fun _ => hr0pos) h𝒰
    (fun u Z l => marksK μ Subtype.val (presum Lab (A u).H) (gMark S0 (G u)) Z l)
    (fun u _ Z => (hdat u).1 Z) hKu (fun u _ Z l hl => (hdat u).2 Z l hl) Y
  refine ⟨?_, hmain.2 ()⟩
  convert hmain.1 using 2 with u
  exact (Ff_zero_eq_Pst μ Lab (A u).H S0 (G u) Y).symm

end Holo

end Balaban.Fluctuation
