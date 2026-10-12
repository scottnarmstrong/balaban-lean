/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexProp26
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The activity bound of the complex step for a small exponent (COMPLETE-STEP §2; non-vacuity)

The hypotheses of `prop26C_class_of_activity` at a complex datum of the chart, for the class with
zero old terms and the source `g = 0`:

* `classRegularC_zeroClass_zero`: `ClassRegularC` holds for the zero class and
  `g = 0` at every step datum (rule 10 for `ClassRegularC`);
* `stepActivityBoundC_of_small`: the one-label activity bound for the exponents of the complex step
  (the complex form of `stepActivityBound_of_small_gen`): if the truncated exponent
  `W₁(s) + W₂(t)` of the complex step is measurable and below the cluster threshold
  `stepActivityThreshold` on the two segments, then `StepActivityBoundC` holds.  No realness of the
  datum;
* `exists_small_radiusC`: on the complex chart the interaction `V^{(k)}(ψ^{(k)}(θ) + s ψ')` is
  uniformly small for `‖ψ̂‖ < p`, `s ∈ [0,1]`, when the radius `p` is small (`V^{(k)}(0) = 0`,
  `VkC_psi0C`, and `V^{(k)}` is continuous on the ray, `contDiffAt_VjointC`);
* `exists_activityBoundC_zeroClass`: hence, for a complex block datum of the chart, the step with
  a small radius `p₁` of `χ_fl` satisfies `StepActivityBoundC` for the zero class and `g = 0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField.Def6
  Balaban.Background Balaban.SmallField MeasureTheory

section Inhab

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  (g : Fld d L N₁ m₁ (k + 1) N)

/-- For the zero effective action, `δℰ_k = 0` at every complex old spin. -/
theorem dEC_zeroClass (ψ : S.EC) : S.dEC (zeroClass d L N₁ m₁ k N ϱ) ψ = 0 := by
  unfold StepSetting.dEC
  show EcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ -
    EcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ = 0
  rw [EcompAtC_zero, EcompAtC_zero, sub_zero]

/-- For the zero effective action, `W₁ = -β_k V^{(k)}` (the complex step). -/
theorem WoneC_zeroClass (s : ℝ) (x : S.E) :
    S.WoneC (zeroClass d L N₁ m₁ k N ϱ) s x = -(S.β : ℂ) * S.VkC (S.psiAtC s x) := by
  unfold StepSetting.WoneC
  rw [dEC_zeroClass, add_zero]

theorem dECT_zeroClass : S.dECT (zeroClass d L N₁ m₁ k N ϱ) = fun _ _ => 0 := by
  funext s x
  unfold StepSetting.dECT
  rw [dEC_zeroClass]
  simp

theorem WtwoCT_zeroClass_zero : S.WtwoCT (zeroClass d L N₁ m₁ k N ϱ) 0 = fun _ _ => 0 := by
  funext t x
  unfold StepSetting.WtwoCT
  rw [WtwoC_zero_class]
  simp

/-- **`ClassRegularC` is inhabited** (rule 10): for the zero effective action and the source
`g = 0` the class exponents of the complex step vanish, at every step datum.  (`W₁ = -β V^{(k)}`
is not zero; it is treated in `isC1Family_WVCT`.) -/
theorem classRegularC_zeroClass_zero :
    S.ClassRegularC (zeroClass d L N₁ m₁ k N ϱ) 0 := by
  refine ⟨⟨Set.univ, fun _ _ => 0, fun _ _ => 0, ?_, ?_⟩⟩
  · rw [dECT_zeroClass]
    exact isC1Family_zero
  · rw [WtwoCT_zeroClass_zero]
    exact isC1Family_zero

open Classical in
/-- **`StepActivityBoundC` for a small exponent** (the complex form of
`stepActivityBound_of_small_gen`): the single label `𝕋` carrying the truncated exponents
`W₁(s) + W₂(t)` of the complex step, uniformly below the cluster threshold
`stepActivityThreshold` on the segments.  The block datum may be complex. -/
theorem stepActivityBoundC_of_small (hp₁ : 0 < S.p₁)
    (hmeas : ∀ p ∈ stepSegments, Measurable (fun x => S.WoneCT C p.1 x + S.WtwoCT C g p.2 x))
    (hsmall : ∀ p ∈ stepSegments, ∀ x,
      ‖S.WoneCT C p.1 x + S.WtwoCT C g p.2 x‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1)) :
    Nonempty (StepActivityBoundC S C g) := by
  have hprob : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hne : Nonempty (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
      Set.univ) := ⟨⟨cbase (cellSide L 0 m₁ (k + 1)) 0, aligned_cbase 0, Set.subset_univ _⟩⟩
  set b₀ := Classical.arbitrary (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0
    (k + 1) Set.univ) with hb₀
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hc1 := one_le_c1 d L
  set κ0 := aEnt d L + 1 with hκ0
  set Kc := K0 d L κ0 + 1 with hKc
  have hKc1 : 1 ≤ Kc := by linarith
  set κH := 3 * κ0 + c1 d L + 3 / 2 with hκH
  set εH := 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + 0 * cG d L)) with hεH
  have hεpos : 0 < εH := by positivity
  let Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1) Set.univ
      Unit :=
    { ysite := fun _ => Set.univ
      dl := fun _ => treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
        Set.univ
      isDj := fun _ => isDj_univ d L N₁ m₁ (k + 1) 0 (k + 1)
      meets := fun _ => by simp
      size := fun _ => Or.inl rfl }
  let BS : BlockSplit S 0 :=
    { Ωb := fun _ => S.E
      μ := oneBlockMeasure S.nuFl b₀
      restr := oneBlockMap b₀
      meas := measurable_oneBlockMap b₀
      map_eq := map_oneBlockMap S.nuFl b₀ }
  let A : ℝ × ℝ → LabelAct Lab BS.Ωb εH κH κ0 Kc := fun p =>
    { H := fun _ Φ => if p ∈ stepSegments then
        S.WoneCT C p.1 (Φ b₀) + S.WtwoCT C g p.2 (Φ b₀) else 0
      meas := fun _ => by
        by_cases hp : p ∈ stepSegments
        · simp only [hp, ite_true]
          exact (hmeas p hp).comp (measurable_pi_apply _)
        · simp only [hp, ite_false]; exact measurable_const
      dep := fun _ Φ Φ' h => by
        have hb : b₀ ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
            Set.univ (Lab.ysite ()) := by
          rw [mem_blocksOf]; exact Set.subset_univ _
        simp only [h b₀ hb]
      bound := fun _ Φ => by
        by_cases hp : p ∈ stepSegments
        · simp only [hp, ite_true]
          refine (hsmall p hp _).trans (le_of_eq ?_)
          simp [stepActivityThreshold, εH, κH, κ0, Kc, Lab]
        · simp only [hp, ite_false, norm_zero]; positivity
      entropy := fun b => by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        split_ifs
        · have h0 : 0 ≤ treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0
              (k + 1) Set.univ := treeLenCovOne_nonneg _ _ _
          have : Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (K := k + 1) 0 (k + 1) Set.univ) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [aEnt_nonneg d L])
          linarith
        · linarith }
  refine ⟨{
    m₀ := 0
    hN := by simp
    BS := BS
    Lb := Unit
    Lab := Lab
    εH := εH
    κH := κH
    κ0 := κ0
    κ' := 0
    Kc := Kc
    A := A
    hκ0 := le_rfl
    hKc := le_rfl
    hεpos := hεpos
    hκ' := le_rfl
    hκ := by rw [hκH]; linarith
    hε := le_rfl
    hW := fun p hp => ?_ }⟩
  filter_upwards [S.ae_ball hp₁] with x hx
  simp only [A, hp, ite_true, Finset.univ_unique, Finset.sum_singleton, BS, oneBlockMap]
  rw [S.WoneCT_of_chi C p.1 x hx, S.WtwoCT_of_chi C g p.2 x hx]

end Inhab

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

theorem psiAtC_zero_right (s : ℝ) : S.psiAtC s 0 = S.psi0C := by
  funext q
  simp [psiAtC, S.shiftUC_apply]

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The radius of smallness on the complex chart** (the complex form of the first part of
`exists_small_radius`): for a complex block datum of the chart and every `ε > 0` there is a radius
`0 < p < p⁺`, `p ≤ 1`, with `‖V^{(k)}(ψ^{(k)}(θ) + s ψ')‖ < ε` for `‖ψ̂‖ < p`, `s ∈ [0,1]`. -/
theorem exists_small_radiusC {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ, 0 < p ∧ p < pp ∧ p ≤ 1 ∧ ∀ x : S.E, ‖x‖ < p → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖S.VkC (S.psiAtC s x)‖ < ε := by
  have hD1 : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν S.D' :=
    (isDecBg_one_of_xiCData hC hD).2.mono
      ((hc7.trans (thm73C3_le_thm73C2 d L N)).trans (thm73C2_le_thm73C1 d L N))
  have hV0 := S.VkC_psi0C ha₁ hC.HBp hD1
  set r : ℝ := min 1 (pp / 2) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  have hrpp : r < pp := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set K : Set (ℝ × S.E) := Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) r with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun q : ℝ × S.E => S.VkC (S.psiAtC q.1 q.2)) K := by
    intro q hq
    have h1 : |q.1| ≤ 1 := by
      rw [abs_of_nonneg hq.1.1]; exact hq.1.2
    have h2 : ‖q.2‖ ≤ r := by simpa using hq.2
    have hq' : |q.1| * ‖q.2‖ < pp := by
      calc |q.1| * ‖q.2‖ ≤ 1 * r := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ < pp := by rw [one_mul]; exact hrpp
    exact (S.contDiffAt_VjointC hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le hpp hδ₁ hD
      hq').continuousAt.continuousWithinAt
  have huc := hKc.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδP⟩ := huc ε hε
  refine ⟨min r δ, lt_min hr0 hδ, lt_of_le_of_lt (min_le_left _ _) hrpp,
    (min_le_left _ _).trans (min_le_left _ _), fun x hx s hs => ?_⟩
  have hxr : ‖x‖ ≤ r := (hx.trans_le (min_le_left _ _)).le
  have ha : ((s, x) : ℝ × S.E) ∈ K := ⟨hs, by simpa using hxr⟩
  have hb : ((s, (0 : S.E)) : ℝ × S.E) ∈ K := ⟨hs, by simpa using hr0.le⟩
  have hd : dist ((s, x) : ℝ × S.E) (s, 0) < δ := by
    rw [Prod.dist_eq]
    simpa using hx.trans_le (min_le_right _ _)
  have h := hδP _ ha _ hb hd
  simp only [S.psiAtC_zero_right, hV0, dist_zero_right] at h
  exact h

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The activity bound of the complex step at a complex datum of the chart, for a small radius**
(non-vacuity of `StepActivityBoundC` with no realness of the datum): for a complex block datum of
the chart there is a radius `0 < p < p⁺` such that the step with `p₁ = p` satisfies
`StepActivityBoundC` for the class with zero old terms and `g = 0` (the exponent is
`W₁ = -β_k V^{(k)}`, small on the support of `ν_p`). -/
theorem exists_activityBoundC_zeroClass :
    ∃ p : ℝ, 0 < p ∧ p < pp ∧
      Nonempty (StepActivityBoundC (S.withRadius p) (zeroClass d L N₁ m₁ k N ϱ) 0) := by
  classical
  have hT0 := stepActivityThreshold_pos d L N₁ m₁ (k + 1)
  obtain ⟨p, hp0, hppp, -, hsmallV⟩ := S.exists_small_radiusC hC hMX hdm hα hsm ha₁ hc7 hR hsmR
    hβ hpp hδ₁ hD (ε := stepActivityThreshold d L N₁ m₁ (k + 1) / S.β) (by positivity)
  refine ⟨p, hp0, hppp, ?_⟩
  set S' := S.withRadius p with hS'
  have hp1 : 0 < S'.p₁ := hp0
  obtain ⟨U, V', hV⟩ := S'.isC1Family_WVCT (pp := pp) hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ.le hpp
    hδ₁ hD hp1 hppp
  have hW : ∀ q : ℝ × ℝ, (fun x => S'.WoneCT (zeroClass d L N₁ m₁ k N ϱ) q.1 x +
      S'.WtwoCT (zeroClass d L N₁ m₁ k N ϱ) 0 q.2 x) = S'.WVCT q.1 := by
    intro q
    funext x
    rw [S'.WoneCT_eq_add, dECT_zeroClass, WtwoCT_zeroClass_zero]
    simp
  refine stepActivityBoundC_of_small S' _ 0 hp1 (fun q hq => ?_) (fun q hq x => ?_)
  · rw [hW q]
    exact hV.measurable q.1 (hV.Icc_subset (mem_Icc_of_mem_stepSegments hq).1)
  · have := congrFun (hW q) x
    rw [this]
    unfold StepSetting.WVCT
    by_cases hx : chiFl S'.U N S'.p₁ x = 1
    · simp only [hx, ↓reduceIte]
      have hxn : ‖x‖ < p := (chiFl_eq_one_iff hp1 x).1 hx
      have h := hsmallV x hxn q.1 (mem_Icc_of_mem_stepSegments hq).1
      have hβ' : |S'.β| = S.β := abs_of_pos hβ
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, hβ']
      show S.β * ‖S.VkC (S.psiAtC q.1 x)‖ ≤ _
      calc S.β * ‖S.VkC (S.psiAtC q.1 x)‖
          ≤ S.β * (stepActivityThreshold d L N₁ m₁ (k + 1) / S.β) :=
            mul_le_mul_of_nonneg_left h.le hβ.le
        _ = stepActivityThreshold d L N₁ m₁ (k + 1) := by field_simp
    · simp only [hx, ↓reduceIte, norm_zero]
      exact hT0.le

end StepSetting

end Balaban.Fluctuation
