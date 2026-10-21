/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkClusterEquiv
public import Balaban.Fluctuation.Thm31CoeffAnalytic
public import Balaban.Localization.DecoupledCovParam

/-!
# Analyticity of the cluster term of one mark in a parameter (Theorem 3.4)

`markTerm_analyticOnNhd`: for activities `A(e, u)` analytic in `(e, u)` on `P × 𝒰` (`𝒰 ⊃ [0, 1]`
open) and a mark `G(e)` analytic in `e ∈ P`, both continuous in the configuration on a compact set
carrying the measure, the mark bounded on `P` and the numerical hypotheses of Theorem 3.4 (entropy
constant `K_c + 1`), the cluster term `∫₀¹ G*(V, S) du` is analytic on `P`.  The families are cut off
outside a product of a ball and `𝒰` so that `Pst_Gst_analyticOnNhd` applies with the mark's site added
to the labels; the integral over `u` is analytic by `analyticOnNhd_intervalIntegral` with the bound of
`marked_cubes_explicit`.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

variable {Lb : Type*} [Fintype Lb]
  {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

open Classical in
/-- **The cluster term of one mark is analytic in a parameter** (Theorem 3.4 with the mark's site
added to the labels, `Pst_Gst_analyticOnNhd`, and the integral over the interpolation parameter,
`analyticOnNhd_intervalIntegral`): for activities `A(e, u)` analytic in `(e, u)` on `P × 𝒰`
(`𝒰 ⊃ [0, 1]` open) and a mark `G(e)` analytic in `e ∈ P`, both continuous in the configuration on a
compact set `Q` carrying the measure, the mark bounded by `B` on `P`, and the numerical hypotheses of
Theorem 3.4 at the entropy constant `K_c + 1`, the term `∫₀¹ G*(V, S) du` is analytic on `P`. -/
theorem markTerm_analyticOnNhd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [∀ b, TopologicalSpace (Ωb b)] [∀ b, OpensMeasurableSpace (Ωb b)]
    [∀ b, SecondCountableTopology (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V)
    (hm : (V ∩ Ω).Nonempty) (G : E → (∀ b, Ωb b) → ℂ) {P : Set E} (hP : IsOpen P)
    {𝒰 : Set ℂ} (h𝒰 : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    {Q : Set (∀ b, Ωb b)} (hQ : IsCompact Q) (hQm : MeasurableSet Q)
    (hμQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hGm : ∀ e ∈ P, Measurable (G e)) (hGdep : ∀ e ∈ P, DepOn (blocksOf m₀ j Ω V) (G e))
    {B : ℝ} (hB : 0 < B) (hG : ∀ e ∈ P, ∀ Φ, ‖G e Φ‖ ≤ B)
    (hAhol : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun q : E × ℂ => (A q.1 q.2).H y Φ) (P ×ˢ 𝒰))
    (hGhol : ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun e => G e Φ) P)
    (hAcont : ∀ y, ∀ e ∈ P, ∀ w ∈ 𝒰, ContinuousOn ((A e w).H y) Q)
    (hGcont : ∀ e ∈ P, ContinuousOn (G e) Q)
    {κ' : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) (hεpos : 0 < εH) (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (Kc + 1) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) (S : Finset 𝔅) :
    AnalyticOnNhd ℂ (fun e => markTerm μ (A e) V (G e) S) P := by
  have hκ0' : 0 ≤ κ0 := by have := aEnt_nonneg d L; linarith
  set t := treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V with ht
  set F0 : ℝ := B * Real.exp (κH * t) with hF0
  have hF0pos : 0 < F0 := by positivity
  have hGF : ∀ e ∈ P, ∀ Φ, ‖G e Φ‖ ≤ F0 * Real.exp (-κH * t) := fun e he Φ => by
    rw [hF0, mul_assoc, ← Real.exp_add, show κH * t + -κH * t = 0 by ring, Real.exp_zero, mul_one]
    exact hG e he Φ
  set Lab' := Lab.sum (singleLabel V hV hm) with hLab'
  have hext : ∀ e w (S' : Finset 𝔅) (G' : (∀ b, Ωb b) → ℂ),
      Gst μ Lab' ((A e w).addMark hεpos.le hκ0' V hV hm).H (blocksOf m₀ j Ω V) G' S' =
        Gst μ Lab (A e w).H (blocksOf m₀ j Ω V) G' S' :=
    fun e w S' G' => Gst_extendByZero Lab Lab' Sum.inl_injective (fun _ => rfl) μ (A e w).H _ G' S'
  intro e₀ he₀
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.1 hP e₀ he₀
  set R := R₀ / 2 with hR
  have hRpos : 0 < R := by positivity
  have hsub : ball e₀ (2 * R) ⊆ P := by
    rw [show 2 * R = R₀ by rw [hR]; ring]; exact hball
  -- the parameter set of the joint family
  set W : Set (E × ℂ) := ball e₀ (2 * R) ×ˢ 𝒰 with hW
  have hWo : IsOpen W := isOpen_ball.prod h𝒰
  obtain ⟨w₀, hw₀⟩ : (𝒰).Nonempty := ⟨_, hseg 0 ⟨le_rfl, zero_le_one⟩⟩
  have he₀W : (e₀, w₀) ∈ W := ⟨mem_ball_self (by positivity), hw₀⟩
  -- the cut-off families
  let A' : E × ℂ → LabelAct Lab' Ωb εH κH κ0 (Kc + 1) := fun q =>
    if q ∈ W then (A q.1 q.2).addMark hεpos.le hκ0' V hV hm
    else (A e₀ w₀).addMark hεpos.le hκ0' V hV hm
  let G' : E × ℂ → (∀ b, Ωb b) → ℂ := fun q => if q ∈ W then G q.1 else fun _ => 0
  have hA'W : ∀ q ∈ W, A' q = (A q.1 q.2).addMark hεpos.le hκ0' V hV hm := fun q hq => by
    simp only [A', hq, ↓reduceIte]
  have hG'W : ∀ q ∈ W, G' q = G q.1 := fun q hq => by simp only [G', hq, ↓reduceIte]
  have hinl : ∀ e w y Φ, ((A e w).addMark hεpos.le hκ0' V hV hm).H (Sum.inl y) Φ = (A e w).H y Φ :=
    fun e w y Φ => congrFun (extendByZero_apply Sum.inl_injective (A e w).H y) Φ
  have hinr : ∀ e w u Φ, ((A e w).addMark hεpos.le hκ0' V hV hm).H (Sum.inr u) Φ = 0 :=
    fun e w u Φ => congrFun (extendByZero_apply_of_not_mem_range (A e w).H
      (fun y => Sum.inl_ne_inr)) Φ
  have hPW : ∀ q ∈ W, q.1 ∈ P := fun q hq => hsub hq.1
  have hjoint := Pst_Gst_analyticOnNhd μ hN hj hΩ (Lab := Lab') (κG := κH) (κ' := κ') (F0 := F0)
    hWo hQ hQm hμQ A' (Sum.inr ()) G'
    (fun q => by
      by_cases hq : q ∈ W
      · rw [hG'W q hq]; exact hGm q.1 (hPW q hq)
      · simp only [G', hq, ↓reduceIte]; exact measurable_const)
    (fun q Φ => by
      by_cases hq : q ∈ W
      · rw [hG'W q hq]; exact hGF q.1 (hPW q hq) Φ
      · simp only [G', hq, ↓reduceIte, norm_zero]
        positivity)
    (fun y Φ hΦ => by
      have h1 : AnalyticOnNhd ℂ (fun q : E × ℂ =>
          ((A q.1 q.2).addMark hεpos.le hκ0' V hV hm).H y Φ) W := by
        cases y with
        | inl y =>
          refine ((hAhol y Φ hΦ).mono fun q hq => ⟨hsub hq.1, hq.2⟩).congr hWo ?_
          intro q _
          exact (hinl _ _ _ _).symm
        | inr u =>
          refine (analyticOnNhd_const (v := (0 : ℂ))).congr hWo ?_
          intro q _
          exact (hinr _ _ _ _).symm
      refine h1.congr hWo fun q hq => ?_
      rw [hA'W q hq])
    (fun Φ hΦ => by
      refine ((hGhol Φ hΦ).comp analyticOnNhd_fst fun q hq => hsub hq.1).congr hWo fun q hq => ?_
      show G q.1 Φ = G' q Φ
      rw [hG'W q hq])
    (fun y q hq => by
      rw [hA'W q hq]
      cases y with
      | inl y =>
        refine (hAcont y q.1 (hsub hq.1) q.2 hq.2).congr fun Φ _ => ?_
        exact hinl _ _ _ _
      | inr u =>
        exact (continuousOn_const (c := (0 : ℂ))).congr fun Φ _ => hinr _ _ _ _)
    (fun q hq => by rw [hG'W q hq]; exact hGcont q.1 (hsub hq.1))
    hκ0 (by linarith) hεpos hF0pos hκ' le_rfl hκ hε S
  -- the joint function
  set F : E × ℂ → ℂ := fun q => Gst μ Lab (A q.1 q.2).H (blocksOf m₀ j Ω V) (G q.1) S with hFdef
  have hFW : AnalyticOnNhd ℂ F W := by
    refine hjoint.2.congr hWo fun q hq => ?_
    show Gst μ Lab' (A' q).H (blocksOf m₀ j Ω V) (G' q) S = F q
    rw [hA'W q hq, hG'W q hq, hext]
  set M : ℝ := |CPE d L (Kc + 1) κH κ0 κ'| * F0 * Real.exp (-κ0 * t) *
    Real.exp (-κ' * dExt S) with hM
  have hM0 : 0 ≤ M := by positivity
  have hmap : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → ∀ e ∈ ball e₀ (2 * R), ((e, (x : ℂ)) : E × ℂ) ∈ W :=
    fun x hx e he => ⟨he, hseg x hx⟩
  have hint := analyticOnNhd_intervalIntegral (G := fun (x : ℝ) (e : E) => F (e, (x : ℂ)))
    (e0 := e₀) hRpos hM0 zero_le_one
    (fun x hx => hFW.comp (analyticOnNhd_id.prod analyticOnNhd_const) fun e he => hmap x hx e he)
    (fun x hx e he => by
      have hcore := marked_cubes_explicit μ hN hj hΩ
        ((A e (x : ℂ)).addMark hεpos.le hκ0' V hV hm) (Sum.inr ()) (G e)
        (hGm e (hsub he)) (hGdep e (hsub he)) (hGF e (hsub he)) hκ0 (by linarith) hεpos hF0pos hκ'
        le_rfl hκ hε
      have hb : ‖Gst μ Lab' ((A e (x : ℂ)).addMark hεpos.le hκ0' V hV hm).H (blocksOf m₀ j Ω V)
          (G e) S‖ ≤ CPE d L (Kc + 1) κH κ0 κ' * F0 * Real.exp (-κ0 * t) * Real.exp (-κ' * dExt S) :=
        hcore.2.2.2.2 S
      rw [hext] at hb
      refine hb.trans ?_
      rw [hM]
      gcongr
      exact le_abs_self _)
    (fun e he => by
      have hc : ContinuousOn F W := hFW.continuousOn
      refine hc.comp (continuous_const.prodMk Complex.continuous_ofReal).continuousOn
        fun x hx => hmap x hx e he)
  have heq : (fun e => markTerm μ (A e) V (G e) S) = fun e => ∫ x in (0 : ℝ)..1, F (e, (x : ℂ)) := by
    funext e
    rfl
  rw [heq]
  exact hint e₀ (mem_ball_self hRpos)

end Balaban.Fluctuation
