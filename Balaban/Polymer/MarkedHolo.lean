/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerHolomorphic
public import Balaban.Polymer.MayerMarked
public import Balaban.Polymer.Holomorphic
public import Balaban.Polymer.Size
public import Balaban.Polymer.CauchySum

/-!
# Holomorphy in a parameter of the local terms with marks (PE (d), MY (ii))

If the activities of a polymer gas depend on a complex parameter `u` holomorphically for each
fixed mark `l`, with a Kotecký–Preiss bound uniform in `u`, then the local terms `P(Y)` and the
derivatives `∂_i P(Y)` at `l = 0` are holomorphic in `u`.  The derivative is handled by the Cauchy
formula on a circle in the mark (`differentiableOn_deriv_zero`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Metric Balaban.Analysis

namespace Balaban.Polymer

/-- If `(u, l) ↦ f u l` is holomorphic in `u` for each `l`, holomorphic in `l` on the disc of
radius `r` for each `u`, and bounded, then `u ↦ ∂_l f u 0` is holomorphic. -/
theorem differentiableOn_deriv_zero {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hdu : ∀ l : ℂ, ‖l‖ < r → DifferentiableOn ℂ (fun u => f u l) U)
    (hdl : ∀ u ∈ U, DifferentiableOn ℂ (f u) (ball 0 r))
    (hbd : ∀ u ∈ U, ∀ l : ℂ, ‖l‖ < r → ‖f u l‖ ≤ M) :
    DifferentiableOn ℂ (fun u => deriv (f u) 0) U := by
  set R : ℝ := r / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRr : R < r := by rw [hRdef]; linarith
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 R θ‖ = R := fun θ => by
    simp [norm_circleMap_zero, abs_of_pos hR]
  set g : ℂ → ℂ → ℂ := fun u l => if u ∈ U then f u l else 0 with hg
  set F : ℂ → ℝ → ℂ := fun u θ =>
    (circleMap 0 R θ * Complex.I) • (((circleMap 0 R θ - 0) ^ 2)⁻¹ • g u (circleMap 0 R θ)) with hF
  have hcirc : ∀ u ∈ U, deriv (f u) 0 =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in Set.Ioc 0 (2 * Real.pi), F u θ := by
    intro u hu
    have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      (isOpen_ball (x := (0 : ℂ)) (ε := r)) (c := 0) (w₀ := 0) (R := R)
      (closedBall_subset_ball hRr) (hdl u hu) (mem_ball_self hR)
    rw [← h]
    congr 1
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
    simp only [deriv_circleMap, hF, hg, hu, ite_true]
  have hcont : ∀ u ∈ U, Continuous (fun θ : ℝ => g u (circleMap 0 R θ)) := by
    intro u hu
    have h1 : ContinuousOn (f u) (ball 0 r) := (hdl u hu).continuousOn
    have h2 : Continuous (fun θ : ℝ => circleMap 0 R θ) := continuous_circleMap 0 R
    have h3 := h1.comp_continuous h2 (fun θ => by simp [hnorm θ, hRr])
    have h4 : (fun θ : ℝ => g u (circleMap 0 R θ)) = f u ∘ fun θ => circleMap 0 R θ := by
      funext θ; simp [hg, hu]
    rw [h4]; exact h3
  have hmeas : ∀ u, Measurable (F u) := by
    intro u
    by_cases hu : u ∈ U
    · have : Continuous (F u) := by
        simp only [hF]
        have hs : Continuous (fun θ : ℝ => ((circleMap 0 R θ - 0) ^ 2)⁻¹) :=
          Continuous.inv₀ (((continuous_circleMap 0 R).sub continuous_const).pow 2) (fun θ => by
            simp [hR.ne'])
        exact ((continuous_circleMap 0 R).mul continuous_const).smul (hs.smul (hcont u hu))
      exact this.measurable
    · have : F u = fun _ => 0 := by funext θ; simp [hF, hg, hu]
      rw [this]; exact measurable_const
  have hdiff : ∀ θ, DifferentiableOn ℂ (fun u => F u θ) U := by
    intro θ
    have h1 : DifferentiableOn ℂ (fun u => g u (circleMap 0 R θ)) U :=
      (hdu (circleMap 0 R θ) (by simp [hnorm θ, hRr])).congr (fun u hu => by simp [hg, hu])
    exact (h1.const_smul (((circleMap 0 R θ - 0) ^ 2)⁻¹)).const_smul (circleMap 0 R θ * Complex.I)
  have hbd' : ∀ u ∈ U, ∀ θ, ‖F u θ‖ ≤ M / R := by
    intro u hu θ
    simp only [hF, norm_smul, norm_mul, Complex.norm_I, mul_one, hnorm θ, sub_zero, norm_inv,
      norm_pow]
    have := hbd u hu (circleMap 0 R θ) (by simp [hnorm θ, hRr])
    have h2 : ‖g u (circleMap 0 R θ)‖ ≤ M := by simpa [hg, hu] using this
    calc R * ((R ^ 2)⁻¹ * ‖g u (circleMap 0 R θ)‖) ≤ R * ((R ^ 2)⁻¹ * M) := by gcongr
      _ = M / R := by field_simp
  have hint : DifferentiableOn ℂ
      (fun u => ∫ θ, F u θ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) U :=
    differentiableOn_integral_of_bound (volume.restrict (Set.Ioc 0 (2 * Real.pi))) hU
      (M := M / R) hmeas hdiff hbd'
  exact (hint.const_smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)).congr (fun u hu => hcirc u hu)

section Parameter

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {B : Type*} (supp : P → Finset B)
  {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ} {κ a : P → ℝ}

omit [Fintype ι] in
theorem mem_polydisc_line (hr : ∀ i, 0 < r i) (i : ι) {l : ℂ} (hl : ‖l‖ < r i) :
    l • (Pi.single i 1 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := by
  have := mem_polydisc_add_single (c := (0 : ι → ℂ)) (r := r) (w := 0)
    (fun k => by simpa using hr k) i (l := l) (by simpa using hl)
  simpa using this

theorem deriv_line (F : (ι → ℂ) → ℂ) (hF : DifferentiableAt ℂ F 0) (i : ι) :
    deriv (fun l : ℂ => F (l • (Pi.single i 1 : ι → ℂ))) 0 = fderiv ℂ F 0 (Pi.single i 1) := by
  have h1 : HasDerivAt (fun t : ℂ => t • (Pi.single i 1 : ι → ℂ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const (Pi.single i 1 : ι → ℂ)
  have h2 : HasFDerivAt F (fderiv ℂ F 0) ((0 : ℂ) • (Pi.single i 1 : ι → ℂ)) := by
    simpa using hF.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

/-- **Holomorphy in the parameter `u`** of `P(Y)` and of `∂_i P(Y)` at `l = 0`, from a
Kotecký–Preiss bound uniform in `u`. -/
theorem holo_of_KP (h : KPCond inc κ a) (hr : ∀ i, 0 < r i) {U : Set ℂ} (hU : IsOpen U)
    (K : ℂ → P → (ι → ℂ) → ℂ)
    (hKl : ∀ u ∈ U, ∀ Z, AnalyticOnNhd ℂ (K u Z) (polydisc 0 r))
    (hKu : ∀ Z, ∀ l ∈ polydisc (0 : ι → ℂ) r, DifferentiableOn ℂ (fun u => K u Z l) U)
    (hb : ∀ u ∈ U, ∀ Z, ∀ l ∈ polydisc (0 : ι → ℂ) r, ‖K u Z l‖ ≤ κ Z) (Y : Finset B) :
    DifferentiableOn ℂ (fun u => PY inc supp (fun Z => K u Z 0) Y) U ∧
      ∀ i, DifferentiableOn ℂ (fun u => D1 i (Ff inc supp (K u) Y)) U := by
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k
  have hPu : ∀ l ∈ polydisc (0 : ι → ℂ) r,
      DifferentiableOn ℂ (fun u => PY inc supp (fun Z => K u Z l) Y) U := fun l hl =>
    (pe_PY_analyticOnNhd inc supp h hU (fun Z u => K u Z l)
      (fun Z => (hKu Z l hl).analyticOnNhd hU) (fun Z u hu => hb u hu Z l hl) Y).differentiableOn
  refine ⟨hPu 0 h0, fun i => ?_⟩
  set M : ℝ := ∑' n, sp inc κ (fun _ => True) n with hM
  have hline : ∀ u ∈ U, ∀ l : ℂ, ‖l‖ < r i →
      Ff inc supp (K u) Y (l • Pi.single i 1) = PY inc supp (fun Z => K u Z (l • Pi.single i 1)) Y :=
    fun _ _ _ _ => rfl
  have key := differentiableOn_deriv_zero hU (hr i)
    (f := fun u l => Ff inc supp (K u) Y (l • (Pi.single i 1 : ι → ℂ))) (M := M)
    (fun l hl => hPu _ (mem_polydisc_line hr i hl))
    (fun u hu => by
      intro l hl
      have hmem : l • (Pi.single i 1 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r :=
        mem_polydisc_line hr i (by simpa using hl)
      have hF := (analyticOnNhd_Ff inc supp h (hKl u hu) (fun Z l hl => hb u hu Z l hl) Y _ hmem)
      have hlin : DifferentiableAt ℂ (fun t : ℂ => t • (Pi.single i 1 : ι → ℂ)) l :=
        (differentiableAt_id.smul_const _)
      exact (hF.differentiableAt.comp l hlin).differentiableWithinAt)
    (fun u hu l hl => norm_PY_le inc supp h _ (fun Z => hb u hu Z _
      (mem_polydisc_line hr i hl)) Y)
  refine key.congr (fun u hu => ?_)
  exact (deriv_line (Ff inc supp (K u) Y)
    ((analyticOnNhd_Ff inc supp h (hKl u hu) (fun Z l hl => hb u hu Z l hl) Y 0 h0).differentiableAt) i).symm

end Parameter

section Data

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a : T → (∀ b, Ω b) → ℂ} {g : ι → T → (∀ b, Ω b) → ℂ} {d : Finset B → ℝ}
  {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ} {r : ι → ℝ}

/-- The Kotecký–Preiss condition for the size weights of PE-L (it does not involve the system). -/
theorem marked_kp {ε : ℝ} (hε0 : 0 ≤ ε) (hd : ∀ Y, 0 ≤ d Y)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : ε * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    KPCond (shareBlock (Subtype.val : NePoly B → Finset B))
      (sizeW (Subtype.val : NePoly B → Finset B) d ε (κ1 - 3 / 2) κ' cP)
      (fun x => (ε * K0P * Real.exp (c1 + κ' * cP)) * (x.1.card : ℝ)) :=
  kp_of_entropy (Subtype.val : NePoly B → Finset B) _
    (sizeW_nonneg (κ := κ1 - 3 / 2) (κ' := κ') (c := cP) (Subtype.val : NePoly B → Finset B) d hε0)
    (size_entropy (Subtype.val : NePoly B → Finset B) d (κ := κ1 - 3 / 2) (κ' := κ')
      (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1) hε0 hd hG1 hG2P hκ hα)

/-- The activities `K(Z, l)` are analytic in the marks and obey the size bound (the first part of
the proof of `mayer_marked_termwise`). -/
theorem marked_bounds (hne : ∀ t, (sup t).Nonempty)
    (ha : ∀ t, Measurable (a t)) (hab : ∀ t, Bdd (a t))
    (hg : ∀ j t, Measurable (g j t)) (hgb : ∀ j t, Bdd (g j t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ l ∈ polydisc (0 : ι → ℂ) r, ∀ t Φ,
      ‖Hlam a g l t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3T : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hK0 : 0 ≤ K0) (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP) :
    (∀ Z : NePoly B, AnalyticOnNhd ℂ (marksK μ sup a g Z) (polydisc 0 r)) ∧
    (∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤ sizeW (Subtype.val : NePoly B → Finset B) d
        (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1) (κ1 - 3 / 2) κ' cP Z) := by
  set ε : ℝ := 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hq0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hb_le : ∀ l ∈ polydisc (0 : ι → ℂ) r, ∀ t Φ, ‖Hlam a g l t Φ‖ ≤ Real.log 2 := by
    intro l hl t Φ
    refine (hH l hl t Φ).trans ?_
    calc H0 * Real.exp (-(κ0 + κ1) * d (sup t)) ≤ H0 * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith [hd (sup t)])
      _ ≤ _ := by rw [mul_one]; exact hH0'
  have hKan : ∀ Z : NePoly B, AnalyticOnNhd ℂ (marksK μ sup a g Z) (polydisc 0 r) := fun Z =>
    analyticOnNhd_mayerK_marks μ sup hq0 hq1 r ha hab hg hgb hb_le Z
  have hKbd : ∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤ ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) := fun Z l hl =>
    mayer_activity_bound μ hH0 hH0' hκ0 hκ1 hc hd hne (hH l hl) hG2T hG3T hc1 hq Z (hG1 Z)
  have hg0 : ∀ Y : Finset B, 0 ≤ κ' * (d Y + cP) := fun Y => by have := hd Y; positivity
  refine ⟨hKan, fun Z l hl => (hKbd Z l hl).trans ?_⟩
  unfold sizeW
  calc ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) = ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) * 1 := by
        rw [mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
        have := hg0 Z.1; simpa using this)) (by positivity)

end Data

end Balaban.Polymer
