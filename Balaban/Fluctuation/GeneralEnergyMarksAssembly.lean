/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralEnergyValue
public import Balaban.Fluctuation.GeneralEnergyMarksBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inherited-energy marks of a class member assembled into the energy record

For a class member `C` the marks of the local energy term are the marks of the zero class together
with the marks of the labels `τ = (j, y, X)` of the old energy,
`Mk τ u x = D(ℰ^{(j)}(y, X) ∘ pair_j)(u ψ'(x))[M_z ψ'(x)]`.

* `norm_maskUC_le`: the mask does not increase the sup norm.
* `exists_oldMarks_of_labels`: from the identity of the first-order derivative of `Φ₁^C`
  (`fderiv_Phi1C_class_eq_zero_add_oldE_labels`), the vanishing of the marks of the labels away from
  the block of `z` (`fderiv_classLabel_eq_zero_of_local`) and the Cauchy bound (`norm_fderiv_classLabel_le`),
  the family `G₁` of old marks on the labels meeting the block of `z`, with the clauses of
  `e1MarksC_class_of_zero_add_old`, and the mark identity `hF'`.
* `e1locC_class_value_of_labels`: the value `ℰ₁^C(z) = ∑_T c^C(T)` with only the activity
  identity `hW'` (the old energy in the exponent) as an additional premise.

The old marks are functions of the block variable `Φ = restr x` through a block-local lift
`xs : Φ ↦ x` of the fluctuation variable (a typing datum of the step); `hfac` states that the marks
at `xs (restr x)` and at `x` agree, and `hlocxs` that they read `Φ` only on the blocks of the anchor.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Metric
  MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The mask does not increase the sup norm.** -/
theorem norm_maskUC_le (S : StepSetting d L N₁ m₁ k N ϱ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (v : S.EC) {ρ : ℝ} (hρ : ‖v‖ ≤ ρ) :
    ‖S.maskUC z v‖ ≤ ρ := by
  refine le_trans ?_ hρ
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun q => ?_
  unfold StepSetting.maskUC
  split_ifs
  · exact norm_le_pi_norm v q
  · simp


/-- **A derivative applied to a varying direction is measurable.** -/
theorem measurable_fderiv_apply_pi {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (f : (ι → ℂ) → ℂ) {y v : α → (ι → ℂ)} (hy : Measurable y) (hv : Measurable v) :
    Measurable fun a => fderiv ℂ f (y a) (v a) := by
  have h : ∀ a, fderiv ℂ f (y a) (v a) =
      ∑ i, v a i * fderiv ℂ f (y a) (Pi.single i 1) := by
    intro a
    conv_lhs => rw [pi_eq_sum_univ (v a)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 3
    ext j
    simp [Pi.single_apply, eq_comm]
  simp_rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp hv).mul
    (((measurable_fderiv ℂ f).comp hy).apply_continuousLinearMap _)


namespace StepSetting

section Chart

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
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
  {m₀ : ℕ} {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

open Classical in
include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The old marks of a class member assembled from the labels of the inherited energy.**

Let `I₀` be a record of the zero class and `𝒯E` the label set of the old energy; `Mk τ u x` is the
mark of the label `τ` (the derivative of the label term at `u ψ'(x)` in the direction `M_z ψ'(x)`,
`hMk`).  The labels `τ` with `rE τ ∉ R` do not meet the block of `z` (`hv`), and along the line of
the direction the complex background does not change on their blocks (`hbg`), so their marks vanish
(`fderiv_classLabel_eq_zero_of_local`).  The remaining labels are indexed by `ι₁`, anchored at
`y1 j` with `𝗱(y1 j) ≤ d_j(X_j)` and `κ_G ≤ κ_dec - 1`; their marks are the functions
`G₁ j u Φ = Mk j u (xs Φ)` of the block variable through the lift `xs` (which lands in the ball of
radius `ρ`, with the polydisc of radius `r` in the chart and in the class domains: `hballU`,
`hdomU`), read only on the blocks of the anchor (`hlocxs`), and equal to the marks at `x` almost
everywhere (`hfac`).  Then the family `G₁` satisfies the clauses of `e1MarksC_class_of_zero_add_old`
(measurability, dependence, the bound `F1 exp(-κ_G 𝗱(y1 j))` with `F1 ≥ E₀ ρ / r`, holomorphy on
`𝒰`) and the mark identity `hF'`: `DΦ₁^C(sψ')[M_z ψ'] = ∑ I₀.G + ∑ G₁` almost everywhere, given the
chart `hdomX` at the real points. -/
theorem exists_oldMarks_of_labels {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀)
    (I₀ : E1MarksC S (zeroClass d L N₁ m₁ k N ϱ) BS z)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    (rE : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) →
      CTorus d L N₁ m₁ (k + 1)) (Rs : Finset (CTorus d L N₁ m₁ (k + 1)))
    (Mk : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) → ℂ → S.E → ℂ)
    (hMk : ∀ τ u x, Mk τ u x = fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
      (u • S.shiftUC x) (S.maskUC z (S.shiftUC x)))
    (hv : ∀ τ ∈ 𝒯E, rE τ ∉ Rs → ∀ (w : S.EC) (x : CTorus d L N₁ m₁ (k + 1)), x ∈ τ.2.2 →
      ∀ i, S.maskUC z w (unitPt S.hG' x, i) = 0)
    (hbg : ∀ τ ∈ 𝒯E, rE τ ∉ Rs →
      ∀ (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2),
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl, ∀ᶠ t : ℂ in nhds 0, ∀ x' ∈ τ.2.2, ∀ y ∈
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
          (hτ.1.2.trans (Nat.le_succ k))).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
            (hτ.1.2.trans (Nat.le_succ k))).layerIndex x') x' ∪
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
          (Nat.le_succ k)).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k)).layerIndex x') x',
        ∀ i, svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k))
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
              (Nat.le_succ k)) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C +
                ((s : ℂ) • S.shiftUC x + t • S.maskUC z (S.shiftUC x))))) y i =
          svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k))
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
              (Nat.le_succ k)) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C +
                ((s : ℂ) • S.shiftUC x))) ) y i)
    (hdomX : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (s : ℂ) • S.shiftUC x ∈ S.shiftDomC pp ∧
      ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X → Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + (s : ℂ) • S.shiftUC x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + (s : ℂ) • S.shiftUC x))).2)
    (xs : (∀ b, BS.Ωb b) → S.E) (hxs : Measurable xs) {ρ r : ℝ} (hr : 0 < r)
    (hρxs : ∀ Φ, ‖S.shiftUC (xs Φ)‖ ≤ ρ)
    (hballU : ∀ Φ, ∀ u ∈ I₀.𝒰, Metric.closedBall (u • S.shiftUC (xs Φ)) r ⊆ S.shiftDomC pp)
    (hdomU : ∀ Φ, ∀ u ∈ I₀.𝒰, ∀ τ ∈ 𝒯E, ∀ w ∈ Metric.closedBall (u • S.shiftUC (xs Φ)) r,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
    (hfac : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl, ∀ τ ∈ 𝒯E, rE τ ∈ Rs →
      Mk τ (s : ℂ) (xs (BS.restr x)) = Mk τ (s : ℂ) x)
    (y1 : {τ // τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs)} → I₀.Lb)
    (hlocxs : ∀ j u Φ Φ', (∀ b ∈ blocksOf m₀ (k + 1) Set.univ (I₀.Lab.ysite (y1 j)), Φ b = Φ' b) →
      Mk j.1 u (xs Φ) = Mk j.1 u (xs Φ'))
    (hdl : ∀ j, I₀.Lab.dl (y1 j) ≤ treeLenCovOne C.m₀ j.1.1 j.1.2.2)
    (hκG : I₀.κG ≤ κdec - 1)
    (F1 : {τ // τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs)} → ℝ) (hF1 : ∀ j, 0 < F1 j)
    (hF1b : ∀ j, P.E₀ / r * ρ ≤ F1 j) :
    ∃ G₁ : {τ // τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs)} → ℂ → (∀ b, BS.Ωb b) → ℂ,
      (∀ j u, Measurable (G₁ j u)) ∧
      (∀ j u, DepOn (blocksOf m₀ (k + 1) Set.univ (I₀.Lab.ysite (y1 j))) (G₁ j u)) ∧
      (∀ j u Φ, ‖G₁ j u Φ‖ ≤ F1 j * Real.exp (-I₀.κG * I₀.Lab.dl (y1 j))) ∧
      (∀ j Φ, DifferentiableOn ℂ (fun u => G₁ j u Φ) I₀.𝒰) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x)) =
          ∑ i, I₀.G i (s : ℂ) (BS.restr x) + ∑ j, G₁ j (s : ℂ) (BS.restr x)) := by
  have hτmem : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2 := by
    intro τ hτ
    rw [h𝒯] at hτ
    obtain ⟨hτ1, hτ2, hτ3, hτ4⟩ := (mem_classLabels_E_iff C.m₀ τ).1 hτ
    exact ⟨hτ1, hτ3, hτ4⟩
  have hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2} :=
    fun j h1 h2 y X hX hy => hcl.analyticE j h1 h2 y X (hm ▸ hX) hy
  have hκG0 : 0 ≤ I₀.κG := by
    have h1 := I₀.hκG
    have h2 := I₀.hκ
    have h3 := I₀.hκ'
    have h4 := I₀.hκ0
    have h5 := aEnt_nonneg d L
    have h6 : 0 ≤ c1 d L := by unfold c1; positivity
    linarith
  refine ⟨fun j u Φ => if u ∈ I₀.𝒰 then Mk j.1 u (xs Φ) else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j u
    by_cases hu : u ∈ I₀.𝒰
    · simp only [hu, ite_true]
      simp_rw [hMk]
      exact measurable_fderiv_apply_pi _
        (show Measurable fun Φ => u • S.shiftUC (xs Φ) from
          (S.continuous_shiftUC.measurable.comp hxs).const_smul u)
        ((S.continuous_maskUC z).measurable.comp (S.continuous_shiftUC.measurable.comp hxs))
    · simp only [hu, ite_false]
      exact measurable_const
  · intro j u Φ Φ' h
    by_cases hu : u ∈ I₀.𝒰
    · simp only [hu, ite_true]
      exact hlocxs j u Φ Φ' h
    · simp only [hu, ite_false]
  · intro j u Φ
    by_cases hu : u ∈ I₀.𝒰
    · simp only [hu, ite_true]
      rw [hMk]
      have hj := Finset.mem_filter.1 j.2
      have hτ := hτmem j.1 hj.1
      refine (S.norm_fderiv_classLabel_le C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hm
        hcl hκ hE₀ hr (hballU Φ u hu) j.1 hτ (hdomU Φ u hu j.1 hj.1) _).trans ?_
      have hmask := norm_maskUC_le S z _ (hρxs Φ)
      have hd0 := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        C.m₀ j.1.1 j.1.2.2
      have hexp : Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j.1.1 j.1.2.2) ≤
          Real.exp (-I₀.κG * I₀.Lab.dl (y1 j)) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_le_mul_of_nonneg_left (hdl j) hκG0
        have := mul_le_mul_of_nonneg_right hκG hd0
        linarith
      have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρxs Φ)
      calc P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j.1.1 j.1.2.2) / r *
            ‖S.maskUC z (S.shiftUC (xs Φ))‖
          ≤ P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j.1.1 j.1.2.2) / r * ρ :=
            mul_le_mul_of_nonneg_left hmask (by positivity)
        _ = (P.E₀ / r * ρ) * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ j.1.1 j.1.2.2) := by
            ring
        _ ≤ F1 j * Real.exp (-I₀.κG * I₀.Lab.dl (y1 j)) :=
            mul_le_mul (hF1b j) hexp (Real.exp_pos _).le (hF1 j).le
    · simp only [hu, ite_false, norm_zero]
      exact mul_nonneg (hF1 j).le (Real.exp_pos _).le
  · intro j Φ
    have hj := Finset.mem_filter.1 j.2
    have hτ := hτmem j.1 hj.1
    have hdiff : DifferentiableOn ℂ (fun u => Mk j.1 u (xs Φ)) I₀.𝒰 := by
      intro u hu
      have hc : AnalyticAt ℂ (fun u : ℂ => u • S.shiftUC (xs Φ)) u :=
        analyticAt_id.smul analyticAt_const
      have hy₀ : u • S.shiftUC (xs Φ) ∈ S.shiftDomC pp :=
        hballU Φ u hu (Metric.mem_closedBall_self hr.le)
      have hcen := hdomU Φ u hu j.1 hj.1 _ (Metric.mem_closedBall_self hr.le)
      have han := ((S.analyticAt_fderiv_classLabel_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
        hpp hδ₁ hD hE hy₀ j.1 hτ hcen (S.maskUC z (S.shiftUC (xs Φ)))).comp_of_eq hc rfl).congr
        (Filter.Eventually.of_forall fun u' => (hMk j.1 u' (xs Φ)).symm)
      exact han.differentiableAt.differentiableWithinAt
    refine hdiff.congr fun u hu => ?_
    simp only [hu, ite_true]
  · intro s hs
    have hvan : ∀ᵐ x ∂S.nuFl, ∀ τ ∈ 𝒯E, rE τ ∉ Rs → Mk τ (s : ℂ) x = 0 := by
      rw [Filter.eventually_all_finset]
      intro τ hτ
      by_cases hR' : rE τ ∈ Rs
      · exact Filter.Eventually.of_forall fun x h => absurd hR' h
      · filter_upwards [hbg τ hτ hR' (hτmem τ hτ) s hs] with x hx h
        rw [hMk]
        exact S.fderiv_classLabel_eq_zero_of_local C hcl _ _ τ (hτmem τ hτ)
          (hv τ hτ hR' _) hx
    filter_upwards [hdomX s hs, hfac s hs, hvan, I₀.hF s hs] with x hx hf hvx hF0
    obtain ⟨hy₀, hdomx⟩ := hx
    have hid := S.fderiv_Phi1C_class_eq_zero_add_oldE_labels C hC hMX hdm hα hsm ha₁ hc7 hR hsmR
      hβ hpp hδ₁ hD hE 𝒯E h𝒯 hy₀ hdomx (S.maskUC z (S.shiftUC x))
    rw [hid, hF0]
    congr 1
    have hsub : ∑ τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs), Mk τ (s : ℂ) x =
        ∑ τ ∈ 𝒯E, Mk τ (s : ℂ) x := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun τ hτ hn => hvx τ hτ ?_
      intro hmem
      exact hn (Finset.mem_filter.2 ⟨hτ, hmem⟩)
    have hs' : (s : ℂ) ∈ I₀.𝒰 := I₀.seg s hs
    calc ∑ τ ∈ 𝒯E, fderiv ℂ (fun w : S.EC =>
          C.Tm.E τ.1 τ.2.1 τ.2.2
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
          ((s : ℂ) • S.shiftUC x) (S.maskUC z (S.shiftUC x))
        = ∑ τ ∈ 𝒯E, Mk τ (s : ℂ) x :=
          Finset.sum_congr rfl fun τ _ => (hMk τ _ x).symm
      _ = ∑ τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs), Mk τ (s : ℂ) x := hsub.symm
      _ = ∑ τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs), Mk τ (s : ℂ) (xs (BS.restr x)) :=
          Finset.sum_congr rfl fun τ hτ =>
            (hf τ (Finset.mem_filter.1 hτ).1 (Finset.mem_filter.1 hτ).2).symm
      _ = _ := by
          rw [← Finset.sum_coe_sort (𝒯E.filter (fun τ => rE τ ∈ Rs))]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hs', ite_true]

open Classical in
include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The value of the local energy term of a class member from the labels of the inherited
energy.**  Under the hypotheses of `exists_oldMarks_of_labels`, with the activity `A'` of the
exponent `WoneC C` (`hW'`; it carries the inherited energy), `ℰ₁^C(z) = ∑_T c^C(T)` with
`c^C = gsumCoeff μ Lab A' (zero anchors ⊕ y1) (zero marks ⊕ G₁)` for the old marks `G₁` of
`exists_oldMarks_of_labels`, and
`‖c^C T‖ ≤ C_PE (∑ F₀ e^{-κ₀ 𝗱} + ∑_j F1 j e^{-κ₀ 𝗱(y1 j)}) e^{-κ' d_Ext(T)}`.  The premises
`hF'` and the clauses of `G₁` of `e1locC_class_value_of_zero_add_old` are discharged. -/
theorem e1locC_class_value_of_labels {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀)
    (I₀ : E1MarksC S (zeroClass d L N₁ m₁ k N ϱ) BS z)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    (rE : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) →
      CTorus d L N₁ m₁ (k + 1)) (Rs : Finset (CTorus d L N₁ m₁ (k + 1)))
    (Mk : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) → ℂ → S.E → ℂ)
    (hMk : ∀ τ u x, Mk τ u x = fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
      (u • S.shiftUC x) (S.maskUC z (S.shiftUC x)))
    (hv : ∀ τ ∈ 𝒯E, rE τ ∉ Rs → ∀ (w : S.EC) (x : CTorus d L N₁ m₁ (k + 1)), x ∈ τ.2.2 →
      ∀ i, S.maskUC z w (unitPt S.hG' x, i) = 0)
    (hbg : ∀ τ ∈ 𝒯E, rE τ ∉ Rs →
      ∀ (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2),
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl, ∀ᶠ t : ℂ in nhds 0, ∀ x' ∈ τ.2.2, ∀ y ∈
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
          (hτ.1.2.trans (Nat.le_succ k))).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
            (hτ.1.2.trans (Nat.le_succ k))).layerIndex x') x' ∪
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
          (Nat.le_succ k)).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k)).layerIndex x') x',
        ∀ i, svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k))
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
              (Nat.le_succ k)) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C +
                ((s : ℂ) • S.shiftUC x + t • S.maskUC z (S.shiftUC x))))) y i =
          svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k))
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
              (Nat.le_succ k)) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C +
                ((s : ℂ) • S.shiftUC x))) ) y i)
    (hdomX : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (s : ℂ) • S.shiftUC x ∈ S.shiftDomC pp ∧
      ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X → Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + (s : ℂ) • S.shiftUC x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + (s : ℂ) • S.shiftUC x))).2)
    (xs : (∀ b, BS.Ωb b) → S.E) (hxs : Measurable xs) {ρ r : ℝ} (hr : 0 < r)
    (hρxs : ∀ Φ, ‖S.shiftUC (xs Φ)‖ ≤ ρ)
    (hballU : ∀ Φ, ∀ u ∈ I₀.𝒰, Metric.closedBall (u • S.shiftUC (xs Φ)) r ⊆ S.shiftDomC pp)
    (hdomU : ∀ Φ, ∀ u ∈ I₀.𝒰, ∀ τ ∈ 𝒯E, ∀ w ∈ Metric.closedBall (u • S.shiftUC (xs Φ)) r,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
    (hfac : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl, ∀ τ ∈ 𝒯E, rE τ ∈ Rs →
      Mk τ (s : ℂ) (xs (BS.restr x)) = Mk τ (s : ℂ) x)
    (y1 : {τ // τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs)} → I₀.Lb)
    (hlocxs : ∀ j u Φ Φ', (∀ b ∈ blocksOf m₀ (k + 1) Set.univ (I₀.Lab.ysite (y1 j)), Φ b = Φ' b) →
      Mk j.1 u (xs Φ) = Mk j.1 u (xs Φ'))
    (hdl : ∀ j, I₀.Lab.dl (y1 j) ≤ treeLenCovOne C.m₀ j.1.1 j.1.2.2)
    (hκG : I₀.κG ≤ κdec - 1)
    (F1 : {τ // τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs)} → ℝ) (hF1 : ∀ j, 0 < F1 j)
    (hF1b : ∀ j, P.E₀ / r * ρ ≤ F1 j)
    (A' : ℂ → LabelAct I₀.Lab BS.Ωb I₀.εH I₀.κH I₀.κ0 I₀.Kc)
    (holA' : ∀ y Φ, DifferentiableOn ℂ (fun u => (A' u).H y Φ) I₀.𝒰)
    (hW' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.WoneC C s x = ∑ y, (A' (s : ℂ)).H y (BS.restr x)) :
    ∃ G₁ : {τ // τ ∈ 𝒯E.filter (fun τ => rE τ ∈ Rs)} → ℂ → (∀ b, BS.Ωb b) → ℂ,
      S.E1locC C z = ∑ T, gsumCoeff BS.μ I₀.Lab A' (Sum.elim I₀.y0 y1) (Sum.elim I₀.G G₁) T ∧
      ∀ T, ‖gsumCoeff BS.μ I₀.Lab A' (Sum.elim I₀.y0 y1) (Sum.elim I₀.G G₁) T‖ ≤
        CPE d L I₀.Kc I₀.κH I₀.κ0 I₀.κ' *
          ((∑ i, I₀.F0 i * Real.exp (-I₀.κ0 * I₀.Lab.dl (I₀.y0 i))) +
            ∑ j, F1 j * Real.exp (-I₀.κ0 * I₀.Lab.dl (y1 j))) * Real.exp (-I₀.κ' * dExt T) := by
  obtain ⟨G₁, hmeas, hdep, hbd, hhol, hF⟩ := S.exists_oldMarks_of_labels C hC hMX hdm hα hsm ha₁ hc7
    hR hsmR hβ hpp hδ₁ hD hm hcl hκ hE₀ I₀ 𝒯E h𝒯 rE Rs Mk hMk hv hbg hdomX xs hxs hr hρxs hballU hdomU hfac y1 hlocxs hdl hκG F1 hF1 hF1b
  exact ⟨G₁, e1locC_class_value_of_zero_add_old I₀ y1 F1 hF1 G₁ hmeas hdep hbd hhol A' holA' hW' hF⟩

end Chart

end StepSetting

end Balaban.Fluctuation
