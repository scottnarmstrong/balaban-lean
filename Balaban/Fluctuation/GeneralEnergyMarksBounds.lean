/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralEnergyMarks
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The old energy terms of a class member in the first-order marks of the step (part 2)

The mark of a label `τ = (j, y, X)` of the old energy is the derivative of the label term
`w ↦ ℰ^{(j)}(y, X; pair_j(w))` at the shift `y₀ = s ψ'` in the direction `v = M_z ψ'`.

* `norm_fderiv_le_of_closedBall`: the Cauchy estimate for a complex-differentiable function on a
  closed ball of a normed space: `‖Df(y)[v]‖ ≤ B ‖v‖ / r`.
* `norm_classLabel_le`: the label term is at most `E₀ exp(-(κ_dec - 1) d_j(X))` on the class domain.
* `norm_fderiv_classLabel_le`: the Cauchy bound of the mark of a label.
* `composedPairAtC_agree_on`, `fderiv_classLabel_eq_zero_of_local`: the mark of a label vanishes when
  the direction does not read the unit points of the polymer and the complex background does not
  change on the blocks of its sites (locality).
* `norm_oldMark_le`: the Cauchy bound in the form of the integrand of `E1locC`.
* `norm_sum_fderiv_classLabels_le`: the sum over the labels, with the per-site summability of the
  weights as an explicit hypothesis.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Metric

/-- **The Cauchy estimate in a normed space.**  A complex-differentiable function bounded by `B` on
the closed ball of radius `r > 0` about `y` has derivative at most `B ‖v‖ / r` in the direction
`v`. -/
theorem norm_fderiv_le_of_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {y : E} {r B : ℝ} (hr : 0 < r) (hd : DifferentiableOn ℂ f (closedBall y r))
    (hB : ∀ w ∈ closedBall y r, ‖f w‖ ≤ B) (v : E) :
    ‖fderiv ℂ f y v‖ ≤ B / r * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv; simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hfy : DifferentiableAt ℂ f y := hd.differentiableAt (closedBall_mem_nhds y hr)
  set R : ℝ := r / ‖v‖ with hR
  have hRpos : 0 < R := div_pos hr hvpos
  set g : ℂ → ℂ := fun t => f (y + t • v) with hg
  have hmaps : ∀ t : ℂ, t ∈ closedBall (0 : ℂ) R → y + t • v ∈ closedBall y r := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm] at ht ⊢
    rw [sub_zero] at ht
    have : y + t • v - y = t • v := by abel
    rw [this, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right ht hvpos.le
      _ = r := by rw [hR]; field_simp
  have haff : Differentiable ℂ (fun t : ℂ => y + t • v) :=
    (differentiable_const _).add ((differentiable_id).smul_const v)
  have hgd : DifferentiableOn ℂ g (closedBall (0 : ℂ) R) :=
    hd.comp haff.differentiableOn hmaps
  have hcl : DiffContOnCl ℂ g (ball (0 : ℂ) R) :=
    ⟨hgd.mono ball_subset_closedBall, by
      rw [closure_ball _ hRpos.ne']; exact hgd.continuousOn⟩
  have hsph : ∀ t ∈ sphere (0 : ℂ) R, ‖g t‖ ≤ B := fun t ht =>
    hB _ (hmaps t (sphere_subset_closedBall ht))
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hcl hsph
  have hder : HasDerivAt g (fderiv ℂ f y v) 0 := by
    have h2 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using hfy.hasFDerivAt
    have h3 : HasDerivAt (fun t : ℂ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    exact h2.comp_hasDerivAt (0 : ℂ) h3
  rw [hder.deriv] at h1
  calc ‖fderiv ℂ f y v‖ ≤ B / R := h1
    _ = B / r * ‖v‖ := by rw [hR]; field_simp

/-- **A derivative along a line on which the function is constant vanishes.** -/
theorem fderiv_apply_eq_zero_of_eventually_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {y : E} (v : E)
    (h : ∀ᶠ t : ℂ in nhds 0, f (y + t • v) = f y) : fderiv ℂ f y v = 0 := by
  by_cases hfy : DifferentiableAt ℂ f y
  · have hder : HasDerivAt (fun t : ℂ => f (y + t • v)) (fderiv ℂ f y v) 0 := by
      have h2 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
        simpa using hfy.hasFDerivAt
      have h3 : HasDerivAt (fun t : ℂ => y + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
      exact h2.comp_hasDerivAt (0 : ℂ) h3
    have hc : HasDerivAt (fun t : ℂ => f (y + t • v)) 0 0 :=
      (hasDerivAt_const (0 : ℂ) (f y)).congr_of_eventuallyEq h
    exact hder.unique hc
  · rw [fderiv_zero_of_not_differentiableAt hfy]; rfl

/-- **A sum with per-site summable weights.**  If `m τ ≤ b τ` with `b ≥ 0`, `m τ = 0` unless
`rE τ ∈ R`, and the weights `b` over every fibre of `rE` add up to at most `ρ`, then
`∑ m ≤ |R| ρ`. -/
theorem sum_le_card_mul_of_fibre {ι σ : Type*} [DecidableEq σ] (𝒯 : Finset ι) (rE : ι → σ)
    (R : Finset σ) (m b : ι → ℝ) (hb0 : ∀ τ ∈ 𝒯, 0 ≤ b τ) (hmb : ∀ τ ∈ 𝒯, m τ ≤ b τ)
    (hz : ∀ τ ∈ 𝒯, rE τ ∉ R → m τ = 0) {ρ : ℝ}
    (hρ : ∀ x, ∑ τ ∈ 𝒯.filter (fun τ => rE τ = x), b τ ≤ ρ) :
    ∑ τ ∈ 𝒯, m τ ≤ R.card * ρ := by
  classical
  have h1 : ∑ τ ∈ 𝒯, m τ ≤ ∑ τ ∈ 𝒯.filter (fun τ => rE τ ∈ R), b τ := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun τ hτ => ?_
    by_cases h : rE τ ∈ R
    · simpa [h] using hmb τ hτ
    · simp [h, hz τ hτ h]
  refine h1.trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := rE) (t := R)
    (fun τ hτ => (Finset.mem_filter.1 hτ).2)]
  calc ∑ x ∈ R, ∑ τ ∈ (𝒯.filter (fun τ => rE τ ∈ R)).filter (fun τ => rE τ = x), b τ
      ≤ ∑ x ∈ R, ρ := by
        refine Finset.sum_le_sum fun x _ => le_trans ?_ (hρ x)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun τ hτ _ => hb0 τ (Finset.mem_filter.1 hτ).1)
        intro τ hτ
        simp only [Finset.mem_filter] at hτ ⊢
        exact ⟨hτ.1.1, hτ.2⟩
    _ = R.card * ρ := by simp

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The label term is bounded on the class domain.**  For `κ_dec - 1 ≤ κ_P` the label term
`ℰ^{(j)}(y, X; Ψ, h)` of the class at a pair in the field domain of the polymer is at most
`E₀ exp(-(κ_dec - 1) d_j(X))`. -/
theorem norm_classLabel_le {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ) (hE₀ : 0 ≤ P.E₀)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N) (hdom : Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2) Ψ h) :
    ‖C.Tm.E τ.1 τ.2.1 τ.2.2 Ψ h‖ ≤
      P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) := by
  obtain ⟨⟨h1, h2⟩, hX, hy⟩ := hτ
  have hb := hcl.boundE τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2 (hm ▸ hX) hy Ψ h hdom
  refine hb.trans ?_
  unfold sizeJ
  rw [hm]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE₀
  have := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
    C.m₀ τ.1 τ.2.2
  nlinarith

/-- **The composed pair at a site depends only on the data and background near the site.**  Let
`1 ≤ j ≤ k ≤ K`, and let `D`, `D'` be complex data of the level `k`.  If the spin and the source of
`D`, `D'` agree on a set `X` of sites, and the complex backgrounds `bgFieldC` of `D`, `D'` agree
(as extended fields `svec`) on the `j`-blocks and the `k`-blocks of the sites of `X`, then the
composed pairs of `D`, `D'` at the level `j` agree on `X`. -/
theorem composedPairAtC_agree_on {K : ℕ} (a : ℕ → ℝ) (ν : ℝ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hk : k ≤ K)
    (D D' : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk) N)
    (X : Set (CTorus d L N₁ m₁ K))
    (hΨ : ∀ x ∈ X, ∀ i, D.Ψ x i = D'.Ψ x i) (hh : ∀ x ∈ X, ∀ i, D.h x i = D'.h x i)
    (hφ : ∀ x ∈ X, ∀ y ∈
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j (hjk.trans hk)).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
            (hjk.trans hk)).layerIndex x) x ∪
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk).layerIndex x) x,
        ∀ i, svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
              a ν (bgC0 d L N) D) y i =
          svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
              a ν (bgC0 d L N) D') y i) :
    ∀ x ∈ X, (composedPairAtC a ν hk j D).1 x = (composedPairAtC a ν hk j D').1 x ∧
      (composedPairAtC a ν hk j D).2 x = (composedPairAtC a ν hk j D').2 x := by
  intro x hx
  have hxΩ : x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      (hjk.trans hk)).Ω 1 := by simp [levelGS, hj1]
  simp only [composedPairAtC, hjk, ↓reduceDIte, composedDataAtC, composeData]
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · simp only [composeField_of_mem _ _ _ hxΩ]
    have e1 : blockMean (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
        (hjk.trans hk)) ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
        (hjk.trans hk)).layerIndex x)
        (fun y => svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
          (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
            a ν (bgC0 d L N) D) y i) x =
        blockMean (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
        (hjk.trans hk)) ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
        (hjk.trans hk)).layerIndex x)
        (fun y => svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
          (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
            a ν (bgC0 d L N) D') y i) x := by
      unfold blockMean
      congr 1
      exact Finset.sum_congr rfl fun y hy => hφ x hx y (Finset.mem_union_left _ hy) i
    have e2 : blockMean (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
        ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk).layerIndex x)
        (fun y => svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
          (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
            a ν (bgC0 d L N) D) y i) x =
        blockMean (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
        ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk).layerIndex x)
        (fun y => svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
          (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) k hk)
            a ν (bgC0 d L N) D') y i) x := by
      unfold blockMean
      congr 1
      exact Finset.sum_congr rfl fun y hy => hφ x hx y (Finset.mem_union_right _ hy) i
    rw [e1, e2, hΨ x hx i]
  · simp only [hxΩ, ite_true, hh x hx i]

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

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The Cauchy bound of the mark of a label of the old energy** (part 2 (ii)).  Let
`y₀` be a complex shift and `r > 0` such that the closed ball of radius `r` about `y₀` lies in the
chart `shiftDomC p⁺` and the composed pair of the label's polymer lies in the class domain at every
shift of the ball (`hdom`, the chart inclusion `hchart` of `classOldEnergy_analytic_bound`).
Then for every direction `v`,
`‖D(ℰ^{(j)}(y, X) ∘ pair)(y₀)[v]‖ ≤ E₀ exp(-(κ_dec - 1) d_j(X)) ‖v‖ / r`.
With `y₀ = s ψ'`, `v = M_z ψ'` this bounds the mark of the label in `E1locC`. -/
theorem norm_fderiv_classLabel_le {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀)
    {y₀ : S.EC} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall y₀ r ⊆ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hdom : ∀ w ∈ Metric.closedBall y₀ r, Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
    (v : S.EC) :
    ‖fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ v‖ ≤
      P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) / r * ‖v‖ := by
  refine norm_fderiv_le_of_closedBall hr ?_ (fun w hw => ?_) v
  · intro w hw
    exact (S.analyticAt_classLabel_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
      (fun j h1 h2 y X hX hy => hcl.analyticE j h1 h2 y X (hm ▸ hX) hy) (hball hw) τ hτ (hdom w hw)).differentiableAt.differentiableWithinAt
  · exact norm_classLabel_le C hm hcl hκ hE₀ τ hτ _ _ (hdom w hw)

/-- **Locality of the mark of a label of the old energy** (part 2 (i)).  Let `v` be a direction of
the unit lattice that vanishes at the unit points of the sites of the polymer `X_τ`
(for `v = M_z ψ'`: the block of `z` does not meet the unit points of `X_τ`), and suppose that along
the line `y₀ + t v` (for small `t`) the complex background of the datum agrees, on the `j`-blocks
and `k`-blocks of the sites of `X_τ`, with the background at `y₀` (`hbg`).  Then the mark of the
label vanishes: the spin and the source of the composed pair on `X_τ` read the datum only at the
unit points of `X_τ`, and the background only on the blocks (`composedPairAtC_agree_on`), and
`ℰ^{(j)}(y, X)` reads its arguments only on `X` (clause `localE`).  The hypothesis `hbg` is the
only non-local ingredient: `bgFieldC` is the solution of a global problem. -/
theorem fderiv_classLabel_eq_zero_of_local {P : Consts} (hcl : SFTermClauses P Dom C.Tm)
    (y₀ v : S.EC)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hv : ∀ x ∈ τ.2.2, ∀ i, v (unitPt S.hG' x, i) = 0)
    (hbg : ∀ᶠ t : ℂ in nhds 0, ∀ x ∈ τ.2.2, ∀ y ∈
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
          (hτ.1.2.trans (Nat.le_succ k))).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) τ.1
            (hτ.1.2.trans (Nat.le_succ k))).layerIndex x) x ∪
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
          (Nat.le_succ k)).blk
          ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k)).layerIndex x) x,
        ∀ i, svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k))
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
              (Nat.le_succ k)) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + (y₀ + t • v)))) y i =
          svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
            (Nat.le_succ k))
            (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
              (Nat.le_succ k)) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + y₀))) y i) :
    fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ v = 0 := by
  refine fderiv_apply_eq_zero_of_eventually_eq v ?_
  filter_upwards [hbg] with t ht
  obtain ⟨⟨h1, h2⟩, hX, hy⟩ := hτ
  have hag := composedPairAtC_agree_on S.a S.ν h1 h2 (Nat.le_succ k)
    (S.dataUC (S.psi0C + (y₀ + t • v))) (S.dataUC (S.psi0C + y₀)) τ.2.2
    (fun x hx i => by
      rw [S.dataUC_Ψ, S.dataUC_Ψ]
      simp [hv x hx i])
    (fun x hx i => by rw [S.dataUC_h, S.dataUC_h]) ht
  exact hcl.localE _ _ _ _ _ _ _ hag

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The mark of a label in the form of `E1locC`** (part 2 (ii)).  For `y₀ = s ψ'(ψ̂)` and
`v = M_z ψ'(ψ̂)` (`ψ' = shiftUC ψ̂`, `M_z = maskUC z`), if `‖ψ'‖ ≤ ρ` the mark of the label
satisfies `‖D(ℰ^{(j)}(y, X) ∘ pair)(y₀)[v]‖ ≤ E₀ exp(-(κ_dec - 1) d_j(X)) ρ / r`. -/
theorem norm_oldMark_le {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀) (s : ℝ) (x : S.E) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    {ρ : ℝ} (hρ : ‖S.shiftUC x‖ ≤ ρ) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall ((s : ℂ) • S.shiftUC x) r ⊆ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hdom : ∀ w ∈ Metric.closedBall ((s : ℂ) • S.shiftUC x) r,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) :
    ‖fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
      ((s : ℂ) • S.shiftUC x) (S.maskUC z (S.shiftUC x))‖ ≤
      P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) / r * ρ := by
  refine (S.norm_fderiv_classLabel_le C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hm hcl hκ
    hE₀ hr hball τ hτ hdom _).trans ?_
  have hmask : ‖S.maskUC z (S.shiftUC x)‖ ≤ ρ := by
    refine le_trans ?_ hρ
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun q => ?_
    unfold maskUC
    split_ifs
    · exact norm_le_pi_norm (S.shiftUC x) q
    · simp
  have hc : 0 ≤ P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) / r :=
    by positivity
  exact mul_le_mul_of_nonneg_left hmask hc

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The sum of the marks of the labels** (part 2 (iii)).  Let `𝒯E` be a finite set of labels of
the class, `R` a finite set of sites, `rE τ` a site attached to `τ`, such that the mark of `τ`
vanishes unless `rE τ ∈ R` (`hloc`; see `fderiv_classLabel_eq_zero_of_local`) and the weights
`E₀ exp(-(κ_dec - 1) d_j(X_τ))` over each fibre of `rE` add up to at most `ρE` (the per-site
summability `hρE` of the constructor).  Then the old-energy part of the marks satisfies
`‖∑_τ D(ℰ_τ ∘ pair)(y₀)[v]‖ ≤ |R| ρE ‖v‖ / r`. -/
theorem norm_sum_fderiv_classLabels_le {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    {y₀ : S.EC} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall y₀ r ⊆ S.shiftDomC pp)
    (hdom : ∀ τ ∈ 𝒯E, ∀ w ∈ Metric.closedBall y₀ r, Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
    (v : S.EC) (rE : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) →
      CTorus d L N₁ m₁ (k + 1)) (R : Finset (CTorus d L N₁ m₁ (k + 1)))
    (hloc : ∀ τ ∈ 𝒯E, rE τ ∉ R → fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ v = 0)
    {ρE : ℝ}
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) ≤ ρE) :
    ‖∑ τ ∈ 𝒯E, fderiv ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ v‖ ≤
      R.card * (ρE / r * ‖v‖) := by
  classical
  refine (norm_sum_le _ _).trans ?_
  refine sum_le_card_mul_of_fibre 𝒯E rE R _
    (fun τ => P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) / r * ‖v‖)
    (fun τ _ => by positivity)
    (fun τ hτ => S.norm_fderiv_classLabel_le C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hm
      hcl hκ hE₀ hr hball τ (h𝒯 τ hτ) (hdom τ hτ) v)
    (fun τ hτ h => by rw [hloc τ hτ h]; simp) (fun x => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_div]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hρE x) hr.le) (norm_nonneg _)

end Chart

end StepSetting

end Balaban.Fluctuation
