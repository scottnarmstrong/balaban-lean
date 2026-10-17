/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalConstants
public import Balaban.Green.FinalConnectedSupport
public import Balaban.Localization.DecEquivCoef
public import Balaban.Fluctuation.LocalClassMRot
public import Balaban.Polymer.TwoTorusFinal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Term-by-term coefficient bounds for the last integral (blocker 5)

The cut-family integral `J_G(s) = ∫_{box ρ} G(φ₀ + β^{-1/2} C_fin(s) ψ) dγ(ψ)` of an interaction
`G = ∑_t f_t` that is a sum of local terms is treated term by term.

* `integrable_cutoff_integrand`: the integrand of a function analytic and bounded on the polydisc of
  radius `R` around `φ₀` is integrable for `s` in the polydisc of radius `e^κ`.
* `coef_cutoff_eq_zero_of_read`: if `G` reads the field only on a set `S` that misses the region
  `Y(C)` of a nonempty set `C` of cut cells, the coefficient of `J_G` at `C` vanishes.  The reason
  is `taggedCfinU_eq_zero_of_not_mem`: at a parameter supported on `C` the cut family has the row
  `x` equal to zero unless `x ∈ Y(C)`.
* `coef_cutoff_term`: the bound of one term by its own sup and the vanishing off its region.
* `coef_cutoff_sum_eq_near`, `norm_coef_cutoff_sum_le_near`: for `F = ∑_{t ∈ T} f_t` the coefficient
  of `J_F` at `C ≠ ∅` is the sum over the terms whose read set meets `Y(C)`, bounded by
  `γ(box) e^{-(κ-1)|C|} ∑_{t near C} b_t`, with no sum over the other terms.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban.Localization Balaban.Analysis

namespace Balaban.Green

section Cut

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The integrand of the cut integral is integrable.**  For `G` analytic and bounded on the
polydisc of radius `Rphys` around `φ₀`, `s` in the polydisc of radius `e^κ`, and
`B β^{-1/2} ρ < Rphys`. -/
theorem integrable_cutoff_integrand (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ Rphys B' β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < Rphys)
    {G : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ}
    (hG : AnalyticOnNhd ℂ G (polydisc φ₀ (fun _ => Rphys)))
    (hGB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖G w‖ ≤ B')
    {s : MacIdx d N₀ M → ℂ}
    (hs : s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :
    Integrable (fun ψ : L1Torus d N₀ → ℝ =>
      G (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)))
      (γ.restrict {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hc0 : 0 < β ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hβ _
  have hcl : ∀ p, ‖s p‖ ≤ Real.exp κ := fun p => by simpa using (hs p).le
  have hclosed : IsClosed {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y => isClosed_le (by fun_prop) continuous_const
  have hmeas : MeasurableSet {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} := hclosed.measurableSet
  have hmem : ∀ ψ ∈ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∈
        polydisc φ₀ (fun _ => Rphys) := by
    intro ψ hψ x
    have h := norm_taggedCfin_mulVec_le (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M)
      hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hcl hρ
      (ψ := fun y => ((ψ y : ℝ) : ℂ)) (fun y => by simpa using hψ y) x
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc0]
    calc _ ≤ β ^ (-(1 / 2 : ℝ)) * ((4 / 3 * (2 * Real.exp (pdH d * κ) *
          ballConst d (pdEps d L / 2)) / Real.sqrt (finalGap d L)) * ρ) :=
          mul_le_mul_of_nonneg_left h hc0.le
      _ = (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) := by ring
      _ < Rphys := hBR
  have hcont : Continuous (fun ψ : L1Torus d N₀ → ℝ =>
      (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) := by
    refine continuous_pi fun x => ?_
    refine continuous_const.add (continuous_const.mul ?_)
    refine continuous_finsetSum _ fun y _ => continuous_const.mul ?_
    exact Complex.continuous_ofReal.comp (continuous_apply y)
  have : IsFiniteMeasure (γ.restrict {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hγ⟩
  refine Integrable.of_bound (C := B') ?_ ?_
  · exact (hG.continuousOn.comp hcont.continuousOn hmem).aestronglyMeasurable hmeas
  · exact ae_restrict_of_forall_mem hmeas fun ψ hψ => hGB _ (hmem ψ hψ)

/-- **A function that reads the field only off the region of `C` has vanishing coefficient at
`C ≠ ∅`.**  If `G w = G w'` whenever `w = w'` on `S` and `S` misses `Y(C)`, the integral
`J_G` is constant on the parameters supported on `C`: there the cut family has the rows
`x ∉ Y(C)` equal to zero (`taggedCfinU_eq_zero_of_not_mem`), so `G` sees `φ₀` on `S`. -/
theorem coef_cutoff_eq_zero_of_read (hd : 0 < d) (hM : 0 < M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ β : ℝ}
    {G : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ} {S : Set (L1Torus d N₀)}
    (hread : ∀ w w' : L1Torus d N₀ → ℂ, (∀ x ∈ S, w x = w' x) → G w = G w')
    {C : Finset (MacIdx d N₀ M)} (hC : C.Nonempty)
    (hS : ∀ x ∈ S, x ∉ macRegion d N₀ M C) :
    coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        G (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hC
  refine coef_eq_zero_of_inv hi₀ ?_
  have key : ∀ s ∈ supportedOn C, ∀ ψ : L1Torus d N₀ → ℝ,
      G (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) = G φ₀ := by
    intro s hs ψ
    refine hread _ _ fun x hx => ?_
    have h0 : ∀ y, taggedCfin d L N₀ k M v a s x y = 0 := fun y => by
      rw [← taggedCfinU_finalOp]
      exact taggedCfinU_eq_zero_of_not_mem hM hd _ hs fun h => hS x hx h.1
    simp [h0]
  intro w hw τ
  have hw' := add_single_mem_supportedOn hw hi₀ τ
  simp only [key w hw, key _ hw']

/-- **One local term of the last-scale interaction.**  Let `f` be analytic on the polydisc of
radius `Rphys` around `φ₀`, bounded there by `b` (the sup `E₀ e^{-κ d_j(X)}` of one term), and let
it read the field only on the set `S`.  Then `J_f` is analytic on the polydisc of radius `e^κ`,
every coefficient is bounded by `b γ(box) e^{-(κ-1)|C|}`, and the coefficient vanishes at every
nonempty `C` whose region `Y(C)` misses `S`. -/
theorem coef_cutoff_term (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ Rphys b β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < Rphys)
    {f : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ} {S : Set (L1Torus d N₀)}
    (hf : AnalyticOnNhd ℂ f (polydisc φ₀ (fun _ => Rphys)))
    (hfB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖f w‖ ≤ b)
    (hread : ∀ w w' : L1Torus d N₀ → ℂ, (∀ x ∈ S, w x = w' x) → f w = f w') :
    AnalyticOnNhd ℂ (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        f (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ C : Finset (MacIdx d N₀ M),
      ‖coef (fun s : MacIdx d N₀ M → ℂ =>
        ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
          f (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
        b * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal *
          Real.exp (-(κ - 1) * C.card)) ∧
    (∀ C : Finset (MacIdx d N₀ M), C.Nonempty → (∀ x ∈ S, x ∉ macRegion d N₀ M C) →
      coef (fun s : MacIdx d N₀ M → ℂ =>
        ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
          f (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C = 0) := by
  have key := cutoffInteraction_final_phys (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a)
    hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR hf hfB
  exact ⟨key.1, key.2.2.2.2.2, fun C hC hS => coef_cutoff_eq_zero_of_read hd hM hread hC hS⟩

open Classical in
/-- **The sum over the local terms, expanded term by term.**  Let `F = ∑_{t ∈ T} f_t`, each `f_t`
analytic on the polydisc of radius `Rphys` around `φ₀`, bounded there by `b t`, and reading the field
only on `S t`.  For every nonempty `C`, the coefficient of the cut integral `J_F` at `C` is the sum
of the coefficients of the terms whose read set meets `Y(C)`, and
`‖coef J_F C‖ ≤ γ(box) e^{-(κ-1)|C|} ∑_{t ∈ T, S t ∩ Y(C) ≠ ∅} b t`: the terms away from `C`
do not contribute, so the bound does not involve the sum over all `t`. -/
theorem coef_cutoff_sum_near {τ : Type*} (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ Rphys β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < Rphys)
    (T : Finset τ) (f : τ → (L1Torus d N₀ → ℂ) → ℂ) (b : τ → ℝ) (S : τ → Set (L1Torus d N₀))
    {φ₀ : L1Torus d N₀ → ℂ}
    (hf : ∀ t ∈ T, AnalyticOnNhd ℂ (f t) (polydisc φ₀ (fun _ => Rphys)))
    (hfB : ∀ t ∈ T, ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖f t w‖ ≤ b t)
    (hread : ∀ t ∈ T, ∀ w w' : L1Torus d N₀ → ℂ, (∀ x ∈ S t, w x = w' x) → f t w = f t w')
    (C : Finset (MacIdx d N₀ M)) (hC : C.Nonempty) :
    coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ) C =
      ∑ t ∈ T.filter (fun t => ∃ x ∈ S t, x ∈ macRegion d N₀ M C),
        coef (fun s : MacIdx d N₀ M → ℂ =>
          ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
            f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C ∧
    ‖coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ) C‖ ≤
      (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * Real.exp (-(κ - 1) * C.card) *
        ∑ t ∈ T.filter (fun t => ∃ x ∈ S t, x ∈ macRegion d N₀ M C), b t := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  have hterm := fun t (ht : t ∈ T) => coef_cutoff_term (N₀ := N₀) (M := M) (k := k) (L := L)
    (v := v) (a := a) hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR (hf t ht)
    (hfB t ht) (hread t ht)
  have hsum : ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      (∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ) =
      ∑ t ∈ T, ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ := fun s hs =>
    integral_finsetSum _ fun t ht => integrable_cutoff_integrand hd hk hv0 hv1 ha1 ha2 hmass hM hκ
      hMB hMκ hρ hβ hγ hBR (hf t ht) (hfB t ht) hs
  have hlin := coef_sum_linear hR T (fun _ => (1 : ℂ))
    (fun t s => ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
    (fun t ht => (hterm t ht).1) C
  have hcongr := coef_congr_polydisc hR (f := fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ)
    (g := fun s => ∑ t ∈ T, (1 : ℂ) * (∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ))
    (fun s hs => by simp only [one_mul]; exact hsum s hs) C
  have heq : coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ) C =
      ∑ t ∈ T.filter (fun t => ∃ x ∈ S t, x ∈ macRegion d N₀ M C),
        coef (fun s : MacIdx d N₀ M → ℂ =>
          ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
            f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C := by
    rw [hcongr, hlin, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [one_mul]
    split_ifs with h
    · rfl
    · push Not at h
      exact (hterm t ht).2.2 C hC h
  refine ⟨heq, ?_⟩
  rw [heq]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  have := (hterm t (Finset.mem_filter.1 ht).1).2.1 C
  calc _ ≤ _ := this
    _ = _ := by ring

end Cut

end Balaban.Green
