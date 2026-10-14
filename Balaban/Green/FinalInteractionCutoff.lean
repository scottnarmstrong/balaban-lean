/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLocalityAE
public import Balaban.Analysis.Cauchy
public import Balaban.Analysis.ParamIntegralAnalytic

/-!
# The cutoff interaction of the last integral (W789)

First leaves of route R1' of `notes/phase1/FINALPHYS3.md`.

* `differentiableOn_integral_pi`, `analyticOnNhd_integral_pi`: a parameter integral over a finite
  measure of functions that are analytic in a parameter `s ∈ ℂ^P` on an open set and uniformly
  bounded is analytic there (differentiation under the integral sign, Cauchy estimate for the
  derivative).
* `analyticOnNhd_integral_box`: the same for `∫_{box ρ} G (Φ s ψ) dγ(ψ)` when `G` is analytic on a
  polydisc that contains `Φ s ψ` for `s` in the polydisc of radius `e^κ` and `ψ` in the box.
* `norm_taggedCfin_mulVec_le`: the cut family applied to a bounded field stays in the box of
  radius `B ρ`, `B` the row bound of `taggedCfin`.
* `cutoffInteraction_final`: Lemma AE for `s ↦ ∫_{box ρ} F (C_fin(s) ψ) dγ(ψ)`.
* `localityAE_cutoffInteraction`, `coef_cutoffInteraction_congr_of_agree`: locality of the same
  integral for a general datum.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Filter Metric
open scoped Topology

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis

section Box

variable {P : Type*} [Fintype P] {I : Type*} [Fintype I]

/-- **L-B.**  Let `G` be analytic and bounded by `B'` on the polydisc of radius `R`, and let
`Φ s ψ` be analytic in `s` on the polydisc of radius `e^κ` for every `ψ` in the box
`{ψ | ∀ y, |ψ y| ≤ ρ}`, jointly continuous on (polydisc) × (box), with values in the polydisc of
radius `R`.  Then `s ↦ ∫_{box ρ} G (Φ s ψ) dγ(ψ)` is analytic on the polydisc of radius `e^κ` and
bounded there by `B' · γ(box ρ)`. -/
theorem analyticOnNhd_integral_box {γ : Measure (I → ℝ)} {ρ R B' κ : ℝ}
    (hγ : γ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {G : (I → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G (polydisc (0 : I → ℂ) (fun _ => R)))
    (hGB : ∀ w ∈ polydisc (0 : I → ℂ) (fun _ => R), ‖G w‖ ≤ B')
    {Φ : (P → ℂ) → (I → ℝ) → (I → ℂ)}
    (hΦan : ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) →
      AnalyticOnNhd ℂ (fun s => Φ s ψ) (polydisc (0 : P → ℂ) (fun _ => Real.exp κ)))
    (hΦcont : ContinuousOn (fun q : (P → ℂ) × (I → ℝ) => Φ q.1 q.2)
      (polydisc (0 : P → ℂ) (fun _ => Real.exp κ) ×ˢ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}))
    (hΦmem : ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ), ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) →
      Φ s ψ ∈ polydisc (0 : I → ℂ) (fun _ => R)) :
    AnalyticOnNhd ℂ (fun s => ∫ ψ in {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}, G (Φ s ψ) ∂γ)
      (polydisc (0 : P → ℂ) (fun _ => Real.exp κ)) ∧
    ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ),
      ‖∫ ψ in {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}, G (Φ s ψ) ∂γ‖ ≤
        B' * (γ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal := by
  set S : Set (I → ℝ) := {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ} with hS
  have hSe : S = Set.pi Set.univ (fun _ : I => Icc (-ρ) ρ) := by
    ext ψ; simp only [hS, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
  have hSk : IsCompact S := by rw [hSe]; exact isCompact_univ_pi fun _ => isCompact_Icc
  have hSm : MeasurableSet S := hSk.isClosed.measurableSet
  have : IsFiniteMeasure (γ.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hγ⟩
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · refine analyticAt_integral_of_continuousOn (μ := γ.restrict S) (K := S) hSk hSm
      (ae_restrict_mem hSm) (U := polydisc (0 : P → ℂ) (fun _ => Real.exp κ))
      ((isOpen_polydisc _ _).mem_nhds hs) (fun ψ hψ => ?_) ?_
    · intro e he
      exact AnalyticAt.comp (g := G) (f := fun s => Φ s ψ) (x := e)
        (hG _ (hΦmem e he ψ hψ)) (hΦan ψ hψ e he)
    · refine hG.continuousOn.comp hΦcont ?_
      intro q hq
      exact hΦmem q.1 hq.1 q.2 hq.2
  · refine (norm_setIntegral_le_of_norm_le_const hγ (fun ψ hψ => hGB _ (hΦmem s hs ψ hψ))).trans ?_
    simp [Measure.real]

end Box

section Final

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **L-A.**  The cut family applied to a bounded field stays in the box of radius `B ρ`:
for `‖ψ y‖ ≤ ρ` and `‖s p‖ ≤ e^κ`, `‖∑_y C_fin(s) x y ψ y‖ ≤ B ρ`, `B` the constant of
`abstract_expansion_taggedCfin_final`. -/
theorem norm_taggedCfin_mulVec_le (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {ψ : L1Torus d N₀ → ℂ} (hψ : ∀ y, ‖ψ y‖ ≤ ρ) (x : L1Torus d N₀) :
    ‖∑ y, taggedCfin d L N₀ k M v a s x y * ψ y‖ ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ := by
  have hrow := taggedCfin_row_bound (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hs (r := 0) le_rfl
    (by have := pdEps_pos (d := d) (L := L) hd; positivity) x
  simp only [zero_mul, Real.exp_zero, one_mul] at hrow
  calc ‖∑ y, taggedCfin d L N₀ k M v a s x y * ψ y‖
      ≤ ∑ y, ‖taggedCfin d L N₀ k M v a s x y * ψ y‖ := norm_sum_le _ _
    _ ≤ ∑ y, ‖taggedCfin d L N₀ k M v a s x y‖ * ρ := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hψ y) (norm_nonneg _)
    _ = (∑ y, ‖taggedCfin d L N₀ k M v a s x y‖) * ρ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow hρ

/-- **The cutoff interaction of the last integral.**  Let `F` be analytic and bounded by `B'` on
the polydisc of radius `R > B ρ` (`B` the constant of `norm_taggedCfin_mulVec_le`), and `γ` a
measure with `γ(box ρ) < ∞`.  Then `J(s) = ∫_{box ρ} F (C_fin(s) ψ) dγ(ψ)` is analytic on the
polydisc of radius `e^κ`, bounded by `B' γ(box ρ)`, takes at `s = 1` the value with
`C_fin(1) = √(final operator)`, and satisfies the conclusions of Lemma AE (sum of coefficients,
coefficient bounds); the datum is the fixed final operator, as in
`abstract_expansion_taggedCfin_final`. -/
theorem cutoffInteraction_final (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ R B' : ℝ} (hρ : 0 ≤ ρ)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * ρ < R)
    {F : (L1Torus d N₀ → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N₀ → ℂ) (fun _ => R)))
    (hFB : ∀ w ∈ polydisc (0 : L1Torus d N₀ → ℂ) (fun _ => R), ‖F w‖ ≤ B') :
    let J : (MacIdx d N₀ M → ℂ) → ℂ := fun s =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ
    AnalyticOnNhd ℂ J (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖J s‖ ≤ B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal) ∧
    J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) x y *
          ((ψ y : ℝ) : ℂ)) ∂γ ∧
    J (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef J C ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal /
      (Real.exp κ - 1) ^ C.card) ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal *
      Real.exp (-(κ - 1) * C.card)) := by
  intro J
  have hκ0 : 0 ≤ κ := by linarith
  have hcl : ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ∀ p, ‖s p‖ ≤ Real.exp κ := fun s hs p => by simpa using (hs p).le
  have hanC : ∀ x y, AnalyticOnNhd ℂ (fun s => taggedCfin d L N₀ k M v a s x y)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := fun x y =>
    (taggedCfin_analyticOnNhd (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk hv0
      hv1 ha1 ha2 hmass hM hκ0 hMB hMκ x y).mono fun s hs p => by simpa using hs p
  set Φ : (MacIdx d N₀ M → ℂ) → (L1Torus d N₀ → ℝ) → (L1Torus d N₀ → ℂ) := fun s ψ x =>
    ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ) with hΦ
  have hbox := analyticOnNhd_integral_box (γ := γ) (ρ := ρ) (R := R) (B' := B') (κ := κ) hγ hF hFB
    (Φ := Φ) ?_ ?_ ?_
  · have hAE := abstract_expansion
      (P := fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (Y := fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C)
      (F := fun (_ : L1Torus d N₀ × L1Torus d N₀ → ℂ) s => J s) hκ
      (B := B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal)
      (fun _ => hbox.1) (fun _ => hbox.2)
      (localityAE_macBox_of_agree (G := fun _ s => J s) fun _ _ _ _ _ _ => rfl)
    have h1 : J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) x y *
          ((ψ y : ℝ) : ℂ)) ∂γ := by
      show ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, taggedCfin d L N₀ k M v a (fun _ => 1) x y * ((ψ y : ℝ) : ℂ)) ∂γ = _
      rw [taggedCfin_one hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ]
    refine ⟨hbox.1, hbox.2, h1, ?_, fun C => hAE.2.2.2.1 (fun _ => 0) C,
      fun C => hAE.2.2.2.2 (fun _ => 0) C⟩
    have := hAE.1 (fun _ => 0)
    classical
    rw [Finset.filter_true_of_mem fun C _ =>
      isConnectedFamily_macBox (d := d) (N₀ := N₀) (M := M) C] at this
    exact this
  · intro ψ _ s hs
    refine AnalyticAt.pi fun x => ?_
    exact Finset.analyticAt_fun_sum _ fun y _ =>
      (hanC x y s hs).mul (analyticAt_const (𝕜 := ℂ))
  · refine continuousOn_pi.2 fun x => ?_
    refine continuousOn_finsetSum _ fun y _ => ?_
    refine ((hanC x y).continuousOn.comp continuousOn_fst fun q hq => hq.1).mul ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply y).comp continuous_snd)).continuousOn
  · intro s hs ψ hψ x
    have h := norm_taggedCfin_mulVec_le (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M)
      hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ (hcl s hs) hρ
      (ψ := fun y => ((ψ y : ℝ) : ℂ)) (fun y => by simpa using hψ y) x
    simpa [Φ] using lt_of_le_of_lt h hBR

/-- **Locality of the cutoff interaction for a general datum.**  For a datum `u` (a matrix
`U x y = u (x, y)`) let `J_u(s) = ∫_{box ρ} F (C_U(s) ψ) dγ(ψ)`, `C_U` the Stieltjes integral
`taggedCfinU`.  Since each entry `C_U(s) x y` satisfies `LocalityAE`, so does `J`, for any
integrand `F` and any measure. -/
theorem localityAE_cutoffInteraction (hM : 0 < M) (hd : 0 < d)
    (γ : Measure (L1Torus d N₀ → ℝ)) (ρ : ℝ) (F : (L1Torus d N₀ → ℂ) → ℂ) :
    LocalityAE (fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C)
      (fun (u : L1Torus d N₀ × L1Torus d N₀ → ℂ) s =>
        ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfinU d N₀ M (Matrix.of fun a b => u (a, b)) s x y *
            ((ψ y : ℝ) : ℂ)) ∂γ) := by
  intro C u u' s s' hs hs' hPs hu
  have h : ∀ x y, taggedCfinU d N₀ M (Matrix.of fun a b => u (a, b)) s x y =
      taggedCfinU d N₀ M (Matrix.of fun a b => u' (a, b)) s' x y := fun x y =>
    localityAE_taggedCfinU hM hd x y C u u' s s' hs hs' hPs hu
  simp only [h]

/-- Congruence of the coefficients of the cutoff interaction in the datum on `Y(C) × Y(C)`. -/
theorem coef_cutoffInteraction_congr_of_agree (hM : 0 < M) (hd : 0 < d)
    (γ : Measure (L1Torus d N₀ → ℝ)) (ρ : ℝ) (F : (L1Torus d N₀ → ℂ) → ℂ)
    (C : Finset (MacIdx d N₀ M)) {u u' : L1Torus d N₀ × L1Torus d N₀ → ℂ}
    (huu : ∀ p ∈ macRegion d N₀ M C ×ˢ macRegion d N₀ M C, u p = u' p) :
    coef (fun s => ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      F (fun x => ∑ y, taggedCfinU d N₀ M (Matrix.of fun a b => u (a, b)) s x y *
        ((ψ y : ℝ) : ℂ)) ∂γ) C =
    coef (fun s => ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      F (fun x => ∑ y, taggedCfinU d N₀ M (Matrix.of fun a b => u' (a, b)) s x y *
        ((ψ y : ℝ) : ℂ)) ∂γ) C :=
  coef_congr_of_agree (localityAE_cutoffInteraction hM hd γ ρ F) C huu

end Final

end Balaban.Green
