/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalRadiusClass
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The final cutoff theorems for the `N`-component field (blocker 5)

`cutoffInteraction_final` and `cutoffInteraction_final_phys` are stated for a scalar field
`ψ : L1Torus d N₀ → ℝ`; the model has `N` components, and the cut family `C_fin(s)` acts on each
component by the same matrix.  Here the sites carry an extra finite index `ι` (`ι = Fin N`): the
field is `ψ : L1Torus d N₀ × ι → ℝ`, `(C_fin(s) ψ)(x, i) = ∑_y C_fin(s) x y ψ(y, i)`.  Only the
row bound, the analyticity of the entries and Lemma AE for `J` are used, and none of them involves
the component index.

* `cutoffInteraction_final_comp`: the conclusions of `cutoffInteraction_final` for `ι`-indexed fields.
* `cutoffInteraction_final_phys_comp`: the conclusions of `cutoffInteraction_final_phys`.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Filter Metric

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis

section Final

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ} {ι : Type*} [Fintype ι]

/-- **The cutoff interaction of the last integral, for fields with a component index `ι`.** -/
theorem cutoffInteraction_final_comp (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ × ι → ℝ)} {ρ R B' : ℝ} (hρ : 0 ≤ ρ)
    (hγ : γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * ρ < R)
    {F : (L1Torus d N₀ × ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N₀ × ι → ℂ) (fun _ => R)))
    (hFB : ∀ w ∈ polydisc (0 : L1Torus d N₀ × ι → ℂ) (fun _ => R), ‖F w‖ ≤ B') :
    let J : (MacIdx d N₀ M → ℂ) → ℂ := fun s =>
      ∫ ψ in {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun xi => ∑ y, taggedCfin d L N₀ k M v a s xi.1 y * ((ψ (y, xi.2) : ℝ) : ℂ)) ∂γ
    AnalyticOnNhd ℂ J (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖J s‖ ≤ B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal) ∧
    J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun xi => ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) xi.1 y *
          ((ψ (y, xi.2) : ℝ) : ℂ)) ∂γ ∧
    J (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef J C ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal /
      (Real.exp κ - 1) ^ C.card) ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal *
      Real.exp (-(κ - 1) * C.card)) := by
  intro J
  have hκ0 : 0 ≤ κ := by linarith
  have hcl : ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ∀ p, ‖s p‖ ≤ Real.exp κ := fun s hs p => by simpa using (hs p).le
  have hanC : ∀ x y, AnalyticOnNhd ℂ (fun s => taggedCfin d L N₀ k M v a s x y)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := fun x y =>
    (taggedCfin_analyticOnNhd (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk hv0
      hv1 ha1 ha2 hmass hM hκ0 hMB hMκ x y).mono fun s hs p => by simpa using hs p
  set Φ : (MacIdx d N₀ M → ℂ) → (L1Torus d N₀ × ι → ℝ) → (L1Torus d N₀ × ι → ℂ) :=
    fun s ψ xi => ∑ y, taggedCfin d L N₀ k M v a s xi.1 y * ((ψ (y, xi.2) : ℝ) : ℂ) with hΦ
  have hbox := analyticOnNhd_integral_box (γ := γ) (ρ := ρ) (R := R) (B' := B') (κ := κ) hγ hF hFB
    (Φ := Φ) ?_ ?_ ?_
  · have hAE := abstract_expansion
      (P := fun i : MacIdx d N₀ M => macBox d N₀ M i ×ˢ macBox d N₀ M i)
      (Y := fun C => macRegion d N₀ M C ×ˢ macRegion d N₀ M C)
      (F := fun (_ : L1Torus d N₀ × L1Torus d N₀ → ℂ) s => J s) hκ
      (B := B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal)
      (fun _ => hbox.1) (fun _ => hbox.2)
      (localityAE_macBox_of_agree (G := fun _ s => J s) fun _ _ _ _ _ _ => rfl)
    have h1 : J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun xi => ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) xi.1 y *
          ((ψ (y, xi.2) : ℝ) : ℂ)) ∂γ := by
      show ∫ ψ in {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun xi => ∑ y, taggedCfin d L N₀ k M v a (fun _ => 1) xi.1 y *
          ((ψ (y, xi.2) : ℝ) : ℂ)) ∂γ = _
      rw [taggedCfin_one hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ]
    refine ⟨hbox.1, hbox.2, h1, ?_, fun C => hAE.2.2.2.1 (fun _ => 0) C,
      fun C => hAE.2.2.2.2 (fun _ => 0) C⟩
    have := hAE.1 (fun _ => 0)
    classical
    rw [Finset.filter_true_of_mem fun C _ =>
      isConnectedFamily_macBox (d := d) (N₀ := N₀) (M := M) C] at this
    exact this
  · intro ψ _ s hs
    refine AnalyticAt.pi fun xi => ?_
    exact Finset.analyticAt_fun_sum _ fun y _ =>
      (hanC xi.1 y s hs).mul (analyticAt_const (𝕜 := ℂ))
  · refine continuousOn_pi.2 fun xi => ?_
    refine continuousOn_finsetSum _ fun y _ => ?_
    refine ((hanC xi.1 y).continuousOn.comp continuousOn_fst fun q hq => hq.1).mul ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply (y, xi.2)).comp
      continuous_snd)).continuousOn
  · intro s hs ψ hψ xi
    have h := norm_taggedCfin_mulVec_le (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M)
      hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ (hcl s hs) hρ
      (ψ := fun y => ((ψ (y, xi.2) : ℝ) : ℂ)) (fun y => by simpa using hψ (y, xi.2)) xi.1
    simpa [Φ] using lt_of_le_of_lt h hBR

/-- **The cutoff interaction for an interaction on a physical field ball, `ι`-indexed fields**
(`ι = Fin N` for the `N`-component model): the statement of `cutoffInteraction_final_phys` with
`ψ : L1Torus d N₀ × ι → ℝ`, `φ₀ : L1Torus d N₀ × ι → ℂ`, `(C_fin(s) ψ)(x, i) = ∑_y C_fin(s) x y ψ(y, i)`. -/
theorem cutoffInteraction_final_phys_comp (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ × ι → ℝ)} {ρ Rphys B' β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < Rphys)
    {F : (L1Torus d N₀ × ι → ℂ) → ℂ} {φ₀ : L1Torus d N₀ × ι → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc φ₀ (fun _ => Rphys)))
    (hFB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖F w‖ ≤ B') :
    let J : (MacIdx d N₀ M → ℂ) → ℂ := fun s =>
      ∫ ψ in {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun xi => φ₀ xi + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s xi.1 y * ((ψ (y, xi.2) : ℝ) : ℂ)) ∂γ
    AnalyticOnNhd ℂ J (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖J s‖ ≤ B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal) ∧
    J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun xi => φ₀ xi + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) xi.1 y *
            ((ψ (y, xi.2) : ℝ) : ℂ)) ∂γ ∧
    J (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef J C ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal /
      (Real.exp κ - 1) ^ C.card) ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ × ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal *
      Real.exp (-(κ - 1) * C.card)) := by
  have hc0 : 0 < β ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hβ _
  have hs0 : 0 < β ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hβ _
  have hcs : β ^ (-(1 / 2 : ℝ)) * β ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hβ]; simp
  set c : ℝ := β ^ (-(1 / 2 : ℝ)) with hc
  set sb : ℝ := β ^ (1 / 2 : ℝ) with hsb
  set F' : (L1Torus d N₀ × ι → ℂ) → ℂ := fun w => F (fun xi => φ₀ xi + ((c : ℝ) : ℂ) * w xi)
    with hF'
  have hmem : ∀ w ∈ polydisc (0 : L1Torus d N₀ × ι → ℂ) (fun _ => sb * Rphys),
      (fun xi => φ₀ xi + ((c : ℝ) : ℂ) * w xi) ∈ polydisc φ₀ (fun _ => Rphys) := by
    intro w hw xi
    have := hw xi
    simp only [Pi.zero_apply, sub_zero] at this
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc0]
    calc c * ‖w xi‖ < c * (sb * Rphys) := mul_lt_mul_of_pos_left this hc0
      _ = Rphys := by rw [← mul_assoc, hcs, one_mul]
  have hFa : AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N₀ × ι → ℂ) (fun _ => sb * Rphys)) := by
    intro w hw
    refine AnalyticAt.comp (g := F) (f := fun w : L1Torus d N₀ × ι → ℂ =>
      fun xi => φ₀ xi + ((c : ℝ) : ℂ) * w xi) (hF _ (hmem w hw)) ?_
    refine analyticAt_pi_iff.2 fun xi => ?_
    exact analyticAt_const.add (analyticAt_const.mul
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : L1Torus d N₀ × ι => ℂ) xi).analyticAt w)))
  have hFB' : ∀ w ∈ polydisc (0 : L1Torus d N₀ × ι → ℂ) (fun _ => sb * Rphys), ‖F' w‖ ≤ B' :=
    fun w hw => hFB _ (hmem w hw)
  have hBR' : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * ρ < sb * Rphys := by
    generalize (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) = Bc at hBR ⊢
    have h1 := mul_lt_mul_of_pos_right hBR hs0
    have h2 : Bc * (c * ρ) * sb = Bc * ρ * (c * sb) := by ring
    rw [h2, hcs, mul_one] at h1
    linarith
  have key := cutoffInteraction_final_comp (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a)
    (ι := ι) hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hγ hBR' hFa hFB'
  simpa only [hF', Finset.mul_sum] using key

end Final

end Balaban.Green
