/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalRadiusClass
public import Balaban.Localization.I5Chain
public import Balaban.SmallField.XiPerturb
public import Balaban.Fluctuation.StepComplex
public import Balaban.Fluctuation.Theorem42WireAct
public import Balaban.Fluctuation.ClassOldBirthConsts
public import Balaban.Fluctuation.StepActivityClassChart
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The polydisc inclusion of the last integral for the class (blocker 5)

The field of the last integral is `φ₀ + β_K^{-1/2} C_fin(s) ψ`, a point of the polydisc of radius
`R = c ε_K` around the critical field `φ₀ = ψ^{(k)}(θ)` (the unit-lattice field of the critical
datum).  A step `S` (`StepSetting`) and an equivalence `e : L1Torus d N₀ ≃ S.U × Fin N` identify
the variable `w : L1Torus d N₀ → ℂ` of the cutoff theorems with the complex old spin
`ψ_w = w ∘ e⁻¹ : S.EC`.  The lift of `w` to the data of the class at level `j` is the composed pair
`Λ_j(w) = composedPairAtC … j (S.dataUC ψ_w)` of (H.2): the datum `(ψ_w, h₀)` of `𝔹_k`
composed down to `𝔹_j`.

* `dataUC_xiCData_of_close`: if the block datum `θ` lies in `Ξ^c_{k+1}(𝔹'; 1, ε₀)`, then for every
  old spin `ψ` with `|ψ - ψ^{(k)}(θ)| ≤ m` the datum `dataUC ψ` lies in
  `Ξ^c_{k+1}(𝔹_k; 1, ε₀ + K₂' N m)` (composition (Ξ3) at `b = 1`, then the perturbation (Ξ2));
* `composedPair_xiDom_of_xiCData`: a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` composes, at every level
  `j ≤ k`, to a pair of `Ξ^c_j(𝔹_j; 1, ε)` (the whole-level chart);
* `analyticOnNhd_composedPair_polydisc`: `Λ_j` is analytic on the polydisc;
* `polydisc_composedPair_mem_xiDom`: `hsub` for terms whose generating set is the whole-level set;
* `cutoffInteraction_final_class_of_polydisc_subset_levels`: the cut-family analyticity for the
  interaction `∑_j ℰ^{(j)}(Λ_j w)` with level-dependent lifts;
* `cutoffInteraction_final_class_polydisc`: the composed theorem.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Fluctuation Balaban.Inhabited Balaban.LargeField.ActionConv

namespace Balaban.Green

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The datum of an old spin near the critical point lies in the chart of `𝔹_k`.**  Let the block
datum `θ = S.D'` lie in `Ξ^c_{k+1}(𝔹'; 1, ε₀)` and let `ψ` be a complex old spin with
`|ψ(q) - ψ^{(k)}(θ)(q)| ≤ m` for all `q`.  Then `dataUC ψ` lies in `Ξ^c_{k+1}(𝔹_k; 1, ε₀ + K₂' N m)`.
The numerical conditions are those of (Ξ3) at `ε₀` and of (Ξ2) with `δ₃ = N m`. -/
theorem dataUC_xiCData_of_close (S : StepSetting d L N₁ m₁ k N ϱ) (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (ha₁ : 0 < S.a₁) {ε₀ m : ℝ}
    (hθ : XiCData S.G' S.a S.ν (k + 1) 1 ε₀ S.D')
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hm : 0 ≤ m) (hm1 : (N : ℝ) * m ≤ 1)
    (hδ₂ : xiC1 d * ε₀ + 5 * ((N : ℝ) * m) ≤ bgC1 d L N)
    (hstar : (N : ℝ) * m ≤ deltaStar d L N)
    (hK1s : bgK1 d L N * (xiC1 d * ε₀) ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε₀) + cK2 d L N * ((N : ℝ) * m) < bgC0 d L N)
    {ψ : S.EC} (hψ : ∀ q, ‖ψ q - S.psi0C q‖ ≤ m) :
    XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 (ε₀ + xiK2 d L N * ((N : ℝ) * m))
      (S.dataUC ψ) := by
  have h1 := xiCData_compose_of_one_le (G := stepG d L N₁ m₁ k ϱ) (G' := S.G') (b := 1) le_rfl ha₁
    HB HB (S.hG.precedes S.hG' le_rfl) (fun z _ => (S.hG' z).1) hsmall hth hθ
  rw [one_mul] at h1
  have h2 : XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 ε₀ (S.dataUC S.psi0C) := by
    rw [S.dataUC_psi0C]; exact h1
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h2
  have hδΨc := isLayerConstant_liftC S.hG S.hG' (ψ - S.psi0C)
  have hδΨ : ∀ x ∈ dataSites (stepG d L N₁ m₁ k ϱ), vn (liftC S.hG' (ψ - S.psi0C) x) ≤
      (N : ℝ) * m := fun x _ => vn_le_card_mul hm fun i => hψ (unitPt S.hG' x, i)
  have hP := xiC_perturb HB (by positivity) hm1 (by
      have := hsmall; nlinarith [hth]) hδ₂ hstar hK1s hsm hδΨc hδΨ hX
  refine ⟨Ψ₀, h₀, _, h'', hP, ?_, ?_⟩
  · intro x hx i
    have hx' := hR.1 x hx i
    rw [S.dataUC_Ψ] at hx' ⊢
    show ψ (unitPt S.hG' x, i) = (Ψ₀ x i : ℂ) +
      (Ψ'' x i + (ψ (unitPt S.hG' x, i) - S.psi0C (unitPt S.hG' x, i)))
    linear_combination hx'
  · intro x hx i
    rw [S.dataUC_h]
    have := hR.2 x hx i
    rw [S.dataUC_h] at this
    exact this

/-- **The composition of a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` to the level `j` lies in the whole-level
chart**: for `1 ≤ j ≤ k`, the pair `(ψ_k^{(j)}, h)` of (H.2) lies in `Ξ^c_j(𝔹_j; 1, ε')` for
every `ε' ≥ ε` (composition (Ξ3) at `b = 1`, the level monotonicity, and the rescaling). -/
theorem composedPair_xiDom_of_xiCData (S : StepSetting d L N₁ m₁ k N ϱ)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε ε' : ℝ}
    {D : BgData (stepG d L N₁ m₁ k ϱ) N}
    (hD : XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 ε D)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hth : xiC1 d * ε ≤ thm73C1 d L N)
    (hε : ε ≤ ε') {j : ℕ} (hjk : j ≤ k) :
    XiDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
        (hjk.trans (Nat.le_succ k))) S.a S.ν j ε'
      (composedPairAtC S.a S.ν (Nat.le_succ k) j D).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) j D).2 := by
  have h1 := xiCData_compose_of_one_le (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k + 1) (ϱ := ϱ) j (hjk.trans (Nat.le_succ k))) (G' := stepG d L N₁ m₁ k ϱ) (b := 1)
    le_rfl ha₁ HB HB (levelGS_precedes_at hjk (Nat.le_succ k)) (fun z _ => (S.hG z).1) hsmall hth hD
  rw [one_mul] at h1
  have h2 := xiCData_level_mono (n' := j) (hjk.trans (Nat.le_succ k)) HB.mass h1
  have h3 := xiDom_of_xiCData_of_one_le (le_refl (1 : ℝ)) (ε' := ε') (by nlinarith) h2
  have e : composedPairAtC S.a S.ν (Nat.le_succ k) j D =
      ((composedDataAtC S.a S.ν hjk (Nat.le_succ k) D).Ψ,
        (composedDataAtC S.a S.ν hjk (Nat.le_succ k) D).h) := by
    simp only [composedPairAtC, hjk, ↓reduceDIte]
  rw [e]
  exact h3

end Chart

end Balaban.Green
