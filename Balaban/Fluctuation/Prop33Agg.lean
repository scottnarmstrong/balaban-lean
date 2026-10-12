/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionLoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weighted sums of localized expansions (the `ℓ¹` structure of the source terms)

The source terms of Proposition 3.3 are linear in the source `g` with `‖g‖_{ℓ¹} < 1`.  Summing
them with the bounds `∑_τ |g(τ)| b_τ(Y) ≤ B(Y)` (rather than `∑_τ b_τ(Y)`) is what keeps the
bound of the localized terms independent of the volume.  `LocInt.wsum` adds localized expansions
`T_τ` with analytic amplitudes `amp τ (g)` and the weighted bound.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section WSum

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F : Type*} {ι : Type*} {κ : Type*}
variable {S : Set Λ} {XW : Set (F × F)} {Rσ : ℝ} {AgΘ : ι → Λ → Λ → Prop}
  {AgF : ι → F → F → Prop}

/-- **Weighted sum of localized expansions with amplitudes depending on the source `g`.**
The bound of the sum is any `B` dominating the weighted sums of the term bounds. -/
theorem LocInt.wsum [DecidableEq ι] (𝒯 : Finset κ) {𝒴 : κ → Finset ι}
    {T : κ → ι → F → F → ℂ → Λ → ℂ} {val : κ → F → F → ℂ → Λ → ℂ} {b : κ → ι → ℝ}
    (h : ∀ τ ∈ 𝒯, LocInt S XW Rσ (𝒴 τ) (T τ) (val τ) (b τ) AgΘ AgF)
    {SG : Set G} {amp : κ → G → ℂ} (hamp : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (amp τ) SG)
    {AgG : ι → G → G → Prop}
    (hloc : ∀ τ ∈ 𝒯, ∀ Y ∈ 𝒴 τ, ∀ g ∈ SG, ∀ g' ∈ SG, AgG Y g g' → amp τ g = amp τ g')
    {B : ι → ℝ}
    (hB : ∀ Y ∈ 𝒯.biUnion 𝒴, ∀ g ∈ SG,
      ∑ τ ∈ 𝒯, (if Y ∈ 𝒴 τ then ‖amp τ g‖ * b τ Y else 0) ≤ B Y) :
    LocInt (S ×ˢ SG) XW Rσ (𝒯.biUnion 𝒴)
      (fun Y x w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then amp τ p.2 * T τ Y x w σ p.1 else 0)
      (fun x w σ p => ∑ τ ∈ 𝒯, amp τ p.2 * val τ x w σ p.1)
      B (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF where
  sum := fun xw hxw σ hσ p hp => by
    classical
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [(h τ hτ).sum xw hxw σ hσ p.1 hp.1, Finset.mul_sum, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem 𝒴 hτ)]
  analytic := fun Y _ xw hxw => by
    classical
    rintro ⟨⟨Θ, g⟩, σ⟩ ⟨⟨hΘ, hg⟩, hσ⟩
    refine Finset.analyticAt_fun_sum _ fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simp only [hY, ite_true]
      have h1 : AnalyticAt ℂ (fun q : (Λ × G) × ℂ => amp τ q.1.2) ((Θ, g), σ) :=
        (hamp τ hτ g hg).comp_of_eq (analyticAt_snd.comp analyticAt_fst) rfl
      have h2 : AnalyticAt ℂ (fun q : (Λ × G) × ℂ => T τ Y xw.1 xw.2 q.2 q.1.1) ((Θ, g), σ) :=
        (((h τ hτ).analytic Y hY xw hxw) (Θ, σ) ⟨hΘ, hσ⟩).comp_of_eq
          ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd) rfl
      exact h1.mul h2
    · simp only [hY, ite_false]; exact analyticAt_const
  bound := fun Y hY xw hxw σ hσ p hp => by
    classical
    refine (norm_sum_le _ _).trans ?_
    calc ∑ τ ∈ 𝒯, ‖if Y ∈ 𝒴 τ then amp τ p.2 * T τ Y xw.1 xw.2 σ p.1 else 0‖
        ≤ ∑ τ ∈ 𝒯, ‖σ‖ * (if Y ∈ 𝒴 τ then ‖amp τ p.2‖ * b τ Y else 0) := by
          refine Finset.sum_le_sum fun τ hτ => ?_
          by_cases hYτ : Y ∈ 𝒴 τ
          · simp only [hYτ, ite_true, norm_mul]
            calc ‖amp τ p.2‖ * ‖T τ Y xw.1 xw.2 σ p.1‖
                ≤ ‖amp τ p.2‖ * (‖σ‖ * b τ Y) :=
                  mul_le_mul_of_nonneg_left ((h τ hτ).bound Y hYτ xw hxw σ hσ p.1 hp.1)
                    (norm_nonneg _)
              _ = _ := by ring
          · simp [hYτ]
      _ = ‖σ‖ * ∑ τ ∈ 𝒯, (if Y ∈ 𝒴 τ then ‖amp τ p.2‖ * b τ Y else 0) := by
          rw [Finset.mul_sum]
      _ ≤ ‖σ‖ * B Y := mul_le_mul_of_nonneg_left (hB Y hY p.2 hp.2) (norm_nonneg _)
  loc := fun Y hY xw hxw xw' hxw' σ hσ p hp p' hp' h1 h2 h3 => by
    classical
    refine Finset.sum_congr rfl fun τ hτ => ?_
    by_cases hYτ : Y ∈ 𝒴 τ
    · simp only [hYτ, ite_true]
      rw [(h τ hτ).loc Y hYτ xw hxw xw' hxw' σ hσ p.1 hp.1 p'.1 hp'.1 h1.1 h2 h3,
        hloc τ hτ Y hYτ p.2 hp.2 p'.2 hp'.2 h1.2]
    · simp [hYτ]
  zero := fun Y hY xw hxw p hp => by
    classical
    refine Finset.sum_eq_zero fun τ hτ => ?_
    by_cases hYτ : Y ∈ 𝒴 τ
    · simp only [hYτ, ite_true]
      rw [(h τ hτ).zero Y hYτ xw hxw p.1 hp.1, mul_zero]
    · simp [hYτ]

/-- Weakening the bound on the labels only. -/
theorem LocInt.mono_on {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b b' : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) (hb : ∀ Y ∈ 𝒴, b Y ≤ b' Y) :
    LocInt S XW Rσ 𝒴 T val b' AgΘ AgF :=
  { h with bound := fun Y hY xw hxw σ hσ Θ hΘ =>
      (h.bound Y hY xw hxw σ hσ Θ hΘ).trans (mul_le_mul_of_nonneg_left (hb Y hY) (norm_nonneg _)) }

/-- **The bound of one term**: for `‖σ‖ < R_σ` and `b ≥ 0`, `|T_Y| ≤ R_σ b_Y`. -/
theorem LocInt.term_le {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) {Y : ι} (hY : Y ∈ 𝒴) (hb : 0 ≤ b Y)
    {xw : F × F} (hxw : xw ∈ XW) {σ : ℂ} (hσ : ‖σ‖ < Rσ) {Θ : Λ} (hΘ : Θ ∈ S) :
    ‖T Y xw.1 xw.2 σ Θ‖ ≤ Rσ * b Y :=
  (h.bound Y hY xw hxw σ hσ Θ hΘ).trans (mul_le_mul_of_nonneg_right hσ.le hb)

end WSum

end Balaban.Fluctuation
