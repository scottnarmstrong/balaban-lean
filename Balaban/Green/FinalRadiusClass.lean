/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalRadiusCompare
public import Balaban.Green.FinalInteractionClass
public import Balaban.Fluctuation.ClassOldBirthFluct
public import Balaban.LargeField.R.CancelIdentity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The radius comparison at the last scale, against the class radius (blocker 5)

The interaction `F_K = ∑_{j ≤ K} ℰ^{(j)}` of the class at level `k_f + 1` lives on a chart of value
radius `ε_{k_f} = α₀ (1 + ∑_{m ≥ k_f} m^{-2}) L^{-k_f α}` (`epsSeq`), which tends to `0` with `k_f`.
The field of the last integral is `φ₀ + β_{k_f}^{-1/2} C_fin(s) ψ`, `|ψ| ≤ p₁(β_{k_f})`, with
`β_{k_f} = β L^{k_f (d-2)}` (`betaK`).  Both are fields at scale `k_f`: the radius `ε_{k_f}` bounds
`‖φ^c - φ^r‖` of the class (`XiCBounds.val`), and `β_{k_f}^{-1/2} C_fin ψ` is the fluctuation field
in the same variable.

* `cutConst_mul_pLog_lt_epsSeq`: for `B ≥ 0`, `c > 0`, `α₀ > 0`, `α ≤ (d-2)/4`, `p ≥ 1` and
  `B A₁ (4p)^p < c α₀ β^{1/4}`, one has `B β_k^{-1/2} p₁(β_k) < c ε_k` for every `k`.
* `cutoffInteraction_final_class_epsSeq`: the corollary of
  `cutoffInteraction_final_class_of_polydisc_subset` at `R = c ε_{k_f}` with `hBR` discharged.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban.Localization Balaban.Analysis Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField.ActionConv

namespace Balaban.Green

/-- `β_k = β L^{(d-2) k}` with the real exponent, for `2 ≤ d`. -/
theorem betaK_eq_rpow {d L : ℕ} (k : ℕ) (hd : 2 ≤ d) (β0 : ℝ) :
    betaK d L k β0 = β0 * (L : ℝ) ^ (((d : ℝ) - 2) * k) := by
  unfold betaK
  rw [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_sub hd]
  push_cast
  ring_nf

/-- **The cutoff against the class radius, uniformly in the scale.**  Let `β_k = β L^{k(d-2)}`,
`ε_k = α₀ (1 + ∑_{m ≥ k} m^{-2}) L^{-k α}`, `p ≥ 1`, `α ≤ (d-2)/4` and
`B A₁ (4p)^p < c α₀ β^{1/4}` (a lower bound on `β`, independent of `k`).  Then for every `k`,
`B β_k^{-1/2} A₁ (log β_k)^p < c ε_k`. -/
theorem cutConst_mul_pLog_lt_epsSeq {d L : ℕ} [NeZero L] {B A₁ α α₀ β0 c : ℝ} {p : ℕ}
    (hd : 2 ≤ d) (hp : 1 ≤ p) (hB : 0 ≤ B) (hA : 0 ≤ A₁) (hα₀ : 0 < α₀) (hc : 0 < c)
    (hα : α ≤ ((d : ℝ) - 2) * (1 / 4)) (hβ0 : 1 < β0)
    (hsize : B * A₁ * (4 * (p : ℝ)) ^ p < c * α₀ * β0 ^ (1 / 4 : ℝ)) (k : ℕ) :
    B * (betaK d L k β0 ^ (-(1 / 2 : ℝ)) * pLog A₁ p (betaK d L k β0)) <
      c * epsSeq L α α₀ k := by
  have hL : 1 ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : 0 < (L : ℝ) := by linarith
  have hβk := betaK_eq_rpow (L := L) k hd β0
  have hβpos : 0 < betaK d L k β0 := by rw [hβk]; positivity
  have h := amp_le_decay (d := d) (L := L) (k := k) (α := α) (u := 1 / 4) (A₁ := A₁) (C := B)
    (M := β0) (p := p) (cc := (((betaK d L k β0 ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ))
    (cψ := pLog A₁ p (betaK d L k β0)) hL hp (by norm_num) (by norm_num) hA hB hβ0
    hβk.ge (by rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hβpos _)]) rfl
    (by linarith) hd
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hβpos _)] at h
  have hE : (L : ℝ) ^ (-α * k) = ((L : ℝ) ^ (-α)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hE0 : 0 < (L : ℝ) ^ (-α * k) := Real.rpow_pos_of_pos hL0 _
  have h4 : (4 : ℝ) * p = (p : ℝ) / (1 / 4) := by field_simp
  have hβq : 0 < β0 ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hneg : β0 ^ (-(1 / 2 - 1 / 4 : ℝ)) = (β0 ^ (1 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg (by linarith)]; norm_num
  have hK : B * A₁ * ((p : ℝ) / (1 / 4)) ^ p * β0 ^ (-(1 / 2 - 1 / 4 : ℝ)) < c * α₀ := by
    rw [hneg, ← div_eq_mul_inv, div_lt_iff₀ hβq, ← h4]; exact hsize
  have hep : α₀ * ((L : ℝ) ^ (-α)) ^ k ≤ epsSeq L α α₀ k := by
    unfold epsSeq
    have := one_le_epsTail k
    nlinarith [mul_pos hα₀ (pow_pos (Real.rpow_pos_of_pos hL0 (-α)) k)]
  calc _ = betaK d L k β0 ^ (-(1 / 2 : ℝ)) * (B * pLog A₁ p (betaK d L k β0)) := by ring
    _ ≤ _ := h
    _ = (B * A₁ * ((p : ℝ) / (1 / 4)) ^ p * β0 ^ (-(1 / 2 - 1 / 4 : ℝ))) * (L : ℝ) ^ (-α * k) := by ring
    _ < (c * α₀) * (L : ℝ) ^ (-α * k) := mul_lt_mul_of_pos_right hK hE0
    _ = c * (α₀ * ((L : ℝ) ^ (-α)) ^ k) := by rw [hE]; ring
    _ ≤ c * epsSeq L α α₀ k := mul_le_mul_of_nonneg_left hep hc.le

section Final

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The last integral for the interaction of the class, with the radius `c ε_K` and the
comparison discharged.**  This is `cutoffInteraction_final_class_of_polydisc_subset` with
`R = c ε_K`, `β = β_K = β₀ L^{K (d'-2)}`, `ρ = p₁(β_K)`; the hypothesis `hBR` is replaced by the
size condition `B A₁ (4p)^p < c α₀ β₀^{1/4}` (with `B = B(κ)` the row constant of the cut family),
which does not depend on `K`.  The inclusion `hsub` of the polydisc of radius `c ε_K` into the
domains of the terms remains a hypothesis. -/
theorem cutoffInteraction_final_class_epsSeq
    {d' : ℕ} {c α α₀ β₀ A₁ : ℝ} {p : ℕ} {N₁ m₁ kc N : ℕ} [NeZero N₁] {ϱ : ℝ}
    {P : Consts} {Dom : FieldDom d' L N₁ m₁ kc N ϱ} {Tm : Terms d' L N₁ m₁ kc N ϱ}
    (hT : SFTermClauses P Dom Tm) {K : ℕ} (hK : K ≤ kc) (hE₀ : 0 ≤ P.E₀)
    {φ₀ : L1Torus d N₀ → ℂ}
    {Λ : (L1Torus d N₀ → ℂ) → Fld d' L N₁ m₁ kc N × Fld d' L N₁ m₁ kc N}
    (hΛ : AnalyticOnNhd ℂ Λ (polydisc φ₀ (fun _ => c * epsSeq L α α₀ K)))
    (hsub : ∀ w ∈ polydisc φ₀ (fun _ => c * epsSeq L α α₀ K), ∀ j, 1 ≤ j → j ≤ K →
      ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) (Λ w).1 (Λ w).2)
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : MeasureTheory.Measure (L1Torus d N₀ → ℝ)}
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)} < ⊤)
    (hd2 : 2 ≤ d') (hp : 1 ≤ p) (hA : 0 ≤ A₁) (hα₀ : 0 < α₀) (hc : 0 < c)
    (hα : α ≤ ((d' : ℝ) - 2) * (1 / 4)) (hβ₀ : 1 < β₀)
    (hsize : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * A₁ * (4 * (p : ℝ)) ^ p < c * α₀ * β₀ ^ (1 / 4 : ℝ)) :
    AnalyticOnNhd ℂ (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)},
        (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
            Edens P.m₀ Tm j (Λ w).1 (Λ w).2)
          (fun x => φ₀ x + (((betaK d' L K β₀) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := by
  have hBc : 0 ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) := (cutConst_pos (d := d) (L := L) hd κ).le
  have hβpos : 0 < betaK d' L K β₀ := by
    rw [betaK_eq_rpow K hd2]
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := hβ₀; positivity
  exact cutoffInteraction_final_class_of_polydisc_subset (R := c * epsSeq L α α₀ K) (N₀ := N₀)
    hT hK hE₀ hΛ hsub hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
    (pLog_nonneg hA p (by
      rw [betaK_eq_rpow K hd2]
      have h1 : 1 ≤ (L : ℝ) ^ (((d' : ℝ) - 2) * K) :=
        Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
          (by have : (2 : ℝ) ≤ d' := by exact_mod_cast hd2
              positivity)
      nlinarith)) hβpos hγ
    (cutConst_mul_pLog_lt_epsSeq hd2 hp hBc hA hα₀ hc hα hβ₀ hsize K)

end Final

end Balaban.Green
