/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledBackground
public import Balaban.Background.CompositionEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem I-4b (ii): the defect of the decoupled background field

For `s ≠ 1` the decoupled background field does not satisfy the constraint (P3 p. 57), but the
defect `g = φ_k(s) · φ_k(s) - 1` is small: `|g|₀ ≤ 4 K₄ δ` and `|Δ g̃|₂ ≤ (5 + 2d) K₄ δ`, where
`g̃` is the zero extension of `g` from `Ω₁`.  This is the hypothesis (P4) for the field
`φ_k(s)` used in I-4c.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

/-- **Discrete Leibniz rule for the Laplacian of a bilinear square.** -/
theorem negLap_sq_identity {d ℓ N : ℕ} (a : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ) :
    ∑ μ : Fin d, (2 * (∑ i, a x i * a x i) - ∑ i, a (x + Pi.single μ 1) i * a (x + Pi.single μ 1) i -
      ∑ i, a (x - Pi.single μ 1) i * a (x - Pi.single μ 1) i) =
    2 * ∑ i, a x i * (∑ μ : Fin d, (2 * a x i - a (x + Pi.single μ 1) i -
        a (x - Pi.single μ 1) i)) -
      ∑ μ : Fin d, (∑ i, (a (x + Pi.single μ 1) i - a x i) * (a (x + Pi.single μ 1) i - a x i) +
        ∑ i, (a (x - Pi.single μ 1) i - a x i) * (a (x - Pi.single μ 1) i - a x i)) := by
  have h : ∀ μ : Fin d, (2 * (∑ i, a x i * a x i) -
      ∑ i, a (x + Pi.single μ 1) i * a (x + Pi.single μ 1) i -
      ∑ i, a (x - Pi.single μ 1) i * a (x - Pi.single μ 1) i) =
      2 * ∑ i, a x i * (2 * a x i - a (x + Pi.single μ 1) i - a (x - Pi.single μ 1) i) -
      (∑ i, (a (x + Pi.single μ 1) i - a x i) * (a (x + Pi.single μ 1) i - a x i) +
        ∑ i, (a (x - Pi.single μ 1) i - a x i) * (a (x - Pi.single μ 1) i - a x i)) := by
    intro μ
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl fun μ _ => h μ, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.mul_sum]
  exact Finset.sum_comm


/-- **The Laplacian of the defect**, abstractly: bounds on a vector field `a` at a point `x` (value,
differences to the neighbours, Laplacian) bound the Laplacian of the bilinear square. -/
theorem negLap_sq_bound {d ℓ N : ℕ} (a : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ) {r U W : ℝ}
    (hr : 0 < r) (hU : U ≤ 1) (hW0 : 0 ≤ W) (hW : W ≤ 1) (hU0 : 0 ≤ U)
    (h1 : vn (a x) ≤ 3 / 2 + U)
    (h2 : ∀ μ : Fin d, vn (a (x + Pi.single μ 1) - a x) ≤ W / r ∧
      vn (a (x - Pi.single μ 1) - a x) ≤ W / r)
    (h3 : vn (fun i => ∑ μ : Fin d, (2 * a x i - a (x + Pi.single μ 1) i -
      a (x - Pi.single μ 1) i)) ≤ W / r ^ 2) :
    r ^ 2 * ‖∑ μ : Fin d, (2 * (∑ i, a x i * a x i) -
      ∑ i, a (x + Pi.single μ 1) i * a (x + Pi.single μ 1) i -
      ∑ i, a (x - Pi.single μ 1) i * a (x - Pi.single μ 1) i)‖ ≤ (5 + 2 * d) * W := by
  rw [negLap_sq_identity]
  have hdot : ‖2 * ∑ i, a x i * (∑ μ : Fin d, (2 * a x i - a (x + Pi.single μ 1) i -
      a (x - Pi.single μ 1) i))‖ ≤ 2 * ((3 / 2 + U) * (W / r ^ 2)) := by
    rw [norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ((norm_dot_le (a x) _).trans ?_) (by norm_num)
    exact mul_le_mul h1 h3 (vn_nonneg _) (by linarith)
  have hsq : ∀ μ : Fin d, ‖∑ i, (a (x + Pi.single μ 1) i - a x i) * (a (x + Pi.single μ 1) i - a x i) +
      ∑ i, (a (x - Pi.single μ 1) i - a x i) * (a (x - Pi.single μ 1) i - a x i)‖ ≤
        2 * (W / r) ^ 2 := by
    intro μ
    refine (norm_add_le _ _).trans ?_
    have a1 := norm_dot_le (a (x + Pi.single μ 1) - a x) (a (x + Pi.single μ 1) - a x)
    have a2 := norm_dot_le (a (x - Pi.single μ 1) - a x) (a (x - Pi.single μ 1) - a x)
    have d1 := mul_le_mul (h2 μ).1 (h2 μ).1 (vn_nonneg _) (by positivity)
    have d2 := mul_le_mul (h2 μ).2 (h2 μ).2 (vn_nonneg _) (by positivity)
    simp only [Pi.sub_apply] at a1 a2
    nlinarith
  have hsum : ‖∑ μ : Fin d, (∑ i, (a (x + Pi.single μ 1) i - a x i) *
      (a (x + Pi.single μ 1) i - a x i) +
      ∑ i, (a (x - Pi.single μ 1) i - a x i) * (a (x - Pi.single μ 1) i - a x i))‖ ≤
        d * (2 * (W / r) ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _μ : Fin d, 2 * (W / r) ^ 2 := Finset.sum_le_sum fun μ _ => hsq μ
      _ = _ := by simp
  have hcomb := (norm_sub_le _ _).trans (add_le_add hdot hsum)
  calc r ^ 2 * _ ≤ r ^ 2 * (2 * ((3 / 2 + U) * (W / r ^ 2)) + d * (2 * (W / r) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = 2 * (3 / 2 + U) * (r ^ 2 * (W / r ^ 2)) + 2 * d * (r ^ 2 * (W / r) ^ 2) := by ring
    _ = 2 * (3 / 2 + U) * W + 2 * d * W ^ 2 := by
        have e1 : r ^ 2 * (W / r ^ 2) = W := by field_simp
        have e2 : r ^ 2 * (W / r) ^ 2 = W ^ 2 := by field_simp
        rw [e1, e2]
    _ ≤ (5 + 2 * d) * W := by
        have hd1 : (0 : ℝ) ≤ d := by positivity
        have q1 := mul_nonneg hW0 (sub_nonneg.2 hU)
        have q2 := mul_nonneg hd1 (mul_nonneg hW0 (sub_nonneg.2 hW))
        have q3 : 2 * (3 / 2 + U) * W ≤ 5 * W := by linarith
        have q4 : 2 * d * W ^ 2 ≤ 2 * d * W := by nlinarith [q2]
        linarith

/-- **The sup of the defect**, abstractly. -/
theorem sq_defect_bound {N : ℕ} (p q : Fin N → ℂ) {U : ℝ} (hU : U ≤ 1)
    (hp : ∑ i, p i * p i = 1) (hp1 : vn p ≤ 3 / 2) (hq : vn q ≤ U) :
    ‖∑ i, (p i + q i) * (p i + q i) - 1‖ ≤ 4 * U := by
  have e : ∑ i, (p i + q i) * (p i + q i) - 1 = 2 * ∑ i, p i * q i + ∑ i, q i * q i := by
    have h2 : ∑ i, (p i + q i) * (p i + q i) =
        ∑ i, p i * p i + 2 * ∑ i, p i * q i + ∑ i, q i * q i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, hp]; ring
  rw [e]
  have hq0 := vn_nonneg q
  have hU0 : 0 ≤ U := hq0.trans hq
  have t1 : ‖2 * ∑ i, p i * q i‖ ≤ 2 * (vn p * vn q) := by
    rw [norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (norm_dot_le _ _) (by norm_num)
  have t2 := norm_dot_le q q
  have t3 : vn p * vn q ≤ 3 / 2 * U :=
    mul_le_mul hp1 hq hq0 (by norm_num)
  have t4 : vn q * vn q ≤ U * 1 := mul_le_mul hq (hq.trans hU) hq0 hU0
  calc _ ≤ ‖2 * ∑ i, p i * q i‖ + ‖∑ i, q i * q i‖ := norm_add_le _ _
    _ ≤ 4 * U := by linarith

section Defect

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- Every decoupled background field in the range of Theorem I-4b has the sup bounds of I-4a. -/
theorem IsDecBg.sup_bounds {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) s D φ α) :
    Small G α (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) ∧
      SupBounds G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
        (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) ∧
      BgBounds G D φ α (K4 d L N BG κ * δ) := by
  obtain ⟨φ', α', -, hu, hsm, hsup, hbb⟩ :=
    i4b_exists_unique hS S HB hκ hM hs hδ0 hδε hε hδ hνε hD
  obtain ⟨e1, e2⟩ := hu φ α h
  subst e1 e2
  exact ⟨hsm, hsup, hbb⟩

/-- The extended field `φ₀ + ũ` (`φ₀` smooth, `u` with sup bounds) has the value, difference and
Laplacian bounds at the sites of `Ω₁`. -/
theorem ext_field_bounds {φ0 : CTorus d L N₁ m₁ K → Fin N → ℂ} {u : G.Ω 1 × Fin N → ℂ}
    {X V : ℝ} (hV0 : 0 ≤ V) (hsm : IsSmoothField G X φ0) (hφ0 : ∀ x : G.Ω 1, vn (φ0 x) ≤ 3 / 2)
    (hsup : SupBounds G u V) (x : G.Ω 1) :
    vn (fun i => φ0 x i + svec G u x i) ≤ 3 / 2 + N * V ∧
    (∀ μ : Fin d,
      vn ((fun i => φ0 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
          svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i) -
        fun i => φ0 x i + svec G u x i) ≤
        (X + N * V) / G.spacing (x : CTorus d L N₁ m₁ K) ∧
      vn ((fun i => φ0 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i +
          svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i) -
        fun i => φ0 x i + svec G u x i) ≤
        (X + N * V) / G.spacing (x : CTorus d L N₁ m₁ K)) ∧
    vn (fun i => ∑ μ : Fin d, (2 * (φ0 x i + svec G u x i) -
      (φ0 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
        svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i) -
      (φ0 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i +
        svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i))) ≤
      (X + N * V) / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by
  have hℓx : 0 < G.spacing (x : CTorus d L N₁ m₁ K) := spacing_pos G
  refine ⟨?_, fun μ => ?_, ?_⟩
  · have e : (fun i => φ0 x i + svec G u x i) = φ0 x + svec G u x := rfl
    rw [e]
    refine (vn_add _ _).trans (add_le_add (hφ0 x) ?_)
    exact vn_le_card_mul hV0 (fun i => hsup.val x i)
  · have hm : 0 ≤ V / G.spacing (x : CTorus d L N₁ m₁ K) := by positivity
    have hg := hsm.grad x x.2 μ
    refine ⟨?_, ?_⟩
    · have e : ((fun i => φ0 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
            svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i) -
          fun i => φ0 x i + svec G u x i) =
          (φ0 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - φ0 x) +
          (svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - svec G u x) := by
        funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
      rw [e]
      refine (vn_add _ _).trans ?_
      have hv := vn_le_card_mul (v := svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        svec G u x) hm (fun i => by
          rw [le_div_iff₀ hℓx, mul_comm]
          simpa using hsup.fwd x x.2 μ i)
      calc _ ≤ X / G.spacing (x : CTorus d L N₁ m₁ K) +
            N * (V / G.spacing (x : CTorus d L N₁ m₁ K)) := add_le_add hg.1 hv
        _ = _ := by ring
    · have e : ((fun i => φ0 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i +
            svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i) -
          fun i => φ0 x i + svec G u x i) =
          (φ0 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - φ0 x) +
          (svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - svec G u x) := by
        funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
      rw [e]
      refine (vn_add _ _).trans ?_
      have hv := vn_le_card_mul (v := svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) -
        svec G u x) hm (fun i => by
          rw [le_div_iff₀ hℓx, mul_comm]
          simpa using hsup.bwd x x.2 μ i)
      calc _ ≤ X / G.spacing (x : CTorus d L N₁ m₁ K) +
            N * (V / G.spacing (x : CTorus d L N₁ m₁ K)) := add_le_add hg.2 hv
        _ = _ := by ring
  · have hm : 0 ≤ V / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
    have e : (fun i => ∑ μ : Fin d, (2 * (φ0 x i + svec G u x i) -
        (φ0 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
          svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i) -
        (φ0 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i +
          svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i))) =
        (fun i => -(∑ μ : Fin d, (φ0 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
          φ0 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i - 2 * φ0 x i))) +
        (fun i => ∑ μ : Fin d, (2 * svec G u x i -
          svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i -
          svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i)) := by
      funext i
      simp only [Pi.add_apply, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      ring
    rw [e]
    refine (vn_add _ _).trans ?_
    have hv := vn_le_card_mul (v := fun i => ∑ μ : Fin d, (2 * svec G u x i -
      svec G u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i -
      svec G u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i)) hm (fun i => by
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact hsup.lap x x.2 i)
    rw [vn_neg]
    calc _ ≤ X / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 +
          N * (V / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2) := add_le_add (hsm.lap x x.2) hv
      _ = _ := by ring

/-- **Theorem I-4b (ii): the defect.**  The decoupled background field satisfies the constraint up
to `|g|₀ ≤ 4 K₄ δ` and `|Δ g̃|₂ ≤ (5 + 2d) K₄ δ`, `g = φ_k(s) · φ_k(s) - 1`, `g̃` the zero extension
of `g` from `Ω₁`. -/
theorem i4b_defect {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) s D φ α) :
    (∀ x : G.Ω 1, ‖∑ i, φ (x, i) * φ (x, i) - 1‖ ≤ 4 * (K4 d L N BG κ * δ)) ∧
    (∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖negLap (zeroExt (G.Ω 1) (fun y : G.Ω 1 => ∑ i, φ (y, i) * φ (y, i) - 1))
        (x : CTorus d L N₁ m₁ K)‖ ≤ (5 + 2 * d) * (K4 d L N BG κ * δ)) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨-, hsup, -⟩ := h.sup_bounds hS S HB hκ hM hs hδ0 hδε hε hδ hνε hD
  obtain ⟨W⟩ := DataWit.exists hD
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  obtain ⟨h1, -, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  obtain ⟨hδa, -, hC32, -⟩ := bgC1_facts d L N hd0 h1
  have Sa : ApproxSetting d L K ϱ a ν δ ε :=
    HB.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
  have hl := lemma53 Sa hδa D W.real W (fun x hx i => W.real_Ψ hx i) (fun x hx i => W.real_h hx i)
  have hW1 := c7_small (L := L) (N := N) (κ := κ) hd0 hBG hδ0.le hδ
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hk := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hC := lemma53Const_pos d L
  have hX0 : 0 < lemma53Const d L * δ := mul_pos hC hδ0
  have hV0 : 0 ≤ cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ) := by positivity
  have hU0 : 0 ≤ N * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) := by positivity
  have hWd1 : lemma53Const d L * δ + N * (cK2' d L N (famConst d L BG κ) *
      (lemma53Const d L * δ)) ≤ 1 := by nlinarith
  have hWK : lemma53Const d L * δ + N * (cK2' d L N (famConst d L BG κ) *
      (lemma53Const d L * δ)) ≤ K4 d L N BG κ * δ := by
    unfold K4
    have : 0 ≤ ((L : ℝ) + 2 * d * (L : ℝ) ^ 2) * (lemma53Const d L * δ) := by positivity
    nlinarith
  have hφx : ∀ (x : G.Ω 1) (i : Fin N), approxField G a ν D.Ψ D.h x i +
      svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) x i = φ (x, i) := by
    intro x i
    rw [svec_of_mem]; ring
  have hone : ∀ y ∈ dataSites G, ∑ i, approxField G a ν D.Ψ D.h y i * approxField G a ν D.Ψ D.h y i = 1 :=
    fun y hy => (hl.1 y hy).1
  have hnb : ∀ (x : G.Ω 1) (μ : Fin d), (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ dataSites G ∧
      (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ dataSites G := by
    intro x μ
    refine ⟨(mem_dataSites G).2 ?_, (mem_dataSites G).2 ?_⟩
    · by_cases hh : (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ G.Ω 1
      · exact Or.inl hh
      · exact Or.inr (mem_collar_of_adj G x.2 hh (adj_add _ μ))
    · by_cases hh : (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ G.Ω 1
      · exact Or.inl hh
      · exact Or.inr (mem_collar_of_adj G x.2 hh (adj_sub _ μ))
  have hext : ∀ y ∈ dataSites G, zeroExt (G.Ω 1) (fun z : G.Ω 1 => ∑ i, φ (z, i) * φ (z, i) - 1) y =
      ∑ i, (approxField G a ν D.Ψ D.h y i + svec G (fun p => φ p -
        approxField G a ν D.Ψ D.h p.1 p.2) y i) * (approxField G a ν D.Ψ D.h y i +
        svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) y i) - 1 := by
    intro y hy
    by_cases hyΩ : y ∈ G.Ω 1
    · rw [zeroExt_mem (G.Ω 1) _ ⟨y, hyΩ⟩]
      simp only [hφx ⟨y, hyΩ⟩]
    · rw [zeroExt_not_mem _ _ hyΩ]
      simp only [svec_of_not_mem G _ hyΩ, add_zero, hone y hy, sub_self]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hb := ext_field_bounds hV0 Hd.smooth (fun x => Hd.phiBd x x.2) hsup x
    have := sq_defect_bound (approxField G a ν D.Ψ D.h x)
      (svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) x)
      (U := N * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ))) (by linarith)
      (hone x ((mem_dataSites G).2 (Or.inl x.2))) (Hd.phiBd x x.2)
      (vn_le_card_mul hV0 (fun i => hsup.val x i))
    simp only [hφx] at this
    refine this.trans ?_
    linarith
  · have hb := ext_field_bounds hV0 Hd.smooth (fun x => Hd.phiBd x x.2) hsup x
    have hn := hnb x
    have hlap : negLap (zeroExt (G.Ω 1) (fun y : G.Ω 1 => ∑ i, φ (y, i) * φ (y, i) - 1))
        (x : CTorus d L N₁ m₁ K) = ∑ μ : Fin d, (2 * (∑ i, (approxField G a ν D.Ψ D.h x i +
          svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) x i) *
          (approxField G a ν D.Ψ D.h x i +
          svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) x i)) -
          ∑ i, (approxField G a ν D.Ψ D.h ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
            svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
              ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i) *
            (approxField G a ν D.Ψ D.h ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i +
            svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
              ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i) -
          ∑ i, (approxField G a ν D.Ψ D.h ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i +
            svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
              ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i) *
            (approxField G a ν D.Ψ D.h ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i +
            svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
              ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i)) := by
      unfold negLap
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [hext _ ((mem_dataSites G).2 (Or.inl x.2)), hext _ (hn μ).1, hext _ (hn μ).2]
      ring
    rw [hlap]
    have key := negLap_sq_bound (fun y i => approxField G a ν D.Ψ D.h y i +
      svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) y i) (x : CTorus d L N₁ m₁ K)
      (spacing_pos G) (U := N * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)))
      (W := lemma53Const d L * δ + N * (cK2' d L N (famConst d L BG κ) *
        (lemma53Const d L * δ))) (by linarith) (by positivity) hWd1 hU0 hb.1
      (fun μ => hb.2.1 μ) hb.2.2
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_left hWK (by positivity)

end Defect

end Balaban.Localization
