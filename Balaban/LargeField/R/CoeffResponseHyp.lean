/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponse
public import Balaban.LargeField.R.MassResponseHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The same-datum coefficient response (P7 p. 500 (2.10)–(2.12))

* `coeffSource_bound` : `ℓ² |f₁| ≤ m · Bh` for the coefficient source, from the bound `m` on the
  coefficient change on every layer and the bound `Bh` on the block read `Ψ - Q φ¹`;
* `prop51Hyp_coeffSource` : `Prop51Hyp` for the coefficient source;
* `coeffChange_sameData_response_of_weighted` : the response, conditional on the weighted
  Proposition 5.1 predicate;
* `coeffChange_sameData_response` : the response with constants `K_w, δ_w` depending only on
  `(d, L, N)`, and the consumer's bound on `w̄` with `√N · K_w`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Finset Matrix

section Source

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **Source bound for the coefficient change**: `ℓ(x)² |f₁(x)| ≤ m · Bh` when the coefficients
differ by at most `m` on every layer and the block read `Ψ - Q φ¹` is at most `Bh`. -/
theorem coeffSource_bound {m Bh : ℝ} (a₀ a₁ : ℕ → ℝ) (D : BgData G N) (φ1 : G.Ω 1 × Fin N → ℂ)
    (hm : ∀ x : G.Ω 1, |a₁ (G.layerIndex (x : Torus d (N₀ * L ^ K))) -
      a₀ (G.layerIndex (x : Torus d (N₀ * L ^ K)))| ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖D.Ψ x i - blockAvg G φ1 x i‖ ≤ Bh)
    (x : G.Ω 1) (i : Fin N) :
    G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 *
      ‖qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) (x, i)‖ ≤ m * Bh := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  have hsp := G.spacing_eq hj1 hjk hxl
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 := by positivity
  unfold qStar
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hsp, abs_div, abs_of_pos hℓ]
  have e : ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 *
      (|(a₁ - a₀) (G.layerIndex (x : Torus d (N₀ * L ^ K)))| /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 *
        ‖D.Ψ x i - blockAvg G φ1 x i‖) =
      |(a₁ - a₀) (G.layerIndex (x : Torus d (N₀ * L ^ K)))| * ‖D.Ψ x i - blockAvg G φ1 x i‖ := by
    field_simp
  simp only [] at e ⊢
  rw [e]
  exact mul_le_mul (by simpa using hm x) (hB x i) (norm_nonneg _) ((abs_nonneg _).trans (hm x))

/-- **`Prop51Hyp` for the coefficient source** (P7 p. 500 (2.10)–(2.12)): at coefficient `a₀`,
`δΨ = 0`, `f₁ = Q*(a₁ - a₀)(Ψ - Q φ¹)`. -/
theorem prop51Hyp_coeffSource (a₀ a₁ : ℕ → ℝ) (ν m Bh δ₀ δ₁ : ℝ) (D : BgData G N)
    {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 : G.Ω 1 → ℂ}
    (hG : GreenSetting G a₀ ν) (h0 : IsEL G a₀ ν D φ0 α0) (hb : BgBounds G D φ0 α0 δ₀)
    (hφ : ∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2)
    (hm : ∀ x : G.Ω 1, |a₁ (G.layerIndex (x : Torus d (N₀ * L ^ K))) -
      a₀ (G.layerIndex (x : Torus d (N₀ * L ^ K)))| ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖D.Ψ x i - blockAvg G φ1 x i‖ ≤ Bh)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hδ₀s : δ₀ ≤ deltaStar d L N) (hδ₁s : δ₁ ≤ deltaStar d L N)
    (hmB : m * Bh ≤ δ₁) :
    Prop51Hyp G a₀ ν α0 (barField G D.Ψ φ0) (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ)
      (fun p => qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) p) δ₀ δ₁ :=
  prop51Hyp_of_zeroChange a₀ ν δ₀ δ₁ D hG h0 hb hφ hδ₀ hδ₁ hδ₀s hδ₁s fun x i =>
    (coeffSource_bound a₀ a₁ D φ1 hm hB x i).trans hmB

end Source

section Response

variable {d L N : ℕ} [NeZero L] {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {Kw δw : ℝ}

/-- **Coefficient response, conditional form.**  On one datum `D` and one mass `ν`, with `φ⁰`, `φ¹`
solving (EL) at coefficients `a₀`, `a₁`: given the weighted Proposition 5.1 predicate, `Prop51Hyp`
for the coefficient source and `Dec2.OpSetting`, and `|α¹ - α⁰|₂ ≤ c₆`, the response is bounded
with weight one by `Kw · (m Bh)`. -/
theorem coeffChange_sameData_response_of_weighted
    (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a₀ a₁ : ℕ → ℝ) (ν m Bh δ₀ δ₁ : ℝ)
    (D : BgData G N) {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 α1 : G.Ω 1 → ℂ}
    (h0 : IsEL G a₀ ν D φ0 α0) (h1 : IsEL G a₁ ν D φ1 α1)
    (hP : Prop51Hyp G a₀ ν α0 (barField G D.Ψ φ0)
      (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ)
      (fun p => qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) p) δ₀ δ₁)
    (hO : Dec2.OpSetting G a₀ ν) (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw)
    (hm0 : 0 ≤ m) (hBh0 : 0 ≤ Bh)
    (hm : ∀ x : G.Ω 1, |a₁ (G.layerIndex (x : Torus d ((N₁ * L ^ m₁) * L ^ K))) -
      a₀ (G.layerIndex (x : Torus d ((N₁ * L ^ m₁) * L ^ K)))| ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖D.Ψ x i - blockAvg G φ1 x i‖ ≤ Bh)
    (hα : Small G (α1 - α0) (c6 d L N)) :
    SmallW G (fun _ => 1) (α1 - α0) (Kw * (m * Bh)) ∧
      SupBoundsW G (fun _ => 1) (φ1 - φ0) (Kw * (m * Bh)) := by
  have hg : ∀ x : G.Ω 1, gdef G (barField G D.Ψ φ0) x = 0 := by
    intro x
    have := h0.2 x
    simp only [gdef, barField, x.2, dite_true]
    rw [this]; ring
  have hd0 : 0 < d := by have := hP.green.hd; omega
  exact hW G a₀ ν α0 (barField G D.Ψ φ0) 0 _ δ₀ δ₁ hP hO hg hδ₀ hδ₁
    (fun _ => 1) (IsWeight.one G (gammaW_nonneg hd0)) (m * Bh) (mul_nonneg hm0 hBh0) (fun x i => by
      rw [pertSource_zero]; simpa using coeffSource_bound a₀ a₁ D φ1 hm hB x i)
    (φ1 - φ0) (α1 - α0) (by rw [pertSource_zero]; exact coeffSource_perturbed a₀ a₁ ν D h0 h1) hα

/-- **Same-datum coefficient response, premises only** (P7 p. 500 (2.10)–(2.12)).  There are
`K_w, δ_w > 0` depending only on `(d, L, N)` such that for every generating set, datum, mass and
pair of Euler–Lagrange backgrounds at coefficients `a₀` and `a₁` with the stated bounds, the
multiplier difference and the field difference are bounded with weight one by `K_w · (m · Bh)`
(`m` bounds `|a₁ - a₀|` on every layer, `Bh` the block read `|Ψ - Q φ¹|`), and the consumer's
`hresp` holds with `K_m = √N · K_w`.  The structure of the constants is that of
`massChange_sameData_response`. -/
theorem coeffChange_sameData_response (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a₀ a₁ : ℕ → ℝ) (ν m Bh δ₀ : ℝ) (D : BgData G N)
        {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 α1 : G.Ω 1 → ℂ},
        IsEL G a₀ ν D φ0 α0 → IsEL G a₁ ν D φ1 α1 →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φ1 α1 δ₀ →
        GreenSetting G a₀ ν → Dec2.OpSetting G a₀ ν →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar d L N) δw → 2 * δ₀ ≤ c6 d L N →
        0 ≤ m → 0 ≤ Bh → m * Bh ≤ min (deltaStar d L N) δw →
        (∀ x : G.Ω 1, |a₁ (G.layerIndex (x : CTorus d L N₁ m₁ K)) -
          a₀ (G.layerIndex (x : CTorus d L N₁ m₁ K))| ≤ m) →
        (∀ (x : G.Ω 1) (i : Fin N), ‖D.Ψ x i - blockAvg G φ1 x i‖ ≤ Bh) →
        (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) →
        (SmallW G (fun _ => 1) (α1 - α0) (Kw * (m * Bh)) ∧
          SupBoundsW G (fun _ => 1) (φ1 - φ0) (Kw * (m * Bh))) ∧
        ∀ x, vnorm (wExt D D φ1 φ0 x) ≤ (Real.sqrt N * Kw) * Bh * m := by
  obtain ⟨Kw, δw, hK, hδ, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a₀ a₁ ν m Bh δ₀ D φ0 φ1 α0 α1 h0 h1 b0 b1 hG hO hδ₀ hδs h2 hm0 hBh0 hmB
    hm hB hφ
  have hP := prop51Hyp_coeffSource a₀ a₁ ν m Bh δ₀ (m * Bh) D hG h0 b0 hφ hm hB hδ₀
    (mul_nonneg hm0 hBh0) (hδs.trans (min_le_left _ _)) (hmB.trans (min_le_left _ _)) le_rfl
  have hα : Small G (α1 - α0) (c6 d L N) := fun x => by
    have := massMultiplier_small b0 b1 x
    linarith
  have hres := coeffChange_sameData_response_of_weighted hW a₀ a₁ ν m Bh δ₀ (m * Bh) D h0 h1 hP hO
    (hδs.trans (min_le_right _ _)) (hmB.trans (min_le_right _ _)) hm0 hBh0 hm hB hα
  refine ⟨hres, fun x => ?_⟩
  have hV : 0 ≤ Kw * (m * Bh) := by have := mul_nonneg hm0 hBh0; positivity
  calc _ ≤ _ := vnorm_wExt_le_of_response D hV hres.2 x
    _ = _ := by ring

end Response

end Balaban.LargeField.ActionConv
