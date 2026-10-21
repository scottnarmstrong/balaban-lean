/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyGraph
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Fluctuation.SizeModG1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Summing coefficients with a given label

* `norm_sum_label_le`: for coefficients `c x C` of the sets `C` rooted in a graph of bounded degree,
  with `‖c x C‖ ≤ B t^{|C|}`, the sum of those whose label is a given set `Y` is at most
  `|Xs| B z^n / (1 - z)` when each of them has `|C| ≥ n` and `x ∈ Xs` (rooted animals,
  `rooted_tail_sum_le`).
* `ncard_le_of_isDj`: a domain `Y ∈ 𝒟_j` has at most `a_j^d c₁ (1 + d^cov_j(Y))` sites.
* `one_add_mul_exp_le`, `tail_decay_aux`: the real inequality that turns the tail `z^n` of the
  rooted sum, `n ≥ (σ/γ - A)/P`, into the decay `e^{-μσ/2}`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Fluctuation Balaban.Localization Finset

/-- `(1 + σ) e^{-μ σ} ≤ (1 + 2/μ) e^{-μσ/2}` for `σ ≥ 0`, `μ > 0`. -/
theorem one_add_mul_exp_le {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 ≤ σ) :
    (1 + σ) * Real.exp (-(μ * σ)) ≤ (1 + 2 / μ) * Real.exp (-(μ / 2 * σ)) := by
  have h1 : Real.exp (-(μ * σ)) = Real.exp (-(μ / 2 * σ)) * Real.exp (-(μ / 2 * σ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : σ * Real.exp (-(μ / 2 * σ)) ≤ 2 / μ := by
    have := Real.add_one_le_exp (μ / 2 * σ)
    have h3 : Real.exp (-(μ / 2 * σ)) * (μ / 2 * σ + 1) ≤ 1 := by
      calc Real.exp (-(μ / 2 * σ)) * (μ / 2 * σ + 1) ≤ Real.exp (-(μ / 2 * σ)) * Real.exp (μ / 2 * σ) :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h4 : (μ / 2) * (σ * Real.exp (-(μ / 2 * σ))) ≤ 1 := by nlinarith [Real.exp_pos (-(μ / 2 * σ))]
    rw [le_div_iff₀ hμ]; nlinarith
  have h5 : 0 < Real.exp (-(μ / 2 * σ)) := Real.exp_pos _
  rw [h1]
  calc (1 + σ) * (Real.exp (-(μ / 2 * σ)) * Real.exp (-(μ / 2 * σ)))
      = (Real.exp (-(μ / 2 * σ)) + σ * Real.exp (-(μ / 2 * σ))) * Real.exp (-(μ / 2 * σ)) := by ring
    _ ≤ (1 + 2 / μ) * Real.exp (-(μ / 2 * σ)) := by
        refine mul_le_mul_of_nonneg_right ?_ h5.le
        have : Real.exp (-(μ / 2 * σ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith

/-- The decay of the weighted tail: `(1 + σ) z^n ≤ e^{λ A / P} (1 + 2/μ) e^{-μσ/2}`, `z = e^{-λ}`,
`μ = λ / (γ P)`, whenever `n ≥ (σ/γ - A)/P`. -/
theorem tail_decay_aux {z γ P A σ : ℝ} {n : ℕ} (hz0 : 0 < z) (hz1 : z < 1) (hγ : 0 < γ) (hP : 0 < P)
    (hσ : 0 ≤ σ) (hn : (σ / γ - A) / P ≤ n) :
    (1 + σ) * z ^ n ≤ Real.exp (-Real.log z * A / P) * ((1 + 2 / (-Real.log z / (γ * P)))) *
      Real.exp (-(-Real.log z / (γ * P) / 2 * σ)) := by
  set lam : ℝ := -Real.log z with hlam
  have hlam0 : 0 < lam := by rw [hlam]; have := Real.log_neg hz0 hz1; linarith
  set μ : ℝ := lam / (γ * P) with hμ
  have hμ0 : 0 < μ := by positivity
  have hzn : z ^ n = Real.exp (-(lam * n)) := by
    rw [hlam, show -(-Real.log z * n) = n * Real.log z by ring, ← Real.log_pow, Real.exp_log (by positivity)]
  have hn' : (σ / γ - A) ≤ P * n := by
    have := (div_le_iff₀ hP).1 hn; linarith
  have h1 : z ^ n ≤ Real.exp (lam * A / P) * Real.exp (-(μ * σ)) := by
    rw [hzn, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have e1 : lam * A / P - μ * σ = -(lam / P) * (σ / γ - A) := by
      rw [hμ]; field_simp; ring
    have e2 : -(lam * n) ≤ -(lam / P) * (σ / γ - A) := by
      have : lam / P * (σ / γ - A) ≤ lam / P * (P * n) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
      have e3 : lam / P * (P * n) = lam * n := by field_simp
      nlinarith
    linarith
  have h2 := one_add_mul_exp_le hμ0 hσ
  calc (1 + σ) * z ^ n ≤ (1 + σ) * (Real.exp (lam * A / P) * Real.exp (-(μ * σ))) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = Real.exp (lam * A / P) * ((1 + σ) * Real.exp (-(μ * σ))) := by ring
    _ ≤ Real.exp (lam * A / P) * ((1 + 2 / μ) * Real.exp (-(μ / 2 * σ))) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by rw [hlam, hμ]; ring


section Sum

variable {ι V Ω : Type*} [Fintype ι] [Fintype V] [DecidableEq V] {Gr : SimpleGraph V}
  [Gr.LocallyFinite]

open Classical in
/-- **The sum of the rooted coefficients with a given label.**  Let `c x C` be coefficients of the
finite sets `C` of vertices of a graph of degree at most `b`, non-zero only for the sets rooted at
a set `N x` of at most `b_root` vertices, with `‖c x C‖ ≤ B t^{|C|}` and `Δ² t < 1`,
`Δ = max (b + 1) b_root`.  If every non-zero coefficient whose label `ℓ x C` is `Y` has
`|C| ≥ n` and `x ∈ Xs`, then the sum of the coefficients with label `Y` is at most
`|Xs| B z^n / (1 - z)`, `z = Δ² t`. -/
theorem norm_sum_label_le {b b_root : ℕ} (hb : ∀ v, Gr.degree v ≤ b) (N : ι → Finset V)
    (hN : ∀ x, (N x).card ≤ b_root) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t < 1) (c : ι → Finset V → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (ℓ : ι → Finset V → Set Ω) (Y : Set Ω) (n : ℕ) (Xs : Finset ι)
    (hroot : ∀ x C, c x C ≠ 0 → C ∈ Polymer.rootedSets (G := Gr) ((N x : Finset V) : Set V))
    (hbd : ∀ x C, ‖c x C‖ ≤ B * t ^ C.card)
    (hn : ∀ x C, c x C ≠ 0 → ℓ x C = Y → n ≤ C.card)
    (hx : ∀ x C, c x C ≠ 0 → ℓ x C = Y → x ∈ Xs) :
    ‖∑ x, ∑ C ∈ Finset.univ.filter (fun C : Finset V => ℓ x C = Y), c x C‖ ≤
      Xs.card * (B * ((((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) ^ n /
        (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t))) := by
  set z : ℝ := ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t with hzdef
  have hper : ∀ x, ∑ C ∈ Finset.univ.filter (fun C : Finset V => ℓ x C = Y), ‖c x C‖ ≤
      if x ∈ Xs then B * (z ^ n / (1 - z)) else 0 := by
    intro x
    by_cases hxX : x ∈ Xs
    · simp only [hxX, ↓reduceIte]
      rw [← Finset.sum_filter_ne_zero]
      have hsub : (Finset.univ.filter (fun C : Finset V => ℓ x C = Y)).filter (fun C => ‖c x C‖ ≠ 0) ⊆
          (Polymer.rootedSets (G := Gr) ((N x : Finset V) : Set V)).filter (fun C => n ≤ C.card) := by
        intro C hC
        obtain ⟨hC1, hC2⟩ := Finset.mem_filter.1 hC
        have hne : c x C ≠ 0 := fun h => hC2 (by rw [h]; simp)
        exact Finset.mem_filter.2 ⟨hroot x C hne, hn x C hne (Finset.mem_filter.1 hC1).2⟩
      calc ∑ C ∈ (Finset.univ.filter (fun C : Finset V => ℓ x C = Y)).filter (fun C => ‖c x C‖ ≠ 0),
            ‖c x C‖
          ≤ ∑ C ∈ (Polymer.rootedSets (G := Gr) ((N x : Finset V) : Set V)).filter
              (fun C => n ≤ C.card), ‖c x C‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ => norm_nonneg _)
        _ ≤ ∑ C ∈ (Polymer.rootedSets (G := Gr) ((N x : Finset V) : Set V)).filter
              (fun C => n ≤ C.card), B * t ^ C.card := Finset.sum_le_sum fun C _ => hbd x C
        _ = B * ∑ C ∈ (Polymer.rootedSets (G := Gr) ((N x : Finset V) : Set V)).filter
              (fun C => n ≤ C.card), t ^ C.card := by rw [Finset.mul_sum]
        _ ≤ B * (z ^ n / (1 - z)) := by
            refine mul_le_mul_of_nonneg_left ?_ hB
            exact rooted_tail_sum_le hb (N x) (hN x) ht hz n
    · simp only [hxX, ↓reduceIte]
      refine le_of_eq (Finset.sum_eq_zero fun C hC => ?_)
      by_contra hne
      exact hxX (hx x C (fun h => hne (by rw [h]; simp)) (Finset.mem_filter.1 hC).2)
  calc ‖∑ x, ∑ C ∈ Finset.univ.filter (fun C : Finset V => ℓ x C = Y), c x C‖
      ≤ ∑ x, ‖∑ C ∈ Finset.univ.filter (fun C : Finset V => ℓ x C = Y), c x C‖ := norm_sum_le _ _
    _ ≤ ∑ x, ∑ C ∈ Finset.univ.filter (fun C : Finset V => ℓ x C = Y), ‖c x C‖ :=
        Finset.sum_le_sum fun x _ => norm_sum_le _ _
    _ ≤ ∑ x, (if x ∈ Xs then B * (z ^ n / (1 - z)) else 0) := Finset.sum_le_sum fun x _ => hper x
    _ = Xs.card * (B * (z ^ n / (1 - z))) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul]

end Sum


variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

open Classical in
/-- **The number of sites of a domain.**  A domain `Y ∈ 𝒟_j` has at most
`a_j^d c₁ (1 + d^cov_j(Y))` sites, `a_j = L^{j+m₀+m₁}`. -/
theorem ncard_le_of_isDj (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Y : Set (Balaban.Localization.CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ j Y) :
    (Y.ncard : ℝ) ≤ ((cellSide L m₀ m₁ j : ℕ) : ℝ) ^ d * (c1 d L * (1 + treeLenCovOne m₀ j Y)) := by
  have h1 := ncard_le_of_isPiPrimeUnion hN hj hY.2.1
  have h2 := G1_cellCount hN hj (Ω := Set.univ) (X := Y)
    ⟨hY, fun z hz => absurd (Set.mem_univ z) hz⟩
  rw [Set.inter_univ, dcovMod_of_subset (Set.subset_univ Y)] at h2
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left h2 (by positivity)


end Balaban.LargeField.Base
