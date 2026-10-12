/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33Count
public import Balaban.Fluctuation.Prop33Parts
public import Balaban.Fluctuation.Prop33Agg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The resummation (3.5) for the terms of the localized interaction

Counting estimates that turn the sums over the terms with `Y ∈ 𝒴_τ` of the bounds of
`interaction_expansion` into volume-independent bounds `C e^{-(2κ_dec - 1) d^cov_{k+1}(Y)}`:

* `polyDom_isMultiDom`, `subset_polyDom`: the label sets;
* `card_blocks_filter_le`: the number of blocks of `B_{n+1}` inside `Y` is at most
  `c₁ M^d (1 + d^cov_{k+1}(Y))`;
* `sum_roots_le`: the sum of the bounds of old terms rooted in `Y` is at most `ρ |Y|`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

section Bound

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The label sets `polyDom` consist of multiscale polymer domains. -/
theorem polyDom_isMultiDom {X₁f : Finset (CTorus d L N₁ m₁ K)} {j m₀ : ℕ}
    {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hS : CovSetup Gp m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polyDom Gp X₁f m₀ j 𝒦X) : IsMultiDom Gp m₀ Y :=
  polymerDomain_isMultiDom (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) hS hd
    (fun i => i.1.2) hopt hY

/-- Every label `Y` contains the set `X₁` of its cover. -/
theorem subset_polyDom {X₁f : Finset (CTorus d L N₁ m₁ K)} {j m₀ : ℕ}
    {𝒦X : Set (CTorus d L N₁ m₁ K)} {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : Y ∈ polyDom Gp X₁f m₀ j 𝒦X) : X1 Gp m₀ j 𝒦X ⊆ Y :=
  subset_of_mem_polymerDomains hY

/-- **Blocks in a domain.**  The number of blocks `B_{n+1}(z)` contained in a multiscale polymer
domain `Y` of the level `n + 1` is at most `c₁ M^d (1 + d^cov(Y))`, `M = L^{m₀ + m₁}`
(Lemma 1.2 (G1)). -/
theorem card_blocks_filter_le {n m₀ : ℕ} (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K)
    (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsMultiDom Gp m₀ Y)
    (S : Finset (Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))))
    (hS : ∀ z ∈ S, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ Y) :
    (S.card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
  have h1 : ((S.card * (L ^ (n + 1)) ^ d : ℕ) : ℝ) ≤ (Y.ncard : ℝ) := by
    exact_mod_cast card_blocks_mul_le hp Y S hS
  have h2 := ncard_le_of_isMultiDom hG' hN hY
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hP : (0 : ℝ) < ((L : ℝ) ^ (n + 1)) ^ d := by positivity
  push_cast at h1
  have h3 : (S.card : ℝ) * ((L : ℝ) ^ (n + 1)) ^ d ≤
      (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y)) *
        ((L : ℝ) ^ (n + 1)) ^ d := by
    nlinarith
  exact le_of_mul_le_mul_right h3 hP

end Bound

section Roots

variable {τι : Type*} {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- **Old terms rooted in a set.**  If the bounds of the terms rooted at each site add up to at
most `ρ`, the terms rooted in `Y` add up to at most `ρ |Y|`. -/
theorem sum_roots_le [DecidableEq τι] (𝒯 : Finset τι) (w : τι → ℝ) (hw : ∀ τ ∈ 𝒯, 0 ≤ w τ)
    (rt : τι → α) (Y : Set α) {ρ : ℝ} (hρ : ∀ x, ∑ τ ∈ 𝒯.filter (fun τ => rt τ = x), w τ ≤ ρ) :
    ∑ τ ∈ 𝒯, (if rt τ ∈ Y then w τ else 0) ≤ ρ * (Y.ncard : ℝ) := by
  classical
  set Yf : Finset α := Finset.univ.filter (· ∈ Y) with hYf
  have hnc : (Y.ncard : ℝ) = (Yf.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card' Y]
    congr 2
    ext x; simp [hYf]
  have e1 : ∑ τ ∈ 𝒯, (if rt τ ∈ Y then w τ else 0) = ∑ τ ∈ 𝒯.filter (fun τ => rt τ ∈ Yf), w τ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [hYf]
  rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := 𝒯.filter (fun τ => rt τ ∈ Yf)) (t := Yf)
    (g := rt) (fun τ hτ => (Finset.mem_filter.1 hτ).2), hnc, mul_comm, ← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul Yf _ ρ fun x _ => ?_)
  refine le_trans ?_ (hρ x)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun τ hτ _ => hw τ (Finset.mem_filter.1 hτ).1
  intro τ hτ
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hτ
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, h2⟩

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- **Weighted sums of site terms.**  With the amplitudes `f : α × β → ℝ` and
`∑ |f| ≤ 1`, the sum `∑_τ f(root τ) w_τ` is at most `ρ`. -/
theorem sum_weighted_le [DecidableEq τι] (𝒯 : Finset τι) (w : τι → ℝ)
    (rt : τι → α × β) (f : α × β → ℝ) (hf : ∀ p, 0 ≤ f p) (hf1 : ∑ p, f p ≤ 1) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ p, ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ ≤ ρ) :
    ∑ τ ∈ 𝒯, f (rt τ) * w τ ≤ ρ := by
  classical
  have e1 : ∑ τ ∈ 𝒯, f (rt τ) * w τ =
      ∑ p, f p * ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := 𝒯) (t := Finset.univ) (g := rt)
      (fun τ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ hτ => by rw [(Finset.mem_filter.1 hτ).2]
  rw [e1]
  calc ∑ p, f p * ∑ τ ∈ 𝒯.filter (fun τ => rt τ = p), w τ ≤ ∑ p, f p * ρ :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hρ p) (hf p)
    _ = (∑ p, f p) * ρ := by rw [Finset.sum_mul]
    _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hf1 hρ0
    _ = ρ := one_mul ρ

end Roots

section Alg

/-- `(1 + t) e^{-2κ t} ≤ e^{-(2κ - 1) t}`: the factor `1 + d^cov` of (G1) is absorbed
by one unit of the decay rate. -/
theorem one_add_mul_exp_le (t κ : ℝ) :
    (1 + t) * Real.exp (-2 * κ * t) ≤ Real.exp (-(2 * κ - 1) * t) := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : Real.exp (-(2 * κ - 1) * t) = Real.exp t * Real.exp (-2 * κ * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- A sum of a constant over the elements satisfying a predicate. -/
theorem sum_ite_card_le {Zt : Type*} [Fintype Zt] (P : Zt → Prop) [DecidablePred P] {v k : ℝ}
    (hv : 0 ≤ v) (hk : ((Finset.univ.filter P).card : ℝ) ≤ k) :
    ∑ z, (if P z then v else 0) ≤ k * v := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hk hv

end Alg

end Balaban.Fluctuation
