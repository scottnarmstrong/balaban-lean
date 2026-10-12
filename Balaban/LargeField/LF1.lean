/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.HardSpin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# LF-1: lower bounds for the multiscale action (LF-RECONSTRUCTION Theorem II.4.1)

P6 Proposition 3.1 for hard spins, with `γ₀ = 1/(28 d)` and no condition on the multiplier.

Setting (§II.4): `G` is a generating set at level `q` on the fine torus `Torus d (N₀ L^q)` (unit
lattice spacing) with separation `ϱ ≥ 2 d L`, layers `Λ_n = Ω_n ∖ Ω_{n+1}` (`n ≥ 1`) and
`Λ_0 = T ∖ Ω₁` (`lam G n`), weights `a_n ∈ [½, 2]` (`IsAdmissibleWeights`), `μ ≥ 0`, `h ∈ ℝ^N`.
`X` is a set of sites such that `X ∩ Λ_n` is a union of `n`-blocks for every `n ≥ 1`.  The
variables are `φ : X → ℝ^N`, `ψ_n` on the `n`-blocks (`ψ n y`, `n ≥ 1`), and `ψ_0 := φ`
(`psiFull`).  The action is `actionG G a μ h X ψ φ`, the pairs are `pairSumT` (the unordered
nearest-neighbour pairs `P_n(X)`) and `crossSumP` (the pairs `P^×_{n+1}(X)`).

* `adjacent_blockAvg_sq_le` and `hardSpin_one_sub_sq_le` (Lemmas II.4.2 and II.4.3, in
  `LF1/Avg.lean`);
* `lf1_gradient`: Theorem II.4.1 (a);
* `lf1_hardSpin`: Theorem II.4.1 (b).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

/-- The constant `γ₀ = 1/(28 d)` of LF-1. -/
noncomputable def gamma0 (d : ℕ) : ℝ := 1 / (28 * d)

/-- The unit direction `(u)_0 = u / ‖u‖`. -/
noncomputable def unitDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E) : E :=
  ‖u‖⁻¹ • u

section Main

variable {Nspin d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

omit [NeZero N₀] [NeZero L] in
theorem psiFull_of_pos {E : Type*} (φ : Site d L N₀ q → E) (ψ : (m : ℕ) → Blk d L N₀ q m → E)
    {n : ℕ} (hn : 1 ≤ n) : psiFull φ ψ n = ψ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 hn)
  rfl

/-- The action dominates `¼ ∑_n Bk_n + ½ E(X) + (μ/2) ∑_X |φ - h|²`. -/
theorem actionG_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GeneratingSet d L N₀ q ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights q a) {μ : ℝ}
    (h : E) (X : Finset (Site d L N₀ q)) (ψ : (m : ℕ) → Blk d L N₀ q m → E)
    (φ : Site d L N₀ q → E) :
    1 / 4 * ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n + 1 / 2 * bondE X φ +
      μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 ≤ actionG G a μ h X ψ φ := by
  unfold actionG
  have h1 : 1 / 4 * ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n ≤ 1 / 2 * ∑ n ∈ Finset.Icc 1 q,
      ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have han := (ha n hn1 (Finset.mem_Icc.1 hn).2).1
    unfold bk
    rw [psiFull_of_pos φ ψ hn1]
    calc 1 / 4 * ((L : ℝ) ^ (n * (d - 2)) * ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2)
        = ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          1 / 4 * ((L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          1 / 2 * (a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have hp : 0 ≤ (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_right han hp]
      _ = _ := by rw [Finset.mul_sum]
  linarith

/-- **Theorem II.4.1 (a)** (LF-1, gradient bound). For arbitrary `ψ`, `φ`,
`A_G(X; ψ, φ) ≥ γ₀ {∑_{n=0}^q (L^{n(d-2)}/2) ∑_{{y,y'}∈P_n(X)} |ψ_n(y) - ψ_n(y')|²
  + ∑_{n=0}^{q-1} (L^{(n+1)(d-2)}/2) ∑_{(b₊,b₋)∈P^×_{n+1}(X)} |ψ_{n+1}(b₊) - (Qψ_n)(b₋)|²}`,
with `γ₀ = 1/(28 d)`, `ψ_0 = φ`. -/
theorem lf1_gradient (G : GeneratingSet d L N₀ q ϱ) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights q a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) (X : Finset (Site d L N₀ q))
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) :
    gamma0 d * (∑ n ∈ Finset.range (q + 1), ((L : ℝ) ^ (n * (d - 2)) / 2) *
          pairSumT (tBlocks d L N₀ q n (lam G n ∩ X)) (psiFull φ ψ n) +
        ∑ n ∈ Finset.range q, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
          crossSumP G n X (psiFull φ ψ)) ≤ actionG G a μ h X ψ φ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := total_bound G hd hL hϱ X hX φ ψ
  have h2 := actionG_ge G ha h X ψ φ
  have hE := bondE_nonneg X φ
  have hB : 0 ≤ ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n :=
    Finset.sum_nonneg fun n _ => bk_nonneg G X φ ψ n
  have hS : 0 ≤ μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  unfold gamma0
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hE (sub_nonneg.2 hd2)]

/-- **Theorem II.4.1 (b)** (LF-1, hard-spin bound). If `|φ(x)| = 1` on `X`, `|h| = 1`,
`μ L^{2q} ≤ 1` and `ψ_n(y) ≠ 0`, then
`A_G(X; ψ, φ) ≥ γ₀ ∑_{n=0}^q L^{n(d-2)} ∑_{y∈T_n(Λ_n∩X)}
  [½(|ψ_n(y)| - 1)² + μ L^{2n}(1 - h·(ψ_n(y))₀)]`. -/
theorem lf1_hardSpin (G : GeneratingSet d L N₀ q ϱ) (hd : 2 ≤ d) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights q a) {μ : ℝ} (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin))
    (hh : ‖h‖ = 1) (X : Finset (Site d L N₀ q))
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ X, ‖φ x‖ = 1)
    (hμq : μ * (L : ℝ) ^ (2 * q) ≤ 1)
    (hψ : ∀ n, 1 ≤ n → n ≤ q → ∀ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), ψ n y ≠ 0) :
    gamma0 d * ∑ n ∈ Finset.range (q + 1), (L : ℝ) ^ (n * (d - 2)) *
        ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          (1 / 2 * (‖psiFull φ ψ n y‖ - 1) ^ 2 + μ * (L : ℝ) ^ (2 * n) *
            (1 - inner ℝ h (unitDir (psiFull φ ψ n y)))) ≤ actionG G a μ h X ψ φ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := hardSpin_total G hd X hX φ hφ h hh hμ hμq ψ (fun n hn1 hnq y hy => by
    rw [psiFull_of_pos φ ψ hn1]; exact hψ n hn1 hnq y hy)
  have h2 := actionG_ge G ha h X ψ φ
  have hE := bondE_nonneg X φ
  have hB : 0 ≤ ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n :=
    Finset.sum_nonneg fun n _ => bk_nonneg G X φ ψ n
  have hS : 0 ≤ μ * ∑ x ∈ X, ‖φ x - h‖ ^ 2 :=
    mul_nonneg hμ (Finset.sum_nonneg fun _ _ => by positivity)
  have hS' : μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 = 1 / 2 * (μ * ∑ x ∈ X, ‖φ x - h‖ ^ 2) := by ring
  unfold gamma0 unitDir
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hE (sub_nonneg.2 hd2), mul_nonneg hB (sub_nonneg.2 hd2),
    mul_nonneg hS (sub_nonneg.2 hd2)]

end Main

end Balaban.LargeField
