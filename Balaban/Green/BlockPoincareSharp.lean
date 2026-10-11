/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BlockPoincare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp (`d`-free) block Poincaré inequality

Brief W2d, item 1; GREEN.md Lemma 4.1. The landed `Balaban.blockPoincare` has the constant `d / 2`.
Here the constant is `1 / 2` in every dimension:

* `Balaban.blockPoincare_sharp`:
  `∑ₓ (φ x - (P φ) x)² ≤ (N² / 2) · innerEnergy N φ` for all `d`;
* `Balaban.blockPoincare_latticeEnergy_sharp`: the same with `latticeEnergy φ`.

(The spectral constant is `N² / 4`; the proof below gives `N² / 2`, which is what the one-dimensional
Cauchy–Schwarz bound `pairSum_le_oneD` provides, and is independent of `d`.)

Proof. Tensorization with an exact variance decomposition instead of the lossy splitting of
`pairSum_succ_le`. For one block cell, with `w_β(y) = ∑_{a ∈ β} f(a, y)` the block sum in the first
coordinate, `pair_expand` gives, for the pair sum `R(y, y')` over the first coordinate,
`R(y, y') = T(y) + T(y') + ∑_β (w_β(y) - w_β(y'))²`, `T(y) = N ∑ₐ f(a, y)² - ∑_β w_β(y)²`.
`2 T(y) ≤ N³ ∑_c innerGap` is the one-dimensional bound, and the last term is the pair sum of the
`d`-dimensional function `w_β`, controlled by induction and Cauchy–Schwarz
(`sum_innerEnergy_wBlock_le`). Hence `pairSum f ≤ N^{d+2} innerEnergy f` (`pairSum_le_sharp`) with no
loss in `d`.
-/

@[expose] public section

namespace Balaban

open Finset

section OneD

variable {ℓ N m : ℕ} [NeZero ℓ]

/-- The sum of `p` over the block `β` of side `N`. -/
noncomputable def blockSum1 (N m : ℕ) (p : ZMod ℓ → ℝ) (β : ZMod m) : ℝ :=
  ∑ a ∈ Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = β, p a

theorem sum_ite_blockCoord_eq' [NeZero m] (hℓ : ℓ = N * m) (a : ZMod ℓ) (K : ℝ) :
    (∑ b : ZMod ℓ, if blockCoord N m a = blockCoord N m b then K else 0) = N * K := by
  rw [← sum_ite_blockCoord_eq hℓ (blockCoord N m a) K]
  exact Finset.sum_congr rfl fun b _ => if_congr eq_comm rfl rfl

theorem pair_expand [NeZero m] (hℓ : ℓ = N * m) (p q : ZMod ℓ → ℝ) :
    (∑ a, ∑ b, if blockCoord N m a = blockCoord N m b then (p a - q b) ^ 2 else 0) =
      N * ∑ a, p a ^ 2 + N * ∑ b, q b ^ 2 -
        2 * ∑ β : ZMod m, blockSum1 N m p β * blockSum1 N m q β := by
  have h1 : ∀ a b : ZMod ℓ, (if blockCoord N m a = blockCoord N m b then (p a - q b) ^ 2 else 0) =
      (if blockCoord N m a = blockCoord N m b then p a ^ 2 else 0) +
      (if blockCoord N m a = blockCoord N m b then q b ^ 2 else 0) -
      2 * (if blockCoord N m a = blockCoord N m b then p a * q b else 0) := by
    intro a b; split_ifs <;> ring
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have e1 : (∑ a, ∑ b : ZMod ℓ, if blockCoord N m a = blockCoord N m b then p a ^ 2 else 0) =
      N * ∑ a, p a ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => sum_ite_blockCoord_eq' hℓ a _
  have e2 : (∑ a : ZMod ℓ, ∑ b : ZMod ℓ, if blockCoord N m a = blockCoord N m b then q b ^ 2 else 0) =
      N * ∑ b, q b ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [← sum_ite_blockCoord_eq' hℓ b]
      exact Finset.sum_congr rfl fun a _ => if_congr eq_comm rfl rfl
  have e3 : (∑ a, ∑ b : ZMod ℓ, if blockCoord N m a = blockCoord N m b then p a * q b else 0) =
      ∑ β : ZMod m, blockSum1 N m p β * blockSum1 N m q β := by
    unfold blockSum1
    simp only [Finset.sum_filter, Finset.sum_mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : blockCoord N m a = blockCoord N m b
    · simp [h]
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun β _ => ?_
      by_cases e : blockCoord N m a = β
      · have : ¬ blockCoord N m b = β := fun e' => h (e.trans e'.symm)
        simp [this]
      · simp [e]
  rw [e1, e2, e3]

theorem blockSum1_sq_le [NeZero m] (hℓ : ℓ = N * m) (u : ZMod ℓ → ℝ) :
    ∑ β : ZMod m, blockSum1 N m u β ^ 2 ≤ N * ∑ a, u a ^ 2 := by
  have h1 : ∀ β : ZMod m, blockSum1 N m u β ^ 2 ≤
      N * ∑ a ∈ Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = β, u a ^ 2 := by
    intro β
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = β)
      (f := u)
    rw [card_blockCoord_fibre hℓ] at this
    exact this
  calc ∑ β : ZMod m, blockSum1 N m u β ^ 2
      ≤ ∑ β : ZMod m, N * ∑ a ∈ Finset.univ.filter fun a : ZMod ℓ => blockCoord N m a = β, u a ^ 2 :=
        Finset.sum_le_sum fun β _ => h1 β
    _ = N * ∑ a, u a ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_fiberwise Finset.univ (blockCoord N m) (fun a => u a ^ 2)

theorem blockSum1_sub (p q : ZMod ℓ → ℝ) (β : ZMod m) :
    blockSum1 N m (fun a => p a - q a) β = blockSum1 N m p β - blockSum1 N m q β := by
  unfold blockSum1; rw [Finset.sum_sub_distrib]

/-- The one-dimensional variance deficit `T(g) = N ∑ g² - ∑_β (∑_{a ∈ β} g)²`
satisfies `2 T(g) ≤ N³ ∑ innerGap`. -/
theorem oneD_T_le [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (g : ZMod ℓ → ℝ) :
    2 * (N * ∑ a, g a ^ 2 - ∑ β : ZMod m, blockSum1 N m g β ^ 2) ≤
      (N : ℝ) ^ 3 * ∑ c, innerGap N g c := by
  have h := pairSum_le_oneD hℓ hN g
  rw [pair_expand hℓ] at h
  have : ∑ β : ZMod m, blockSum1 N m g β * blockSum1 N m g β =
      ∑ β : ZMod m, blockSum1 N m g β ^ 2 := Finset.sum_congr rfl fun β _ => by ring
  rw [this] at h
  linarith

end OneD

section Cube

variable {ℓ N m : ℕ} [NeZero ℓ]

omit [NeZero ℓ] in
theorem sameBlock_symm {d : ℕ} {y y' : Fin d → ZMod ℓ} :
    SameBlock N m y y' ↔ SameBlock N m y' y :=
  ⟨fun h i => (h i).symm, fun h i => (h i).symm⟩

theorem sum_reorder4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (G : α → β → γ → δ → ℝ) :
    ∑ a, ∑ y, ∑ b, ∑ y', G a y b y' = ∑ y, ∑ y', ∑ a, ∑ b, G a y b y' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  calc ∑ a, ∑ b, ∑ y', G a y b y' = ∑ a, ∑ y', ∑ b, G a y b y' :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The block sums over the first coordinate. -/
noncomputable def wBlock (N m : ℕ) {d : ℕ} (f : (Fin (d + 1) → ZMod ℓ) → ℝ) (β : ZMod m)
    (y : Fin d → ZMod ℓ) : ℝ :=
  blockSum1 N m (fun a => f (Fin.cons a y)) β

theorem sum_innerEnergy_wBlock_le {d : ℕ} [NeZero m] (hℓ : ℓ = N * m)
    (f : (Fin (d + 1) → ZMod ℓ) → ℝ) :
    ∑ β : ZMod m, innerEnergy N (wBlock N m f β) ≤
      N * ∑ a : ZMod ℓ, innerEnergy N (fun y : Fin d → ZMod ℓ => f (Fin.cons a y)) := by
  unfold innerEnergy
  have e1 : ∀ (H : ZMod m → (Fin d → ZMod ℓ) → Fin d → ℝ),
      ∑ β, ∑ x, ∑ μ, H β x μ = ∑ x, ∑ μ, ∑ β, H β x μ := by
    intro H
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have e2 : ∀ (H : ZMod ℓ → (Fin d → ZMod ℓ) → Fin d → ℝ),
      ∑ a, ∑ x, ∑ μ, H a x μ = ∑ x, ∑ μ, ∑ a, H a x μ := by
    intro H
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  by_cases h : (x μ).val % N + 1 < N
  · simp only [h, ↓reduceIte]
    have := blockSum1_sq_le (N := N) (m := m) hℓ
      (fun a => f (Fin.cons a (Function.update x μ (x μ + 1))) - f (Fin.cons a x))
    simp only [wBlock, ← blockSum1_sub]
    exact this
  · simp [h]


theorem pairSum_succ_sharp {d : ℕ} [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (H : ∀ f : (Fin d → ZMod ℓ) → ℝ, pairSum N m f ≤ (N : ℝ) ^ (d + 2) * innerEnergy N f)
    (f : (Fin (d + 1) → ZMod ℓ) → ℝ) :
    pairSum N m f ≤ (N : ℝ) ^ (d + 1 + 2) * innerEnergy N f := by
  set T : (Fin d → ZMod ℓ) → ℝ := fun y =>
    N * ∑ a, f (Fin.cons a y) ^ 2 - ∑ β : ZMod m, wBlock N m f β y ^ 2 with hT
  set E0 : (Fin d → ZMod ℓ) → ℝ := fun y =>
    ∑ c, innerGap N (fun a => f (Fin.cons a y)) c with hE0
  have hTle : ∀ y, 2 * T y ≤ (N : ℝ) ^ 3 * E0 y := fun y =>
    oneD_T_le hℓ hN (fun a => f (Fin.cons a y))
  -- pointwise identity
  have hR : ∀ y y' : Fin d → ZMod ℓ,
      (∑ a : ZMod ℓ, ∑ b : ZMod ℓ, if blockCoord N m a = blockCoord N m b then
          (f (Fin.cons a y) - f (Fin.cons b y')) ^ 2 else 0) =
        T y + T y' + ∑ β : ZMod m, (wBlock N m f β y - wBlock N m f β y') ^ 2 := by
    intro y y'
    rw [pair_expand hℓ (fun a => f (Fin.cons a y)) (fun b => f (Fin.cons b y'))]
    have : ∀ β : ZMod m, (wBlock N m f β y - wBlock N m f β y') ^ 2 =
        wBlock N m f β y ^ 2 + wBlock N m f β y' ^ 2 - 2 * (wBlock N m f β y * wBlock N m f β y') := by
      intro β; ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hT]
    simp only [wBlock]
    ring
  have hS : pairSum N m f = ∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
      ((if SameBlock N m y y' then T y else 0) + (if SameBlock N m y y' then T y' else 0) +
      ∑ β : ZMod m, (if SameBlock N m y y' then
        (wBlock N m f β y - wBlock N m f β y') ^ 2 else 0)) := by
    unfold pairSum
    simp only [sum_pi_succ]
    rw [sum_reorder4]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    have h1 : ∀ a b : ZMod ℓ, (if SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y')
        then (f (Fin.cons a y) - f (Fin.cons b y')) ^ 2 else 0) =
        if SameBlock N m y y' then (if blockCoord N m a = blockCoord N m b then
          (f (Fin.cons a y) - f (Fin.cons b y')) ^ 2 else 0) else 0 := by
      intro a b
      by_cases h1 : blockCoord N m a = blockCoord N m b
      · by_cases h2 : SameBlock N m y y'
        · have hc := (sameBlock_cons (N := N) (m := m) a b y y').2 ⟨h1, h2⟩
          simp only [hc, h1, h2, ↓reduceIte]
        · have hc : ¬ SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') :=
            fun h => h2 ((sameBlock_cons a b y y').1 h).2
          simp only [hc, h2, ↓reduceIte]
      · have hc : ¬ SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') :=
          fun h => h1 ((sameBlock_cons a b y y').1 h).1
        simp only [hc, h1, ↓reduceIte, ite_self]
    simp only [h1]
    by_cases h2 : SameBlock N m y y'
    · simp only [h2, ↓reduceIte]
      exact hR y y'
    · simp [h2]
  have A1 : (∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ, if SameBlock N m y y' then T y else 0) =
      (N : ℝ) ^ d * ∑ y, T y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => sum_ite_sameBlock hℓ y (T y)
  have A2 : (∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ, if SameBlock N m y y' then T y' else 0) =
      (N : ℝ) ^ d * ∑ y, T y := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [← sum_ite_sameBlock hℓ y' (T y')]
    exact Finset.sum_congr rfl fun y _ => if_congr sameBlock_symm rfl rfl
  have A3 : (∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ, ∑ β : ZMod m,
      if SameBlock N m y y' then (wBlock N m f β y - wBlock N m f β y') ^ 2 else 0) =
      ∑ β : ZMod m, pairSum N m (wBlock N m f β) := by
    unfold pairSum
    calc _ = ∑ y : Fin d → ZMod ℓ, ∑ β : ZMod m, ∑ y' : Fin d → ZMod ℓ,
          if SameBlock N m y y' then (wBlock N m f β y - wBlock N m f β y') ^ 2 else 0 :=
          Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hT1 : ∑ y, T y ≤ (N : ℝ) ^ 3 / 2 * ∑ y, E0 y := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => by linarith [hTle y]
  have hW := sum_innerEnergy_wBlock_le hℓ f
  have hA3 : ∑ β : ZMod m, pairSum N m (wBlock N m f β) ≤
      (N : ℝ) ^ (d + 2) * (N * ∑ a : ZMod ℓ, innerEnergy N (fun y : Fin d → ZMod ℓ => f (Fin.cons a y))) := by
    calc _ ≤ ∑ β : ZMod m, (N : ℝ) ^ (d + 2) * innerEnergy N (wBlock N m f β) :=
          Finset.sum_le_sum fun β _ => H _
      _ = (N : ℝ) ^ (d + 2) * ∑ β : ZMod m, innerEnergy N (wBlock N m f β) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (by positivity)
  rw [hS]
  simp only [Finset.sum_add_distrib]
  rw [A1, A2, A3, innerEnergy_succ]
  have hE0' : ∑ y, E0 y = ∑ y : Fin d → ZMod ℓ, ∑ c : ZMod ℓ,
      innerGap N (fun a => f (Fin.cons a y)) c := rfl
  have hp : (N : ℝ) ^ (d + 1 + 2) = (N : ℝ) ^ d * (N : ℝ) ^ 3 := by ring
  have hp2 : (N : ℝ) ^ (d + 2) * N = (N : ℝ) ^ d * (N : ℝ) ^ 3 := by ring
  have hNd : 0 ≤ (N : ℝ) ^ d := by positivity
  have h3 := mul_le_mul_of_nonneg_left hT1 hNd
  rw [← hE0', hp]
  have hA3' : ∑ β : ZMod m, pairSum N m (wBlock N m f β) ≤
      (N : ℝ) ^ d * (N : ℝ) ^ 3 * ∑ a : ZMod ℓ, innerEnergy N (fun y : Fin d → ZMod ℓ => f (Fin.cons a y)) :=
    hA3.trans (le_of_eq (by rw [← mul_assoc, hp2]))
  nlinarith [hA3', h3]


/-- Sharp pair-sum bound, `d`-free: `∑_{x ~ x'} (f x - f x')² ≤ N^{d+2} E_N(f)`. -/
theorem pairSum_le_sharp [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) :
    ∀ (d : ℕ) (f : (Fin d → ZMod ℓ) → ℝ),
      pairSum N m f ≤ (N : ℝ) ^ (d + 2) * innerEnergy N f
  | 0, f => by rw [pairSum_zero]; simp [innerEnergy]
  | d + 1, f => pairSum_succ_sharp hℓ hN (pairSum_le_sharp hℓ hN d) f

section Torus

variable {d : ℕ} [NeZero m]

/-- **Sharp block Poincaré inequality** (`d`-free): the variance of `φ` over the blocks of side
`N` is at most `N² / 2` times the energy of the bonds inside blocks. -/
theorem blockPoincare_sharp (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    ∑ x, (φ x - blockProjection N m φ x) ^ 2 ≤ (1 / 2) * (N : ℝ) ^ 2 * innerEnergy N φ := by
  have h := pairSum_le_sharp hℓ hN d φ
  rw [pairSum_eq hℓ hN] at h
  have e : (N : ℝ) ^ (d + 2) * innerEnergy N φ =
      2 * (N : ℝ) ^ d * ((1 / 2) * (N : ℝ) ^ 2 * innerEnergy N φ) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h (by positivity)

/-- **Sharp block Poincaré inequality, full-energy form.** -/
theorem blockPoincare_latticeEnergy_sharp (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    ∑ x, (φ x - blockProjection N m φ x) ^ 2 ≤ (1 / 2) * (N : ℝ) ^ 2 * latticeEnergy φ :=
  (blockPoincare_sharp hℓ hN φ).trans
    (mul_le_mul_of_nonneg_left (innerEnergy_le_latticeEnergy φ) (by positivity))

end Torus

end Cube

end Balaban
