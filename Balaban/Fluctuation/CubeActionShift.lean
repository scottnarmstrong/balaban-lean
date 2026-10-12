/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The first-order expansion bound for the cube action (FLUCTUATION.md §4.2, Step 3)

Expanding each block or kinetic square by `Q(v + w) - Q(v) = 2 B(v, w) + Q(w)` and the mass term
by `ν (φ - h) · w + ½ ν w · w` (Step 3): `cubeAction_shift_bound` bounds
`|A_Q(φ + τ) - A_Q(φ)|` by `½ |Q| (W + d + 1) N (2 E T + T²)` when the first-variation coefficients
`Ψ - Qφ`, `∂φ̄`, `ν (φ - h)` are at most `E` and the changes `Qτ`, `∂τ̄`, `τ` at most `T`
(componentwise, on the sites of the cube and the bonds based there).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Finset

section Bound

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem norm_sq_shift_le (u v : ℂ) : ‖(u + v) * (u + v) - u * u‖ ≤ 2 * ‖u‖ * ‖v‖ + ‖v‖ ^ 2 := by
  have : (u + v) * (u + v) - u * u = 2 * u * v + v * v := by ring
  rw [this]
  calc ‖2 * u * v + v * v‖ ≤ ‖2 * u * v‖ + ‖v * v‖ := norm_add_le _ _
    _ = 2 * ‖u‖ * ‖v‖ + ‖v‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_mul]; simp; ring

theorem sum_sq_shift_le (u v : Fin N → ℂ) {E T : ℝ} (hu : ∀ i, ‖u i‖ ≤ E) (hv : ∀ i, ‖v i‖ ≤ T)
    (hE : 0 ≤ E) (hT : 0 ≤ T) :
    ‖∑ i, ((u i + v i) * (u i + v i) - u i * u i)‖ ≤ N * (2 * E * T + T ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(u i + v i) * (u i + v i) - u i * u i‖ ≤ ∑ _i : Fin N, (2 * E * T + T ^ 2) := by
        refine Finset.sum_le_sum fun i _ => (norm_sq_shift_le _ _).trans ?_
        have := hu i; have := hv i
        have h0 := norm_nonneg (u i); have h1 := norm_nonneg (v i)
        nlinarith [mul_le_mul (hu i) (hv i) h1 hE]
    _ = N * (2 * E * T + T ^ 2) := by simp; ring

theorem card_filter_subtype_le (Q : Finset (Torus d (N₀ * L ^ k))) :
    (Finset.univ.filter fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ Q).card ≤ Q.card := by
  refine Finset.card_le_card_of_injOn (fun x => (x : Torus d (N₀ * L ^ k))) ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.1 hx).2
  · intro x _ y _ h
    exact Subtype.ext h

theorem norm_sum_ite_subtype_le (Q : Finset (Torus d (N₀ * L ^ k))) (f : G.Ω 1 → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ‖f x‖ ≤ c) :
    ‖∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then f x else 0)‖ ≤ Q.card * c := by
  classical
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x : G.Ω 1, ‖(if (x : Torus d (N₀ * L ^ k)) ∈ Q then f x else 0)‖
      ≤ ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then c else 0) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Q
        · simp only [hx, ↓reduceIte]; exact h x hx
        · simp [hx]
    _ = (Finset.univ.filter fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ Q).card * c := by
        rw [← Finset.sum_filter]; simp
    _ ≤ Q.card * c := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_subtype_le Q) hc

theorem norm_sum_ite_le (Q : Finset (Torus d (N₀ * L ^ k))) (f : Torus d (N₀ * L ^ k) → ℂ)
    {c : ℝ} (h : ∀ x ∈ Q, ‖f x‖ ≤ c) :
    ‖∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then f x else 0)‖ ≤ Q.card * c := by
  classical
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => x ∈ Q) = Q := by
    ext x; simp
  rw [this]
  calc ‖∑ x ∈ Q, f x‖ ≤ ∑ x ∈ Q, ‖f x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Q, c := Finset.sum_le_sum h
    _ = Q.card * c := by simp



omit [NeZero L] in
theorem sum_ite_sub {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (f g : α → ℂ) :
    ∑ x, (if p x then f x else 0) - ∑ x, (if p x then g x else 0) =
      ∑ x, (if p x then f x - g x else 0) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x <;> simp [h]

open Classical in
theorem cubeBlock_shift_bound (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) {W E T : ℝ}
    (hW : ∀ x : G.Ω 1, ‖((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ)‖ ≤ W)
    (hW0 : 0 ≤ W) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (HB : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i,
      ‖Ψ x i - blockAvg G φ x i‖ ≤ E)
    (TB : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ‖blockAvg G τ x i‖ ≤ T) :
    ‖∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ (φ + τ) x else 0) -
      ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ φ x else 0)‖ ≤
      Q.card * (W * (N * (2 * E * T + T ^ 2))) := by
  rw [sum_ite_sub]
  refine norm_sum_ite_subtype_le Q _ (by positivity) fun x hx => ?_
  have hsum : cubeBlockTerm G a Ψ (φ + τ) x - cubeBlockTerm G a Ψ φ x =
      ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ∑ i, (((Ψ x i - blockAvg G φ x i) + (-blockAvg G τ x i)) *
          ((Ψ x i - blockAvg G φ x i) + (-blockAvg G τ x i)) -
          (Ψ x i - blockAvg G φ x i) * (Ψ x i - blockAvg G φ x i)) := by
    unfold cubeBlockTerm
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [blockAvg_add]; ring_nf
  rw [hsum, norm_mul]
  refine mul_le_mul (hW x) ?_ (norm_nonneg _) hW0
  exact sum_sq_shift_le _ _ (fun i => HB x hx i) (fun i => by rw [norm_neg]; exact TB x hx i) hE hT


open Classical in
theorem cubeBond_shift_bound (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) {E T : ℝ}
    (hE : 0 ≤ E) (hT : 0 ≤ T)
    (HG : ∀ x ∈ Q, ∀ μ : Fin d, (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ≤ E)
    (TG : ∀ x ∈ Q, ∀ μ : Fin d, (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖svec G τ (x + Pi.single μ 1) i - svec G τ x i‖ ≤ T) :
    ‖∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then cubeBondTerm G Ψ (φ + τ) x else 0) -
      ∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then cubeBondTerm G Ψ φ x else 0)‖ ≤
      Q.card * (d * (N * (2 * E * T + T ^ 2))) := by
  rw [sum_ite_sub]
  have hP0 : 0 ≤ (N : ℝ) * (2 * E * T + T ^ 2) := by positivity
  refine norm_sum_ite_le Q _ fun x hx => ?_
  have hsum : cubeBondTerm G Ψ (φ + τ) x - cubeBondTerm G Ψ φ x =
      ∑ μ : Fin d, (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (((barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) +
            (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) *
          ((barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) +
            (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) -
          (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
            (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i)) else 0) := by
    unfold cubeBondTerm
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hμ : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hμ, ↓reduceIte]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [barField_add, barField_add]; ring_nf
    · simp [hμ]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ μ : Fin d, ‖(if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (((barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) +
            (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) *
          ((barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) +
            (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) -
          (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
            (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i)) else 0)‖
      ≤ ∑ _μ : Fin d, ((N : ℝ) * (2 * E * T + T ^ 2)) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        by_cases hμ : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
        · simp only [hμ, ↓reduceIte]
          exact sum_sq_shift_le _ _ (fun i => HG x hx μ hμ i) (fun i => TG x hx μ hμ i) hE hT
        · simp [hμ, hP0]
    _ = d * (N * (2 * E * T + T ^ 2)) := by simp

open Classical in
theorem cubeMass_shift_bound (Q : Finset (Torus d (N₀ * L ^ k)))
    (h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) {E T : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (HF : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ν * ‖φ (x, i) - h x i‖ ≤ E)
    (TF : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ‖τ (x, i)‖ ≤ T) :
    ‖(ν : ℂ) * (∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h (φ + τ) x else 0) -
      ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h φ x else 0))‖ ≤
      Q.card * (N * (2 * E * T + T ^ 2)) := by
  rw [sum_ite_sub]
  have hP0 : 0 ≤ (N : ℝ) * (2 * E * T + T ^ 2) := by positivity
  have hmul : (ν : ℂ) * ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then
      cubeMassTerm G h (φ + τ) x - cubeMassTerm G h φ x else 0) =
      ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then
        (ν : ℂ) * (cubeMassTerm G h (φ + τ) x - cubeMassTerm G h φ x) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Q <;> simp [hx]
  rw [hmul]
  refine norm_sum_ite_subtype_le (G := G) Q (fun x => (ν : ℂ) * (cubeMassTerm G h (φ + τ) x - cubeMassTerm G h φ x))
    hP0 (fun x hx => ?_)
  · have hsum : cubeMassTerm G h (φ + τ) x - cubeMassTerm G h φ x =
        ∑ i, (((φ (x, i) - h x i) + τ (x, i)) * ((φ (x, i) - h x i) + τ (x, i)) -
          (φ (x, i) - h x i) * (φ (x, i) - h x i)) := by
      unfold cubeMassTerm
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring_nf
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hν0]
    calc ν * ‖∑ i, (((φ (x, i) - h x i) + τ (x, i)) * ((φ (x, i) - h x i) + τ (x, i)) -
          (φ (x, i) - h x i) * (φ (x, i) - h x i))‖
        ≤ ν * ∑ i, ‖((φ (x, i) - h x i) + τ (x, i)) * ((φ (x, i) - h x i) + τ (x, i)) -
          (φ (x, i) - h x i) * (φ (x, i) - h x i)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hν0
      _ ≤ ν * ∑ i, (2 * ‖φ (x, i) - h x i‖ * T + T ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hν0
          refine (norm_sq_shift_le _ _).trans ?_
          have := TF x hx i
          have h0 := norm_nonneg (φ (x, i) - h x i)
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h0),
            pow_le_pow_left₀ (norm_nonneg _) this 2]
      _ ≤ ∑ _i : Fin N, (2 * E * T + T ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := HF x hx i
          nlinarith [mul_le_mul_of_nonneg_right h1 hT, mul_nonneg hν0 (sq_nonneg T)]
      _ = N * (2 * E * T + T ^ 2) := by simp; ring


open Classical in
/-- **The first-order expansion bound for the cube action.**  Let the fields `Ψ - Qφ`, `∂ φ̄`,
`ν (φ - h)` have components at most `E` on the sites of `Q` (resp. on the bonds based at `Q`), and
the corresponding changes `Q τ`, `∂ τ̄`, `τ` components at most `T`.  Then
`|A_Q(φ + τ) - A_Q(φ)| ≤ ½ |Q| (W + d + 1) N (2 E T + T²)`, where `W` bounds the weights
`a_n L^{-2n}` and `0 ≤ ν ≤ 1`. -/
theorem cubeAction_shift_bound (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) {W E T : ℝ}
    (hW : ∀ x : G.Ω 1, ‖((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ)‖ ≤ W)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hW0 : 0 ≤ W) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (HB : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i,
      ‖Ψ x i - blockAvg G φ x i‖ ≤ E)
    (HG : ∀ x ∈ Q, ∀ μ : Fin d, (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ≤ E)
    (HF : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ν * ‖φ (x, i) - h x i‖ ≤ E)
    (TB : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ‖blockAvg G τ x i‖ ≤ T)
    (TG : ∀ x ∈ Q, ∀ μ : Fin d, (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖svec G τ (x + Pi.single μ 1) i - svec G τ x i‖ ≤ T)
    (TF : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ‖τ (x, i)‖ ≤ T) :
    ‖cubeActionR G a ν Q Ψ h (φ + τ) - cubeActionR G a ν Q Ψ h φ‖ ≤
      (1 / 2) * (Q.card * ((W + d + 1) * (N * (2 * E * T + T ^ 2)))) := by
  have h1 := cubeBlock_shift_bound Q Ψ φ τ hW hW0 hE hT HB TB
  have h2 := cubeBond_shift_bound Q Ψ φ τ hE hT HG TG
  have h3 := cubeMass_shift_bound Q h φ τ hν0 hν1 hE hT HF TF
  have hdiff : cubeActionR G a ν Q Ψ h (φ + τ) - cubeActionR G a ν Q Ψ h φ =
      (1 / 2) * (∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ (φ + τ) x else 0) -
        ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ φ x else 0)) +
      (1 / 2) * (∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then cubeBondTerm G Ψ (φ + τ) x else 0) -
        ∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then cubeBondTerm G Ψ φ x else 0)) +
      (1 / 2) * ((ν : ℂ) * (∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h (φ + τ) x else 0) -
        ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h φ x else 0))) := by
    unfold cubeActionR; ring
  rw [hdiff]
  refine (norm_add₃_le).trans ?_
  have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  simp only [norm_mul (1 / 2 : ℂ), e]
  nlinarith [h1, h2, h3]

end Bound

end Balaban.Fluctuation
