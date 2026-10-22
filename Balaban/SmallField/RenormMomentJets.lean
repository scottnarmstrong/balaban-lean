/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.Jet
public import Balaban.Fluctuation.RenormIdentity

/-!
# Jets of the pairings of `C₁`

The pairings `blockPair`, `bondPair`, `massPair` of `renormC1` are finite sums of products of the
coordinates of the fields; along a curve of fields with coordinate jets they have the jets of the
bilinear (resp. quadratic) form (`isJet_blockPair`, `isJet_bondPair`, `isJet_massPair`), and the
block average is linear (`isJet_blockAvg`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Flow Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- A curve `s ↦ φ s` of fields on `Ω₁` has the coordinate jets `(φ0, φ1, φ2)`. -/
def VJet (φ : ℂ → G.Ω 1 × Fin N → ℂ) (φ0 φ1 φ2 : G.Ω 1 × Fin N → ℂ) : Prop :=
  ∀ q, IsJet (fun s => φ s q) (φ0 q) (φ1 q) (φ2 q)

theorem vjet_svec {φ : ℂ → G.Ω 1 × Fin N → ℂ} {φ0 φ1 φ2 : G.Ω 1 × Fin N → ℂ}
    (h : VJet φ φ0 φ1 φ2) (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    IsJet (fun s => svec G (φ s) y i) (svec G φ0 y i) (svec G φ1 y i) (svec G φ2 y i) := by
  classical
  unfold svec zeroExt
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, ↓reduceDIte]
    exact h (⟨y, hy⟩, i)
  · simp only [hy, ↓reduceDIte]
    exact isJet_const 0

theorem vjet_blockAvg {φ : ℂ → G.Ω 1 × Fin N → ℂ} {φ0 φ1 φ2 : G.Ω 1 × Fin N → ℂ}
    (h : VJet φ φ0 φ1 φ2) (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    IsJet (fun s => blockAvg G (φ s) x i) (blockAvg G φ0 x i) (blockAvg G φ1 x i)
      (blockAvg G φ2 x i) := by
  unfold blockAvg
  have := IsJet.const_mul ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ))
    (IsJet.sum (G.blk (G.layerIndex x) x) fun y _ => vjet_svec h y i)
  simpa [Finset.mul_sum] using this

theorem isJet_blockPair (a : ℕ → ℝ)
    {A B : ℂ → Torus d (N₀ * L ^ K) → Fin N → ℂ}
    {A0 A1 A2 B0 B1 B2 : Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hA : ∀ x i, IsJet (fun s => A s x i) (A0 x i) (A1 x i) (A2 x i))
    (hB : ∀ x i, IsJet (fun s => B s x i) (B0 x i) (B1 x i) (B2 x i)) :
    IsJet (fun s => blockPair G a (A s) (B s)) (blockPair G a A0 B0)
      (blockPair G a A1 B0 + blockPair G a A0 B1)
      (blockPair G a A2 B0 + 2 * blockPair G a A1 B1 + blockPair G a A0 B2) := by
  unfold blockPair
  have h := IsJet.sum (Finset.univ : Finset (G.Ω 1)) fun x _ =>
    IsJet.const_mul ((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ)
      (IsJet.sum (Finset.univ : Finset (Fin N)) fun i _ => (hA x i).mul (hB x i))
  refine h.of_eq rfl ?_ ?_ <;>
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

theorem isJet_barField {Ψ : ℂ → Torus d (N₀ * L ^ K) → Fin N → ℂ}
    {Ψ0 Ψ1 Ψ2 : Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hΨ : ∀ x i, IsJet (fun s => Ψ s x i) (Ψ0 x i) (Ψ1 x i) (Ψ2 x i))
    {φ : ℂ → G.Ω 1 × Fin N → ℂ} {φ0 φ1 φ2 : G.Ω 1 × Fin N → ℂ} (hφ : VJet φ φ0 φ1 φ2)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    IsJet (fun s => barField G (Ψ s) (φ s) x i) (barField G Ψ0 φ0 x i) (barField G Ψ1 φ1 x i)
      (barField G Ψ2 φ2 x i) := by
  classical
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceDIte]; exact hφ (⟨x, hx⟩, i)
  · simp only [hx, ↓reduceDIte]; exact hΨ x i

theorem isJet_bondPair {Ψ : ℂ → Torus d (N₀ * L ^ K) → Fin N → ℂ}
    {Ψ0 Ψ1 Ψ2 : Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hΨ : ∀ x i, IsJet (fun s => Ψ s x i) (Ψ0 x i) (Ψ1 x i) (Ψ2 x i))
    {φ : ℂ → G.Ω 1 × Fin N → ℂ} {φ0 φ1 φ2 : G.Ω 1 × Fin N → ℂ} (hφ : VJet φ φ0 φ1 φ2)
    (hflat : ∀ x μ i, barField G Ψ0 φ0 (x + Pi.single μ 1) i = barField G Ψ0 φ0 x i) :
    IsJet (fun s => bondPair G (Ψ s) (φ s)) 0 0 (2 * bondPair G Ψ1 φ1) := by
  classical
  unfold bondPair
  have hterm : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d),
      IsJet (fun s => if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
          ∑ i, (barField G (Ψ s) (φ s) (x + Pi.single μ 1) i - barField G (Ψ s) (φ s) x i) *
            (barField G (Ψ s) (φ s) (x + Pi.single μ 1) i - barField G (Ψ s) (φ s) x i) else 0)
        (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
          ∑ i, (barField G Ψ0 φ0 (x + Pi.single μ 1) i - barField G Ψ0 φ0 x i) *
            (barField G Ψ0 φ0 (x + Pi.single μ 1) i - barField G Ψ0 φ0 x i) else 0)
        (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
          ∑ i, ((barField G Ψ1 φ1 (x + Pi.single μ 1) i - barField G Ψ1 φ1 x i) *
            (barField G Ψ0 φ0 (x + Pi.single μ 1) i - barField G Ψ0 φ0 x i) +
            (barField G Ψ0 φ0 (x + Pi.single μ 1) i - barField G Ψ0 φ0 x i) *
            (barField G Ψ1 φ1 (x + Pi.single μ 1) i - barField G Ψ1 φ1 x i)) else 0)
        (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
          ∑ i, ((barField G Ψ2 φ2 (x + Pi.single μ 1) i - barField G Ψ2 φ2 x i) *
            (barField G Ψ0 φ0 (x + Pi.single μ 1) i - barField G Ψ0 φ0 x i) +
            2 * (barField G Ψ1 φ1 (x + Pi.single μ 1) i - barField G Ψ1 φ1 x i) *
            (barField G Ψ1 φ1 (x + Pi.single μ 1) i - barField G Ψ1 φ1 x i) +
            (barField G Ψ0 φ0 (x + Pi.single μ 1) i - barField G Ψ0 φ0 x i) *
            (barField G Ψ2 φ2 (x + Pi.single μ 1) i - barField G Ψ2 φ2 x i)) else 0) := by
    intro x μ
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      exact IsJet.sum (Finset.univ : Finset (Fin N)) fun i _ =>
        ((isJet_barField hΨ hφ (x + Pi.single μ 1) i).sub (isJet_barField hΨ hφ x i)).mul
          ((isJet_barField hΨ hφ (x + Pi.single μ 1) i).sub (isJet_barField hΨ hφ x i))
    · simp only [hc, ↓reduceIte]; exact isJet_const 0
  have h := IsJet.sum (Finset.univ : Finset (Torus d (N₀ * L ^ K))) fun x _ =>
    IsJet.sum (Finset.univ : Finset (Fin d)) fun μ _ => hterm x μ
  refine h.of_eq ?_ ?_ ?_
  · refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun μ _ => ?_
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      exact Finset.sum_eq_zero fun i _ => by rw [hflat]; ring
    · simp only [hc, ↓reduceIte]
  · refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun μ _ => ?_
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      exact Finset.sum_eq_zero fun i _ => by rw [hflat]; ring
    · simp only [hc, ↓reduceIte]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hflat]; ring
    · simp only [hc, ↓reduceIte]; ring

theorem isJet_massPair (h : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    {φ : ℂ → G.Ω 1 × Fin N → ℂ} {φ0 φ1 φ2 : G.Ω 1 × Fin N → ℂ} (hφ : VJet φ φ0 φ1 φ2)
    (h0 : ∀ x : G.Ω 1, ∀ i, φ0 (x, i) = h x i) :
    IsJet (fun s => massPair G h (φ s)) 0 0 (2 * massPair G (fun _ _ => 0) φ1) := by
  unfold massPair
  have hh := IsJet.sum (Finset.univ : Finset (G.Ω 1)) fun x _ =>
    IsJet.sum (Finset.univ : Finset (Fin N)) fun i _ =>
      ((hφ (x, i)).sub (isJet_const (h x i))).mul ((hφ (x, i)).sub (isJet_const (h x i)))
  refine hh.of_eq ?_ ?_ ?_
  · exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun i _ => by rw [h0]; ring
  · exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun i _ => by rw [h0]; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h0]; ring

end Balaban.Fluctuation
