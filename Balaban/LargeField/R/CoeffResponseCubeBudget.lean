/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseCubeDecomp
public import Balaban.LargeField.R.CoeffResponseBudgetFlow
public import Balaban.SmallField.Xi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The per-cube budgets on layer blocks

A cell of the decomposition of `CoeffResponseCubeDecomp` is a layer block `Δ_ℓ(x)` with `L^{ℓ d}`
sites in the layer `ℓ`.  Its three site sums of `hcoef_of_response_flow` are therefore
`|a(ℓ)| L^{ℓ(d-2)}`, `L^{ℓ(d-2)}` and `L^{ℓ d} |ν|`, and, for the real flow, the budgets with
`wt = 1` and `A = cs.beta(j+1) ε_{j+1}²` hold with explicit constants (`ℓ ≤ j + 1 ≤ k`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.SmallField Finset

section Cell

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- A site function that depends only on the layer sums over a layer block to the number of
sites times its value on the layer. -/
theorem Region.layerBlock_sum_layer (X : Region G) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ X.sites)
    (f : ℕ → ℝ) :
    ∑ y ∈ G.blk (G.layerIndex x) x, f (G.layerIndex y) =
      ((L : ℝ) ^ G.layerIndex x) ^ d * f (G.layerIndex x) := by
  rw [Finset.sum_congr rfl (g := fun _ => f (G.layerIndex x))
    (fun y hy => by rw [X.layerBlock_layerIndex hx hy]), Finset.sum_const, nsmul_eq_mul,
    X.layerBlock_card hx]
  push_cast
  rfl

/-- The coefficient sum over a layer block. -/
theorem Region.layerBlock_sum_levelCoeff (X : Region G) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) (a : ℕ → ℝ) :
    ∑ y ∈ G.blk (G.layerIndex x) x, ‖levelCoeff G a y‖ =
      ((L : ℝ) ^ G.layerIndex x) ^ d * (|a (G.layerIndex x)| / ((L : ℝ) ^ G.layerIndex x) ^ 2) := by
  have hpos : ∀ n : ℕ, 0 < ((L : ℝ) ^ n) ^ 2 := fun n => by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have := X.layerBlock_sum_layer hx (fun n => |a n| / ((L : ℝ) ^ n) ^ 2)
  rw [← this]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold levelCoeff
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (hpos _)]

/-- The spacing sum over a layer block. -/
theorem Region.layerBlock_sum_spacing (X : Region G) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) :
    ∑ y ∈ G.blk (G.layerIndex x) x, ((G.spacing y) ^ 2)⁻¹ =
      ((L : ℝ) ^ G.layerIndex x) ^ d * ((((L : ℝ) ^ G.layerIndex x) ^ 2)⁻¹) := by
  have := X.layerBlock_sum_layer hx (fun n => ((((L : ℝ) ^ n)) ^ 2)⁻¹)
  rw [← this]
  rfl

/-- The mass sum over a layer block. -/
theorem Region.layerBlock_sum_const (X : Region G) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) (c : ℝ) :
    ∑ _y ∈ G.blk (G.layerIndex x) x, c = ((L : ℝ) ^ G.layerIndex x) ^ d * c := by
  have := X.layerBlock_sum_layer hx (fun _ => c)
  exact this

end Cell

section Real

variable {d L : ℕ} [NeZero L]

theorem pow_layer_mul (hd : 2 ≤ d) (ℓ : ℕ) (c : ℝ) :
    ((L : ℝ) ^ ℓ) ^ d * (c / ((L : ℝ) ^ ℓ) ^ 2) = c * (L : ℝ) ^ (ℓ * (d - 2)) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← pow_mul, ← pow_mul, show ℓ * (e + 2) = ℓ * e + ℓ * 2 by ring, pow_add]
  field_simp

theorem one_le_pow_L (n : ℕ) : (1 : ℝ) ≤ (L : ℝ) ^ n :=
  one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L))

theorem pow_L_mono {m n : ℕ} (h : m ≤ n) : (L : ℝ) ^ m ≤ (L : ℝ) ^ n :=
  pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)) h

/-- **The core inequality.**  With `β̂_k = β g_k`, `A = β L^{(d-2)(j+1)} g_{j+1} ε²` and
`ε² ≥ ε₀² > 0`, a layer `ℓ ≤ j + 1`: `β̂_k X L^{ℓ(d-2)} ≤ (e^{2η} X / ε₀²) A`. -/
theorem cube_budget_core {β η gk gj X E2 Elo : ℝ} {ℓ j : ℕ} (hβ : 0 < β)
    (hgk : gk ≤ Real.exp η) (hgj : Real.exp (-η) ≤ gj) (hX : 0 ≤ X) (hElo : 0 < Elo)
    (hE : Elo ≤ E2) (hℓ : ℓ ≤ j + 1) :
    β * gk * (X * (L : ℝ) ^ (ℓ * (d - 2))) ≤
      (Real.exp (2 * η) * X / Elo) *
        (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E2) := by
  have hP : (L : ℝ) ^ (ℓ * (d - 2)) ≤ (L : ℝ) ^ ((d - 2) * (j + 1)) := by
    apply pow_L_mono
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hℓ
  have hP0 : 0 < (L : ℝ) ^ ((d - 2) * (j + 1)) := lt_of_lt_of_le one_pos (one_le_pow_L _)
  have e2 : Real.exp (2 * η) * Real.exp (-η) = Real.exp η := by
    rw [← Real.exp_add]; ring_nf
  have hgk0 : gk ≤ Real.exp η := hgk
  have hgjE : Real.exp (-η) * Elo ≤ gj * E2 :=
    mul_le_mul hgj hE hElo.le ((Real.exp_pos _).le.trans hgj)
  set P := (L : ℝ) ^ ((d - 2) * (j + 1))
  have hEX : 0 ≤ Real.exp (2 * η) * X / Elo := by positivity
  calc β * gk * (X * (L : ℝ) ^ (ℓ * (d - 2))) ≤ β * Real.exp η * (X * P) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hgk0 hβ.le) (mul_le_mul_of_nonneg_left hP hX)
          (by positivity) (by positivity)
    _ = (Real.exp (2 * η) * X / Elo) * (β * P * (Real.exp (-η) * Elo)) := by
        rw [← e2]; field_simp
    _ ≤ (Real.exp (2 * η) * X / Elo) * (β * P * (gj * E2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgjE (by positivity)) hEX
    _ = _ := by ring

end Real

end Balaban.LargeField.ActionConv
