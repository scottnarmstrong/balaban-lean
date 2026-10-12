/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassChangeChord
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-!
# The wall estimate of the regional mass change (WALL-COLLAR (1.2)-(1.3))

* `vnorm`: the Euclidean norm of a vector of `ℂ^N`;
* `starBond_le`: the bondwise implication (1.2): if `|∂_b φ̄| ≤ r_b` and `|w(x)| ≤ R_x` at the
  endpoints, the flux of the bond is at most `r_b (R_{b₋} + R_{b₊})/2`;
* `starPair_norm_le`: the sum over the crossing bonds;
* `massChange_wall_bound_of_bounds`: the conditional estimate (1.3), with the open inputs of the note as
  hypotheses: the gradient bound `hgrad`, the mass response `hresp` and the Hessian bound `hHess`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The Euclidean norm of a vector of `ℂ^N`. -/
noncomputable def vnorm {N : ℕ} (v : Fin N → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖

theorem vnorm_nonneg {N : ℕ} (u : Fin N → ℂ) : 0 ≤ vnorm u := norm_nonneg _

theorem vnorm_add {N : ℕ} (u v : Fin N → ℂ) : vnorm (fun i => u i + v i) ≤ vnorm u + vnorm v := by
  unfold vnorm
  have : (WithLp.toLp 2 (fun i => u i + v i) : EuclideanSpace ℂ (Fin N)) =
      WithLp.toLp 2 u + WithLp.toLp 2 v := rfl
  rw [this]; exact norm_add_le _ _

theorem vnorm_smul {N : ℕ} (c : ℂ) (u : Fin N → ℂ) :
    vnorm (fun i => c * u i) = ‖c‖ * vnorm u := by
  unfold vnorm
  have : (WithLp.toLp 2 (fun i => c * u i) : EuclideanSpace ℂ (Fin N)) =
      c • WithLp.toLp 2 u := rfl
  rw [this, norm_smul]

/-- Cauchy-Schwarz for the bilinear sum. -/
theorem norm_sum_mul_le {N : ℕ} (p q : Fin N → ℂ) :
    ‖∑ i, p i * q i‖ ≤ vnorm p * vnorm q := by
  unfold vnorm
  have h : ∑ i, p i * q i = inner ℂ
      (WithLp.toLp 2 (fun i => starRingEnd ℂ (p i)) : EuclideanSpace ℂ (Fin N))
      (WithLp.toLp 2 q) := by
    simp [PiLp.inner_apply, mul_comm]
  have h2 : ‖(WithLp.toLp 2 (fun i => starRingEnd ℂ (p i)) : EuclideanSpace ℂ (Fin N))‖ =
      ‖(WithLp.toLp 2 p : EuclideanSpace ℂ (Fin N))‖ := by
    simp [EuclideanSpace.norm_eq]
  rw [h, ← h2]
  exact norm_inner_le_norm _ _

/-- **The bondwise flux bound** (WALL-COLLAR (1.2)): for one crossing bond with endpoint values
`w x`, `w y` and oriented derivative `q`, with `|w x| ≤ Rx`, `|w y| ≤ Ry`, `|q| ≤ r`. -/
theorem starBond_le {N : ℕ} (wx wy q : Fin N → ℂ) {Rx Ry r : ℝ} (hx : vnorm wx ≤ Rx)
    (hy : vnorm wy ≤ Ry) (hq : vnorm q ≤ r) :
    ‖∑ i, ((wx i + wy i) / 2) * q i‖ ≤ r * ((Rx + Ry) / 2) := by
  have e : (fun i => (wx i + wy i) / 2) = fun i => (1 / 2 : ℂ) * (wx i + wy i) := by
    funext i; ring
  refine (norm_sum_mul_le _ _).trans ?_
  rw [e, vnorm_smul]
  have h1 := vnorm_add wx wy
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  have h0 := vnorm_nonneg q
  have h3 : vnorm (fun i => wx i + wy i) ≤ Rx + Ry := h1.trans (add_le_add hx hy)
  have h4 : 1 / 2 * vnorm (fun i => wx i + wy i) ≤ (Rx + Ry) / 2 := by linarith
  calc 1 / 2 * vnorm (fun i => wx i + wy i) * vnorm q
      ≤ (Rx + Ry) / 2 * vnorm q := mul_le_mul_of_nonneg_right h4 h0
    _ ≤ (Rx + Ry) / 2 * r := mul_le_mul_of_nonneg_left hq
        (by have := vnorm_nonneg wx; have := vnorm_nonneg wy; linarith)
    _ = r * ((Rx + Ry) / 2) := by ring

/-- **The flux over the crossing bonds**: `|S_D(w, f)| ≤ Σ_{b ∈ st(D)} r_b (R_{b₋} + R_{b₊})/2`,
given `|∂_b^{out} f| ≤ r_b` on crossing bonds and `|w(x)| ≤ R_x`. -/
theorem starPair_norm_le (D : Region G) (w f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (r : Torus d (N₀ * L ^ K) × Fin d → ℝ) (R : Torus d (N₀ * L ^ K) → ℝ)
    (hr : ∀ b ∈ D.crossing, vnorm (D.outwardDeriv f b) ≤ r b) (hR : ∀ x, vnorm (w x) ≤ R x) :
    ‖D.starPair w f‖ ≤
      ∑ b ∈ D.crossing, r b * ((R b.1 + R (b.1 + Pi.single b.2 1)) / 2) := by
  unfold Region.starPair
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  exact starBond_le _ _ _ (hR _) (hR _) (hr b hb)

/-- **The conditional wall estimate** (WALL-COLLAR (1.3)).  Premises: `φᵐ` solves the complete
Euler-Lagrange system and `φ⁰` is hard-spin; the open inputs of the note, for the actual window,
are `hgrad` (the gradient bound `|∂_b φ̄ᵐ| ≤ r_b` on crossing bonds), `hresp` (the mass response
`|w(x)| ≤ K_m B_h m` for `w = φ̄⁰ - φ̄ᵐ`) and `hHess` (the Hessian bound
`|⟨w,(H+α)w⟩| ≤ C_H n (K_m B_h m)²`, `n = |Y|`).  Conclusion, for `β ≥ 0`:
`β |ΔA_Y| ≤ ½ C_H K_m² B_h² β m² n + K_m B_h β m Σ_b r_b`. 

The plain name `massChange_wall_bound` is reserved for the version in which the response and Hessian
bounds are proved for the actual window. -/
theorem massChange_wall_bound_of_bounds (D : Region G) {a : ℕ → ℝ} {ν : ℝ} {Dat : BgData G N}
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hEL : IsEL G a ν Dat φm α)
    (hφ0 : ∀ x : G.Ω 1, ∑ i, φ0 (x, i) * φ0 (x, i) = 1)
    {β m Km Bh CH n : ℝ} (hβ : 0 ≤ β)
    (r : Torus d (N₀ * L ^ K) × Fin d → ℝ)
    (hgrad : ∀ b ∈ D.crossing, vnorm (D.outwardDeriv (barField G Dat.Ψ φm) b) ≤ r b)
    (hresp : ∀ x, vnorm (wExt Dat Dat φm φ0 x) ≤ Km * Bh * m)
    (hHess : ‖2 * massChangeChord D a ν Dat φ0 φm α‖ ≤ CH * n * (Km * Bh * m) ^ 2) :
    β * ‖actionRegionC D a ν Dat φ0 - actionRegionC D a ν Dat φm‖ ≤
      (1 / 2) * CH * (Km * Bh) ^ 2 * β * m ^ 2 * n +
        Km * Bh * β * m * ∑ b ∈ D.crossing, r b := by
  rw [massChange_region_chord_with_star D hEL hφ0]
  have hS := starPair_norm_le D (wExt Dat Dat φm φ0) (barField G Dat.Ψ φm) r
    (fun _ => Km * Bh * m) hgrad hresp
  have hS' : ‖D.starPair (wExt Dat Dat φm φ0) (barField G Dat.Ψ φm)‖ ≤
      Km * Bh * m * ∑ b ∈ D.crossing, r b := by
    refine hS.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hc : ‖massChangeChord D a ν Dat φ0 φm α‖ ≤ (1 / 2) * (CH * n * (Km * Bh * m) ^ 2) := by
    rw [norm_mul] at hHess
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this] at hHess
    linarith
  calc β * ‖massChangeChord D a ν Dat φ0 φm α +
        D.starPair (wExt Dat Dat φm φ0) (barField G Dat.Ψ φm)‖
      ≤ β * (‖massChangeChord D a ν Dat φ0 φm α‖ +
        ‖D.starPair (wExt Dat Dat φm φ0) (barField G Dat.Ψ φm)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hβ
    _ ≤ β * ((1 / 2) * (CH * n * (Km * Bh * m) ^ 2) + Km * Bh * m * ∑ b ∈ D.crossing, r b) :=
        mul_le_mul_of_nonneg_left (add_le_add hc hS') hβ
    _ = _ := by ring

end Balaban.LargeField.ActionConv
