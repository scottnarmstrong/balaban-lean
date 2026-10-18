/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBudgetCount
public import Balaban.LargeField.R.CoeffResponseHcoef
import Balaban.Multiscale.ConstraintKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The read-energy budgets (52) from the response sup bounds (P7CONV §3.4)

For a perturbation `δ = φ¹ - φ⁰` with the weight-one sup bounds `V` of
`coeffChange_sameData_response` (`SupBoundsW (fun _ => 1) δ V`), the three primed read energies of
(52) are counted over the cubes of a `StepDecomp`:

* `Region.blockEnergy_response_le`: `β ∑_x |a(x)| |Qδ(x)|² ≤ N C_b · A |X|_{mix} V²`;
* `Region.bondEnergy_response_le`: `β ∑_b ω_b |∂δ̄(b)|² ≤ d N C_g · A |X|_{mix} V²`;
* `Region.massEnergy_response_le`: `β ∑_x |ν| |δ(x)|² ≤ N C_m · A |X|_{mix} V²`;

under the per-cube coefficient budgets `β ∑_{x ∈ cube} |a(x)| ≤ C_b A wt(cube)`,
`β ∑_{x ∈ cube} ℓ(x)⁻² ≤ C_g A wt(cube)`, `β ∑_{x ∈ cube} |ν| ≤ C_m A wt(cube)` (the counting of the
decomposition: the cubes are layer blocks of weight one).  The unprimed energies of (52) follow in
the same way from sup bounds on the datum read.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- A block average is bounded by the sup bound of the field on the block. -/
theorem blockAvg_norm_le_of_sup (τ : G.Ω 1 × Fin N → ℂ) {V : ℝ}
    {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1)
    (hbd : ∀ (y : G.Ω 1) (i : Fin N), ‖τ (y, i)‖ ≤ V) (i : Fin N) :
    ‖blockAvg G τ x i‖ ≤ V := by
  obtain ⟨h1, h2, hxl⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G h1 h2 hxl
  unfold blockAvg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsum : ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G τ y i‖ ≤
      ((G.blk (G.layerIndex x) x).card : ℝ) * V := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ G.blk (G.layerIndex x) x, ‖svec G τ y i‖
        ≤ ∑ _y ∈ G.blk (G.layerIndex x) x, V := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [svec_of_mem G τ ⟨y, hsub hy⟩ i]
          exact hbd ⟨y, hsub hy⟩ i
      _ = _ := by simp
  rw [card_blk_cast G _ h2] at hsum
  have hpos : (0 : ℝ) < (((L : ℝ) ^ G.layerIndex x) ^ d) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  calc (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ‖∑ y ∈ G.blk (G.layerIndex x) x, svec G τ y i‖
      ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * ((((L : ℝ) ^ G.layerIndex x) ^ d) * V) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = V := by field_simp

/-- **Block energy of the response** (the first of the primed budgets (52)). -/
theorem Region.blockEnergy_response_le {X : Region G} (Dc : StepDecomp X) (a : ℕ → ℝ)
    (δ : G.Ω 1 × Fin N → ℂ) {V Cb A β : ℝ} (hβ : 0 ≤ β)
    (hval : ∀ (x : G.Ω 1) (j : Fin N), 1 * ‖δ (x, j)‖ ≤ V)
    (hcube : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a x‖ ≤ Cb * (A * Dc.wt c)) :
    β * ∑ x ∈ X.sites, ‖levelCoeff G a x‖ * ∑ j, ‖blockAvg G δ x j‖ ^ 2 ≤
      (N * Cb) * (A * Dc.total * V ^ 2) := by
  have := Region.siteEnergy_le Dc (fun x => ‖levelCoeff G a x‖) (blockAvg G δ) (B := N * V ^ 2)
    (κ := Cb * A) hβ (by positivity) (fun x => norm_nonneg _) (fun x hx => sumsq_le_of_comp
      (fun j => blockAvg_norm_le_of_sup δ (X.sub_Ω hx) (fun y i => by simpa using hval y i) j))
    (fun c => by simpa only [mul_assoc] using hcube c)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The square of a scaled norm sum from coordinatewise scaled bounds. -/
theorem sq_mul_sumsq_le {v : Fin N → ℂ} {s V : ℝ} (hs : 0 ≤ s) (h : ∀ j, s * ‖v j‖ ≤ V) :
    s ^ 2 * ∑ j, ‖v j‖ ^ 2 ≤ N * V ^ 2 := by
  calc s ^ 2 * ∑ j, ‖v j‖ ^ 2 = ∑ j, (s * ‖v j‖) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ _j : Fin N, V ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (by positivity) (h j) 2
    _ = N * V ^ 2 := by simp

/-- **Bond energy of the response** (the second of the primed budgets (52)). -/
theorem Region.bondEnergy_response_le {X : Region G} (Dc : StepDecomp X)
    (δ : G.Ω 1 × Fin N → ℂ) {V Cg A β : ℝ} (hβ : 0 ≤ β)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G δ (x + Pi.single μ 1) j - svec G δ x j‖) ≤ V)
    (hbwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G δ (x - Pi.single μ 1) j - svec G δ x j‖) ≤ V)
    (hcube : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ Cg * (A * Dc.wt c)) :
    β * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 *
        ∑ j, ‖svec G δ (z.1 + Pi.single z.2 1) j - svec G δ z.1 j‖ ^ 2 ≤
      (d * (N * Cg)) * (A * Dc.total * V ^ 2) := by
  have hsp : ∀ x, 0 ≤ G.spacing x := fun x => (spacing_pos G (x := x)).le
  have := Region.bondEnergy_le Dc (svec G δ) (B := N * V ^ 2) (κ := Cg * A) hβ (by positivity)
    (fun x hx μ => sq_mul_sumsq_le (hsp x) (fun j => by
      simpa using hfwd x (X.sub_Ω hx) μ j))
    (fun x hx μ => sq_mul_sumsq_le (hsp x) (fun j => by
      simpa using hbwd x (X.sub_Ω hx) μ j))
    (fun c => by simpa only [mul_assoc] using hcube c)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Mass energy of the response** (the third of the primed budgets (52)). -/
theorem Region.massEnergy_response_le {X : Region G} (Dc : StepDecomp X)
    (δ : G.Ω 1 × Fin N → ℂ) {V Cm A β ν : ℝ} (hβ : 0 ≤ β)
    (hval : ∀ (x : G.Ω 1) (j : Fin N), 1 * ‖δ (x, j)‖ ≤ V)
    (hcube : ∀ c, β * ∑ _x ∈ (Dc.cube c).sites, |ν| ≤ Cm * (A * Dc.wt c)) :
    β * ∑ x ∈ X.sites, |ν| * ∑ j, ‖svec G δ x j‖ ^ 2 ≤
      (N * Cm) * (A * Dc.total * V ^ 2) := by
  have := Region.siteEnergy_le Dc (fun _ => |ν|) (svec G δ) (B := N * V ^ 2)
    (κ := Cm * A) hβ (by positivity) (fun _ => abs_nonneg _) (fun x hx => sumsq_le_of_comp
      (fun j => by
        rw [svec_of_mem G δ ⟨x, X.sub_Ω hx⟩ j]
        simpa using hval ⟨x, X.sub_Ω hx⟩ j))
    (fun c => by simpa only [mul_assoc] using hcube c)
  calc _ ≤ _ := this
    _ = _ := by ring

end Balaban.LargeField.ActionConv
