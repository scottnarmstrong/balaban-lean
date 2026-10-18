/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Region energies by cube counting (P7CONV §3.4 (52))

Counting lemmas that turn pointwise bounds on a field and its difference quotients into the
region energies of the budgets (52):

* `StepDecomp.sum_sites_le`: a sum over the sites of a region is at most `κ` times the mixed
  count when it is so on every cube of the decomposition;
* `Region.starSum_le`: a sum over the half-weighted bonds of a region is at most `d` times the sum,
  over the sites of the region, of a bound valid for the bonds at that site (both directions);
* `Region.siteEnergy_le`, `Region.bondEnergy_le`: the block and mass energies and the bond energy
  from sup bounds on the field and its difference quotients.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- A sum over the sites of a region is bounded cube by cube. -/
theorem StepDecomp.sum_sites_le {X : Region G} (Dc : StepDecomp X)
    (f : Torus d (N₀ * L ^ K) → ℝ) {κ : ℝ}
    (h : ∀ c, ∑ x ∈ (Dc.cube c).sites, f x ≤ κ * Dc.wt c) :
    ∑ x ∈ X.sites, f x ≤ κ * Dc.total := by
  rw [Dc.cube_union, Finset.sum_biUnion (fun c _ c' _ hc => Dc.cube_disj hc), StepDecomp.total,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => h c

/-- A sum over the half-weighted bonds of a region: each bond has an endpoint in the region, and
the bonds at a site `x` of the region are the forward bonds `(x, μ)` and the backward bonds
`(x - e_μ, μ)`. -/
theorem Region.starSum_le (X : Region G) (g : Torus d (N₀ * L ^ K) × Fin d → ℝ)
    (c : Torus d (N₀ * L ^ K) → ℝ)
    (hc : ∀ x ∈ X.sites, ∀ μ, g (x, μ) ≤ c x ∧ g (x - Pi.single μ 1, μ) ≤ c x) :
    ∑ z, X.starWeight z.1 z.2 * g z ≤ d * ∑ x ∈ X.sites, c x := by
  classical
  have e1 : ∀ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * g z =
      (1 / 2) * (if z.1 ∈ X.sites then g z else 0) +
      (1 / 2) * (if z.1 + Pi.single z.2 1 ∈ X.sites then g z else 0) := by
    intro z
    unfold Region.starWeight
    split_ifs <;> ring
  simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have A : ∑ y : Torus d (N₀ * L ^ K), ∑ μ : Fin d, (if y ∈ X.sites then g (y, μ) else 0) ≤
      d * ∑ x ∈ X.sites, c x := by
    rw [Finset.sum_comm]
    calc _ = ∑ μ : Fin d, ∑ y ∈ X.sites, g (y, μ) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ ≤ ∑ _μ : Fin d, ∑ y ∈ X.sites, c y :=
          Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun y hy => (hc y hy μ).1
      _ = d * ∑ x ∈ X.sites, c x := by simp
  have B : ∑ y : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if y + Pi.single μ 1 ∈ X.sites then g (y, μ) else 0) ≤ d * ∑ x ∈ X.sites, c x := by
    rw [Finset.sum_comm]
    calc _ = ∑ μ : Fin d, ∑ y ∈ X.sites, g (y - Pi.single μ 1, μ) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          have key : ∑ y : Torus d (N₀ * L ^ K),
              (if y + Pi.single μ 1 ∈ X.sites then g (y, μ) else 0) =
              ∑ x : Torus d (N₀ * L ^ K),
                (if x ∈ X.sites then g (x - Pi.single μ 1, μ) else 0) :=
            Fintype.sum_equiv (Equiv.addRight (Pi.single μ 1)) _ _ (fun y => by simp)
          rw [key, Finset.sum_ite_mem, Finset.univ_inter]
      _ ≤ ∑ _μ : Fin d, ∑ y ∈ X.sites, c y :=
          Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun y hy => (hc y hy μ).2
      _ = d * ∑ x ∈ X.sites, c x := by simp
  linarith

/-- The sum of the squared coordinate norms of a vector bounded coordinatewise by `V`. -/
theorem sumsq_le_of_comp {v : Fin N → ℂ} {V : ℝ} (h : ∀ i, ‖v i‖ ≤ V) :
    ∑ i, ‖v i‖ ^ 2 ≤ N * V ^ 2 := by
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, V ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = N * V ^ 2 := by simp

/-- **Site energy from a sup bound.**  `β ∑_{x ∈ X} w(x) |u(x)|² ≤ B κ |X|_{mix}` if
`|u(x)|² ≤ B` on `X` and `β ∑_{x ∈ cube} w(x) ≤ κ wt(cube)` on every cube. -/
theorem Region.siteEnergy_le {X : Region G} (Dc : StepDecomp X) (w : Torus d (N₀ * L ^ K) → ℝ)
    (u : Torus d (N₀ * L ^ K) → Fin N → ℂ) {B κ β : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hw : ∀ x, 0 ≤ w x) (hu : ∀ x ∈ X.sites, ∑ j, ‖u x j‖ ^ 2 ≤ B)
    (hcube : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, w x ≤ κ * Dc.wt c) :
    β * ∑ x ∈ X.sites, w x * ∑ j, ‖u x j‖ ^ 2 ≤ B * (κ * Dc.total) := by
  have h1 : ∑ x ∈ X.sites, w x * ∑ j, ‖u x j‖ ^ 2 ≤ B * ∑ x ∈ X.sites, w x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left (hu x hx) (hw x)
  have h2 : β * ∑ x ∈ X.sites, w x ≤ κ * Dc.total := by
    have := Dc.sum_sites_le (fun x => β * w x) (κ := κ) (fun c => by
      rw [← Finset.mul_sum]; exact hcube c)
    rwa [← Finset.mul_sum] at this
  calc β * ∑ x ∈ X.sites, w x * ∑ j, ‖u x j‖ ^ 2 ≤ β * (B * ∑ x ∈ X.sites, w x) :=
        mul_le_mul_of_nonneg_left h1 hβ
    _ = B * (β * ∑ x ∈ X.sites, w x) := by ring
    _ ≤ B * (κ * Dc.total) := mul_le_mul_of_nonneg_left h2 hB

/-- **Bond energy from sup bounds on the difference quotients.**  If `ℓ(x)² |∂f|² ≤ B` on the
bonds at every site `x` of `X` (both directions) and `β ∑_{x ∈ cube} ℓ(x)⁻² ≤ κ wt(cube)` on every
cube, the half-weighted bond energy is at most `d B κ |X|_{mix}`. -/
theorem Region.bondEnergy_le {X : Region G} (Dc : StepDecomp X)
    (f : Torus d (N₀ * L ^ K) → Fin N → ℂ) {B κ β : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hfwd : ∀ x ∈ X.sites, ∀ μ : Fin d,
      G.spacing x ^ 2 * ∑ j, ‖f (x + Pi.single μ 1) j - f x j‖ ^ 2 ≤ B)
    (hbwd : ∀ x ∈ X.sites, ∀ μ : Fin d,
      G.spacing x ^ 2 * ∑ j, ‖f (x - Pi.single μ 1) j - f x j‖ ^ 2 ≤ B)
    (hcube : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ κ * Dc.wt c) :
    β * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 *
        ∑ j, ‖f (z.1 + Pi.single z.2 1) j - f z.1 j‖ ^ 2 ≤ d * (B * (κ * Dc.total)) := by
  have hsp : ∀ x, 0 < G.spacing x ^ 2 := fun x => by
    have := spacing_pos G (x := x); positivity
  have hq : ∀ (x : Torus d (N₀ * L ^ K)) (v : ℝ), G.spacing x ^ 2 * v ≤ B →
      v ≤ B * ((G.spacing x) ^ 2)⁻¹ := fun x v h => by
    rw [le_mul_inv_iff₀ (hsp x)]; linarith
  have hfw : ∀ x ∈ X.sites, ∀ μ : Fin d,
      (∑ j, ‖f (x + Pi.single μ 1) j - f x j‖ ^ 2) ≤ B * ((G.spacing x) ^ 2)⁻¹ :=
    fun x hx μ => hq x _ (hfwd x hx μ)
  have hbw : ∀ x ∈ X.sites, ∀ μ : Fin d,
      (∑ j, ‖f (x - Pi.single μ 1 + Pi.single μ 1) j - f (x - Pi.single μ 1) j‖ ^ 2) ≤
        B * ((G.spacing x) ^ 2)⁻¹ := by
    intro x hx μ
    refine hq x _ ?_
    have := hbwd x hx μ
    simp only [sub_add_cancel]
    simpa only [norm_sub_rev (f (x - Pi.single μ 1) _)] using this
  have h1 := Region.starSum_le X
    (fun z => ∑ j, ‖f (z.1 + Pi.single z.2 1) j - f z.1 j‖ ^ 2)
    (fun x => B * ((G.spacing x) ^ 2)⁻¹) (by
      intro x hx μ
      refine ⟨?_, ?_⟩
      · simpa only using hfw x hx μ
      · simpa only using hbw x hx μ)
  have h2 : β * ∑ x ∈ X.sites, ((G.spacing x) ^ 2)⁻¹ ≤ κ * Dc.total := by
    have := Dc.sum_sites_le (fun x => β * ((G.spacing x) ^ 2)⁻¹) (κ := κ) (fun c => by
      rw [← Finset.mul_sum]; exact hcube c)
    rwa [← Finset.mul_sum] at this
  calc _ ≤ β * (d * ∑ x ∈ X.sites, B * ((G.spacing x) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 hβ
    _ = d * (B * (β * ∑ x ∈ X.sites, ((G.spacing x) ^ 2)⁻¹)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ d * (B * (κ * Dc.total)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB) (Nat.cast_nonneg d)

end Balaban.LargeField.ActionConv
