/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.XiCDomains
public import Balaban.LargeField.Base.SpinsNearBackground
public import Balaban.LargeField.Characteristic.Measurable
public import Balaban.Background.WeightedProp51Basic
public import Balaban.Fluctuation.FarDecay
public import Balaban.Fluctuation.Lemma25Xi
import Mathlib.Tactic.Positivity

/-!
# Inhabitation of structures on background data

* `realFamily_const`: the constant family `y ↦ clip(unit, h)` is a `RealFamily` for every
  `h` and every parameter space `Y` (non-degenerate data: `Ψ ≡ e₀` on `Ω₁ ∪ collar`);
* `baseSpinSupport_nonempty`: constant unit spins `φ ≡ h ≡ e₀`, `D = clip(e₀, e₀)`, every
  `δ₀ > 0`, `ν` (non-degenerate: the block condition holds with equality `Ψ = Qφ`);
* `starBoundW_exists`, `supBoundsW_exists`: for every field `u` and every weight `w` there is a
  finite `V` with `StarBoundW`/`SupBoundsW` (finiteness of the torus);
* `chiUBounds_exists`: for every data `D'`, `φ₁`, `α₁`, `ν` there is `δ > 0` with `ChiUBounds`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField
  Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The constant unit datum `clip(e₀, h)`. -/
noncomputable def unitBg (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) (h : Fin N → ℝ) :
    BgData G N :=
  BgData.clip G (fun _ i => (unitVec hN i : ℂ)) (fun _ i => (h i : ℂ))
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)

theorem unitBg_Ψ_of_mem (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) (h : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) (i : Fin N) :
    (unitBg G hN h).Ψ x i = (unitVec hN i : ℂ) := by
  simp [unitBg, BgData.clip, hx]

theorem unitBg_h_of_mem (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) (h : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    (unitBg G hN h).h x i = (h i : ℂ) := by
  simp [unitBg, BgData.clip, hx]

/-- **`RealFamily` is inhabited** for every parameter space and every `h`. -/
theorem realFamily_const {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) (h : Fin N → ℝ) :
    RealFamily (fun _ : Y => unitBg G hN h) h where
  real := fun _ x i => by
    by_cases hx : x ∈ dataSites G
    · rw [unitBg_Ψ_of_mem G hN h hx]; simp
    · simp [unitBg, BgData.clip, hx]
  hconst := fun _ x hx i => unitBg_h_of_mem G hN h hx i
  Ψc := fun _ _ => continuous_const
  hc := fun _ _ => continuous_const

/-- **`BaseSpinSupport` is inhabited** for every generating set of level `1`, `δ₀ > 0` and `ν`. -/
theorem baseSpinSupport_nonempty (G : GeneratingSet d L N₀ 1 ϱ) (hN : 0 < N) (ν : ℝ) {δ₀ : ℝ}
    (hδ : 0 < δ₀) :
    BaseSpinSupport G ν δ₀ (fun _ => unitVec hN) (unitVec hN) (unitBg G hN (unitVec hN)) where
  delta_pos := hδ
  spin_unit := fun _ => sum_sq_unitVec hN
  h_unit := sum_sq_unitVec hN
  block_real := fun x hx i => by
    rw [unitBg_Ψ_of_mem G hN _ ((mem_dataSites G).2 (Or.inl hx))]; simp
  collar_eq := fun x hx i => unitBg_Ψ_of_mem G hN _ ((mem_dataSites G).2 (Or.inr hx)) i
  field_eq := fun x hx i => unitBg_h_of_mem G hN _ hx i
  block_cond := fun x hx => by
    have hc : ((G.blk 1 x).card : ℝ) = ((L : ℝ) ^ 1) ^ d := card_blk_cast G 1 le_rfl x
    have hq : ∀ i, spinBlockAverage G (fun _ => unitVec hN) x i = unitVec hN i := by
      intro i
      unfold spinBlockAverage
      rw [Finset.sum_const, nsmul_eq_mul, hc]
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      field_simp
    have : (fun i => ((unitBg G hN (unitVec hN)).Ψ x i).re - spinBlockAverage G
        (fun _ => unitVec hN) x i) = fun _ => 0 := by
      funext i
      rw [unitBg_Ψ_of_mem G hN _ ((mem_dataSites G).2 (Or.inl hx)), hq]; simp
    rw [this]; simpa [rn] using by positivity
  bond_cond := fun x μ _ => by simpa [rn] using by positivity
  site_cond := fun x _ => by simpa using by positivity

theorem exists_ub {ι : Type*} [Finite ι] (f : ι → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, f i ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range f).bddAbove
  exact ⟨|C|, abs_nonneg _, fun i => (hC ⟨i, rfl⟩).trans (le_abs_self _)⟩

/-- **`StarBoundW` is inhabited** for every weight `w` and field `u`: the torus is finite. -/
theorem starBoundW_exists (G : GeneratingSet d L N₀ k ϱ) (w : Torus d (N₀ * L ^ k) → ℝ)
    (u : G.Ω 1 × Fin N → ℂ) : ∃ V : ℝ, StarBoundW G w u V := by
  obtain ⟨C1, h1, hC1⟩ := exists_ub (fun p : Torus d (N₀ * L ^ k) × Fin N =>
    w p.1 * ‖svec G u p.1 p.2‖)
  obtain ⟨C2, h2, hC2⟩ := exists_ub (fun p : Torus d (N₀ * L ^ k) × Fin d × Fin N =>
    w p.1 * (G.spacing p.1 * ‖svec G u (p.1 + Pi.single p.2.1 1) p.2.2 - svec G u p.1 p.2.2‖))
  obtain ⟨C3, h3, hC3⟩ := exists_ub (fun p : Torus d (N₀ * L ^ k) × Fin d × Fin N =>
    w p.1 * (G.spacing p.1 * ‖svec G u (p.1 - Pi.single p.2.1 1) p.2.2 - svec G u p.1 p.2.2‖))
  exact ⟨C1 + C2 + C3, fun y i => by have := hC1 (y, i); linarith,
    fun x _ μ i => by have := hC2 (x, μ, i); linarith,
    fun x _ μ i => by have := hC3 (x, μ, i); linarith⟩

/-- **`SupBoundsW` is inhabited** for every weight `w` and field `u`. -/
theorem supBoundsW_exists {N₁ m₁ K : ℕ} [NeZero N₁]
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (w : Localization.CTorus d L N₁ m₁ K → ℝ)
    (u : G.Ω 1 × Fin N → ℂ) : ∃ V : ℝ, SupBoundsW G w u V := by
  obtain ⟨C1, h1, hC1⟩ := exists_ub (fun p : G.Ω 1 × Fin N => w p.1 * ‖u p‖)
  obtain ⟨C2, h2, hC2⟩ := exists_ub (fun p : Localization.CTorus d L N₁ m₁ K × Fin d × Fin N =>
    w p.1 * (G.spacing p.1 * ‖svec G u (p.1 + Pi.single p.2.1 1) p.2.2 - svec G u p.1 p.2.2‖))
  obtain ⟨C3, h3, hC3⟩ := exists_ub (fun p : Localization.CTorus d L N₁ m₁ K × Fin d × Fin N =>
    w p.1 * (G.spacing p.1 * ‖svec G u (p.1 - Pi.single p.2.1 1) p.2.2 - svec G u p.1 p.2.2‖))
  obtain ⟨C4, h4, hC4⟩ := exists_ub (fun p : Localization.CTorus d L N₁ m₁ K × Fin N =>
    w p.1 * (G.spacing p.1 ^ 2 * ‖∑ μ : Fin d, (2 * svec G u p.1 p.2 -
      svec G u (p.1 + Pi.single μ 1) p.2 - svec G u (p.1 - Pi.single μ 1) p.2)‖))
  exact ⟨C1 + C2 + C3 + C4, fun x i => by have := hC1 (x, i); linarith,
    fun x _ μ i => by have := hC2 (x, μ, i); linarith,
    fun x _ μ i => by have := hC3 (x, μ, i); linarith,
    fun x _ i => by have := hC4 (x, i); linarith⟩

/-- **`ChiUBounds` is inhabited**: for all data `D'`, `φ₁`, `α₁` and `ν` there is a `δ > 0` for
which the five tests of `χ_{k+1,u}` hold (they are strict upper bounds by finitely many numbers). -/
theorem chiUBounds_exists (G' : GeneratingSet d L N₀ k ϱ) (ν : ℝ) (D' : BgData G' N)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (α₁ : G'.Ω 1 → ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ChiUBounds G' ν δ D' φ₁ α₁ := by
  obtain ⟨C1, h1, hC1⟩ := exists_ub (fun x : Torus d (N₀ * L ^ k) =>
    vn (fun i => D'.Ψ x i - blockAvg G' φ₁ x i))
  obtain ⟨C2, h2, hC2⟩ := exists_ub (fun p : Torus d (N₀ * L ^ k) × Fin d =>
    G'.spacing p.1 * vn (fun i => barField G' D'.Ψ φ₁ (p.1 + Pi.single p.2 1) i -
      barField G' D'.Ψ φ₁ p.1 i))
  obtain ⟨C2', h2', hC2'⟩ := exists_ub (fun p : Torus d (N₀ * L ^ k) × Fin d =>
    G'.spacing p.1 * vn (fun i => barField G' D'.Ψ φ₁ (p.1 - Pi.single p.2 1) i -
      barField G' D'.Ψ φ₁ p.1 i))
  obtain ⟨C3, h3, hC3⟩ := exists_ub (fun x : Torus d (N₀ * L ^ k) =>
    G'.spacing x ^ 2 * vn (fun i => ∑ μ : Fin d,
      (barField G' D'.Ψ φ₁ (x + Pi.single μ 1) i + barField G' D'.Ψ φ₁ (x - Pi.single μ 1) i -
        2 * barField G' D'.Ψ φ₁ x i)))
  obtain ⟨C4, h4, hC4⟩ := exists_ub (fun x : G'.Ω 1 =>
    G'.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₁ x‖)
  obtain ⟨C5, h5, hC5⟩ := exists_ub (fun z : G'.Ω 1 =>
    Real.sqrt ν * G'.spacing (z : Torus d (N₀ * L ^ k)) * vn (fun i => φ₁ (z, i) - D'.h z i))
  set C := C1 + C2 + C2' + C3 + C4 + C5 with hC
  refine ⟨2 * (C + 1), by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _; have := hC1 x; linarith
  · intro x _ μ
    have hs : 0 < G'.spacing x := spacing_pos G'
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hs]; have := hC2 (x, μ); nlinarith
    · rw [lt_div_iff₀ hs]; have := hC2' (x, μ); nlinarith
  · intro x _
    have hs : 0 < G'.spacing x ^ 2 := by have := spacing_pos G' (x := x); positivity
    rw [lt_div_iff₀ hs]; have := hC3 x; nlinarith
  · intro x; have := hC4 x; linarith
  · intro z; have := hC5 z; linarith

end Balaban.Inhabited
