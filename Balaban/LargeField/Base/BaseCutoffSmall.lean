/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCutoffTransfer
public import Balaban.LargeField.Base.BaseRemainderLocal
public import Balaban.LargeField.Base.BaseFirstProductForm

/-!
# The first-step cutoff at small fluctuation: pointwise margins (BASE-KERNEL-4 Lemma 2.2)

At scale one (`K = 1`) every cube has a nonempty test footprint, so the strict global margins
(2.4) of BASE-KERNEL-4 on the whole fine torus make every factor `A_c B_c = chiPrimeZero` equal
to one (`chiPrimeZero_eq_one_of_global_margins`). For the sector product this gives
`baseSectorCubeProduct_eq_one_of_margins`: if the spins are within `r` of the background `e` and
the background satisfies the margins (block `< 2δ₀ - r`, bond `< δ₀ - 2r`, site
`√ν |e - h| < δ₀ - √ν r`), the all-good cutoff is `1`. The chart geometry
(`norm_chartPoint_sub_le`) gives `r = (3/2) ρ/√β` for tangent vectors of size `ρ ≤ √β/2`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background

variable {d N : ℕ} {nn : ℕ → ℕ} {L M : ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- At scale one every cube has a nonempty test footprint. -/
theorem baseFootprint_nonempty_one (regimeB : Prop) (c : Torus d (nn 1)) :
    (baseFootprint nn L M 1 regimeB c).Nonempty := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hLp : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 := card_blockFibre (d := d) (ℓ := M * nn 1 * L ^ (1 - 1)) (N := M) (m := nn 1)
    (by simp) c
  obtain ⟨y, hy⟩ : (blockFibre (ℓ := M * nn 1 * L ^ (1 - 1)) M (nn 1) c : Finset _).Nonempty := by
    rw [← Finset.card_pos, hc1]; positivity
  have hc2 := card_blockFibre (d := d) (ℓ := M * nn 1 * L ^ 1) (N := L) (m := M * nn 1 * L ^ (1 - 1))
    (by simp; ring) y
  obtain ⟨x, hx⟩ : (blockFibre (ℓ := M * nn 1 * L ^ 1) L (M * nn 1 * L ^ (1 - 1)) y : Finset _).Nonempty := by
    rw [← Finset.card_pos, hc2]; positivity
  exact ⟨x, Or.inl ⟨y, mem_blockFibre.1 hy, mem_blockFibre.1 hx⟩⟩

/-- **Global margins give all cube factors equal to one** (BASE-KERNEL-4 Lemma 2.2 with
`𝒥₊` the set of all cubes): at scale one, if the spins are within `r` of a unit background `e` and
the background has the margins (2.4) on all blocks, bonds and (regime (B)) sites, then
`A_c B_c = 1` for every cube `c`. -/
theorem chiPrimeZero_eq_one_of_global_margins {regimeB : Prop} {ν δ₀ r : ℝ} (hν : 0 ≤ ν)
    {h : Fin N → ℝ} {φ e : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ}
    {θ : Torus d (M * nn 1 * L ^ (1 - 1)) → Fin N → ℝ}
    (hunit : ∀ x, ∑ i, e x i ^ 2 = 1) (hclose : ∀ x, rn (fun i => φ x i - e x i) ≤ r)
    (hblock : ∀ y, rn (fun i => θ y i - spinAverage nn L M 1 e y i) < 2 * δ₀ - r)
    (hbond : ∀ (x : Torus d (M * nn 1 * L ^ 1)) (μ : Fin d),
      rn (fun i => e (x + Pi.single μ 1) i - e x i) < δ₀ - 2 * r)
    (hsite : regimeB → ∀ x, Real.sqrt ν * rn (fun i => e x i - h i) < δ₀ - Real.sqrt ν * r)
    (c : Torus d (nn 1)) :
    chiPrimeZero nn L M 1 regimeB ν δ₀ h c (φ, θ) = 1 := by
  have hm : BaseCutoffMargins nn L M 1 regimeB ν δ₀ r h (∅ : Set (Torus d (nn 1)))
      (Set.univ : Set (Torus d (M * nn 1 * L ^ 1))) φ e θ :=
    { unit := fun _ _ x _ => hunit x
      close := fun _ _ x _ => hclose x
      block := fun _ _ y _ => hblock y
      bond := fun _ _ x μ _ => hbond x μ
      site := fun _ _ hB x _ => hsite hB x }
  have hne := baseFootprint_nonempty_one (d := d) (nn := nn) (L := L) (M := M) regimeB c
  have hc : c ∈ baseJPlus nn L M 1 regimeB (∅ : Set (Torus d (nn 1)))
      (Set.univ : Set (Torus d (M * nn 1 * L ^ 1))) := ⟨by simp, by simpa using hne⟩
  exact chiPrimeZero_eq_one_of_margins le_rfl hν hm hc

section Sector

variable {n : ℕ} [NeZero n]

/-- **The all-good cutoff is one under margins** (sector form of
`chiPrimeZero_eq_one_of_global_margins`): `eF` is the background on the fine torus of the sector,
`φ` the sphere spins and `θ` the coarse field. -/
theorem baseSectorCubeProduct_eq_one_of_margins {regimeB : Prop} {ν δ₀ r : ℝ}
    (hν : 0 ≤ ν) (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) (eF : Torus d (1 * n * L ^ 1) → Fin N → ℝ)
    (hunit : ∀ x, ∑ i, eF x i ^ 2 = 1)
    (hclose : ∀ x, rn (fun i => baseSectorSpin φ x i - eF x i) ≤ r)
    (hblock : ∀ y, rn (fun i => baseSectorTheta θ y i -
      spinAverage (baseSectorN L n) L 1 1 eF y i) < 2 * δ₀ - r)
    (hbond : ∀ (x : Torus d (1 * n * L ^ 1)) (μ : Fin d),
      rn (fun i => eF (x + Pi.single μ 1) i - eF x i) < δ₀ - 2 * r)
    (hsite : regimeB → ∀ x, Real.sqrt ν * rn (fun i => eF x i - h i) <
      δ₀ - Real.sqrt ν * r) :
    baseSectorCubeProduct regimeB ν δ₀ h θ φ = 1 := by
  unfold baseSectorCubeProduct
  refine Finset.prod_eq_one fun c _ => ?_
  exact chiPrimeZero_eq_one_of_global_margins (nn := baseSectorN L n) (M := 1) hν hunit hclose
    hblock hbond hsite c

/-- **Chart geometry: the pointwise margin.** If the spins are the chart point of a tangent
vector `w` with `‖w_x‖ ≤ ρ ≤ √β/2`, then `|φ_x - e_x| ≤ r := (3/2) ρ/√β`, and the all-good cutoff
is one as soon as the background `e` has the margins (block `< 2δ₀ - r`, bond `< δ₀ - 2r`, site
`√ν |e - h| < δ₀ - √ν r`). -/
theorem baseSectorCubeProduct_eq_one_of_chart {β : ℝ} (hβ : 0 < β) {regimeB : Prop}
    {ν δ₀ ρ : ℝ} (hν : 0 ≤ ν) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (e w : Config (Torus d (L * n)) N) (he : ∀ x, ‖e x‖ = 1)
    (hρ : ρ ≤ Real.sqrt β / 2) (hw : ∀ x, ‖w x‖ ≤ ρ)
    (hφ : ∀ y, (φ y : EuclideanSpace ℝ (Fin N)) = chartPoint β e w y)
    (hblock : ∀ y, rn (fun i => baseSectorTheta θ y i -
      spinAverage (baseSectorN L n) L 1 1 (fun x i => e (baseSector_side L n ▸ x) i) y i) <
        2 * δ₀ - 3 / 2 * (ρ / Real.sqrt β))
    (hbond : ∀ (x : Torus d (1 * n * L ^ 1)) (μ : Fin d),
      rn (fun i => e (baseSector_side L n ▸ (x + Pi.single μ 1)) i -
        e (baseSector_side L n ▸ x) i) < δ₀ - 2 * (3 / 2 * (ρ / Real.sqrt β)))
    (hsite : regimeB → ∀ x : Torus d (1 * n * L ^ 1),
      Real.sqrt ν * rn (fun i => e (baseSector_side L n ▸ x) i - h i) <
        δ₀ - Real.sqrt ν * (3 / 2 * (ρ / Real.sqrt β))) :
    baseSectorCubeProduct regimeB ν δ₀ h θ φ = 1 := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  refine baseSectorCubeProduct_eq_one_of_margins (r := 3 / 2 * (ρ / Real.sqrt β)) hν h θ φ
    (fun x i => e (baseSector_side L n ▸ x) i) (fun x => ?_) (fun x => ?_) hblock ?_ hsite
  · have hn := he (baseSector_side L n ▸ x)
    have := EuclideanSpace.norm_sq_eq (e (baseSector_side L n ▸ x))
    simp only [Real.norm_eq_abs, sq_abs] at this
    rw [hn] at this
    simpa using this.symm
  · have hx := norm_chartPoint_sub_le hβ he (w := w) (baseSector_side L n ▸ x)
      ((hw _).trans hρ)
    have h1 : ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) -
        e (baseSector_side L n ▸ x)‖ ≤ 3 / 2 * (ρ / Real.sqrt β) := by
      rw [hφ]
      refine hx.trans ?_
      gcongr
      exact hw _
    have h2 := rn_eq_norm ((φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) -
        e (baseSector_side L n ▸ x))
    rw [← h2] at h1
    exact h1
  · exact hbond

end Sector

end Balaban.LargeField
