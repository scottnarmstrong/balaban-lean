/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootSupportBridge
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition

/-!
# From a cube-indexed coefficient family to the root's term family

A coefficient family `C x i g T′` indexed by finite sets `T′` of cubes (with support, source
locality on the unit ball, analyticity on the unit ball and an exponential bound in `dExt T′`)
is regrouped by the site set `X` of `T′` into a family `U x X g` with the clauses of the
frozen root: vanishing unless `x ∈ X` and `X` is a polymer, locality for all sources, analyticity
on the unit ball, the decay `exp (-κ |X| / (M L^K)^d)`, and the regrouping identity.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L]

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ

open Classical in
/-- Regrouping of a cube-indexed coefficient family by site sets, with the clauses of the
root's terms. -/
theorem rootTermFamily_of_cubeFamily (hN : L ∣ N₁)
    (C : CTorus d L N₁ m₁ K → Fin N → (CTorus d L N₁ m₁ K → Fin N → ℂ) → Finset 𝔅 → ℂ)
    {κ lam B : ℝ} (hκ : 0 < κ) (hlam : c1 d L * κ ≤ lam) (hB : 0 ≤ B)
    (hsupp : ∀ x i, ∀ g ∈ {g : CTorus d L N₁ m₁ K → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1},
      ∀ T', C x i g T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex x) ∈ T' ∧ IsPolyDom 1 K (sitesOf T'))
    (hloc : ∀ x i T', ∀ g ∈ {g : CTorus d L N₁ m₁ K → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1},
      ∀ g' ∈ {g : CTorus d L N₁ m₁ K → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1},
      (∀ y ∈ sitesOf T', g y = g' y) → C x i g T' = C x i g' T')
    (han : ∀ x i T', AnalyticOnNhd ℂ (fun g => C x i g T')
      {g : CTorus d L N₁ m₁ K → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1})
    (hbd : ∀ x i T', ∀ g : CTorus d L N₁ m₁ K → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
      ‖C x i g T'‖ ≤ B * Real.exp (-lam * dExt T')) :
    ∃ U : CTorus d L N₁ m₁ K → Finset (CTorus d L N₁ m₁ K) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → (Fin N → ℂ),
      (∀ x X, ¬ (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ K) (L ^ (m₁ + 1) * L ^ K) X) →
        U x X = 0) ∧
      (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
      (∀ x X, AnalyticOnNhd ℂ (U x X)
        {g : CTorus d L N₁ m₁ K → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
      (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
        ‖U x X g‖ ≤ B * Real.exp lam *
          Real.exp (-κ * (X.card : ℝ) / ((L ^ (m₁ + 1) * L ^ K : ℕ) : ℝ) ^ d)) ∧
      (∀ g ∈ {g : CTorus d L N₁ m₁ K → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}, ∀ x i,
        ∑ X : Finset (CTorus d L N₁ m₁ K), U x X g i = ∑ T' : Finset 𝔅, C x i g T') := by
  -- the restriction to `X` as a continuous linear map
  have hres : ∀ X : Finset (CTorus d L N₁ m₁ K),
      ∃ r : (CTorus d L N₁ m₁ K → Fin N → ℂ) →L[ℂ] (CTorus d L N₁ m₁ K → Fin N → ℂ),
        ∀ g, r g = fun y i => if y ∈ X then g y i else 0 := by
    intro X
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun g y i => if y ∈ X then g y i else 0
        map_add' := ?_
        map_smul' := ?_ }, fun g => rfl⟩
    · intro g g'; funext y i; by_cases h : y ∈ X <;> simp [h]
    · intro c g; funext y i; by_cases h : y ∈ X <;> simp [h]
  have hnorm : ∀ (X : Finset (CTorus d L N₁ m₁ K)) (g : CTorus d L N₁ m₁ K → Fin N → ℂ),
      ∑ y, ∑ i, ‖(fun y i => if y ∈ X then g y i else (0 : ℂ)) y i‖ ≤ ∑ y, ∑ i, ‖g y i‖ := by
    intro X g
    refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun i _ => ?_
    by_cases h : y ∈ X <;> simp [h]
  refine ⟨fun x X g i => if (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ K)
      (L ^ (m₁ + 1) * L ^ K) X) then
      ∑ T' ∈ (Finset.univ.filter fun T' : Finset 𝔅 =>
        Finset.univ.filter (· ∈ sitesOf T') = X),
        C x i (fun y i => if y ∈ X then g y i else 0) T' else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro x X h; funext g i; simp [h]
  · intro x X g g' h
    funext i
    have : (fun y i => if y ∈ X then g y i else (0 : ℂ)) =
        (fun y i => if y ∈ X then g' y i else (0 : ℂ)) := by
      funext y j; by_cases hy : y ∈ X
      · simp [hy, h y hy]
      · simp [hy]
    simp only [this]
  · intro x X
    obtain ⟨r, hr⟩ := hres X
    refine analyticOnNhd_pi_iff.2 fun i => ?_
    by_cases hc : (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ K) (L ^ (m₁ + 1) * L ^ K) X)
    · simp only [hc, and_self, ite_true]
      refine Finset.analyticOnNhd_fun_sum (𝕜 := ℂ) _ fun T' _ => ?_
      have hr' : (fun g => C x i (fun y i => if y ∈ X then g y i else 0) T') =
          (fun g => C x i g T') ∘ r := by
        funext g; simp [hr]
      rw [hr']
      refine (han x i T').comp (r.analyticOnNhd _) fun g hg => ?_
      simp only [Set.mem_ofPred_eq, hr] at hg ⊢
      exact lt_of_le_of_lt (hnorm X g) hg
    · simp only [hc, ite_false]
      exact analyticOnNhd_const
  · intro x X g hg
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    by_cases hc : (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ K) (L ^ (m₁ + 1) * L ^ K) X)
    · simp only [hc, and_self, ite_true]
      set s := Finset.univ.filter fun T' : Finset 𝔅 => Finset.univ.filter (· ∈ sitesOf T') = X
        with hs
      have hone : ∀ T' ∈ s, ‖C x i (fun y i => if y ∈ X then g y i else 0) T'‖ ≤
          B * Real.exp lam *
            Real.exp (-κ * (X.card : ℝ) / ((L ^ (m₁ + 1) * L ^ K : ℕ) : ℝ) ^ d) := by
        intro T' hT'
        have hX : Finset.univ.filter (· ∈ sitesOf T') = X := (Finset.mem_filter.1 hT').2
        have hg' : ∑ y, ∑ i, ‖(fun y i => if y ∈ X then g y i else (0 : ℂ)) y i‖ ≤ 1 / 2 :=
          (hnorm X g).trans hg
        have hgB : ∑ y, ∑ i, ‖(fun y i => if y ∈ X then g y i else (0 : ℂ)) y i‖ < 1 := by
          linarith
        by_cases h0 : C x i (fun y i => if y ∈ X then g y i else 0) T' = 0
        · rw [h0, norm_zero]; positivity
        · obtain ⟨-, hpoly⟩ := hsupp x i _ hgB T' h0
          have h1 := rootRate_of_dExt (m₁ := m₁) (d := d) hN T' hpoly hκ hlam hB
          rw [hX] at h1
          exact (hbd x i T' _ hg').trans h1
      by_cases hse : s = ∅
      · rw [hse, Finset.sum_empty, norm_zero]; positivity
      · obtain ⟨T0, hT0⟩ := Finset.nonempty_iff_ne_empty.2 hse
        have hsing : s = {T0} := by
          refine (Finset.eq_singleton_iff_unique_mem).2 ⟨hT0, fun T1 hT1 => ?_⟩
          exact filter_sitesOf_injective hN
            (((Finset.mem_filter.1 hT1).2).trans ((Finset.mem_filter.1 hT0).2).symm)
        rw [hsing, Finset.sum_singleton]
        exact hone T0 (by rw [hsing]; exact Finset.mem_singleton_self _)
    · simp only [hc, ite_false, norm_zero]; positivity
  · intro g hg x i
    rw [← Finset.sum_fiberwise Finset.univ
      (fun T' : Finset 𝔅 => Finset.univ.filter (· ∈ sitesOf T')) (fun T' => C x i g T')]
    refine Finset.sum_congr rfl fun X _ => ?_
    have hgB : ∑ y, ∑ i, ‖(fun y i => if y ∈ X then g y i else (0 : ℂ)) y i‖ < 1 :=
      lt_of_le_of_lt (hnorm X g) hg
    by_cases hc : (x ∈ X ∧ IsPolymer d ((N₁ * L ^ m₁) * L ^ K) (L ^ (m₁ + 1) * L ^ K) X)
    · simp only [hc, and_self, ite_true]
      refine Finset.sum_congr rfl fun T' hT' => ?_
      have hX : Finset.univ.filter (· ∈ sitesOf T') = X := (Finset.mem_filter.1 hT').2
      refine hloc x i T' _ hgB g hg fun y hy => ?_
      have : y ∈ X := by rw [← hX]; simpa using hy
      simp [this]
    · simp only [hc, ite_false]
      symm
      refine Finset.sum_eq_zero fun T' hT' => ?_
      have hX : Finset.univ.filter (· ∈ sitesOf T') = X := (Finset.mem_filter.1 hT').2
      by_contra h0
      obtain ⟨hroot, hpoly⟩ := hsupp x i g hg T' h0
      apply hc
      refine ⟨?_, ?_⟩
      · rw [← hX]; simpa using mem_sitesOf_of_rootCube_blockIndex T' x hroot
      · rw [← hX]; exact sitesOf_isPolymer hN T' hpoly

/-- The pairing form of the regrouping identity (the shape of the root's sum at one scale): if
`U` regroups `C` as in the last clause of `rootTermFamily_of_cubeFamily`, then
`∑ x, ∑ X, ∑ i, g x i * U x X g i = ∑ x, ∑ i, g x i * ∑ T′, C x i g T′`. -/
theorem pairing_of_regroup
    (C : CTorus d L N₁ m₁ K → Fin N → (CTorus d L N₁ m₁ K → Fin N → ℂ) → Finset 𝔅 → ℂ)
    (U : CTorus d L N₁ m₁ K → Finset (CTorus d L N₁ m₁ K) →
      (CTorus d L N₁ m₁ K → Fin N → ℂ) → (Fin N → ℂ))
    (g : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hv : ∀ x i, ∑ X : Finset (CTorus d L N₁ m₁ K), U x X g i = ∑ T' : Finset 𝔅, C x i g T') :
    ∑ x, ∑ X : Finset (CTorus d L N₁ m₁ K), ∑ i, g x i * U x X g i =
      ∑ x, ∑ i, g x i * ∑ T' : Finset 𝔅, C x i g T' := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, hv]

end Balaban.Fluctuation
