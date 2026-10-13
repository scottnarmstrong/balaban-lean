/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorSource
public import Balaban.SmallField.GsSpecPolyClass

/-!
# Covariance of the local generating set under the lattice symmetries

The layers of `localB j hj X hsep` are built from the cubes of side `L ^ m₁ L ^ n`, `n ≤ j`.
A permutation of the step torus that preserves the distances of the cube indices at all these
scales maps `localB j hj X` to `localB j hj (r '' X)` layer by layer (`localB_Ω_image_of_cubeIso`).
The translations, reflections and coordinate exchanges of `symGroupBy s`, `L ^ (n + m₁) ∣ s` for
`n ≤ j`, are such permutations (`localB_Ω_image_of_mem_symGroupBy`), in particular those of
`pavingSymGroup L m₀ j` (`pavingGS_localB`, the clause `pavingGS` of `SFTermClausesStrong` at
`Tm.gs j X = localB j hj X hsep`) and the translations by multiples of the cube side
(`localB_Ω_image_transBy`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField Finset

section Cov

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

omit [NeZero L] [NeZero N₁] in
theorem side_eq_localCube {n : ℕ} (hn : n ≤ k) :
    N₁ * L ^ m₁ * L ^ k = (L ^ n * L ^ m₁) * (N₁ * L ^ (k - n)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

/-- The cube index of a site of the step torus, read coordinatewise as a block coordinate. -/
theorem fineCubeIdx_torusCast_coord {n : ℕ} (x : CTorus d L N₁ m₁ k) (ν : Fin d) :
    fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) ν =
      blockCoord (L ^ n * L ^ m₁) (N₁ * L ^ (k - n)) (x ν) := by
  have hc : N₁ * L ^ m₁ * L ^ k = L ^ m₁ * N₁ * L ^ k := by rw [mul_comm (L ^ m₁) N₁]
  simp only [fineCubeIdx, blockMap_apply, blockCoord, torusCast_val hc, mul_comm (L ^ n)]

theorem localCube_transBy {j s : ℕ} (hs : ∀ n ≤ j, L ^ (n + m₁) ∣ s) (hj : j ≤ k) (μ : Fin d)
    {n : ℕ} (hn : n ≤ j) (x y : CTorus d L N₁ m₁ k) :
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ y) :
          Torus d (L ^ m₁ * N₁ * L ^ k))) =
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) := by
  have hcoord : ∀ (x : CTorus d L N₁ m₁ k) ν,
      fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)) ν =
      fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) ν +
        (if ν = μ then ((s / (L ^ n * L ^ m₁) : ℕ) : ZMod (N₁ * L ^ (k - n))) else 0) := by
    intro x ν
    rw [fineCubeIdx_torusCast_coord, fineCubeIdx_torusCast_coord]
    simp only [transBy, Equiv.coe_addRight, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    by_cases h : ν = μ
    · simp only [h, ite_true, nsmul_eq_mul, mul_one]
      exact blockCoord_add_nat (side_eq_localCube (hn.trans hj))
        (by rw [← pow_add]; exact hs n hn) _
    · simp [h, blockCoord]
  refine Finset.sup_congr rfl fun ν _ => ?_
  rw [hcoord, hcoord]
  congr 1
  ring

theorem localCube_flipBy {j s : ℕ} (hs : ∀ n ≤ j, L ^ (n + m₁) ∣ s) (hj : j ≤ k) (μ : Fin d)
    {n : ℕ} (hn : n ≤ j) (x y : CTorus d L N₁ m₁ k) :
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ y) :
          Torus d (L ^ m₁ * N₁ * L ^ k))) =
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) := by
  have hcoord : ∀ (x : CTorus d L N₁ m₁ k) ν,
      fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)) ν =
      if ν = μ then ((s / (L ^ n * L ^ m₁) : ℕ) : ZMod (N₁ * L ^ (k - n))) - 1 -
        fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) ν
      else fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) ν := by
    intro x ν
    rw [fineCubeIdx_torusCast_coord]
    simp only [flipBy, Equiv.coe_fn_mk, Function.update_apply]
    by_cases h : ν = μ
    · simp only [h, ite_true]
      rw [fineCubeIdx_torusCast_coord]
      exact blockCoord_flip (side_eq_localCube (hn.trans hj))
        (by rw [← pow_add]; exact hs n hn) _
    · simp only [h, ite_false]
      rw [fineCubeIdx_torusCast_coord]
  refine Finset.sup_congr rfl fun ν _ => ?_
  rw [hcoord, hcoord]
  by_cases h : ν = μ
  · simp only [h, ite_true]
    rw [cycNorm_sub_comm]
    congr 1
    ring
  · simp [h]

theorem localCube_swapJ (μ ν : Fin d)
    {n : ℕ} (x y : CTorus d L N₁ m₁ k) :
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν y) :
          Torus d (L ^ m₁ * N₁ * L ^ k))) =
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) := by
  have hcoord : ∀ (x : CTorus d L N₁ m₁ k) κ,
      fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)) κ =
      fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k))
        (Equiv.swap μ ν κ) := by
    intro x κ
    rw [fineCubeIdx_torusCast_coord, fineCubeIdx_torusCast_coord]
    rfl
  refine le_antisymm (supDist_le_iff.2 fun κ => ?_) (supDist_le_iff.2 fun κ => ?_)
  · rw [hcoord, hcoord]; exact cycNorm_le_supDist _ _ _
  · have h := cycNorm_le_supDist
      (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x) :
          Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν y) :
          Torus d (L ^ m₁ * N₁ * L ^ k))) (Equiv.swap μ ν κ)
    rw [hcoord, hcoord, Equiv.swap_apply_self] at h
    exact h

/-- The group `symGroupBy s` preserves the distances of the cube indices (cubes of side
`L ^ m₁ L ^ n`) at all scales `n ≤ j`, when `L ^ (n + m₁) ∣ s` for `n ≤ j ≤ k`. -/
theorem localCube_of_mem_symGroupBy {j s : ℕ} (hs : ∀ n ≤ j, L ^ (n + m₁) ∣ s) (hj : j ≤ k)
    {g : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hg : g ∈ symGroupBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s) {n : ℕ} (hn : n ≤ j)
    (x y : CTorus d L N₁ m₁ k) :
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (g x) : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (g y) : Torus d (L ^ m₁ * N₁ * L ^ k))) =
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) := by
  unfold symGroupBy at hg
  have key : ∀ g : Equiv.Perm (CTorus d L N₁ m₁ k),
      g ∈ Subgroup.closure ({g | ∃ μ, g = transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ} ∪
        {g | ∃ μ, g = flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ} ∪
        {g | ∃ μ ν, g = swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν}) →
      ∀ x y : CTorus d L N₁ m₁ k,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (g x) : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (g y) : Torus d (L ^ m₁ * N₁ * L ^ k))) =
      supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with (⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩
      · exact fun x y => localCube_transBy hs hj μ hn x y
      · exact fun x y => localCube_flipBy hs hj μ hn x y
      · exact fun x y => localCube_swapJ μ ν x y
    | one => exact fun x y => rfl
    | mul a b _ _ h1 h2 =>
      intro x y
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, h2]
    | inv a _ h =>
      intro x y
      have := h (a⁻¹ x) (a⁻¹ y)
      simpa using this.symm
  exact key g hg x y

variable {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- **Layers of `𝔹_j` under an isometry of the cube indices.**  If `r` preserves the distances
of the cube indices (cubes of side `L ^ m₁ L ^ n`) at all scales `n ≤ j`, then
`x ∈ Ω_n(𝔹_j(r X)) ↔ r⁻¹ x ∈ Ω_n(𝔹_j(X))` for all `n`. -/
theorem mem_localB_Ω_image_iff_of_cubeIso {r : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hr : ∀ n ≤ j, ∀ x y : CTorus d L N₁ m₁ k,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (r x) : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (r y) : Torus d (L ^ m₁ * N₁ * L ^ k))) =
      supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))))
    (n : ℕ) (x : CTorus d L N₁ m₁ k) :
    x ∈ (localB j hj (r '' X) hsep).Ω n ↔ r.symm x ∈ (localB j hj X hsep).Ω n := by
  have hiff : ∀ n ≤ j, ∀ x y : CTorus d L N₁ m₁ k,
      fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (r x) : Torus d (L ^ m₁ * N₁ * L ^ k)) =
        fineCubeIdx (L ^ m₁) N₁ L k n (torusCast (r y) : Torus d (L ^ m₁ * N₁ * L ^ k)) ↔
      fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) =
        fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) :=
    fun n hn x y => by rw [← supDist_eq_zero, hr n hn, supDist_eq_zero]
  by_cases hnj : n ≤ j
  · obtain ⟨t, ht⟩ : ∃ t, n + t = j := ⟨j - n, by omega⟩
    induction t generalizing n x with
    | zero =>
      have hn : n = j := by omega
      subst hn
      rw [mem_localB_Ω_top, mem_localB_Ω_top]
      constructor
      · intro h y hy
        have hy' : fineCubeIdx (L ^ m₁) N₁ L k n
            (torusCast (r y) : Torus d (L ^ m₁ * N₁ * L ^ k)) =
            fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) := by
          simpa using (hiff n le_rfl y (r.symm x)).2 hy
        exact r.injective.mem_set_image.1 (h (r y) hy')
      · intro h y hy
        have hy' : fineCubeIdx (L ^ m₁) N₁ L k n
            (torusCast (r (r.symm y)) : Torus d (L ^ m₁ * N₁ * L ^ k)) =
            fineCubeIdx (L ^ m₁) N₁ L k n
              (torusCast (r (r.symm x)) : Torus d (L ^ m₁ * N₁ * L ^ k)) := by
          simpa using hy
        exact ⟨r.symm y, h _ ((hiff n le_rfl _ _).1 hy'), by simp⟩
    | succ t ih =>
      have hlt : n < j := by omega
      rw [mem_localB_Ω_succ hlt, mem_localB_Ω_succ hlt]
      constructor
      · rintro ⟨y, hy, hd⟩
        refine ⟨r.symm y, (ih (n + 1) y (by omega) (by omega)).1 hy, ?_⟩
        have e := hr n hnj (r.symm x) (r.symm y)
        simp only [Equiv.apply_symm_apply] at e
        rw [← e]
        exact hd
      · rintro ⟨y, hy, hd⟩
        refine ⟨r y, (ih (n + 1) (r y) (by omega) (by omega)).2 (by simpa using hy), ?_⟩
        have e := hr n hnj (r.symm x) y
        simp only [Equiv.apply_symm_apply] at e
        rw [e]
        exact hd
  · have h1 : j < n := by omega
    rw [localB_Ω_of_gt h1, localB_Ω_of_gt h1]
    simp

/-- **T1: covariance of the layers of `𝔹_j`** under the translations, reflections and coordinate
exchanges of `symGroupBy s`, `L ^ (n + m₁) ∣ s` for `n ≤ j`: `Ω_n(𝔹_j(r X)) = r Ω_n(𝔹_j(X))`. -/
theorem localB_Ω_image_of_mem_symGroupBy {s : ℕ} (hs : ∀ n ≤ j, L ^ (n + m₁) ∣ s)
    {r : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hr : r ∈ symGroupBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s) (n : ℕ) :
    (((localB j hj (r '' X) hsep).Ω n : Finset (CTorus d L N₁ m₁ k)) :
        Set (CTorus d L N₁ m₁ k)) =
      r '' (((localB j hj X hsep).Ω n : Finset (CTorus d L N₁ m₁ k)) :
        Set (CTorus d L N₁ m₁ k)) := by
  ext z
  rw [Set.mem_image_equiv]
  simp only [Finset.mem_coe]
  exact mem_localB_Ω_image_iff_of_cubeIso (fun n hn x y => localCube_of_mem_symGroupBy hs hj hr hn x y) n z

/-- **T1 for translations**: the translation by `s • e_μ`, `L ^ (n + m₁) ∣ s` for `n ≤ j`. -/
theorem localB_Ω_image_transBy {s : ℕ} (hs : ∀ n ≤ j, L ^ (n + m₁) ∣ s) (μ : Fin d) (n : ℕ) :
    (((localB j hj (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ '' X) hsep).Ω n :
        Finset (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k)) =
      transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ ''
        (((localB j hj X hsep).Ω n : Finset (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k)) :=
  localB_Ω_image_of_mem_symGroupBy hs (Subgroup.subset_closure (Or.inl (Or.inl ⟨μ, rfl⟩))) n

/-- **`pavingGS` for the local sets `𝔹_j(X)`** (T2): `Ω_n(𝔹_j(r X)) = r Ω_n(𝔹_j(X))` for `r` in
the paving group of scale `j`, in exactly the form of the clause `pavingGS` of
`SFTermClausesStrong` at `Tm.gs j X = localB j hj X hsep`. -/
theorem pavingGS_localB {m₀ : ℕ} {r : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j) (n : ℕ) :
    (((localB j hj (r '' X) hsep).Ω n : Finset (CTorus d L N₁ m₁ k)) :
        Set (CTorus d L N₁ m₁ k)) =
      r '' (((localB j hj X hsep).Ω n : Finset (CTorus d L N₁ m₁ k)) :
        Set (CTorus d L N₁ m₁ k)) :=
  localB_Ω_image_of_mem_symGroupBy (s := cellSide L m₀ m₁ j)
    (fun n hn => pow_dvd_pow L (by omega)) hr n

end Cov
