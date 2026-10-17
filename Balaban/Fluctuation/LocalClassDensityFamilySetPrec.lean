/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorSource
public import Balaban.Fluctuation.ClassOldLocalGk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local sets `𝔹_j(X) ≺ 𝔹_k(Z)` and the collar (`LocalClassDensityFamilySetPrec`)

Let `Z` be the set of sites whose `𝒞_k`-cube is at cube-index distance `≤ 5 L` from a site of `X`.
For `j ≤ k` every layer `n ≤ j` of `𝔹_k(Z)` contains the `𝒞_n`-cube-index neighbourhood of radius
`5 L` of the layer `n` of `𝔹_j(X)`.  Hence `𝔹_j(X) ≺ 𝔹_k(Z)` and the collar of `𝔹_j(X)` lies in
`Ω₁(𝔹_k(Z))`: these are the fields `hq`, `colj` of `BgSetting` for the ambient set `𝔹_k(Z)`.

* `idxDist_succ_le`: cube-index distance `≤ 5 L` at level `n` is `≤ 5 L` at level `n + 1`;
* `localB_layer_nbhd`: the layerwise statement;
* `localB_precedes_localB`, `localB_collar_subset`: `hq` and `colj`;
* `Zset_dist_le`: the sites of `Z` are within `(5 L + 1) L^{m₁} L^k` of `X`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.LargeField Finset

section Idx

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- Cube-index distance `≤ 5 L` at level `n` implies the same at level `n + 1`. -/
theorem idxDist_succ_le (hL : 2 ≤ L) {n : ℕ} (hn : n + 1 ≤ q) (a b : Torus d (M1 * N₁ * L ^ q))
    (h : supDist (fineCubeIdx M1 N₁ L q n a) (fineCubeIdx M1 N₁ L q n b) ≤ 5 * L) :
    supDist (fineCubeIdx M1 N₁ L q (n + 1) a) (fineCubeIdx M1 N₁ L q (n + 1) b) ≤ 5 * L := by
  have h1 := supDist_le_of_mem_nearStep (d := d) (M1 := M1) (N₁ := N₁) (by omega : n ≤ q) h
  have hP : M1 * N₁ * L ^ q = (L ^ (n + 1) * M1) * (N₁ * L ^ (q - (n + 1))) :=
    fine_eq_cube hn
  have h2 := supDist_blockMap_le (d := d) hP a b
  unfold fineCubeIdx
  refine h2.trans ?_
  set m := M1 * L ^ n with hm
  have hm0 : 0 < m :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M1)) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
  have hPm : L ^ (n + 1) * M1 = L * m := by rw [hm]; ring
  rw [hPm]
  have hLm : 0 < L * m := Nat.mul_pos (by omega) hm0
  have : (supDist a b + L * m - 1) / (L * m) ≤ 6 := by
    have h3 : supDist a b + L * m - 1 < 7 * (L * m) := by
      have : (5 * L + 1) * m = 5 * (L * m) + m := by ring
      have hmLm : m ≤ L * m := Nat.le_mul_of_pos_left m (by omega)
      omega
    have := (Nat.div_lt_iff_lt_mul hLm).2 (by linarith : supDist a b + L * m - 1 < 7 * (L * m))
    omega
  omega

end Idx

section Layers

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ₁ ϱ₂ : ℝ}

omit [NeZero L] [NeZero N₁] in
theorem supDist_torusCast_val {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (x y : Torus d a) :
    supDist (torusCast x : Torus d b) (torusCast y) = supDist x y := by
  subst h
  have e : ∀ z : Torus d a, (torusCast z : Torus d a) = z := fun z => by
    funext μ; simp [torusCast]
  rw [e, e]

omit [NeZero L] [NeZero N₁] in
theorem supDist_le_one_of_adj {n : ℕ} [NeZero n] {x y : Torus d n}
    (h : ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ x = y + Pi.single μ 1) : supDist y x ≤ 1 := by
  classical
  obtain ⟨μ, h | h⟩ := h
  · refine supDist_le_iff.2 fun ν => ?_
    rw [cycNorm_le_iff]
    by_cases hν : ν = μ
    · exact ⟨1, by simp, by simp [h, hν]⟩
    · exact ⟨0, by simp, by simp [h, hν]⟩
  · refine supDist_le_iff.2 fun ν => ?_
    rw [cycNorm_le_iff]
    by_cases hν : ν = μ
    · exact ⟨-1, by simp, by simp [h, hν]⟩
    · exact ⟨0, by simp, by simp [h, hν]⟩

/-- **The layers of `𝔹_j(X)` and `𝔹_{k'}(Z)`.**  Let `j ≤ k' ≤ k`, and suppose every site whose
`𝒞_{k'}`-cube is at cube-index distance `≤ 5 L` from a site of `X` lies in `Ω_{k'}(𝔹_{k'}(Z))`.
Then for `n ≤ j` every site at level-`n` cube-index distance `≤ 5 L` from a site of
`Ω_n(𝔹_j(X))` lies in `Ω_n(𝔹_{k'}(Z))`. -/
theorem localB_layer_nbhd (hL : 2 ≤ L) {j k' : ℕ} (hjk : j ≤ k') (hk' : k' ≤ k) (hj : j ≤ k)
    {X Z : Set (CTorus d L N₁ m₁ k)} {h₁ : ϱ₁ ≤ minSep L (L ^ m₁)}
    {h₂ : ϱ₂ ≤ minSep L (L ^ m₁)}
    (hZ : ∀ x : CTorus d L N₁ m₁ k, (∃ y ∈ X,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L) →
      x ∈ (localB k' hk' Z h₂).Ω k') :
    ∀ t n : ℕ, n + t = j → ∀ x : CTorus d L N₁ m₁ k,
      (∃ y ∈ (localB j hj X h₁).Ω n,
        supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
          (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L) →
      x ∈ (localB k' hk' Z h₂).Ω n := by
  intro t
  induction t with
  | zero =>
    intro n hn x ⟨y, hy, hd⟩
    obtain rfl : n = j := by omega
    have hyX : y ∈ X := (mem_localB_Ω_top y).1 hy y rfl
    by_cases hjk' : n = k'
    · subst hjk'
      exact hZ x ⟨y, hyX, hd⟩
    · have hlt : n < k' := by omega
      rw [mem_localB_Ω_succ hlt]
      refine ⟨y, ?_, hd⟩
      have hyk : y ∈ (localB k' hk' Z h₂).Ω k' := hZ y ⟨y, hyX, by rw [supDist_self]; omega⟩
      exact (localB k' hk' Z h₂).Ω_antitone (by omega) (by omega) (by omega) hyk
  | succ t ih =>
    intro n hn x ⟨y, hy, hd⟩
    have hnj : n < j := by omega
    rw [mem_localB_Ω_succ hnj] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    have hyk : y ∈ (localB k' hk' Z h₂).Ω (n + 1) :=
      ih (n + 1) (by omega) y ⟨w, hw, idxDist_succ_le hL (by omega) _ _ hyw⟩
    rw [mem_localB_Ω_succ (by omega : n < k')]
    exact ⟨y, hyk, hd⟩

/-- **`𝔹_j(X) ≺ 𝔹_{k'}(Z)`** (the field `hq` of `BgSetting` for the ambient set `𝔹_{k'}(Z)`). -/
theorem localB_precedes_localB (hL : 2 ≤ L) {j k' : ℕ} (hjk : j ≤ k') (hk' : k' ≤ k) (hj : j ≤ k)
    {X Z : Set (CTorus d L N₁ m₁ k)} {h₁ : ϱ₁ ≤ minSep L (L ^ m₁)}
    {h₂ : ϱ₂ ≤ minSep L (L ^ m₁)}
    (hZ : ∀ x : CTorus d L N₁ m₁ k, (∃ y ∈ X,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L) →
      x ∈ (localB k' hk' Z h₂).Ω k') :
    Precedes (localB j hj X h₁) (localB k' hk' Z h₂) := by
  intro i _ _ x hx
  by_cases hij : i ≤ j
  · exact localB_layer_nbhd hL hjk hk' hj hZ (j - i) i (by omega) x
      ⟨x, hx, by rw [supDist_self]; omega⟩
  · rw [localB_Ω_of_gt (by omega : j < i)] at hx
    exact absurd hx (Finset.notMem_empty _)

/-- **The collar of `𝔹_j(X)` lies in `Ω₁(𝔹_{k'}(Z))`** (the field `colj` of `BgSetting`). -/
theorem localB_collar_subset (hL : 2 ≤ L) {j k' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k') (hk' : k' ≤ k)
    (hj : j ≤ k) {X Z : Set (CTorus d L N₁ m₁ k)} {h₁ : ϱ₁ ≤ minSep L (L ^ m₁)}
    {h₂ : ϱ₂ ≤ minSep L (L ^ m₁)}
    (hZ : ∀ x : CTorus d L N₁ m₁ k, (∃ y ∈ X,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L) →
      x ∈ (localB k' hk' Z h₂).Ω k') :
    ∀ z ∈ collar (localB j hj X h₁), z ∈ (localB k' hk' Z h₂).Ω 1 := by
  intro z hz
  obtain ⟨-, x0, hx0, hadj⟩ := (mem_collar _).1 hz
  refine localB_layer_nbhd hL hjk hk' hj hZ (j - 1) 1 (by omega) z ⟨x0, hx0, ?_⟩
  have hc : N₁ * L ^ m₁ * L ^ k = L ^ m₁ * N₁ * L ^ k := by rw [mul_comm (L ^ m₁) N₁]
  have h1 : supDist (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ k)) (torusCast x0) ≤ 1 := by
    rw [supDist_torusCast_val hc]
    exact supDist_le_one_of_adj hadj
  have hP : (L ^ m₁) * N₁ * L ^ k = (L ^ 1 * L ^ m₁) * (N₁ * L ^ (k - 1)) :=
    fine_eq_cube (by omega : 1 ≤ k)
  have hD : 1 ≤ L ^ 1 * L ^ m₁ :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
  have h2 := supDist_blockMap_le_one (d := d) hP (D := 1) hD _ _ h1
  unfold fineCubeIdx
  omega

end Layers

section Zset

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ₂ : ℝ}

/-- **The hypothesis `hZ` for the cube neighbourhood.**  If `Z` is the set of sites at
`𝒞_{k'}`-cube-index distance `≤ 5 L` from a site of `X` then every site at that distance from `X`
lies in `Ω_{k'}(𝔹_{k'}(Z))` (a union of `𝒞_{k'}`-cubes is its own top layer). -/
theorem Zset_hZ {k' : ℕ} (hk' : k' ≤ k) {X Z : Set (CTorus d L N₁ m₁ k)}
    (hZ : ∀ z : CTorus d L N₁ m₁ k, z ∈ Z ↔ ∃ y ∈ X,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L)
    {h₂ : ϱ₂ ≤ minSep L (L ^ m₁)} :
    ∀ x : CTorus d L N₁ m₁ k, (∃ y ∈ X,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L) →
      x ∈ (localB k' hk' Z h₂).Ω k' := by
  intro x hx
  rw [mem_localB_Ω_top]
  intro y hy
  rw [hZ]
  obtain ⟨w, hwX, hw⟩ := hx
  exact ⟨w, hwX, by rw [hy]; exact hw⟩

/-- **The sites of `Z` are near `X`**: within sup-distance `(5 L + 1) L^{m₁} L^{k'}`. -/
theorem Zset_dist_le {k' : ℕ} (hk' : k' ≤ k) {X Z : Set (CTorus d L N₁ m₁ k)}
    (hZ : ∀ z : CTorus d L N₁ m₁ k, z ∈ Z ↔ ∃ y ∈ X,
      supDist (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ k)))
        (fineCubeIdx (L ^ m₁) N₁ L k k' (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L) :
    ∀ z ∈ Z, ∃ w ∈ X, supDist z w ≤ (5 * L + 1) * (L ^ m₁ * L ^ k') := by
  intro z hz
  obtain ⟨w, hwX, hw⟩ := (hZ z).1 hz
  refine ⟨w, hwX, ?_⟩
  have hc : N₁ * L ^ m₁ * L ^ k = L ^ m₁ * N₁ * L ^ k := by rw [mul_comm (L ^ m₁) N₁]
  have h1 := supDist_le_of_mem_nearStep (d := d) (M1 := L ^ m₁) (N₁ := N₁) (L := L) (q := k)
    hk' hw
  rwa [supDist_torusCast_val hc] at h1

end Zset

end Balaban.Fluctuation
