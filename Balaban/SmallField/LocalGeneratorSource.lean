/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.GsSpecPolyEqv
public import Balaban.Multiscale.WeakenSep
public import Balaban.LargeField.Background.LocalGen

/-!
# The local generating set `𝔹_j(X)` of a polymer on the step torus

`localB j hj X hsep` is the minimal generating set of P3 (4.4)-(4.6) (Definition II.2.2) of a
set `X` of sites of the step torus `CTorus d L N₁ m₁ k`, with cubes of side `M₁ L ^ n`,
`M₁ = L ^ m₁`: the landed `minimalGenSetAt` on the fine torus `Torus d (L ^ m₁ * N₁ * L ^ k)`,
transported along `L ^ m₁ * N₁ = N₁ * L ^ m₁`.

* `mem_localB_Ω_top`, `mem_localB_Ω_succ`, `localB_Ω_of_gt`: the layers;
* `localB_Ω_top_eq` : the top layer of a union of `L ^ m₁ L ^ j`-cubes is the set itself;
* `gsSpecStrong_localB`: the specification of `GsSpecStrong`;
* `localB_dataSites_range`: every data site is within `11 L ^ m₁ L ^ j + 1` of `X`.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField Finset

section LocalB

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The local generating set `𝔹_j(X)` of P3 (4.4)-(4.6) on the step torus.**  The landed
`minimalGenSetAt` (cubes of side `L ^ m₁ L ^ n`, `M₁ = L ^ m₁`) of the set of fine sites lying over
`X`, transported along `L ^ m₁ * N₁ = N₁ * L ^ m₁`; the separation is any `ϱ ≤ 5 L L ^ m₁`. -/
noncomputable def localB (j : ℕ) (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) : GeneratingSet d L (N₁ * L ^ m₁) k ϱ :=
  castG (mul_comm (L ^ m₁) N₁)
    (minimalGenSetAt (M1 := L ^ m₁) (N₁ := N₁) (q := k) hj
      (Finset.univ.filter fun y : Torus d (L ^ m₁ * N₁ * L ^ k) =>
        (torusCast y : CTorus d L N₁ m₁ k) ∈ X) hsep)

variable {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)}

theorem torusCast_torusCast' (y : Torus d (L ^ m₁ * N₁ * L ^ k)) :
    (torusCast (torusCast y : Torus d (N₁ * L ^ m₁ * L ^ k)) : Torus d (L ^ m₁ * N₁ * L ^ k)) = y :=
  torusCast_torusCast (by rw [mul_comm (L ^ m₁) N₁]) y

theorem torusCast_torusCast'' (y : CTorus d L N₁ m₁ k) :
    (torusCast (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) : CTorus d L N₁ m₁ k) = y :=
  torusCast_torusCast (by rw [mul_comm (L ^ m₁) N₁]) y

/-- **The top layer** (P3 (4.4)): `x ∈ Ω_j(𝔹_j(X))` iff the whole `𝒞_j`-cube of `x` (side
`L ^ m₁ L ^ j`) lies in `X`. -/
theorem mem_localB_Ω_top (x : CTorus d L N₁ m₁ k) :
    x ∈ (localB j hj X hsep).Ω j ↔
      ∀ y : CTorus d L N₁ m₁ k,
        fineCubeIdx (L ^ m₁) N₁ L k j (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) =
          fineCubeIdx (L ^ m₁) N₁ L k j (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) → y ∈ X := by
  classical
  unfold localB
  rw [mem_castG_Ω, minimalGenSetAt_Ω, minLayer_self, mem_cubeInterior]
  constructor
  · intro h y hy
    have := h (torusCast y) hy
    simpa [Finset.mem_filter, torusCast_torusCast''] using this
  · intro h y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h _ (by rwa [torusCast_torusCast'])

/-- **The recursion** (P3 (4.5)-(4.6)): for `n < j`, `Ω_n` is the union of the `𝒞_n`-cubes
(side `L ^ m₁ L ^ n`) at cube-index distance `≤ 5 L` from a site of `Ω_{n+1}`. -/
theorem mem_localB_Ω_succ {n : ℕ} (hn : n < j) (x : CTorus d L N₁ m₁ k) :
    x ∈ (localB j hj X hsep).Ω n ↔
      ∃ y : CTorus d L N₁ m₁ k, y ∈ (localB j hj X hsep).Ω (n + 1) ∧
        supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
          (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) ≤ 5 * L := by
  classical
  unfold localB
  simp only [mem_castG_Ω, minimalGenSetAt_Ω]
  rw [minLayer_of_lt _ hn, mem_nearStep]
  constructor
  · rintro ⟨y, hy, hd⟩
    exact ⟨torusCast y, by rwa [torusCast_torusCast'], by rwa [torusCast_torusCast']⟩
  · rintro ⟨y, hy, hd⟩
    exact ⟨torusCast y, hy, hd⟩

/-- No layer above `j`: `Ω_n(𝔹_j(X)) = ∅` for `n > j`. -/
theorem localB_Ω_of_gt {n : ℕ} (hn : j < n) : (localB j hj X hsep).Ω n = ∅ := by
  classical
  ext x
  simp only [Finset.notMem_empty, iff_false]
  unfold localB
  rw [mem_castG_Ω, minimalGenSetAt_Ω, minLayer_of_gt _ hn]
  exact Finset.notMem_empty _

/-- **The top layer of a union of `𝒞_j`-cubes is the set itself**: if `X` contains the whole
`𝒞_j`-cube (side `L ^ m₁ L ^ j`) of each of its sites, then `Ω_j(𝔹_j(X)) = X`. -/
theorem localB_Ω_top_eq
    (hX : ∀ x ∈ X, ∀ y : CTorus d L N₁ m₁ k,
      fineCubeIdx (L ^ m₁) N₁ L k j (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) =
        fineCubeIdx (L ^ m₁) N₁ L k j (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) → y ∈ X) :
    ((localB j hj X hsep).Ω j : Set (CTorus d L N₁ m₁ k)) = X := by
  ext x
  rw [Finset.mem_coe, mem_localB_Ω_top]
  constructor
  · intro h
    exact h x rfl
  · intro hx y hy
    exact hX x hx y hy

/-- **The specification of `𝔹_j(X)`**: for `1 ≤ j ≤ k` and a union `X` of `𝒞_j`-cubes, `X ⊆ Ω₁`,
no layer lies above `j`, `X` is in the top layer `j`, and the layer indices and `j`-blocks on `X`
are those of the whole-level set (`GsSpecStrong`). -/
theorem gsSpecCore_localB (hj1 : 1 ≤ j)
    (hX : ∀ x ∈ X, ∀ y : CTorus d L N₁ m₁ k,
      fineCubeIdx (L ^ m₁) N₁ L k j (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) =
        fineCubeIdx (L ^ m₁) N₁ L k j (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) → y ∈ X) :
    GsSpecCore j X (localB j hj X hsep) where
  subset := fun z hz => by
    have h1 : z ∈ (localB j hj X hsep).Ω j := by
      have := localB_Ω_top_eq (hj := hj) (hsep := hsep) hX
      rw [← Finset.mem_coe, this]; exact hz
    exact Finset.mem_coe.2 ((localB j hj X hsep).Ω_antitone le_rfl hj1 (by omega) h1)
  noAbove := fun i hi => localB_Ω_of_gt hi
  topLayer := fun z hz => by
    have h1 : z ∈ (localB j hj X hsep).Ω j := by
      have := localB_Ω_top_eq (hj := hj) (hsep := hsep) hX
      rw [← Finset.mem_coe, this]; exact hz
    refine ((localB j hj X hsep).mem_layer).2 ⟨h1, ?_⟩
    rw [localB_Ω_of_gt (Nat.lt_succ_self j)]
    exact Finset.notMem_empty _

theorem gsSpecStrong_localB (hj1 : 1 ≤ j)
    (hX : ∀ x ∈ X, ∀ y : CTorus d L N₁ m₁ k,
      fineCubeIdx (L ^ m₁) N₁ L k j (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) =
        fineCubeIdx (L ^ m₁) N₁ L k j (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) → y ∈ X) :
    GsSpecStrong j hj X (localB j hj X hsep) :=
  (gsSpecCore_localB hj1 hX).toStrong hj1 hj

/-- Data sites after transport: a data site of the transported set is within `r` of a point of `X'`
(read on the other torus) if the data sites of the original are. -/
theorem dataSites_castG_range {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (X' : Set (Torus d (N₀' * L ^ k))) (r : ℕ)
    (hG : ∀ x ∈ dataSites G, ∃ y ∈ X', supDist x y ≤ r) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites (castG h G)) :
    ∃ y ∈ X', supDist x (torusCast y : Torus d (N₀ * L ^ k)) ≤ r := by
  subst h
  obtain ⟨y, hy, hd⟩ := hG x (by simpa [castG] using hx)
  have e : (torusCast y : Torus d (N₀' * L ^ k)) = y := by
    funext μ; simp [torusCast]
  exact ⟨y, hy, by rw [e]; exact hd⟩

/-- **The support bound**: every data site of `𝔹_j(X)` is within sup-distance
`11 L ^ m₁ L ^ j + 1` of a site of `X` (transport of `localGen_dataSites_range`). -/
theorem localB_dataSites_range (hL : 2 ≤ L) {x : CTorus d L N₁ m₁ k}
    (hx : x ∈ dataSites (localB j hj X hsep)) :
    ∃ y ∈ X, supDist x y ≤ 11 * L ^ m₁ * L ^ j + 1 := by
  classical
  obtain ⟨y, hy, hd⟩ := dataSites_castG_range (mul_comm (L ^ m₁) N₁) _
    ((Finset.univ.filter fun y : Torus d (L ^ m₁ * N₁ * L ^ k) =>
        (torusCast y : CTorus d L N₁ m₁ k) ∈ X : Finset _) : Set _) (11 * L ^ m₁ * L ^ j + 1)
    (fun x hx => by
      obtain ⟨y, hy, hd⟩ := localGen_dataSites_range_weakenSep hL hj _ hsep hx
      exact ⟨y, Finset.mem_coe.2 hy, hd⟩) hx
  exact ⟨_, by simpa using hy, hd⟩

end LocalB

end Balaban.SmallField.GsSpec
