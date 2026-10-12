/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.GsSpecStrong

/-!
# Class polymers are unions of `𝒞_j`-cubes; the minimal generating set on polymers

* `isPolyDom_blockUnion`: a set with a chosen family of `π'_j`-cubes (`ChosenOne`, in particular
  every polymer of `𝒟_j`, P1 (2.26)) is a union of `j`-blocks (`cellSide L m₀ m₁ j = L ^ (j + m₀ + m₁)`
  is a multiple of `L ^ j`, `L_pow_dvd_cellSide`);
* `torusCast`, `castG`: the identification of the fine torus `Torus d (1 * (N₁ L ^ m₁) * L ^ k)` of
  P3's minimal set (`M1 = 1`, `N₁' = N₁ L ^ m₁`, `q = k`) with `CTorus d L N₁ m₁ k`;
* `polyGS`: the minimal generating set `𝔹_j(X)` (P3 (4.4)-(4.6)) of a set `X` of `CTorus`;
* `gsSpecCore_polyGS`, `gsSpecStrong_polyGS`: for a polymer `X ∈ 𝒟_j` it satisfies the core and
  the strong specification.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField Finset

section Block

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
theorem L_pow_dvd_cellSide (m₀ j : ℕ) : L ^ j ∣ cellSide L m₀ m₁ j :=
  pow_dvd_pow L (by omega)

/-- **A set with a chosen family of `π'_j`-cubes is a union of `j`-blocks**: if `x ∈ X` and `y`
lies in the `j`-block of `x` (`cbase (L ^ j) y = cbase (L ^ j) x`), then `y ∈ X`.  The aligned
box `box b (L a)`, `a = cellSide L m₀ m₁ j`, has base and side divisible by `L ^ j ∣ a`. -/
theorem isPolyDom_blockUnion {m₀ j : ℕ} (hj : j ≤ K) {X : Set (CTorus d L N₁ m₁ K)}
    (h : ∃ 𝒦, ChosenOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j X 𝒦)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X) {y : CTorus d L N₁ m₁ K}
    (hy : cbase (L ^ j) y = cbase (L ^ j) x) : y ∈ X := by
  obtain ⟨𝒦, hK, hcov⟩ := h
  obtain ⟨b, hb, w, hw, rfl⟩ := hcov x hx
  obtain ⟨hba, hbX⟩ := hK b hb
  have hApos : 0 < L ^ j := Nat.pos_of_ne_zero (by have := NeZero.ne L; positivity)
  have hAn : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hj) _
  have hAa := L_pow_dvd_cellSide (L := L) m₀ (m₁ := m₁) j
  have hbA : Aligned (L ^ j) b := fun μ => by
    rw [← Nat.mod_mod_of_dvd _ hAa, hba μ]; simp
  have hcb := cbase_add hAn hbA w
  obtain ⟨v, hv, hyv⟩ := mem_box_cbase hApos y
  refine hbX ⟨fun μ => (w μ - w μ % L ^ j) + v μ, fun μ => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hAa
    have hwt : w μ < L ^ j * (L * t) := by
      have := hw μ
      rw [ht] at this
      calc w μ < L * (L ^ j * t) := this
        _ = L ^ j * (L * t) := by ring
    have h1 : w μ / L ^ j < L * t := (Nat.div_lt_iff_lt_mul hApos).2 (by rwa [mul_comm] at hwt)
    have h2 : w μ - w μ % L ^ j = L ^ j * (w μ / L ^ j) := by
      have := Nat.div_add_mod (w μ) (L ^ j)
      omega
    have h3 := hv μ
    show w μ - w μ % L ^ j + v μ < _
    rw [h2]
    calc L ^ j * (w μ / L ^ j) + v μ < L ^ j * (w μ / L ^ j) + L ^ j := by omega
      _ = L ^ j * (w μ / L ^ j + 1) := by ring
      _ ≤ L ^ j * (L * t) := Nat.mul_le_mul_left _ h1
      _ = L * cellSide L m₀ m₁ j := by rw [ht]; ring
  · rw [hyv, hy, hcb, add_assoc, ← natT_add]
    rfl

end Block


section Cast

variable {d L k : ℕ} [NeZero L]

/-- The identification of two tori with equal side (`ZMod` coordinates through their values). -/
def torusCast {a b : ℕ} (y : Torus d a) : Torus d b := fun μ => (((y μ).val : ℕ) : ZMod b)

theorem torusCast_torusCast {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (y : Torus d a) :
    (torusCast (torusCast y : Torus d b) : Torus d a) = y := by
  subst h
  funext μ
  simp [torusCast]

theorem torusCast_val {a b : ℕ} [NeZero a] (h : a = b) (y : Torus d a) (μ : Fin d) :
    ((torusCast y : Torus d b) μ).val = (y μ).val := by
  subst h
  simp [torusCast]

/-- Transport of a generating set along an equality of coarse sides `N₀' = N₀`. -/
def castG {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] {ϱ : ℝ} (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) : GeneratingSet d L N₀ k ϱ := h ▸ G

theorem mem_castG_Ω {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] {ϱ : ℝ} (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (i : ℕ) (x : Torus d (N₀ * L ^ k)) :
    x ∈ (castG h G).Ω i ↔
      (torusCast x : Torus d (N₀' * L ^ k)) ∈ G.Ω i := by
  subst h
  have : (torusCast x : Torus d (N₀' * L ^ k)) = x := by
    funext μ; simp [torusCast]
  simp [castG, this]

end Cast

section MinimalPoly

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- The set `X` of `CTorus` as a finite set of sites of P3's fine torus
`Torus d (1 * (N₁ L ^ m₁) * L ^ k)` (`M1 = 1`, `N₁' = N₁ L ^ m₁`, `q = k`). -/
noncomputable def polyFinset (X : Set (CTorus d L N₁ m₁ k)) :
    Finset (Torus d (1 * (N₁ * L ^ m₁) * L ^ k)) :=
  Finset.univ.filter fun y => (torusCast y : CTorus d L N₁ m₁ k) ∈ X

/-- **`T2`: a class polymer is a union of `𝒞_j`-cubes in the form of `minimalGenSet_core`.** -/
theorem polyFinset_cubeUnion {m₀ j : ℕ} (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : ∃ 𝒦, ChosenOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) m₀ j X 𝒦) :
    ∀ x ∈ polyFinset X, ∀ y, fineCubeIdx 1 (N₁ * L ^ m₁) L k j y = fineCubeIdx 1 (N₁ * L ^ m₁) L k j x →
      y ∈ polyFinset X := by
  intro x hx y hxy
  classical
  simp only [polyFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  refine isPolyDom_blockUnion hjk hX hx ?_
  funext μ
  have hμ := congrFun hxy μ
  unfold fineCubeIdx at hμ
  have hℓ : 1 * (N₁ * L ^ m₁) * L ^ k = (L ^ j * 1) * ((N₁ * L ^ m₁) * L ^ (k - j)) := by
    rw [Nat.mul_one, Nat.one_mul]; exact side_eq hjk
  have e := congrArg ZMod.val hμ
  simp only [blockMap_apply] at e
  rw [blockCoord_val hℓ, blockCoord_val hℓ] at e
  simp only [Nat.mul_one] at e
  have hc : 1 * (N₁ * L ^ m₁) * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [Nat.one_mul]
  simp only [cbase]
  rw [torusCast_val hc, torusCast_val hc, e]


/-- **The minimal generating set `𝔹_j(X)`** (P3 (4.4)-(4.6)) of a set `X` of `CTorus d L N₁ m₁ k`,
as a generating set of the class torus: `minimalGenSet` with `M1 = 1`, `N₁' = N₁ L ^ m₁`, `q = k`
of the finite set `polyFinset X` (`Set.toFinset` on the finite torus), transported along
`1 * (N₁ L ^ m₁) = N₁ L ^ m₁`; the separation constant is `minSep L 1 = 5 L`. -/
noncomputable def polyGS {j : ℕ} (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    GeneratingSet d L (N₁ * L ^ m₁) k (minSep L 1) :=
  castG (Nat.one_mul (N₁ * L ^ m₁)) (minimalGenSet (M1 := 1) (N₁ := N₁ * L ^ m₁) hjk (polyFinset X))

/-- **`T3` (core).**  For a polymer `X ∈ 𝒟_j`, `1 ≤ j ≤ k`, the minimal generating set satisfies
the core specification: `X ⊆ Ω₁`, no layer above `j`, `X` in the top layer `j`. -/
theorem gsSpecCore_polyGS {m₀ j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom m₀ j X) : GsSpecCore j X (polyGS hjk X) := by
  have hc : 1 * (N₁ * L ^ m₁) * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [Nat.one_mul]
  have hcore := minimalGenSet_core (M1 := 1) (N₁ := N₁ * L ^ m₁) (L := L) (q := k) hj1 hjk
    (polyFinset X) (polyFinset_cubeUnion hjk hX.2.1)
  have hmem : ∀ z : CTorus d L N₁ m₁ k, z ∈ X →
      (torusCast z : Torus d (1 * (N₁ * L ^ m₁) * L ^ k)) ∈ polyFinset X := fun z hz => by
    classical
    simp only [polyFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [torusCast_torusCast hc.symm]
  refine ⟨fun z hz => ?_, fun i hi => ?_, fun z hz => ?_⟩
  · have := hcore.subset (Finset.mem_coe.2 (hmem z hz))
    exact Finset.mem_coe.2 ((mem_castG_Ω _ _ _ _).2 (Finset.mem_coe.1 this))
  · ext z
    simp only [polyGS, mem_castG_Ω, Finset.notMem_empty, iff_false]
    have := hcore.noAbove i hi
    rw [this]; exact Finset.notMem_empty _
  · have := hcore.topLayer _ (Finset.mem_coe.2 (hmem z hz))
    rw [GeneratingSet.mem_layer] at this ⊢
    exact ⟨(mem_castG_Ω _ _ _ _).2 this.1, fun h => this.2 ((mem_castG_Ω _ _ _ _).1 h)⟩

/-- **`T3` (strong).**  For a polymer `X ∈ 𝒟_j`, `1 ≤ j ≤ k`, the minimal generating set satisfies
the strong specification (`layerEq` and `blkEq` follow from the core, `GsSpecCore.toStrong`). -/
theorem gsSpecStrong_polyGS {m₀ j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom m₀ j X) : GsSpecStrong j hjk X (polyGS hjk X) :=
  (gsSpecCore_polyGS hj1 hjk hX).toStrong hj1 hjk

end MinimalPoly

end Balaban.SmallField.GsSpec
