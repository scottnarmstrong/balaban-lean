/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilySetCast
public import Balaban.Fluctuation.LevelLocalCover
public import Balaban.SmallField.LocalGeneratorPoly
public import Balaban.Fluctuation.LocalClassDensityIrrelSupport

/-!
# Specification of the cast local generators of the labels (`LocalClassDensityIrrelSuppSpec`)

* `gsSpecStrong_castLocalB` (core `gsSpecStrong_castLocalB_of_cells`: a union of cells `X`, every
  subset `A ⊆ X`): for a polymer `X` of `𝒟_j`, the local generating set `𝔹_j(X')` of the
  set `X'` of sites of a finer cube torus `(N₁', m₁')`, `N₁' L^{m₁'} = N₁ L^{m₁}`,
  `m₁' ≤ m₀ + m₁`, lying over `X`, and transported by `castG`, satisfies `GsSpecStrong j X`;
* `exists_optimal_chosen`: a polymer has a chosen family and a connected structure attaining
  `d^cov_j` (the premise of `CovSetup` and of the optimal structure, for the family so chosen);
* `covSetup_of_chosen`: a chosen family of a set of `𝒟_j` (`j < K`) in a whole-lattice generating
  set of the top level `K` satisfies `CovSetup`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.GsSpec Balaban.LargeField

section Spec

variable {d L N₁ m₁ : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A union of cells of `𝒟_j` read on a finer cube torus is a union of the `𝒞'_j`-cubes of side
`L^{m₁'} L^j` there (the core of `castLocal_cubeUnion`). -/
theorem castLocal_cubeUnion_of_cells {N₁' m₁' k m₀ j : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)}
    (hcell : ∀ z ∈ X, Localization.box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X) :
    ∀ x' ∈ {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X},
      ∀ y' : CTorus d L N₁' m₁' k,
      fineCubeIdx (L ^ m₁') N₁' L k j (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ k)) =
        fineCubeIdx (L ^ m₁') N₁' L k j (torusCast x' : Torus d (L ^ m₁' * N₁' * L ^ k)) →
      y' ∈ {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X} := by
  intro x' hx' y' hy
  have hcc : N₁' * L ^ m₁' * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [hc]
  have hpos := cellSide_pos (L := L) m₀ m₁ j
  have e : L ^ m₁' * N₁' * L ^ k = (L ^ j * L ^ m₁') * (N₁' * L ^ (k - j)) := by
    have : L ^ k = L ^ j * L ^ (k - j) := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have hv' : ∀ (z : CTorus d L N₁' m₁' k) μ,
      ((torusCast z : Torus d (L ^ m₁' * N₁' * L ^ k)) μ).val = (z μ).val := fun z μ =>
    torusCast_val (by rw [mul_comm (L ^ m₁') N₁']) z μ
  have hv : ∀ (z : CTorus d L N₁' m₁' k) μ,
      ((torusCast z : CTorus d L N₁ m₁ k) μ).val = (z μ).val := fun z μ =>
    torusCast_val hcc z μ
  have hdv : L ^ j * L ^ m₁' ∣ cellSide L m₀ m₁ j := by
    unfold cellSide
    rw [← pow_add]
    exact pow_dvd_pow L (by omega)
  obtain ⟨t, ht⟩ := hdv
  have hq : ∀ μ, (y' μ).val / cellSide L m₀ m₁ j = (x' μ).val / cellSide L m₀ m₁ j := by
    intro μ
    have h1 := congrFun hy μ
    have e1 := blockCoord_val (N := L ^ j * L ^ m₁') (m := N₁' * L ^ (k - j)) e
      ((torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ k)) μ)
    have e2 := blockCoord_val (N := L ^ j * L ^ m₁') (m := N₁' * L ^ (k - j)) e
      ((torusCast x' : Torus d (L ^ m₁' * N₁' * L ^ k)) μ)
    have h3 : (blockCoord (L ^ j * L ^ m₁') (N₁' * L ^ (k - j))
        ((torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ k)) μ)) =
        (blockCoord (L ^ j * L ^ m₁') (N₁' * L ^ (k - j))
        ((torusCast x' : Torus d (L ^ m₁' * N₁' * L ^ k)) μ)) := by
      simpa [fineCubeIdx, blockMap_apply] using h1
    have h2 : (y' μ).val / (L ^ j * L ^ m₁') = (x' μ).val / (L ^ j * L ^ m₁') := by
      rw [← hv' y' μ, ← hv' x' μ, ← e1, ← e2, h3]
    rw [ht, ← Nat.div_div_eq_div_mul (y' μ).val, ← Nat.div_div_eq_div_mul (x' μ).val, h2]
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hcb : cbase (cellSide L m₀ m₁ j) (torusCast y' : CTorus d L N₁ m₁ k) =
      cbase (cellSide L m₀ m₁ j) (torusCast x' : CTorus d L N₁ m₁ k) := by
    funext μ
    simp only [cbase, hv, hq]
  have hz : (torusCast y' : CTorus d L N₁ m₁ k) ∈
      Localization.box (cbase (cellSide L m₀ m₁ j) (torusCast x' : CTorus d L N₁ m₁ k)) (cellSide L m₀ m₁ j) := by
    rw [← hcb]; exact mem_box_cbase hpos _
  exact hcell _ hx' hz

/-- A polymer of `𝒟_j` read on a finer cube torus is a union of the `𝒞'_j`-cubes of side
`L^{m₁'} L^j` there. -/
theorem castLocal_cubeUnion {N₁' m₁' k m₀ j : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) :
    ∀ x' ∈ {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X},
      ∀ y' : CTorus d L N₁' m₁' k,
      fineCubeIdx (L ^ m₁') N₁' L k j (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ k)) =
        fineCubeIdx (L ^ m₁') N₁' L k j (torusCast x' : Torus d (L ^ m₁' * N₁' * L ^ k)) →
      y' ∈ {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X} :=
  castLocal_cubeUnion_of_cells hc hN hm hjk (cell_subset_of_isPolyDom hN hjk hX)

theorem castG_noAbove {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] {k j : ℕ} (h : N₀' = N₀)
    {G : GeneratingSet d L N₀' k ϱ} (hG : ∀ i, j < i → G.Ω i = ∅) :
    ∀ i, j < i → (castG h G).Ω i = ∅ := by
  intro i hi
  ext z
  rw [mem_castG_Ω, hG i hi]
  simp

/-- **The strong specification of the cast local generator of a union of cells, on every subset**
(the core of `gsSpecStrong_castLocalB`): for `X` a union of cells of `𝒟_j` and `A ⊆ X`,
`GsSpecStrong j A` holds for `castG hc (𝔹_j(X'))`. -/
theorem gsSpecStrong_castLocalB_of_cells {N₁' m₁' k m₀ j : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X A : Set (CTorus d L N₁ m₁ k)}
    (hcell : ∀ z ∈ X, Localization.box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X)
    (hA : A ⊆ X) (hs : ϱ ≤ minSep L (L ^ m₁')) :
    GsSpecStrong j hjk A (castG hc (localB j hjk
      {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X} hs)) := by
  have hcc : N₁' * L ^ m₁' * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [hc]
  have hcore := gsSpecCore_localB (hj := hjk) (hsep := hs) hj1
    (castLocal_cubeUnion_of_cells hc hN hm hjk hcell)
  have hrt : ∀ z : CTorus d L N₁ m₁ k, z ∈ A →
      (torusCast z : CTorus d L N₁' m₁' k) ∈
        {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X} := fun z hz => by
    show (torusCast (torusCast z : CTorus d L N₁' m₁' k) : CTorus d L N₁ m₁ k) ∈ X
    rw [torusCast_torusCast hcc.symm]
    exact hA hz
  refine GsSpecCore.toStrong hj1 hjk
    { subset := fun z hz => ?_
      noAbove := castG_noAbove hc hcore.noAbove
      topLayer := fun z hz => ?_ }
  · rw [Finset.mem_coe, mem_castG_Ω]
    exact hcore.subset (hrt z hz)
  · have h := hcore.topLayer _ (hrt z hz)
    rw [GeneratingSet.mem_layer] at h ⊢
    rw [mem_castG_Ω, mem_castG_Ω]
    exact h

/-- **The strong specification of the cast local generator.** -/
theorem gsSpecStrong_castLocalB {N₁' m₁' k m₀ j : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X)
    (hs : ϱ ≤ minSep L (L ^ m₁')) :
    GsSpecStrong j hjk X (castG hc (localB j hjk
      {x' : CTorus d L N₁' m₁' k | (torusCast x' : CTorus d L N₁ m₁ k) ∈ X} hs)) :=
  gsSpecStrong_castLocalB_of_cells hc hN hm hj1 hjk (cell_subset_of_isPolyDom hN hjk hX)
    subset_rfl hs

end Spec

section Cov

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **A polymer has an admissible connected structure for every chosen family**: all its sites
with all its bonds. -/
theorem exists_admissible_of_isPolyDom {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsPolyDom m₀ j X) :
    ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨𝒦, hch⟩, hcon⟩ := hX
  have hpos : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  refine ⟨𝒦, Finset.univ.filter (· ∈ X),
    Finset.univ.filter fun p : CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K =>
      p.1 ∈ X ∧ p.2 ∈ X ∧ Nbr p.1 p.2, hch, ⟨⟨x₀, by simpa using hx₀⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp
  · intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ (hcon x hx y hy)
    left
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hab
  · intro x hx
    simpa using hx
  · intro b hb
    refine ⟨b, ?_, mem_box_self b hpos⟩
    have := (hch.1 b hb).2 (mem_box_self b hpos)
    simpa using this

/-- **The optimal chosen family of a polymer exists**: a chosen family `𝒦` of `X` and a connected
structure in `X` meeting every cube of `𝒦` with `bondCost = d^cov_j(X)`. -/
theorem exists_optimal_chosen {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ j X) :
    ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W ∧
      bondCost (scaleW L m₀ m₁ j) E = treeLenCovOne m₀ j X :=
  treeLenCovOne_attained m₀ j X (exists_admissible_of_isPolyDom hX)

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **`CovSetup` of a chosen family** of a set of `𝒟_j`, `j < K`, in a whole-lattice generating set
of the top level `K`. -/
theorem covSetup_of_chosen (hG : IsLevel G K) {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K)
    (hL : 2 ≤ L) {X 𝒦 : Set (CTorus d L N₁ m₁ K)} (hch : ChosenOne m₀ j X 𝒦) :
    CovSetup G m₀ j X 𝒦 where
  hU := layerUnion_of_isLevel hG m₀
  hN := hN
  hjK := hj
  chosen := hch
  nest := by
    intro b hb
    have hs0 := cellSide_pos (L := L) m₀ m₁ K
    have hsj : L * cellSide L m₀ m₁ j ≤ cellSide L m₀ m₁ K := by
      unfold cellSide
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (NeZero.pos L) (by omega)
    refine ⟨cbase (cellSide L m₀ m₁ K) b, aligned_cbase b, ?_,
      fun y _ => Finset.mem_coe.2 (hG.mem_layer y)⟩
    rintro x ⟨u, hu, rfl⟩
    refine ⟨(fun μ => (b μ).val % cellSide L m₀ m₁ K) + u, fun μ => ?_, ?_⟩
    · have h1 : (b μ).val % cellSide L m₀ m₁ K < cellSide L m₀ m₁ K := Nat.mod_lt _ hs0
      have h2 : 2 * cellSide L m₀ m₁ K ≤ L * cellSide L m₀ m₁ K := Nat.mul_le_mul_right _ hL
      have := hu μ
      simp only [Pi.add_apply]
      omega
    · rw [natT_add, cbase_eq_sub]
      abel

end Cov

end Balaban.Fluctuation
