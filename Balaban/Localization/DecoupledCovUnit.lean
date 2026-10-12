/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledIdent

/-!
# The unit lattice of I-4c: `Q_k` and `P` for the generating set

LOCALIZATION.md §3.4 consumes the unit lattice through the typing data `IsUnitLatticeB`. Here the
actual block average of the project is built and the data is proved.

* `UnitTorus`, `unitBlock`: the unit lattice `T^{(k)}_1` (blocks of side `L ^ k` of the fine torus
  `CTorus d L N₁ m₁ (k + 1)`) and the block of a fine site; `unitBlock1` the `L`-block of a unit
  point;
* `unitPts G`: the unit points of `Λ`, i.e. the blocks contained in the top layer `Ω_{k+1}`
  (a union of `(k+1)`-blocks, `layer_of_unitBlock`);
* `unitQ G`: the block average `Q_k : Ω₁ → Λ` with entries `(L ^ k)^{-d/2}` (so `Q Q* = 1`);
  `unitP G`: the projection onto the constants of the `L`-blocks of `Λ`;
* `unitQ_blk1`, `unitQ_blk2`: `Q* Q = P_k` and `Q* P Q = P_{k+1}` (the block matrices of the
  x-variant operator);
* `isUnitLatticeB_unit : IsUnitLatticeB G (unitQ G) (unitP G)`, and `unitQ_real`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The unit lattice `T^{(k)}_1`: the blocks of side `L ^ k` of the fine torus
`CTorus d L N₁ m₁ (k + 1)`. -/
abbrev UnitTorus (d L N₁ m₁ k : ℕ) : Type := Torus d ((N₁ * L ^ m₁) * L ^ (k + 1 - k))

/-- The `L ^ k`-block of a fine site, a point of the unit lattice. -/
def unitBlock (x : CTorus d L N₁ m₁ (k + 1)) : UnitTorus d L N₁ m₁ k :=
  blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) x

omit [NeZero N₁] [NeZero L] in
theorem unitBlock_side : (N₁ * L ^ m₁) * L ^ (k + 1) = L ^ k * ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) :=
  side_eq (N₀ := N₁ * L ^ m₁) (L := L) (k := k + 1) (j := k) (by omega)

theorem unitBlock_eq_iff (x x' : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock x = unitBlock x' ↔ ∀ i, (x i).val / L ^ k = (x' i).val / L ^ k := by
  unfold unitBlock
  constructor
  · intro h i
    have h1 := congrFun h i
    rw [blockMap_apply, blockMap_apply] at h1
    have h2 := congrArg ZMod.val h1
    rwa [blockCoord_val unitBlock_side, blockCoord_val unitBlock_side] at h2
  · intro h
    funext i
    apply ZMod.val_injective
    rw [blockMap_apply, blockMap_apply, blockCoord_val unitBlock_side,
      blockCoord_val unitBlock_side]
    exact h i

theorem jBlock_eq_of_unitBlock_eq {x x' : CTorus d L N₁ m₁ (k + 1)}
    (h : unitBlock x = unitBlock x') :
    jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x' := by
  rw [unitBlock_eq_iff] at h
  unfold jBlock
  funext i
  apply ZMod.val_injective
  have hs : (N₁ * L ^ m₁) * L ^ (k + 1) = L ^ (k + 1) * ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) :=
    side_eq (N₀ := N₁ * L ^ m₁) (L := L) (k := k + 1) (j := k + 1) le_rfl
  have key : ∀ z : ℕ, z / L ^ (k + 1) = z / L ^ k / L := fun z => by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [blockMap_apply, blockMap_apply, blockCoord_val hs, blockCoord_val hs, key, key, h i]

section Unit

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

open Classical in
/-- The unit points of `Λ`: the blocks of side `L ^ k` inside the top layer `Ω_{k+1}`. -/
noncomputable def unitPts : Finset (UnitTorus d L N₁ m₁ k) :=
  Finset.univ.filter fun b => ∃ x ∈ G.layer (k + 1), unitBlock x = b

theorem mem_unitPts {b : UnitTorus d L N₁ m₁ k} :
    b ∈ unitPts G ↔ ∃ x ∈ G.layer (k + 1), unitBlock x = b := by
  classical
  simp [unitPts]

/-- The layer `k + 1` is a union of `(k+1)`-blocks. -/
theorem layer_top_of_jBlock {x x' : CTorus d L N₁ m₁ (k + 1)}
    (h : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x')
    (hx : x ∈ G.layer (k + 1)) : x' ∈ G.layer (k + 1) := by
  have hU := G.blockUnion (k + 1) (by omega) le_rfl x x' h
  rw [G.mem_layer] at hx ⊢
  refine ⟨hU.1 hx.1, ?_⟩
  rw [G.top]; simp

theorem layer_of_unitBlock {x x' : CTorus d L N₁ m₁ (k + 1)} (h : unitBlock x = unitBlock x')
    (hx : x ∈ G.layer (k + 1)) : x' ∈ G.layer (k + 1) :=
  layer_top_of_jBlock G (jBlock_eq_of_unitBlock_eq h) hx

/-- The `L`-block of a unit point, a point of the next coarser lattice. -/
def unitBlock1 (b : UnitTorus d L N₁ m₁ k) : Torus d ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) :=
  blockMap (L ^ 1) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) b

omit [NeZero N₁] [NeZero L] in
theorem unitBlock1_side : (N₁ * L ^ m₁) * L ^ (k + 1 - k) =
    L ^ 1 * ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) := by
  have h1 : k + 1 - k = 1 := by omega
  have h2 : k + 1 - (k + 1) = 0 := by omega
  rw [h1, h2]; ring

theorem unitBlock1_unitBlock (x : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock1 (unitBlock x) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x := by
  unfold unitBlock1 unitBlock jBlock
  have := blockMap_pow_add (d := d) (L := L) (j := k) (k := 1)
    (m₁ := (N₁ * L ^ m₁) * L ^ (k + 1 - k)) (m₂ := (N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1)))
    (ℓ := (N₁ * L ^ m₁) * L ^ (k + 1)) unitBlock_side unitBlock1_side x
  rw [this]

theorem card_unit_fibre {b : UnitTorus d L N₁ m₁ k} (hb : b ∈ unitPts G) :
    ((G.Ω 1).filter fun y => unitBlock y = b).card = (L ^ k) ^ d := by
  classical
  obtain ⟨x, hx, hxb⟩ := (mem_unitPts G).1 hb
  have : ((G.Ω 1).filter fun y => unitBlock y = b) =
      (blockFibre (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) b :
        Finset (CTorus d L N₁ m₁ (k + 1))) := by
    ext y
    simp only [Finset.mem_filter, mem_blockFibre]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hy : y ∈ G.layer (k + 1) := layer_of_unitBlock G (hxb.trans h.symm) hx
      exact G.layer_subset (by omega) le_rfl hy
  rw [this]
  exact card_blockFibre (N := L ^ k) unitBlock_side b

/-- The block average `Q_k` on the top layer, with the normalisation `Q Q* = 1`
(entries `(L ^ k)^{-d/2}`), as a matrix from `Ω₁` to the unit points of `Λ`. -/
noncomputable def unitQ : Matrix (unitPts G) (G.Ω 1) ℂ := fun b y =>
  if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = (b : UnitTorus d L N₁ m₁ k) then
    ((Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) : ℝ) : ℂ) else 0

/-- The projection onto the constants on the blocks of side `L` of the unit lattice. -/
noncomputable def unitP : Matrix (unitPts G) (unitPts G) ℂ := fun b b' =>
  if unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) then
    (((((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) else 0

theorem unitQ_mul_self (y y' : G.Ω 1) :
    ((unitQ G)ᵀ * unitQ G) y y' =
      if (unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G ∧
          unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) = unitBlock (y : CTorus d L N₁ m₁ (k + 1)))
        then ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ : ℝ) else 0 := by
  classical
  have hc : (0 : ℝ) ≤ (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, unitQ]
  by_cases h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
  · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), h⟩ : unitPts G)]
    · by_cases h' : unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) = unitBlock (y : CTorus d L N₁ m₁ (k + 1))
      · simp only [h, h', ↓reduceIte, and_self]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
      · simp [h, h']
    · intro b _ hb
      have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
        intro e; apply hb; exact Subtype.ext e.symm
      simp [this]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro b _
      have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
        intro e; exact h (e ▸ b.2)
      simp [this]

theorem Pk_apply (y y' : G.Ω 1) : Pk G y y' =
    ((if (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) ∧
        (y' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) then
      (if blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y : CTorus d L N₁ m₁ (k + 1)) =
          blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y' : CTorus d L N₁ m₁ (k + 1)) then
        ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ : ℝ) else 0) else 0 : ℝ) : ℂ) := rfl

theorem Pk1_apply (y y' : G.Ω 1) : Pk1 G y y' =
    ((if (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) ∧
        (y' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) then
      (if blockMap (L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1)))
          (y : CTorus d L N₁ m₁ (k + 1)) =
          blockMap (L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1)))
          (y' : CTorus d L N₁ m₁ (k + 1)) then
        ((((L ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ : ℝ) else 0) else 0 : ℝ) : ℂ) := rfl

theorem unitQ_blk1 : (unitQ G)ᵀ * unitQ G = Pk G := by
  classical
  ext y y'
  rw [unitQ_mul_self, Pk_apply]
  by_cases hA : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G ∧
      unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) = unitBlock (y : CTorus d L N₁ m₁ (k + 1))
  · obtain ⟨hy, hyy⟩ := hA
    obtain ⟨x, hx, hxy⟩ := (mem_unitPts G).1 hy
    have hyl : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
      layer_of_unitBlock G hxy hx
    have hy'l : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
      layer_of_unitBlock G (hxy.trans hyy.symm) hx
    have heq : blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y : CTorus d L N₁ m₁ (k + 1)) =
        blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y' : CTorus d L N₁ m₁ (k + 1)) :=
      hyy.symm
    simp [hy, hyy, hyl, hy'l, heq]
  · simp only [hA, ↓reduceIte]
    by_cases hl : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) ∧
        (y' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1)
    · by_cases heq : blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y : CTorus d L N₁ m₁ (k + 1)) =
          blockMap (L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) (y' : CTorus d L N₁ m₁ (k + 1))
      · exfalso
        apply hA
        exact ⟨(mem_unitPts G).2 ⟨_, hl.1, rfl⟩, heq.symm⟩
      · simp [hl, heq]
    · simp [hl]

theorem unitBlock_mem_iff (y : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock y ∈ unitPts G ↔ y ∈ G.layer (k + 1) := by
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := (mem_unitPts G).1 h
    exact layer_of_unitBlock G hxy hx
  · intro h; exact (mem_unitPts G).2 ⟨y, h, rfl⟩

theorem unitQ_P_Q_apply (y y' : G.Ω 1) :
    ((unitQ G)ᵀ * unitP G * unitQ G) y y' =
      if (unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G ∧
          unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G ∧
          unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) =
            unitBlock1 (unitBlock (y' : CTorus d L N₁ m₁ (k + 1))))
        then (((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * (((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  have hc : (0 : ℝ) ≤ (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  set q : ℝ := Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) with hq
  have hqq : q * q = (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := Real.mul_self_sqrt hc
  -- first factor
  have h1 : ∀ b' : unitPts G, ((unitQ G)ᵀ * unitP G) y b' =
      if h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G then
        (q : ℂ) * unitP G ⟨_, h⟩ b' else 0 := by
    intro b'
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, unitQ]
    by_cases h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
    · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), h⟩ : unitPts G)]
      · simp [h, hq]
      · intro b _ hb
        have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; apply hb; exact Subtype.ext e.symm
        simp [this]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro b _
        have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; exact h (e ▸ b.2)
        simp [this]
  rw [Matrix.mul_apply]
  simp only [h1]
  by_cases hy : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
  · simp only [hy, ↓reduceDIte]
    by_cases hy' : unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
    · rw [Finset.sum_eq_single (⟨unitBlock (y' : CTorus d L N₁ m₁ (k + 1)), hy'⟩ : unitPts G)]
      · by_cases hP : unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) =
            unitBlock1 (unitBlock (y' : CTorus d L N₁ m₁ (k + 1)))
        · simp only [unitP, unitQ, hP, hy', ↓reduceIte, and_self]
          rw [← hq, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
          congr 1
          calc q * ((((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹) * q = (q * q) * ((((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹) := by ring
            _ = _ := by rw [hqq]
        · simp [unitP, unitQ, hP, hy']
      · intro b _ hb
        have : unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; apply hb; exact Subtype.ext e.symm
        simp [unitQ, this]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [Finset.sum_eq_zero]
      · simp [hy']
      · intro b _
        have : unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; exact hy' (e ▸ b.2)
        simp [unitQ, this]
  · simp [hy]

theorem unitBlock1_eq_iff (y y' : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock1 (unitBlock y) = unitBlock1 (unitBlock y') ↔
      blockMap (L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) y =
        blockMap (L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) y' := by
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock]
  rfl

theorem unitQ_blk2 : (unitQ G)ᵀ * unitP G * unitQ G = Pk1 G := by
  classical
  ext y y'
  rw [unitQ_P_Q_apply, Pk1_apply]
  have hcoef : (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * (((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹ =
      (((L ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [← mul_inv, ← mul_pow]
    congr 2
    push_cast; ring
  by_cases hA : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G ∧
      unitBlock (y' : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G ∧
      unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) =
        unitBlock1 (unitBlock (y' : CTorus d L N₁ m₁ (k + 1)))
  · obtain ⟨hy, hy', hP⟩ := hA
    have hyl := (unitBlock_mem_iff G _).1 hy
    have hy'l := (unitBlock_mem_iff G _).1 hy'
    have hb := (unitBlock1_eq_iff _ _).1 hP
    simp only [hy, hy', hP, and_self, ↓reduceIte, hyl, hy'l, hb, hcoef]
  · simp only [hA, ↓reduceIte]
    by_cases hl : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) ∧
        (y' : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1)
    · by_cases hb : blockMap (L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1)))
          (y : CTorus d L N₁ m₁ (k + 1)) =
          blockMap (L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1)))
          (y' : CTorus d L N₁ m₁ (k + 1))
      · exfalso
        exact hA ⟨(unitBlock_mem_iff G _).2 hl.1, (unitBlock_mem_iff G _).2 hl.2,
          (unitBlock1_eq_iff _ _).2 hb⟩
      · simp [hl, hb]
    · simp [hl]

theorem sum_unit_fibre {b : UnitTorus d L N₁ m₁ k} (hb : b ∈ unitPts G) :
    ∑ y : G.Ω 1, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b then (1 : ℝ) else 0) =
      ((L ^ k : ℕ) : ℝ) ^ d := by
  classical
  have h1 : ∑ y : G.Ω 1, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b then (1 : ℝ) else 0) =
      ∑ y ∈ G.Ω 1, (if unitBlock y = b then (1 : ℝ) else 0) :=
    Finset.sum_coe_sort (G.Ω 1) (fun y => if unitBlock y = b then (1 : ℝ) else 0)
  rw [h1, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [card_unit_fibre G hb]
  push_cast; rfl

theorem unitQ_layer : ∀ (b : unitPts G) (y : G.Ω 1), unitQ G b y ≠ 0 →
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) := by
  intro b y h
  by_contra hy
  apply h
  have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
    intro e
    exact hy ((unitBlock_mem_iff G _).1 (e ▸ b.2))
  simp [unitQ, this]

theorem unitQ_contr (f : G.Ω 1 → ℂ) : Green.sqNorm (unitQ G *ᵥ f) ≤ Green.sqNorm f := by
  classical
  have hc : (0 : ℝ) ≤ (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  set q : ℝ := Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) with hq
  have hqq : q * q = (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := Real.mul_self_sqrt hc
  have hn : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) := by
      have := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L)); exact_mod_cast this
    positivity
  have hqn : q * q * (((L ^ k : ℕ) : ℝ) ^ d) = 1 := by rw [hqq]; field_simp
  -- pointwise bound
  have hpt : ∀ b : unitPts G, ‖(unitQ G *ᵥ f) b‖ ^ 2 ≤
      ∑ y : G.Ω 1, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then ‖f y‖ ^ 2 else 0) := by
    intro b
    set S : Finset (G.Ω 1) := Finset.univ.filter fun y => unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1
      with hS
    have hcard : (S.card : ℝ) = ((L ^ k : ℕ) : ℝ) ^ d := by
      have := sum_unit_fibre G b.2
      rw [Finset.sum_boole] at this
      exact this
    have hQf : (unitQ G *ᵥ f) b = (q : ℂ) * ∑ y ∈ S, f y := by
      simp only [Matrix.mulVec, dotProduct, unitQ, hS, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp [hq]
    rw [hQf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    have h1 : ‖∑ y ∈ S, f y‖ ^ 2 ≤ (S.card : ℝ) * ∑ y ∈ S, ‖f y‖ ^ 2 := by
      calc ‖∑ y ∈ S, f y‖ ^ 2 ≤ (∑ y ∈ S, ‖f y‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ (S.card : ℝ) * ∑ y ∈ S, ‖f y‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    calc q ^ 2 * ‖∑ y ∈ S, f y‖ ^ 2 ≤ q ^ 2 * ((S.card : ℝ) * ∑ y ∈ S, ‖f y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (q * q * (S.card : ℝ)) * ∑ y ∈ S, ‖f y‖ ^ 2 := by ring
      _ = ∑ y ∈ S, ‖f y‖ ^ 2 := by rw [hcard, hqn, one_mul]
      _ = _ := by rw [hS, Finset.sum_filter]
  calc Green.sqNorm (unitQ G *ᵥ f) = ∑ b : unitPts G, ‖(unitQ G *ᵥ f) b‖ ^ 2 := rfl
    _ ≤ ∑ b : unitPts G, ∑ y : G.Ω 1,
          (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then ‖f y‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = ∑ y : G.Ω 1, ∑ b : unitPts G,
          (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then ‖f y‖ ^ 2 else 0) :=
        Finset.sum_comm
    _ ≤ ∑ y : G.Ω 1, ‖f y‖ ^ 2 := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases h : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
        · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), h⟩ : unitPts G)]
          · simp
          · intro b _ hb
            have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
              intro e; apply hb; exact Subtype.ext e.symm
            simp [this]
          · intro hh; exact absurd (Finset.mem_univ _) hh
        · rw [Finset.sum_eq_zero]
          · positivity
          · intro b _
            have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
              intro e; exact h (e ▸ b.2)
            simp [this]
    _ = Green.sqNorm f := rfl

theorem unitQ_contrT (h : unitPts G → ℂ) : Green.sqNorm ((unitQ G)ᵀ *ᵥ h) ≤ Green.sqNorm h := by
  classical
  have hc : (0 : ℝ) ≤ (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  set q : ℝ := Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) with hq
  have hqq : q * q = (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := Real.mul_self_sqrt hc
  have hn : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) := by
      have := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L)); exact_mod_cast this
    positivity
  have hqn : q * q * (((L ^ k : ℕ) : ℝ) ^ d) = 1 := by rw [hqq]; field_simp
  have hpt : ∀ y : G.Ω 1, ‖((unitQ G)ᵀ *ᵥ h) y‖ ^ 2 =
      ∑ b : unitPts G, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then
        (q * q) * ‖h b‖ ^ 2 else 0) := by
    intro y
    have e : ((unitQ G)ᵀ *ᵥ h) y = ∑ b : unitPts G, unitQ G b y * h b := by
      simp [Matrix.mulVec, dotProduct]
    rw [e]
    by_cases hy : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ∈ unitPts G
    · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), hy⟩ : unitPts G)]
      · rw [Finset.sum_eq_single (⟨unitBlock (y : CTorus d L N₁ m₁ (k + 1)), hy⟩ : unitPts G)]
        · simp only [unitQ, ↓reduceIte, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.sqrt_nonneg _)]
          rw [mul_pow, ← hq, sq]
        · intro b _ hb
          have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
            intro e; apply hb; exact Subtype.ext e.symm
          simp [this]
        · intro hh; exact absurd (Finset.mem_univ _) hh
      · intro b _ hb
        have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; apply hb; exact Subtype.ext e.symm
        simp [unitQ, this]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · simp
      · intro b _
        have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; exact hy (e ▸ b.2)
        simp [this]
      · intro b _
        have : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
          intro e; exact hy (e ▸ b.2)
        simp [unitQ, this]
  calc Green.sqNorm ((unitQ G)ᵀ *ᵥ h) = ∑ y : G.Ω 1, ‖((unitQ G)ᵀ *ᵥ h) y‖ ^ 2 := rfl
    _ = ∑ y : G.Ω 1, ∑ b : unitPts G, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then
          (q * q) * ‖h b‖ ^ 2 else 0) := Finset.sum_congr rfl fun y _ => hpt y
    _ = ∑ b : unitPts G, ∑ y : G.Ω 1, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then
          (q * q) * ‖h b‖ ^ 2 else 0) := Finset.sum_comm
    _ = ∑ b : unitPts G, ‖h b‖ ^ 2 := by
        refine Finset.sum_congr rfl fun b _ => ?_
        have := sum_unit_fibre G b.2
        calc ∑ y : G.Ω 1, (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then
              (q * q) * ‖h b‖ ^ 2 else 0) =
            ((q * q) * ‖h b‖ ^ 2) * ∑ y : G.Ω 1,
              (if unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b.1 then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              split_ifs <;> simp
          _ = ‖h b‖ ^ 2 := by rw [this]; nlinarith [hqn]
    _ ≤ Green.sqNorm h := le_of_eq rfl

theorem unitBlock_surj (b : UnitTorus d L N₁ m₁ k) : ∃ x, unitBlock x = b := by
  have h := card_blockFibre (d := d) (N := L ^ k) (ℓ := (N₁ * L ^ m₁) * L ^ (k + 1))
    (m := (N₁ * L ^ m₁) * L ^ (k + 1 - k)) unitBlock_side b
  have hpos : 0 < (L ^ k) ^ d := pow_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) _
  rw [← h] at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
  exact ⟨x, (mem_blockFibre.1 hx)⟩

theorem mem_unitPts_of_unitBlock1_eq {b b' : UnitTorus d L N₁ m₁ k} (hb : b ∈ unitPts G)
    (h : unitBlock1 b' = unitBlock1 b) : b' ∈ unitPts G := by
  obtain ⟨x, hx, rfl⟩ := (mem_unitPts G).1 hb
  obtain ⟨x', rfl⟩ := unitBlock_surj (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) b'
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock] at h
  exact (mem_unitPts G).2 ⟨x', layer_top_of_jBlock G h.symm hx, rfl⟩

theorem card_unitBlock1_fibre {b : UnitTorus d L N₁ m₁ k} (hb : b ∈ unitPts G) :
    (unitPts G).filter (fun b' => unitBlock1 b' = unitBlock1 b) =
      (blockFibre (L ^ 1) ((N₁ * L ^ m₁) * L ^ (k + 1 - (k + 1))) (unitBlock1 b) :
        Finset (UnitTorus d L N₁ m₁ k)) := by
  ext b'
  simp only [Finset.mem_filter, mem_blockFibre]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨mem_unitPts_of_unitBlock1_eq G hb h, h⟩

theorem sum_unitBlock1_fibre (b : unitPts G) :
    ∑ b' : unitPts G, (if unitBlock1 (b' : UnitTorus d L N₁ m₁ k) = unitBlock1 (b : UnitTorus d L N₁ m₁ k)
      then (1 : ℝ) else 0) = ((L ^ 1 : ℕ) : ℝ) ^ d := by
  classical
  have h1 : ∑ b' : unitPts G, (if unitBlock1 (b' : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) then (1 : ℝ) else 0) =
      ∑ b' ∈ unitPts G, (if unitBlock1 b' = unitBlock1 (b : UnitTorus d L N₁ m₁ k)
        then (1 : ℝ) else 0) :=
    Finset.sum_coe_sort (unitPts G) (fun b' => if unitBlock1 b' = unitBlock1 (b : UnitTorus d L N₁ m₁ k)
        then (1 : ℝ) else 0)
  rw [h1, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [card_unitBlock1_fibre G b.2, card_blockFibre (N := L ^ 1) unitBlock1_side]
  push_cast; rfl

theorem unitP_herm : (unitP G)ᴴ = unitP G := by
  ext b b'
  simp only [Matrix.conjTranspose_apply, unitP]
  by_cases h : unitBlock1 (b' : UnitTorus d L N₁ m₁ k) = unitBlock1 (b : UnitTorus d L N₁ m₁ k)
  · simp only [h, ↓reduceIte]
    exact Complex.conj_ofReal _
  · have h' : ¬ unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) :=
      fun e => h e.symm
    simp only [h, h', ↓reduceIte, star_zero]

theorem unitP_idem : unitP G * unitP G = unitP G := by
  classical
  ext b b''
  rw [Matrix.mul_apply]
  set r : ℝ := (((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹ with hr
  have hn : (0 : ℝ) < ((L ^ 1 : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((L ^ 1 : ℕ) : ℝ) := by
      have := Nat.pos_of_ne_zero (pow_ne_zero 1 (NeZero.ne L)); exact_mod_cast this
    positivity
  have hrn : r * r * (((L ^ 1 : ℕ) : ℝ) ^ d) = r := by rw [hr]; field_simp
  by_cases hbb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b'' : UnitTorus d L N₁ m₁ k)
  · have hterm : ∀ b' : unitPts G, unitP G b b' * unitP G b' b'' =
        (((r * r) * (if unitBlock1 (b' : UnitTorus d L N₁ m₁ k) =
          unitBlock1 (b : UnitTorus d L N₁ m₁ k) then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      intro b'
      by_cases h : unitBlock1 (b' : UnitTorus d L N₁ m₁ k) = unitBlock1 (b : UnitTorus d L N₁ m₁ k)
      · have h1 : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) :=
          h.symm
        have h2 : unitBlock1 (b' : UnitTorus d L N₁ m₁ k) =
            unitBlock1 (b'' : UnitTorus d L N₁ m₁ k) := h.trans hbb
        simp only [unitP, h1, h2, ↓reduceIte, mul_one, ← Complex.ofReal_mul]
        rfl
      · have h1 : ¬ unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) :=
          fun e => h e.symm
        simp only [unitP, h, h1, ↓reduceIte, mul_zero, zero_mul, Complex.ofReal_zero]
    simp only [hterm]
    have hs := sum_unitBlock1_fibre G b
    calc (∑ x : unitPts G, (((r * r) * (if unitBlock1 (x : UnitTorus d L N₁ m₁ k) =
          unitBlock1 (b : UnitTorus d L N₁ m₁ k) then (1 : ℝ) else 0) : ℝ) : ℂ)) =
        (((r * r) * ∑ x : unitPts G, (if unitBlock1 (x : UnitTorus d L N₁ m₁ k) =
          unitBlock1 (b : UnitTorus d L N₁ m₁ k) then (1 : ℝ) else 0) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
          simp only [Complex.ofReal_mul]
      _ = (r : ℂ) := by rw [hs, hrn]
      _ = unitP G b b'' := by simp [unitP, hbb, hr]
  · have hterm : ∀ b' : unitPts G, unitP G b b' * unitP G b' b'' = 0 := by
      intro b'
      by_cases h : unitBlock1 (b' : UnitTorus d L N₁ m₁ k) = unitBlock1 (b : UnitTorus d L N₁ m₁ k)
      · have h1 : ¬ unitBlock1 (b' : UnitTorus d L N₁ m₁ k) =
            unitBlock1 (b'' : UnitTorus d L N₁ m₁ k) := fun e => hbb (h.symm.trans e)
        simp only [unitP, h1, ↓reduceIte, mul_zero]
      · have h1 : ¬ unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) :=
          fun e => h e.symm
        simp only [unitP, h1, ↓reduceIte, zero_mul]
    simp only [hterm, Finset.sum_const_zero]
    simp [unitP, hbb]

theorem unitQ_real (b : unitPts G) (y : G.Ω 1) : star (unitQ G b y) = unitQ G b y := by
  unfold unitQ
  split_ifs
  · exact Complex.conj_ofReal _
  · simp

/-- **The unit lattice of the project.** The block average `Q_k` (normalised by `Q Q* = 1`) from
the fine sites `Ω₁` to the unit points of `Λ` (blocks of side `L ^ k` inside the top layer) and the
projection `P` onto the constants of the `L`-blocks of the unit lattice satisfy all the typing data
of I-4c: `IsUnitLatticeB`. -/
theorem isUnitLatticeB_unit : IsUnitLatticeB G (unitQ G) (unitP G) :=
  { layer := unitQ_layer G, contr := unitQ_contr G, contrT := unitQ_contrT G,
    herm := unitP_herm G, idem := unitP_idem G, blk1 := unitQ_blk1 G, blk2 := unitQ_blk2 G }

end Unit

end Balaban.Localization
