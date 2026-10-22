/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActionBridge

/-!
# The physical first-step action of a configuration on a good region

For a generating set `G` at the first step whose `Ω 1` is a union of first blocks, a physical
configuration `φ` of the torus `𝕋_{Ln}` and data `D` of `G` that agree with `φ` on the collar and
with the lifted coarse field on `Ω`, the physical action
`energy μ h φ + (a₀ L^d / (2 L²)) ∑_y ‖θ_y - (Qφ)_y‖²`
is the action of `G` at the restriction of `φ` to `Ω` plus a term that only depends on the
configuration off `Ω` (`baseGood_action_add_ext`).  The terms are split along the sites of `Ω`
(`sum_split_Ω`), the bonds touching `Ω` (`bond_split`) and the blocks of `Ω`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical

noncomputable section

variable {d N L n : ℕ} [NeZero L] [NeZero n] {ϱ : ℝ} (G : GeneratingSet d L (1 * n) 1 ϱ)

/-- A sum over the sites of `Ω` is the sum over the torus of the function cut off outside `Ω`. -/
theorem sum_Ω_eq_ite {R : Type*} [AddCommMonoid R] (f : Torus d (1 * n * L ^ 1) → R) :
    ∑ x : G.Ω 1, f x = ∑ x, (if x ∈ G.Ω 1 then f x else 0) := by
  rw [Finset.sum_coe_sort (G.Ω 1) f, Finset.sum_ite_mem Finset.univ (G.Ω 1) f]
  simp

/-- A sum over the torus splits into the sites of `Ω` and the others. -/
theorem sum_split_Ω {R : Type*} [AddCommMonoid R] (f : Torus d (1 * n * L ^ 1) → R) :
    ∑ x, f x = ∑ x : G.Ω 1, f x + ∑ x, (if x ∈ G.Ω 1 then 0 else f x) := by
  rw [sum_Ω_eq_ite, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ G.Ω 1 <;> simp [hx]

/-- The spin field of `G.Ω 1` of a physical configuration. -/
def physSpin (φ : CfgT d N L n) : G.Ω 1 × Fin N → ℂ := fun p =>
  (((φ (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) :
    EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)

/-- **The mass term**: the mass term of the action of `G` plus the mass off `Ω` is the physical
mass term. -/
theorem mass_bridge (μ : ℝ) (h : EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) (D : BgData G N)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ)) :
    μ / 2 * ∑ x : G.Ω 1, ∑ i, ‖physSpin G φ (x, i) - D.h x i‖ ^ 2 +
      μ / 2 * ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
        ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) =
    μ / 2 * ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
  have hs (x : G.Ω 1) : (∑ i, ‖physSpin G φ (x, i) - D.h x i‖ ^ 2) =
      ‖(φ (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) :
        EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
    rw [← sum_coord_norm_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hh x x.2 i]
    rfl
  rw [← mul_add]
  congr 1
  calc _ = ∑ x : G.Ω 1, ‖(φ (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) :
        EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 +
      ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
        ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) := by
        rw [Finset.sum_congr rfl fun x _ => hs x]
    _ = ∑ x : Torus d (1 * n * L ^ 1),
        ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :=
        (sum_split_Ω G (fun x => ‖(φ (baseSector_side L n ▸ x) :
          EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)).symm
    _ = _ := sum_torus_cast (baseSector_side L n)
      (fun x : Torus d (L * n) => ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)

/-- The extended field `φ̄` of a physical configuration is the configuration itself on `Ω` and on
its collar, when the data agree with the configuration on the collar. -/
theorem barField_physSpin (φ : CfgT d N L n) (D : BgData G N)
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (((φ (baseSector_side L n ▸ x) :
      EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    {x : Torus d (1 * n * L ^ 1)} (hx : x ∈ G.Ω 1 ∨ x ∈ collar G) (i : Fin N) :
    barField G D.Ψ (physSpin G φ) x i =
      (((φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
  by_cases hΩ : x ∈ G.Ω 1
  · simp [barField, hΩ, physSpin]
  · have hc : x ∈ collar G := hx.resolve_left hΩ
    simp only [barField, hΩ, dite_false]
    exact hDc x hc i

/-- **The bond term**: the bonds of the action of `G` plus the bonds off `Ω` are the physical
bonds. -/
theorem bond_bridge (φ : CfgT d N L n) (D : BgData G N)
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (((φ (baseSector_side L n ▸ x) :
      EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) :
    (1 / 2) * ∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ (physSpin G φ) (x + Pi.single j 1) i -
          barField G D.Ψ (physSpin G φ) x i‖ ^ 2 else 0) +
    (1 / 2) * ∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then 0 else
        ‖(φ ((baseSector_side L n ▸ x) + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) -
          φ (baseSector_side L n ▸ x)‖ ^ 2) =
    (1 / 2) * ∑ x : Torus d (L * n), ∑ j : Fin d,
      ‖(φ (x + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2 := by
  rw [← mul_add, ← baseSector_bond_sum_cast φ, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcast : baseSector_side L n ▸ (x + Pi.single j 1) =
      (baseSector_side L n ▸ x) + Pi.single j 1 := by
    rw [torus_cast_add, torus_cast_single]
  by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1
  · simp only [hc, ↓reduceIte, add_zero]
    have hx : x ∈ G.Ω 1 ∨ x ∈ collar G := by
      by_cases h1 : x ∈ G.Ω 1
      · exact Or.inl h1
      · exact Or.inr (mem_collar_of_adj G (x := x + Pi.single j 1) (x' := x)
          (hc.resolve_left h1) h1 ⟨j, Or.inr rfl⟩)
    have hx' : x + Pi.single j 1 ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ collar G := by
      by_cases h1 : x + Pi.single j 1 ∈ G.Ω 1
      · exact Or.inl h1
      · exact Or.inr (mem_collar_of_adj G (x := x) (x' := x + Pi.single j 1)
          (hc.resolve_right h1) h1 ⟨j, Or.inl rfl⟩)
    rw [← sum_coord_norm_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [barField_physSpin G φ D hDc hx' i, barField_physSpin G φ D hDc hx i, hcast]
  · simp [hc]

/-- The physical block of a site of the native torus. -/
def blkOf (x : Torus d (1 * n * L ^ 1)) : Torus d n :=
  blockMap L n (baseSector_side L n ▸ x)

omit [NeZero L] [NeZero n] in
/-- The sites of the native torus with the same first block have the same physical block. -/
theorem blkOf_eq_of_jBlock_eq {x y : Torus d (1 * n * L ^ 1)}
    (h : jBlock d L (1 * n) 1 1 x = jBlock d L (1 * n) 1 1 y) : blkOf x = blkOf y := by
  unfold blkOf
  rw [← baseSector_blockMap_transport (d := d) (L := L) (n := n) x,
    ← baseSector_blockMap_transport (d := d) (L := L) (n := n) y, h]

/-- **The block average of a physical configuration on a union of first blocks** is the physical
block average `baseQ`. -/
theorem blockAvg_physSpin (φ : CfgT d N L n)
    (hblk : ∀ x y : Torus d (1 * n * L ^ 1), blkOf x = blkOf y → (x ∈ G.Ω 1 ↔ y ∈ G.Ω 1))
    {x : Torus d (1 * n * L ^ 1)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    blockAvg G (physSpin G φ) x i = ((baseQ d N L n φ (blkOf x) i : ℝ) : ℂ) := by
  have hl : G.layerIndex x = 1 := by
    obtain ⟨h1, h2, -⟩ := G.layerIndex_spec hx
    omega
  have hsum : (∑ y ∈ G.blk 1 x, svec G (physSpin G φ) y i) =
      ((∑ y ∈ blockFibre (ℓ := L * n) L n (blkOf x),
        (φ y : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
    rw [show G.blk 1 x = blockFibre (L ^ 1) (1 * n * L ^ (1 - 1))
      (jBlock d L (1 * n) 1 1 x) from rfl]
    calc
      _ = ∑ y ∈ blockFibre (L ^ 1) (1 * n * L ^ (1 - 1)) (jBlock d L (1 * n) 1 1 x),
          (((φ (baseSector_side L n ▸ y) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun y hy => ?_
            have hyj : jBlock d L (1 * n) 1 1 y = jBlock d L (1 * n) 1 1 x :=
              mem_blockFibre.mp hy
            have hyΩ : y ∈ G.Ω 1 := (hblk x y (blkOf_eq_of_jBlock_eq hyj.symm)).1 hx
            exact svec_of_mem G (physSpin G φ) ⟨y, hyΩ⟩ i
      _ = _ := by
        rw [← Complex.ofReal_sum]
        congr 1
        have hb : blkOf x = baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x :=
          (baseSector_blockMap_transport (d := d) (L := L) (n := n) x).symm
        rw [hb]
        exact sum_fibre_cast (baseSector_side L n) (baseSector_coarse L n)
          (pow_one L) (jBlock d L (1 * n) 1 1 x)
          (fun y => (φ y : EuclideanSpace ℝ (Fin N)) i)
  unfold blockAvg baseQ
  rw [hl]
  simp only [pow_one]
  rw [hsum]
  simp [Finset.sum_apply, Complex.ofReal_mul]

/-- **The block term**: the block term of the action of `G` plus the blocks off `Ω` is the
physical block term. -/
theorem block_bridge (a : ℕ → ℝ) (a₀ : ℝ) (ha : a 1 = a₀)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) (D : BgData G N)
    (hΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = ((θ (blkOf x) i : ℝ) : ℂ))
    (hblk : ∀ x y : Torus d (1 * n * L ^ 1), blkOf x = blkOf y → (x ∈ G.Ω 1 ↔ y ∈ G.Ω 1)) :
    (1 / 2) * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (1 * n * L ^ 1))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (1 * n * L ^ 1))) ^ 2) *
        ∑ i, ‖D.Ψ x i - blockAvg G (physSpin G φ) x i‖ ^ 2 +
      (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
        ∑ y : Torus d n, (if ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y then 0 else
          ‖θ y - baseQ d N L n φ y‖ ^ 2) =
    (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) * ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 := by
  set F : Torus d n → ℝ := fun y => ‖θ y - baseQ d N L n φ y‖ ^ 2 with hF
  have h1 : ∀ x : G.Ω 1, (a (G.layerIndex (x : Torus d (1 * n * L ^ 1))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (1 * n * L ^ 1))) ^ 2) *
        ∑ i, ‖D.Ψ x i - blockAvg G (physSpin G φ) x i‖ ^ 2 =
      (a₀ / (L : ℝ) ^ 2) * F (blkOf (x : Torus d (1 * n * L ^ 1))) := by
    intro x
    have hl : G.layerIndex (x : Torus d (1 * n * L ^ 1)) = 1 := by
      obtain ⟨h1, h2, -⟩ := G.layerIndex_spec x.2
      omega
    rw [hl, ha, pow_one]
    congr 1
    rw [hF]
    dsimp only
    rw [← sum_coord_norm_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΨ x x.2 i, blockAvg_physSpin G φ hblk x.2 i]
  set g : Torus d n → ℝ := fun y => if ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y then F y else 0 with hg
  have h2 : ∀ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then F (blkOf x) else 0) = g (blkOf x) := by
    intro x
    by_cases hx : x ∈ G.Ω 1
    · have : ∃ x', x' ∈ G.Ω 1 ∧ blkOf x' = blkOf x := ⟨x, hx, rfl⟩
      simp [hg, hx, this]
    · have : ¬ ∃ x', x' ∈ G.Ω 1 ∧ blkOf x' = blkOf x := by
        rintro ⟨x', hx', he⟩
        exact hx ((hblk x' x he).1 hx')
      simp [hg, hx, this]
  have h3 : ∑ x : G.Ω 1, F (blkOf (x : Torus d (1 * n * L ^ 1))) = (L : ℝ) ^ d * ∑ y, g y := by
    rw [sum_Ω_eq_ite G (fun x => F (blkOf x)), Finset.sum_congr rfl fun x _ => h2 x]
    calc ∑ x : Torus d (1 * n * L ^ 1), g (blkOf x)
        = ∑ x : Torus d (L * n), g (blockMap L n x) :=
          sum_torus_cast (baseSector_side L n) (fun x : Torus d (L * n) => g (blockMap L n x))
      _ = _ := baseSector_sum_over_blocks g
  have h4 : ∑ y : Torus d n, F y = ∑ y, g y + ∑ y, (if ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y then 0 else F y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y <;> simp [hg, hy]
  rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum, h3, h4]
  ring

/-- **The part of the physical action off `Ω`**: the bonds with no end in `Ω`, the mass off `Ω`
and the blocks off `Ω`. -/
def bridgeExt (a₀ μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) : ℝ :=
  (1 / 2) * ∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then 0 else
        ‖(φ ((baseSector_side L n ▸ x) + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) -
          φ (baseSector_side L n ▸ x)‖ ^ 2) +
    μ / 2 * ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
        ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) +
    (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
      ∑ y : Torus d n, (if ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y then 0 else
        ‖θ y - baseQ d N L n φ y‖ ^ 2)

/-- **The physical first-step action splits into the action of `G` and the part off `Ω`.**
Let `G` have `Ω 1` a union of first blocks, and let the data `D` of `G` be the lifted coarse field
on `Ω`, the configuration `φ` on the collar, and `h` as the field `h̃`.  Then
`energy μ h φ + (a₀ L^d / (2 L²)) ∑_y ‖θ_y - (Qφ)_y‖² = A_G(φ|_Ω) + bridgeExt`. -/
theorem baseGood_action_add_ext (a : ℕ → ℝ) (a₀ μ : ℝ) (ha : a 1 = a₀)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) (D : BgData G N)
    (hΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = ((θ (blkOf x) i : ℝ) : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (((φ (baseSector_side L n ▸ x) :
      EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ))
    (hblk : ∀ x y : Torus d (1 * n * L ^ 1), blkOf x = blkOf y → (x ∈ G.Ω 1 ↔ y ∈ G.Ω 1)) :
    action G a μ D (physSpin G φ) + bridgeExt G a₀ μ h θ φ =
      energy d N (L * n) μ h φ +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) * ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 := by
  have hm := mass_bridge G μ h φ D hh
  have hb := bond_bridge G φ D hDc
  have hk := block_bridge G a a₀ ha θ φ D hΨ hblk
  unfold action bridgeExt energy
  linarith

/-- The part off `Ω` only depends on the configuration off `Ω`. -/
theorem bridgeExt_congr (a₀ μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ φ' : CfgT d N L n)
    (hagree : ∀ x : Torus d (1 * n * L ^ 1), x ∉ G.Ω 1 →
      φ (baseSector_side L n ▸ x) = φ' (baseSector_side L n ▸ x)) :
    bridgeExt G a₀ μ h θ φ = bridgeExt G a₀ μ h θ φ' := by
  have hcast (x : Torus d (1 * n * L ^ 1)) (j : Fin d) :
      baseSector_side L n ▸ (x + Pi.single j 1) =
        (baseSector_side L n ▸ x) + Pi.single j 1 := by
    rw [torus_cast_add, torus_cast_single]
  unfold bridgeExt
  have e1 : ∀ (x : Torus d (1 * n * L ^ 1)) (j : Fin d),
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then 0 else
        ‖(φ ((baseSector_side L n ▸ x) + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) -
          φ (baseSector_side L n ▸ x)‖ ^ 2) =
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then 0 else
        ‖(φ' ((baseSector_side L n ▸ x) + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) -
          φ' (baseSector_side L n ▸ x)‖ ^ 2) := by
    intro x j
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      push Not at hc
      rw [← hcast x j, hagree x hc.1, hagree (x + Pi.single j 1) hc.2]
  have e2 : ∀ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
        ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) =
      (if x ∈ G.Ω 1 then 0 else
        ‖(φ' (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) := by
    intro x
    by_cases hx : x ∈ G.Ω 1
    · simp [hx]
    · simp only [hx, ↓reduceIte]; rw [hagree x hx]
  have e3 : ∀ y : Torus d n, (if ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y then 0 else
        ‖θ y - baseQ d N L n φ y‖ ^ 2) =
      (if ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y then 0 else ‖θ y - baseQ d N L n φ' y‖ ^ 2) := by
    intro y
    by_cases hy : ∃ x, x ∈ G.Ω 1 ∧ blkOf x = y
    · simp [hy]
    · simp only [hy, ↓reduceIte]
      have hq : baseQ d N L n φ y = baseQ d N L n φ' y := by
        unfold baseQ
        congr 1
        refine Finset.sum_congr rfl fun x' hx' => ?_
        have hb : blockMap L n x' = y := mem_blockFibre.mp hx'
        have hx'' : (baseSector_side L n).symm ▸ x' ∉ G.Ω 1 := by
          intro hmem
          exact hy ⟨_, hmem, by
            unfold blkOf
            rw [show baseSector_side L n ▸ ((baseSector_side L n).symm ▸ x') = x' from
              cast_roundtrip_fwd (F := fun m : ℕ => Torus d m) (baseSector_side L n) x']
            exact hb⟩
        have := hagree _ hx''
        rw [show baseSector_side L n ▸ ((baseSector_side L n).symm ▸ x') = x' from
          cast_roundtrip_fwd (F := fun m : ℕ => Torus d m) (baseSector_side L n) x'] at this
        rw [this]
      rw [hq]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => e1 x j,
    Finset.sum_congr rfl fun x _ => e2 x, Finset.sum_congr rfl fun y _ => e3 y]

end

end Balaban.LargeField
