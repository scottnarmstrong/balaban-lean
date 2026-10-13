module

public import Balaban.LargeField.Base.BaseChartQuadraticPhysical

/-!
# The first-step lifted action and the physical block action

The physical coefficient and block average are those of P4 (2.42)–(2.44). The following
finite-fibre and torus-transport lemmas identify them with the single-scale background action.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical

variable {d N L n : ℕ}

private theorem cast_roundtrip_fwd {α : Type*} {F : α → Type*} {a b : α}
    (e : a = b) (x : F b) : e ▸ (e.symm ▸ x) = x := by cases e; rfl

private theorem cast_roundtrip_rev {α : Type*} {F : α → Type*} {a b : α}
    (e : a = b) (x : F a) : e.symm ▸ (e ▸ x) = x := by cases e; rfl

private theorem torus_cast_add {d ℓ ℓ' : ℕ} (e : ℓ = ℓ')
    (x y : Torus d ℓ) : e ▸ (x + y) = (e ▸ x) + (e ▸ y) := by
  cases e
  rfl

private theorem torus_cast_single {d ℓ ℓ' : ℕ} (e : ℓ = ℓ')
    (j : Fin d) : e ▸ (Pi.single j (1 : ZMod ℓ) : Torus d ℓ) =
      (Pi.single j (1 : ZMod ℓ') : Torus d ℓ') := by
  cases e
  rfl

private theorem blockMap_congr {d ℓ ℓ' m m' K K' : ℕ}
    (hℓ : ℓ = ℓ') (hm : m = m') (hK : K = K') (x : Torus d ℓ) :
    hm ▸ blockMap K m x = blockMap K' m' (hℓ ▸ x) := by
  cases hℓ; cases hm; cases hK; rfl

private theorem sum_fibre_cast {d ℓ ℓ' m m' K K' : ℕ} [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ = ℓ') (hm : m = m') (hK : K = K')
    (y : Torus d m) (f : Torus d ℓ' → ℝ) :
    ∑ x ∈ blockFibre (ℓ := ℓ) K m y, f (hℓ ▸ x) =
      ∑ x ∈ blockFibre (ℓ := ℓ') K' m' (hm ▸ y), f x := by
  let e : Torus d ℓ ≃ Torus d ℓ' :=
    { toFun := fun x => hℓ ▸ x
      invFun := fun x => hℓ.symm ▸ x
      left_inv := cast_roundtrip_rev hℓ
      right_inv := cast_roundtrip_fwd hℓ }
  apply Finset.sum_equiv e
  · intro x
    rw [mem_blockFibre, mem_blockFibre]
    have hc := blockMap_congr hℓ hm hK x
    change blockMap K m x = y ↔ blockMap K' m' (hℓ ▸ x) = hm ▸ y
    rw [← hc]
    cases hm
    rfl
  · intro x hx
    rfl

/-- The first-step block map is the physical block map after transport of the side lengths. -/
theorem baseSector_blockMap_transport (x : Torus d (1 * n * L ^ 1)) :
    baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x =
      blockMap L n (baseSector_side L n ▸ x) := by
  exact blockMap_congr (baseSector_side L n) (baseSector_coarse L n)
    (pow_one L) x

variable [NeZero L] [NeZero n]

private theorem baseSector_physical_svec (ϱ : ℝ) (φ : CfgT d N L n)
    (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    svec (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ)
      (fun p => (((φ (baseSector_side L n ▸
        (p.1 : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ))
      x i =
        (((φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
  have hx := baseSector_mem_single (d := d) (L := L) (n := n) ϱ x
  change svec (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
    (k := 1) ϱ) _ (⟨x, hx⟩ : (GeneratingSet.single (d := d) (L := L)
    (N₀ := 1 * n) (k := 1) ϱ).Ω 1) i = _
  rw [svec_of_mem]

/-- The lifted fine-site block average equals the physical `baseQ` after transport. -/
theorem baseSector_blockAvg_eq_baseQ (ϱ : ℝ) (φ : CfgT d N L n)
    (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    blockAvg (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ)
      (fun p => (((φ (baseSector_side L n ▸
        (p.1 : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ))
      x i =
        ((baseQ d N L n φ (baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ) := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  have hsum : (∑ y ∈ G.blk 1 x,
      svec G (fun p => (((φ (baseSector_side L n ▸
        (p.1 : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) y i) =
      ((∑ y ∈ blockFibre (ℓ := L * n) L n
        (baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x),
        (φ y : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
    rw [show G.blk 1 x = blockFibre (L ^ 1) (1 * n * L ^ (1 - 1))
      (jBlock d L (1 * n) 1 1 x) from rfl]
    calc
      _ = ∑ y ∈ blockFibre (L ^ 1) (1 * n * L ^ (1 - 1))
          (jBlock d L (1 * n) 1 1 x),
          (((φ (baseSector_side L n ▸ y) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact baseSector_physical_svec ϱ φ y i
      _ = _ := by
        rw [← Complex.ofReal_sum]
        congr 1
        exact sum_fibre_cast (baseSector_side L n) (baseSector_coarse L n)
          (pow_one L) (jBlock d L (1 * n) 1 1 x)
          (fun y => (φ y : EuclideanSpace ℝ (Fin N)) i)
  unfold blockAvg baseQ
  rw [layerIndex_single (ϱ := ϱ) (d := d) (L := L)
    (N₀ := 1 * n) (k := 1) le_rfl x]
  simp only [pow_one]
  rw [hsum]
  simp [Finset.sum_apply, Complex.ofReal_mul]

private theorem sum_torus_cast {d ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ = ℓ')
    (f : Torus d ℓ' → ℝ) :
    ∑ x : Torus d ℓ, f (hℓ ▸ x) = ∑ x : Torus d ℓ', f x := by
  let e : Torus d ℓ ≃ Torus d ℓ' :=
    { toFun := fun x => hℓ ▸ x
      invFun := fun x => hℓ.symm ▸ x
      left_inv := cast_roundtrip_rev hℓ
      right_inv := cast_roundtrip_fwd hℓ }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem sum_single_sites (ϱ : ℝ) (f : Torus d (1 * n * L ^ 1) → ℝ) :
    ∑ x : (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ).Ω 1, f x =
        ∑ x : Torus d (1 * n * L ^ 1), f x := by
  classical
  symm
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  have h : ∀ x : Torus d (1 * n * L ^ 1), x ∈ Finset.univ ↔ x ∈ G.Ω 1 := by
    intro x
    simp [G, single_Ω_one (ϱ := ϱ) (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) le_rfl]
  have hs := Finset.sum_subtype (F := inferInstance) Finset.univ h f
  simpa [G] using hs

/-- Every physical block has `L^d` fine sites, so a block-constant function sums with that
multiplicity. -/
theorem baseSector_sum_over_blocks (f : Torus d n → ℝ) :
    ∑ x : Torus d (L * n), f (blockMap L n x) =
      (L : ℝ) ^ d * ∑ y : Torus d n, f y := by
  classical
  calc
    _ = ∑ y : Torus d n, ∑ x ∈ blockFibre (ℓ := L * n) L n y,
          f (blockMap L n x) := by
            simpa [blockFibre] using
              (Finset.sum_fiberwise Finset.univ (blockMap L n)
                (fun x => f (blockMap L n x))).symm
    _ = ∑ y : Torus d n, (L : ℝ) ^ d * f y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hc : (blockFibre (ℓ := L * n) L n y).card = L ^ d :=
        card_blockFibre (ℓ := L * n) (N := L) (m := n) (by ring) y
      calc
        _ = ∑ x ∈ blockFibre (ℓ := L * n) L n y, f y := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(mem_blockFibre.mp hx)]
        _ = (L : ℝ) ^ d * f y := by simp [hc]
    _ = _ := by rw [Finset.mul_sum]

/-- Counting blocks in the subtype carrier of the single-scale background domain. -/
theorem baseSector_sum_single_blocks (ϱ : ℝ) (f : Torus d n → ℝ) :
    ∑ x : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
        f (blockMap L n (baseSector_side L n ▸
          (x : Torus d (1 * n * L ^ 1)))) =
      (L : ℝ) ^ d * ∑ y : Torus d n, f y := by
  calc
    _ = ∑ x : Torus d (1 * n * L ^ 1),
          f (blockMap L n (baseSector_side L n ▸ x)) := sum_single_sites ϱ _
    _ = ∑ x : Torus d (L * n), f (blockMap L n x) :=
      sum_torus_cast (baseSector_side L n)
        (fun x : Torus d (L * n) => f (blockMap L n x))
    _ = _ := baseSector_sum_over_blocks f

private theorem sum_coord_norm_sq (u v : EuclideanSpace ℝ (Fin N)) :
    (∑ i : Fin N, ‖((u i : ℝ) : ℂ) - ((v i : ℝ) : ℂ)‖ ^ 2) =
      ‖u - v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp

private theorem baseSector_datum_h (ϱ : ℝ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (h : EuclideanSpace ℝ (Fin N)) (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    (baseSectorDatum ϱ θ h).h x i = ((h i : ℝ) : ℂ) := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  have hx : x ∈ G.Ω 1 := baseSector_mem_single ϱ x
  change (liftSingle G (baseSectorThetaC (L := L) θ)
    (fun i => (h i : ℂ))).h x i = _
  rw [liftSingle_h G (baseSectorThetaC (L := L) θ)
    (fun i => (h i : ℂ)) hx]

private theorem baseSector_barField_physical (ϱ : ℝ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (h : EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    barField (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ) (baseSectorDatum ϱ θ h).Ψ
      (fun p => ((baseSectorSpin φ
        (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)) x i =
      (((φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
  have hx := baseSector_mem_single (d := d) (L := L) (n := n) ϱ x
  simp [barField, hx, baseSectorSpin]

/-- The lifted mass term is the physical hard-spin mass term. -/
theorem baseSector_action_mass_eq (ϱ : ℝ) (μ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
    μ / 2 * ∑ x : G.Ω 1, ∑ i, ‖σ (x, i) - D.h (x : Torus d (1 * n * L ^ 1)) i‖ ^ 2 =
      μ / 2 * ∑ x : Torus d (L * n),
        ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let σ : G.Ω 1 × Fin N → ℂ := fun p =>
    ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
  have hs (x : G.Ω 1) :
      (∑ i, ‖σ (x, i) - D.h (x : Torus d (1 * n * L ^ 1)) i‖ ^ 2) =
        ‖(φ (baseSector_side L n ▸
          (x : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
    calc
      _ = ∑ i, ‖((((φ (baseSector_side L n ▸
          (x : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) -
          ((h i : ℝ) : ℂ))‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [baseSector_datum_h ϱ θ h (x : Torus d (1 * n * L ^ 1)) i]
            rfl
      _ = _ := sum_coord_norm_sq _ _
  congr 1
  calc
    _ = ∑ x : G.Ω 1,
        ‖(φ (baseSector_side L n ▸
          (x : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hs x
    _ = ∑ x : Torus d (1 * n * L ^ 1),
        ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :=
          sum_single_sites ϱ (fun x : Torus d (1 * n * L ^ 1) =>
            ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)
    _ = _ := sum_torus_cast (baseSector_side L n)
      (fun x : Torus d (L * n) => ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)

private theorem baseSector_bond_site_eq (ϱ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (x : Torus d (1 * n * L ^ 1)) (j : Fin d) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
    (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then
      ∑ i, ‖barField G D.Ψ σ (x + Pi.single j 1) i -
        barField G D.Ψ σ x i‖ ^ 2 else 0) =
    ‖(φ ((baseSector_side L n ▸ x) + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) -
      φ (baseSector_side L n ▸ x)‖ ^ 2 := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let σ : G.Ω 1 × Fin N → ℂ := fun p =>
    ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
  have hx : x ∈ G.Ω 1 := baseSector_mem_single ϱ x
  have hcond : x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 := Or.inl hx
  rw [ite_eq_left hcond]
  have hcast : baseSector_side L n ▸ (x + Pi.single j 1) =
      (baseSector_side L n ▸ x) + Pi.single j 1 := by
    rw [torus_cast_add, torus_cast_single]
  let u : EuclideanSpace ℝ (Fin N) := φ ((baseSector_side L n ▸ x) + Pi.single j 1)
  let v : EuclideanSpace ℝ (Fin N) := φ (baseSector_side L n ▸ x)
  calc
    _ = ∑ i : Fin N,
      ‖((u i : ℝ) : ℂ) - ((v i : ℝ) : ℂ)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [baseSector_barField_physical ϱ θ h φ (x + Pi.single j 1) i,
            baseSector_barField_physical ϱ θ h φ x i, hcast]
    _ = _ := sum_coord_norm_sq u v

private theorem baseSector_bond_sum_cast (φ : CfgT d N L n) :
    (∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
      ‖(φ ((baseSector_side L n ▸ x) + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) -
        φ (baseSector_side L n ▸ x)‖ ^ 2) =
    ∑ x : Torus d (L * n), ∑ j : Fin d,
      ‖(φ (x + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2 := by
  let f : Torus d (L * n) → ℝ := fun x => ∑ j : Fin d,
    ‖(φ (x + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2
  change (∑ x : Torus d (1 * n * L ^ 1), f (baseSector_side L n ▸ x)) =
    ∑ x : Torus d (L * n), f x
  exact sum_torus_cast (d := d) (ℓ := 1 * n * L ^ 1) (ℓ' := L * n)
    (baseSector_side L n) f

private theorem baseSector_bond_sum_native_eq (ϱ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
    (∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ σ (x + Pi.single j 1) i -
          barField G D.Ψ σ x i‖ ^ 2 else 0)) =
      ∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
        ‖(φ ((baseSector_side L n ▸ x) + Pi.single j 1) :
          EuclideanSpace ℝ (Fin N)) - φ (baseSector_side L n ▸ x)‖ ^ 2 := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let σ : G.Ω 1 × Fin N → ℂ := fun p =>
    ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  exact baseSector_bond_site_eq ϱ h θ φ x j

/-- The nearest-neighbor term of the lifted action is the physical bond energy. -/
theorem baseSector_action_bond_eq (ϱ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
    (1 / 2) * ∑ x : Torus d (1 * n * L ^ 1), ∑ j : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single j 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ σ (x + Pi.single j 1) i -
          barField G D.Ψ σ x i‖ ^ 2 else 0) =
      (1 / 2) * ∑ x : Torus d (L * n), ∑ j : Fin d,
        ‖(φ (x + Pi.single j 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2 := by
  dsimp only
  exact congrArg (fun t : ℝ => (1 / 2) * t)
    ((baseSector_bond_sum_native_eq ϱ h θ φ).trans (baseSector_bond_sum_cast φ))

/-- The lifted block term is the physical first-step block quadratic of P4 (2.42), with
`aw 1 = a₀` and the factor `L^d` from the number of fine sites in each block. -/
theorem baseSector_action_block_eq (ϱ : ℝ) (aw : ℕ → ℝ) (a₀ : ℝ)
    (ha : aw 1 = a₀) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
    (1 / 2) * ∑ x : G.Ω 1,
      (aw (G.layerIndex (x : Torus d (1 * n * L ^ 1))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (1 * n * L ^ 1))) ^ 2) *
        ∑ i, ‖D.Ψ (x : Torus d (1 * n * L ^ 1)) i -
          blockAvg G σ (x : Torus d (1 * n * L ^ 1)) i‖ ^ 2 =
      (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
        ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let σ : G.Ω 1 × Fin N → ℂ := fun p =>
    ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
  have hΨ (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
      D.Ψ x i = ((θ (baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ) := by
    have hx : x ∈ G.Ω 1 := baseSector_mem_single ϱ x
    have hd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    change (liftSingle G (baseSectorThetaC (L := L) θ)
      (fun i => (h i : ℂ))).Ψ x i = _
    rw [liftSingle_Ψ G (baseSectorThetaC (L := L) θ)
      (fun i => (h i : ℂ)) hd]
    rfl
  have hnorm (x : G.Ω 1) :
      (∑ i, ‖D.Ψ x i - blockAvg G σ x i‖ ^ 2) =
      ‖θ (blockMap L n (baseSector_side L n ▸
          (x : Torus d (1 * n * L ^ 1)))) -
        baseQ d N L n φ (blockMap L n (baseSector_side L n ▸
          (x : Torus d (1 * n * L ^ 1))))‖ ^ 2 := by
    rw [← baseSector_blockMap_transport (d := d) (L := L) (n := n)
      (x := (x : Torus d (1 * n * L ^ 1)))]
    calc
      _ = ∑ i : Fin N,
          ‖((θ (baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ) -
            ((baseQ d N L n φ (baseSector_coarse L n ▸
              jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hb := baseSector_blockAvg_eq_baseQ ϱ φ
                (x : Torus d (1 * n * L ^ 1)) i
              change blockAvg G σ (x : Torus d (1 * n * L ^ 1)) i = _ at hb
              rw [hΨ (x : Torus d (1 * n * L ^ 1)) i, hb]
      _ = _ := sum_coord_norm_sq _ _
  have hsite :
      (∑ x : G.Ω 1,
        ‖θ (blockMap L n (baseSector_side L n ▸
            (x : Torus d (1 * n * L ^ 1)))) -
          baseQ d N L n φ (blockMap L n (baseSector_side L n ▸
            (x : Torus d (1 * n * L ^ 1))))‖ ^ 2) =
      (L : ℝ) ^ d * ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 :=
    baseSector_sum_single_blocks ϱ (fun y => ‖θ y - baseQ d N L n φ y‖ ^ 2)
  calc
    _ = (1 / 2) * (a₀ / (L : ℝ) ^ 2) *
        ∑ x : G.Ω 1,
          ‖θ (blockMap L n (baseSector_side L n ▸
              (x : Torus d (1 * n * L ^ 1)))) -
            baseQ d N L n φ (blockMap L n (baseSector_side L n ▸
              (x : Torus d (1 * n * L ^ 1))))‖ ^ 2 := by
          calc
            _ = (1 / 2) * ∑ x : G.Ω 1, (a₀ / (L : ℝ) ^ 2) *
                ‖θ (blockMap L n (baseSector_side L n ▸
                    (x : Torus d (1 * n * L ^ 1)))) -
                  baseQ d N L n φ (blockMap L n (baseSector_side L n ▸
                    (x : Torus d (1 * n * L ^ 1))))‖ ^ 2 := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro x hx
                  have hw : G.layerIndex (x : Torus d (1 * n * L ^ 1)) = 1 :=
                    layerIndex_single (ϱ := ϱ) (d := d) (L := L)
                      (N₀ := 1 * n) (k := 1) le_rfl x
                  rw [hw, ha, pow_one, hnorm x]
            _ = _ := by rw [← Finset.mul_sum]; ring
    _ = _ := by rw [hsite]; ring

/-- The single-scale background action is the physical first-step block action of
P4 (2.42)–(2.44), with the hard-spin kinetic and mass terms of `energy`. -/
theorem baseSector_action_eq_physical (ϱ : ℝ) (aw : ℕ → ℝ) (a₀ μ : ℝ)
    (ha : aw 1 = a₀) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorSpin φ (p.1 : Torus d (1 * n * L ^ 1)) p.2 : ℝ) : ℂ)
    action G aw μ D σ =
      energy d N (L * n) μ h φ +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 := by
  dsimp only
  unfold action energy
  rw [baseSector_action_block_eq ϱ aw a₀ ha h θ φ,
    baseSector_action_bond_eq ϱ h θ φ,
    baseSector_action_mass_eq ϱ μ h θ φ]
  ring

/-- The physical block action has the constrained chord quadratic on the nonzero all-good
support. The displayed physical action is P4 (2.42) at hard spin. -/
theorem baseSector_physical_B_chord_of_product_ne_zero
    (ϱ : ℝ) (aw : ℕ → ℝ) (a₀ : ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    let G := GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ
    let D := baseSectorDatum ϱ θ h
    let e : Torus d (L * n) → EuclideanSpace ℝ (Fin N) :=
      baseSectorCenter ϱ aw regimeB ν h θ
    let ec : CfgT d N L n := fun x => ⟨e x,
      mem_sphere_zero_iff_norm.mpr (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ x)⟩
    let σ : G.Ω 1 × Fin N → ℂ := fun p =>
      (((φ (baseSector_side L n ▸
        (p.1 : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)
    let ε : G.Ω 1 × Fin N → ℂ := fun p =>
      ((e (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)
    let α := bgMult G aw (if regimeB then ν else 0) D
    ((((energy d N (L * n) (if regimeB then ν else 0) h φ +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2) -
       (energy d N (L * n) (if regimeB then ν else 0) h ec +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ)) : ℂ) =
      (1 / 2) * pair G (σ - ε)
        (liftOp N (dirichletOperator G aw (if regimeB then ν else 0) α) *ᵥ (σ - ε)) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let e : Torus d (L * n) → EuclideanSpace ℝ (Fin N) :=
    baseSectorCenter ϱ aw regimeB ν h θ
  let ec : CfgT d N L n := fun x => ⟨e x,
    mem_sphere_zero_iff_norm.mpr (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ x)⟩
  let σ : G.Ω 1 × Fin N → ℂ := fun p =>
    (((φ (baseSector_side L n ▸
      (p.1 : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)
  let ε : G.Ω 1 × Fin N → ℂ := fun p =>
    ((e (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)
  have hφ := baseSector_action_eq_physical ϱ aw a₀ (if regimeB then ν else 0)
    ha h θ φ
  have hec := baseSector_action_eq_physical ϱ aw a₀ (if regimeB then ν else 0)
    ha h θ ec
  have hch := baseSector_physical_action_chord_of_product_ne_zero
    ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  change (((action G aw (if regimeB then ν else 0) D σ -
    action G aw (if regimeB then ν else 0) D ε : ℝ)) : ℂ) = _ at hch
  change action G aw (if regimeB then ν else 0) D σ = _ at hφ
  change action G aw (if regimeB then ν else 0) D ε = _ at hec
  rw [hφ, hec] at hch
  exact hch

end Balaban.LargeField
