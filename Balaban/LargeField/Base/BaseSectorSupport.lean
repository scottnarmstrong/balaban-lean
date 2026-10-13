/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartIdentity
public import Balaban.LargeField.Base.BaseSupport
public import Balaban.LargeField.Background.Lift
public import Balaban.Background.SingleScale
public import Balaban.LargeField.Characteristic.MeasurableChi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The physical first-step good sector

The cube factors are exactly `chiPrimeZero` at `K=M=1`. The finite product is transported
from the block convention `n*L` to the physical-density convention `L*n`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale MeasureTheory

theorem baseSector_side (L n : ℕ) : 1 * n * L ^ 1 = L * n := by
  simp [Nat.mul_comm]

private theorem baseSector_cast_roundtrip {α : Type*} {F : α → Type*} {a b : α}
    (e : a = b) (x : F b) : e ▸ (e.symm ▸ x) = x := by
  cases e
  rfl

theorem baseSector_coarse (L n : ℕ) : 1 * n * L ^ (1 - 1) = n := by simp

/-- Scale sequence for the first physical step: `n₀=L n`, `n₁=n`. -/
def baseSectorN (L n : ℕ) (j : ℕ) : ℕ := if j = 0 then L * n else n

instance baseSectorN_neZero (L n : ℕ) [NeZero L] [NeZero n] (j : ℕ) :
    NeZero (baseSectorN L n j) := by
  unfold baseSectorN
  split_ifs <;> infer_instance

private theorem baseSectorN_step (L n : ℕ) :
    ∀ j, j < 1 → baseSectorN L n j = L * baseSectorN L n (j + 1) := by
  intro j hj
  have : j = 0 := by omega
  subst j
  simp [baseSectorN]

/-- The sphere spins, as real coordinates on the record torus. -/
noncomputable def baseSectorSpin {d N L n : ℕ} (φ : CfgT d N L n) :
    Torus d (1 * n * L ^ 1) → Fin N → ℝ :=
  fun x i => (φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i

/-- The coarse real field on the record's one-block torus. -/
def baseSectorTheta {d N L n : ℕ} (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Torus d (1 * n * L ^ (1 - 1)) → Fin N → ℝ :=
  fun y i => (θ (baseSector_coarse L n ▸ y)) i

/-- The complex coarse datum associated with the real coarse field. -/
def baseSectorThetaC {d N L n : ℕ} (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Torus d (1 * n * L ^ (1 - 1)) → Fin N → ℂ :=
  fun y i => ((θ (baseSector_coarse L n ▸ y) i : ℝ) : ℂ)

/-- The full first-step datum: the lifted coarse field and the constant external field. -/
noncomputable def baseSectorDatum {d N L n : ℕ} [NeZero L] [NeZero n] (ϱ : ℝ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N)) :
    BgData (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ) N :=
  liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
    (baseSectorThetaC (L := L) θ) (fun i => (h i : ℂ))

/-- The all-good P5 (2.6) factor, before testing the background domain. -/
noncomputable def baseSectorCubeProduct {d N L n : ℕ} [NeZero L] [NeZero n]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) : ℝ :=
  ∏ c : Torus d n,
    chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ)

/-- Every cube factor of the physical product is the landed `chiPrimeZero`. -/
theorem baseSectorCubeProduct_eq (d N L n : ℕ) [NeZero L] [NeZero n]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    baseSectorCubeProduct regimeB ν δ₀ h θ φ =
      ∏ c : Torus d n,
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
          (baseSectorSpin φ, baseSectorTheta θ) := rfl


/-- A fixed site and spin coordinate is measurable as a function of the sphere configuration. -/
theorem measurable_baseSectorSpin {d N L n : ℕ}
    (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    Measurable (fun φ : CfgT d N L n => baseSectorSpin φ x i) := by
  unfold baseSectorSpin
  exact (EuclideanSpace.proj i).continuous.measurable.comp
    (measurable_subtype_coe.comp (measurable_pi_apply (baseSector_side L n ▸ x)))

/-- The block average of the transported physical spins is measurable. -/
theorem measurable_baseSectorAverage {d N L n : ℕ} [NeZero L] [NeZero n]
    (y : Torus d (1 * n * L ^ (1 - 1))) (i : Fin N) :
    Measurable (fun φ : CfgT d N L n =>
      spinAverage (baseSectorN L n) L 1 1 (baseSectorSpin φ) y i) := by
  unfold spinAverage
  exact measurable_const.mul (Finset.measurable_sum _ fun x _ => measurable_baseSectorSpin x i)

/-- A fixed proposition is a measurable subset of any measurable space. -/
theorem measurableSet_baseSectorConst {X : Type*} [MeasurableSpace X] (P : Prop) :
    MeasurableSet {_x : X | P} := by
  by_cases h : P
  · simp [h]
  · simp [h]

/-- The physical cube block test is a Borel subset of sphere configurations. -/
theorem measurableSet_baseSectorBlock {d N L n : ℕ} [NeZero L] [NeZero n]
    (δ₀ : ℝ) (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (c : Torus d n) :
    MeasurableSet {φ : CfgT d N L n |
      ChiBlockProp (baseSectorN L n) L 1 1 δ₀ (baseSectorSpin φ) (baseSectorTheta θ) c} := by
  unfold ChiBlockProp
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun y => ?_
  have hm : Measurable (fun φ : CfgT d N L n =>
      rn (fun i => baseSectorTheta θ y i -
        spinAverage (baseSectorN L n) L 1 1 (baseSectorSpin φ) y i)) := by
    unfold rn
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum _ fun i _ =>
        (measurable_const.sub (measurable_baseSectorAverage y i)).pow_const 2)
  exact (measurableSet_baseSectorConst (X := CfgT d N L n)
    (blockMap 1 (baseSectorN L n 1) y = c)).imp
    (measurableSet_lt hm measurable_const)

/-- The physical cube bond test is a Borel subset of sphere configurations. -/
theorem measurableSet_baseSectorBond {d N L n : ℕ} [NeZero L] [NeZero n]
    (δ₀ : ℝ) (c : Torus d n) :
    MeasurableSet {φ : CfgT d N L n |
      ChiBondProp (baseSectorN L n) L 1 1 δ₀ (baseSectorSpin φ) c} := by
  unfold ChiBondProp
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun x => ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun μ => ?_
  have hm : Measurable (fun φ : CfgT d N L n =>
      rn (fun i => baseSectorSpin φ (x + Pi.single μ 1) i - baseSectorSpin φ x i)) := by
    unfold rn
    exact Real.continuous_sqrt.measurable.comp
      (Finset.measurable_sum _ fun i _ =>
        ((measurable_baseSectorSpin (x + Pi.single μ 1) i).sub
          (measurable_baseSectorSpin x i)).pow_const 2)
  exact (measurableSet_baseSectorConst (X := CfgT d N L n)
    (cubeMap (baseSectorN L n) L 1 1 1 x = c ∨
      cubeMap (baseSectorN L n) L 1 1 1 (x + Pi.single μ 1) = c)).imp
    (measurableSet_lt hm measurable_const)

/-- The physical cube site test is a Borel subset of sphere configurations. -/
theorem measurableSet_baseSectorSite {d N L n : ℕ} [NeZero L] [NeZero n]
    (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N)) (c : Torus d n) :
    MeasurableSet {φ : CfgT d N L n |
      ChiSiteProp (baseSectorN L n) L 1 1 ν δ₀ (baseSectorSpin φ) (fun i => h i) c} := by
  unfold ChiSiteProp
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun x => ?_
  have hm : Measurable (fun φ : CfgT d N L n =>
      ν * ∑ i, (baseSectorSpin φ x i - h i) ^ 2) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      ((measurable_baseSectorSpin x i).sub measurable_const).pow_const 2)
  exact (measurableSet_baseSectorConst (X := CfgT d N L n)
    (cubeMap (baseSectorN L n) L 1 1 1 x = c)).imp
    (measurableSet_lt hm measurable_const)

/-- Each literal P5 cube factor is measurable in the sphere spins. -/
theorem measurable_baseSectorCube {d N L n : ℕ} [NeZero L] [NeZero n]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (c : Torus d n) :
    Measurable (fun φ : CfgT d N L n =>
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ)) := by
  let A : CfgT d N L n → Prop := fun φ =>
    ChiBlockProp (baseSectorN L n) L 1 1 δ₀ (baseSectorSpin φ) (baseSectorTheta θ) c
  let B : CfgT d N L n → Prop := fun φ =>
    ChiBondProp (baseSectorN L n) L 1 1 δ₀ (baseSectorSpin φ) c ∧
      (regimeB → ChiSiteProp (baseSectorN L n) L 1 1 ν δ₀ (baseSectorSpin φ) (fun i => h i) c)
  have hA : MeasurableSet {φ | A φ} := measurableSet_baseSectorBlock δ₀ θ c
  have hB : MeasurableSet {φ | B φ} := by
    change MeasurableSet {φ | ChiBondProp (baseSectorN L n) L 1 1 δ₀ (baseSectorSpin φ) c ∧
      (regimeB → ChiSiteProp (baseSectorN L n) L 1 1 ν δ₀ (baseSectorSpin φ) (fun i => h i) c)}
    exact (measurableSet_baseSectorBond δ₀ c).inter
      ((measurableSet_baseSectorConst (X := CfgT d N L n) regimeB).imp
        (measurableSet_baseSectorSite (d := d) (N := N) (L := L) (n := n) ν δ₀ h c))
  have hm : Measurable (fun φ : CfgT d N L n => charFn A φ * charFn B φ) :=
    (measurable_charFn hA).mul (measurable_charFn hB)
  convert hm using 1
  funext φ
  rfl

/-- The all-good P5 (2.6) factor is measurable in the sphere spins. -/
theorem measurable_baseSectorCubeProduct {d N L n : ℕ} [NeZero L] [NeZero n]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Measurable (baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n) regimeB ν δ₀ h θ) := by
  unfold baseSectorCubeProduct
  exact Finset.measurable_prod _ fun c _ => measurable_baseSectorCube (d := d) (N := N) (L := L) (n := n) regimeB ν δ₀ h θ c


/-- A nonzero all-good product forces every literal cube test to pass. -/
theorem baseSectorCube_eq_one_of_product_ne_zero {d N L n : ℕ} [NeZero L] [NeZero n]
    (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) (c : Torus d n) :
    chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ) = 1 := by
  have hc : chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ) ≠ 0 := by
    apply (Finset.prod_ne_zero_iff.mp ?_) c (Finset.mem_univ c)
    simpa [baseSectorCubeProduct] using hp
  rcases chiPrimeZero_eq_zero_or_one (baseSectorN L n) L 1 1 regimeB ν δ₀
    (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) with hz | ho
  · exact False.elim (hc hz)
  · exact ho

/-- The full first-step generating set has every fine site in its first domain. -/
theorem baseSector_mem_single {d L n : ℕ} [NeZero L] [NeZero n] (ϱ : ℝ)
    (x : Torus d (1 * n * L ^ 1)) :
    x ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ).Ω 1 := by
  rw [single_Ω_one (ϱ := ϱ) (d := d) (L := L) (N₀ := 1 * n) (k := 1) le_rfl]
  exact Finset.mem_univ x

open Classical in
/-- Sphere spins passing every cube test give the hypotheses of the background support lemma. -/
theorem baseSectorSpinSupport_of_product_ne_zero {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    BaseSpinSupport (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
      (if regimeB then ν else 0) δ₀ (baseSectorSpin φ) (fun i => h i)
      (baseSectorDatum ϱ θ h) := by
  classical
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  have hunit : ∀ x, ∑ i, baseSectorSpin φ x i ^ 2 = 1 := by
    intro x
    have hn : ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (φ (baseSector_side L n ▸ x)).property
    have hs := EuclideanSpace.norm_sq_eq
      (φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N))
    simp only [Real.norm_eq_abs, sq_abs] at hs
    simpa [baseSectorSpin] using hs.symm.trans (by rw [hn]; norm_num)
  have hhunit : ∑ i, h i ^ 2 = 1 := by
    have hs := EuclideanSpace.norm_sq_eq h
    simp only [Real.norm_eq_abs, sq_abs] at hs
    calc ∑ i, h i ^ 2 = ‖h‖ ^ 2 := hs.symm
      _ = 1 := by rw [hh]; norm_num
  have hc : ∀ c : Torus d n,
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ) = 1 :=
    baseSectorCube_eq_one_of_product_ne_zero regimeB ν δ₀ h θ φ hp
  have hu : ∀ x : Torus d (1 * n * L ^ 1), x ∈ G.Ω 1 := by
    intro x
    exact baseSector_mem_single ϱ x
  have hud : ∀ x : Torus d (1 * n * L ^ 1), x ∈ dataSites G := by
    intro x
    exact (mem_dataSites G).2 (Or.inl (hu x))
  have hdata : ∀ x i, (baseSectorDatum ϱ θ h).Ψ x i =
      baseSectorThetaC (L := L) θ (jBlock d L (1 * n) 1 1 x) i := by
    intro x i
    exact congrFun (liftSingle_Ψ G (baseSectorThetaC (L := L) θ)
      (fun i => (h i : ℂ)) (hud x)) i
  refine
    { delta_pos := hδ
      spin_unit := hunit
      h_unit := hhunit
      block_real := ?_
      collar_eq := ?_
      field_eq := ?_
      block_cond := ?_
      bond_cond := ?_
      site_cond := ?_ }
  · intro x hx i
    rw [hdata x i]
    simp [baseSectorThetaC]
  · intro x hx i
    have he : collar G = ∅ := collar_single (ϱ := ϱ) (d := d) (L := L) (N₀ := 1 * n) (k := 1) le_rfl
    rw [he] at hx
    simp at hx
  · intro x hx i
    simpa [D, baseSectorDatum] using
      congrFun (liftSingle_h G (baseSectorThetaC (L := L) θ) (fun i => (h i : ℂ)) hx) i
  · intro x hx
    have htest := ((chiPrimeZero_eq_one_iff (baseSectorN L n) L 1 1 regimeB ν δ₀
      (fun i => h i) (cubeMap (baseSectorN L n) L 1 1 1 x)
      (baseSectorSpin φ, baseSectorTheta θ)).1 (hc _)).1
    have hb := htest (jBlock d L (1 * n) 1 1 x)
      (cubeMap_eq_comp (baseSectorN_step L n) le_rfl x)
    convert hb using 1
    congr 1
    funext i
    rw [hdata x i]
    have havg := spinAverage_eq_spinBlockAverage (nn := baseSectorN L n) (M := 1)
      G (baseSectorSpin φ) x i
    have havg' : spinBlockAverage (GeneratingSet.single (d := d) (L := L)
        (N₀ := 1 * n) (k := 1) ϱ) (baseSectorSpin φ) x i =
        spinAverage (baseSectorN L n) L 1 1 (baseSectorSpin φ)
          (jBlock d L (1 * n) 1 1 x) i := by
      simpa [baseSectorN] using havg.symm
    rw [havg']
    rfl
  · intro x μ hx
    have htest := ((chiPrimeZero_eq_one_iff (baseSectorN L n) L 1 1 regimeB ν δ₀
      (fun i => h i) (cubeMap (baseSectorN L n) L 1 1 1 x)
      (baseSectorSpin φ, baseSectorTheta θ)).1 (hc _)).2.1
    exact htest x μ (Or.inl rfl)
  · intro x hx
    by_cases hr : regimeB
    · have htest := ((chiPrimeZero_eq_one_iff (baseSectorN L n) L 1 1 regimeB ν δ₀
        (fun i => h i) (cubeMap (baseSectorN L n) L 1 1 1 x)
        (baseSectorSpin φ, baseSectorTheta θ)).1 (hc _)).2.2 hr
      simp only [hr, ↓reduceIte]
      exact htest x rfl
    · simpa [hr] using pow_pos hδ 2


open Classical in
/-- Every passing physical cube product puts the lifted coarse datum in the real background domain. -/
theorem baseSectorDatum_domain_of_product_ne_zero {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    InUnionDomainR (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
      (bgC1 d L N) (if regimeB then ν else 0) (baseSectorDatum ϱ θ h) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast H.hL
  have hsmall : 4 * d * L * δ₀ ≤ 1 / 1024 :=
    (approxDelta_le d L (bgC1_facts d L N hd0 hΛ1).1).1
  have S := baseSectorSpinSupport_of_product_ne_zero ϱ regimeB ν δ₀ hδ h hh θ φ hp
  have hδp : 0 < 4 * d * L * δ₀ := by positivity
  exact ⟨4 * d * L * δ₀, hδp, hΛ1, inDomainR_base H S hsmall⟩

open Classical in
/-- The physical all-good factor, restricted to coarse fields where the real background exists. -/
noncomputable def baseSectorCutoff {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) : ℝ :=
  if InUnionDomainR (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
      (bgC1 d L N) (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    then baseSectorCubeProduct regimeB ν δ₀ h θ φ else 0

open Classical in
/-- Under the numeric domain margin, the chart cutoff equals the literal all-good P5 product. -/
theorem baseSectorCutoff_eq_cubeProduct {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    baseSectorCutoff ϱ regimeB ν δ₀ h θ φ =
      baseSectorCubeProduct regimeB ν δ₀ h θ φ := by
  classical
  by_cases hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ = 0
  · by_cases hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
        (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
        (baseSectorDatum ϱ θ h)
    · simp [baseSectorCutoff, hU, hp]
    · simp [baseSectorCutoff, hU, hp]
  · have hU := baseSectorDatum_domain_of_product_ne_zero ϱ a regimeB ν δ₀ hδ
      h hh H hΛ1 θ φ hp
    simp [baseSectorCutoff, hU]

/-- The cutoff is measurable as a function of the sphere spins for fixed coarse field. -/
theorem measurable_baseSectorCutoff {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Measurable (baseSectorCutoff (d := d) (N := N) (L := L) (n := n)
      ϱ regimeB ν δ₀ h θ) := by
  classical
  by_cases hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h)
  · have he : baseSectorCutoff (d := d) (N := N) (L := L) (n := n)
        ϱ regimeB ν δ₀ h θ = baseSectorCubeProduct regimeB ν δ₀ h θ := by
      funext φ
      simp [baseSectorCutoff, hU]
    rw [he]
    exact measurable_baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
      regimeB ν δ₀ h θ
  · have he : baseSectorCutoff (d := d) (N := N) (L := L) (n := n)
        ϱ regimeB ν δ₀ h θ = fun _ => 0 := by
      funext φ
      simp [baseSectorCutoff, hU]
    rw [he]
    exact measurable_const

/-- The P5 cube product and the domain-restricted cutoff have absolute value at most one. -/
theorem baseSectorCutoff_abs_le_one {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : |baseSectorCutoff ϱ regimeB ν δ₀ h θ φ| ≤ 1 := by
  classical
  have hfactor : ∀ c : Torus d n,
      0 ≤ chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ) ∧
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ) ≤ 1 := by
    intro c
    rcases chiPrimeZero_eq_zero_or_one (baseSectorN L n) L 1 1 regimeB ν δ₀
      (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ) with hz | ho
    · rw [hz]; constructor <;> norm_num
    · rw [ho]; constructor <;> norm_num
  have hp0 : 0 ≤ baseSectorCubeProduct regimeB ν δ₀ h θ φ := by
    unfold baseSectorCubeProduct
    exact Finset.prod_nonneg fun c _ => (hfactor c).1
  have hp1 : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≤ 1 := by
    unfold baseSectorCubeProduct
    exact Finset.prod_le_one₀ (fun c _ => (hfactor c).1) fun c _ => (hfactor c).2
  by_cases hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h)
  · have he : baseSectorCutoff ϱ regimeB ν δ₀ h θ φ =
        baseSectorCubeProduct regimeB ν δ₀ h θ φ := by simp [baseSectorCutoff, hU]
    rw [he, abs_of_nonneg hp0]
    exact hp1
  · have he : baseSectorCutoff ϱ regimeB ν δ₀ h θ φ = 0 := by
      simp [baseSectorCutoff, hU]
    rw [he]
    norm_num

open Classical in
/-- The chart centre is the real first-step background where it exists, and `h` elsewhere. -/
noncomputable def baseSectorCenter {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (x : Torus d (L * n)) :
    EuclideanSpace ℝ (Fin N) :=
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let xr : Torus d (1 * n * L ^ 1) := (baseSector_side L n).symm ▸ x
  if InUnionDomainR G (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h)
    then WithLp.toLp 2 (fun i =>
      (bgField G a (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
        (⟨xr, baseSector_mem_single ϱ xr⟩, i)).re)
    else h

open Classical in
/-- On its real domain, the background centre has unit Euclidean norm. -/
theorem baseSectorCenter_unit {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (x : Torus d (L * n)) :
    ‖baseSectorCenter ϱ a regimeB ν h θ x‖ = 1 := by
  classical
  by_cases hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h)
  · let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let xr : Torus d (1 * n * L ^ 1) := (baseSector_side L n).symm ▸ x
    have he : baseSectorCenter ϱ a regimeB ν h θ x =
        (WithLp.toLp 2 (fun i =>
          (bgField G a (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
            (⟨xr, baseSector_mem_single ϱ xr⟩, i)).re) : EuclideanSpace ℝ (Fin N)) := by
      simp [baseSectorCenter, hU, G, xr]
    rw [he]
    have hreal := ((theorem71 (G := G) H hU).2.1 ⟨xr, baseSector_mem_single ϱ xr⟩).1
    have hsum := ((theorem71 (G := G) H hU).2.1 ⟨xr, baseSector_mem_single ϱ xr⟩).2
    have heq : ∑ i, (bgField G a (if regimeB then ν else 0)
        (baseSectorDatum ϱ θ h) (⟨xr, baseSector_mem_single ϱ xr⟩, i)).re ^ 2 = 1 := by
      calc
        _ = ∑ i, ‖bgField G a (if regimeB then ν else 0)
            (baseSectorDatum ϱ θ h) (⟨xr, baseSector_mem_single ϱ xr⟩, i)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Complex.sq_norm, Complex.normSq_apply, hreal i]
              ring
        _ = 1 := hsum
    have hn2 : ‖(WithLp.toLp 2 (fun i =>
        (bgField G a (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
          (⟨xr, baseSector_mem_single ϱ xr⟩, i)).re) : EuclideanSpace ℝ (Fin N))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      exact heq
    have hn0 : 0 ≤ ‖(WithLp.toLp 2 (fun i =>
        (bgField G a (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
          (⟨xr, baseSector_mem_single ϱ xr⟩, i)).re) : EuclideanSpace ℝ (Fin N))‖ :=
      norm_nonneg _
    nlinarith [hn2]
  · have he : baseSectorCenter ϱ a regimeB ν h θ x = h := by
      simp [baseSectorCenter, hU]
    rw [he]
    exact hh


open Classical in
/-- A nonzero physical cutoff puts every spin in the background hemisphere. -/
theorem baseSectorCenter_inner_pos_of_cutoff_ne_zero {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hχ : baseSectorCutoff ϱ regimeB ν δ₀ h θ φ ≠ 0)
    (x : Torus d (L * n)) :
    0 < inner ℝ (baseSectorCenter ϱ a regimeB ν h θ x)
      (φ x : EuclideanSpace ℝ (Fin N)) := by
  classical
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let xr : Torus d (1 * n * L ^ 1) := (baseSector_side L n).symm ▸ x
  have hU : InUnionDomainR G (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) := by
    by_contra hnot
    have hz : baseSectorCutoff ϱ regimeB ν δ₀ h θ φ = 0 := by
      simp [baseSectorCutoff, hnot, G]
    exact hχ hz
  have hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0 := by
    simpa [baseSectorCutoff, hU, G] using hχ
  have S := baseSectorSpinSupport_of_product_ne_zero ϱ regimeB ν δ₀ hδ h hh θ φ hp
  have hpos := (spins_near_background (G := G) H S hΛ1 hΛ2
    ⟨xr, baseSector_mem_single ϱ xr⟩).2.2.1
  have he : baseSectorCenter ϱ a regimeB ν h θ x =
      (WithLp.toLp 2 (fun i =>
        (bgField G a (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
          (⟨xr, baseSector_mem_single ϱ xr⟩, i)).re) : EuclideanSpace ℝ (Fin N)) := by
    simp [baseSectorCenter, hU, G, xr]
  have hcoord : ∀ i, baseSectorSpin φ xr i = (φ x : EuclideanSpace ℝ (Fin N)) i := by
    intro i
    have hcast : baseSector_side L n ▸ ((baseSector_side L n).symm ▸ x) = x :=
      baseSector_cast_roundtrip (F := fun m => Torus d m) (baseSector_side L n) x
    simp [baseSectorSpin, xr, hcast]
  rw [he, EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct, hcoord, mul_comm] using hpos

open Classical in
/-- The cutoff vanishes whenever any spin leaves its background hemisphere. -/
theorem baseSectorCutoff_hemisphere_support {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hbad : ∃ x, ¬ 0 < inner ℝ (baseSectorCenter ϱ a regimeB ν h θ x)
      (φ x : EuclideanSpace ℝ (Fin N))) :
    baseSectorCutoff ϱ regimeB ν δ₀ h θ φ = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := hbad
  exact hx (baseSectorCenter_inner_pos_of_cutoff_ne_zero ϱ a regimeB ν δ₀ hδ h hh H
    hΛ1 hΛ2 θ φ hne x)


open Classical in
/-- The frozen partition function splits at the literal P5 first-step all-good cutoff. -/
theorem baseSector_partitionFunction_eq_bad_add_chart {d N L n : ℕ}
    [NeZero L] [NeZero n] [NeZero N]
    (ϱ : ℝ) (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    {β a₀ z₁ : ℝ} (hβ : 0 < β) (ha₀ : 0 < a₀) (hz : 0 < z₁)
    (g : Torus d (L * n) → Fin N → ℂ) :
    partitionFunction d N (L * n) β ν h g =
      ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N),
        ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
          ((∫ φ, ((1 - baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
                  regimeB ν δ₀ h (z₁ • ψ) φ : ℝ) : ℂ) *
              ((baseKernel d N L n β a₀ (z₁ • ψ) φ : ℝ) : ℂ) *
              Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
                + ∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
              ∂aprioriMeasure d N (L * n)) +
            baseChartIntegral d N L n β a₀ ν h g (z₁ • ψ)
              (baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
                regimeB ν δ₀ h (z₁ • ψ))
              (baseSectorCenter ϱ aw regimeB ν h (z₁ • ψ))
              (baseSectorCenter_unit ϱ aw regimeB ν h hh H (z₁ • ψ)))
        ∂(Measure.pi fun _ => volume) := by
  have hmeas : ∀ θ : Torus d n → EuclideanSpace ℝ (Fin N),
      Measurable (baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
        regimeB ν δ₀ h θ) := fun θ => measurable_baseSectorCubeProduct regimeB ν δ₀ h θ
  have hbound : ∀ θ φ, |baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
      regimeB ν δ₀ h θ φ| ≤ 1 := by
    intro θ φ
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ]
    exact baseSectorCutoff_abs_le_one ϱ regimeB ν δ₀ h θ φ
  have hsupport : ∀ θ φ, (∃ x, ¬ 0 < inner ℝ (baseSectorCenter ϱ aw regimeB ν h θ x)
      (φ x : EuclideanSpace ℝ (Fin N))) →
      baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
        regimeB ν δ₀ h θ φ = 0 := by
    intro θ φ hbad
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ]
    exact baseSectorCutoff_hemisphere_support ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 hΛ2 θ φ hbad
  exact partitionFunction_eq_integral_bad_add_chart (d := d) (N := N) (L := L) (n := n)
    hβ ha₀ hz ν h g
    (baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n) regimeB ν δ₀ h)
    hmeas hbound
    (baseSectorCenter ϱ aw regimeB ν h)
    (fun θ x => baseSectorCenter_unit ϱ aw regimeB ν h hh H θ x) hsupport

end Balaban.LargeField
