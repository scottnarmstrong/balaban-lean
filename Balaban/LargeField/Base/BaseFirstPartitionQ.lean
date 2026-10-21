/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFirstPhysicalP
public import Balaban.LargeField.Characteristic.MeasurableChi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The second decomposition of the first step: the cubes `𝖰₁`

LFR Definition II.7.1, Lemma II.7.2; P5 (2.5)–(2.6), (2.14); BASE-KERNEL §1 (factor inventory:
"P5, 𝖰" and "𝖰 collar"). After the first decomposition over the failed cubes `𝖯₁`
(`baseRho1_eq_sum_firstP`), the cubes of `Ω₁(𝖯₁) = Op_1(𝖯₁^{∼3}; 𝕋_1)` are tested by `χ'_1` on the
mixed data of the spins `φ` (layer `0`) and `θ = z₁ψ₁` (layer `1`): the second partition of unity is
`1 = ∏_{c ∈ C} (χ'_1(c) + (1 - χ'_1(c))) = ∑_{𝖰₁ ⊆ C} ∏_{c ∈ 𝖰₁} (1 - χ'_1(c)) ∏_{c ∈ C ∖ 𝖰₁} χ'_1(c)`.

The cube set `C` is the set where `𝖰₁` lives; the record constraint is `𝖰₁ ⊆ Ω₁^{∼3}`
(`BaseRecord.Q_sub`), so the source's reading is `C = Ω₁(𝖯₁)^{∼3}`. The identity holds for every
finite cube set `C` (any function of `𝖯₁`), in particular for `C = Ω₁^{∼3}` (`baseCubesQ`) and for
the narrower reading `C = Ω₁` (`baseCubesOmega`).

* `baseOmegaFin`, `baseChiPrimeOne`: `χ'_1(c)` at the first step: the landed `chiPrimeNew` at
  `k = 0`, `M₁ = 1`, `N₁ = n`, `c = 1` (the convention of `baseSectorN`: the fine torus is
  `Torus d (1 * n * L ^ 1)` and the cubes are the `1`-blocks) on the spins `baseSectorSpin φ` and the
  coarse field `baseSectorTheta θ`; measurable in `φ`, with values in `{0, 1}`;
* `integral_partition_prod`: the partition of unity for the integral of an integrable function;
* `baseRho1_eq_sum_firstP_Q`: the exact identity `ρ₁ = z₁^{N|𝕋_n|} ∑_{𝖯₁} ∑_{𝖰₁ ⊆ C(𝖯₁)} ∫ [P-factors]
  ∏_{𝖰₁}(1 - χ'_1) ∏_{C ∖ 𝖰₁} χ'_1 · K e^{-βH + ⟨g, φ⟩} dσ`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale MeasureTheory

section Partition

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [DecidableEq ι]

/-- The partition of unity on a finite cube set:
`∑_{Q ⊆ C} ∏_{c ∈ Q} (1 - χ_c) ∏_{c ∈ C ∖ Q} χ_c = 1`. -/
theorem sum_powerset_prod_eq_one (C : Finset ι) (χ : ι → ℝ) :
    ∑ Q ∈ C.powerset, (∏ c ∈ Q, (1 - χ c)) * ∏ c ∈ C \ Q, χ c = 1 := by
  rw [← Finset.prod_add]
  exact Finset.prod_eq_one fun c _ => by ring

/-- **The second partition of unity for an integral**: for an integrable `G` and measurable cube
tests with values in `[0, 1]`, `∫ G = ∑_{Q ⊆ C} ∫ ∏_{Q}(1 - χ) ∏_{C ∖ Q} χ · G`. -/
theorem integral_partition_prod (μ : Measure X) (C : Finset ι) (χ : ι → X → ℝ)
    (hm : ∀ c, Measurable (χ c)) (h01 : ∀ c x, 0 ≤ χ c x ∧ χ c x ≤ 1) (G : X → ℂ)
    (hG : Integrable G μ) :
    ∫ x, G x ∂μ = ∑ Q ∈ C.powerset, ∫ x,
      (((∏ c ∈ Q, (1 - χ c x)) * ∏ c ∈ C \ Q, χ c x : ℝ) : ℂ) * G x ∂μ := by
  have hw : ∀ Q : Finset ι, Measurable fun x =>
      (∏ c ∈ Q, (1 - χ c x)) * ∏ c ∈ C \ Q, χ c x := fun Q =>
    (Finset.measurable_prod _ fun c _ => measurable_const.sub (hm c)).mul
      (Finset.measurable_prod _ fun c _ => hm c)
  have hw1 : ∀ (Q : Finset ι) x, 0 ≤ (∏ c ∈ Q, (1 - χ c x)) * ∏ c ∈ C \ Q, χ c x ∧
      (∏ c ∈ Q, (1 - χ c x)) * ∏ c ∈ C \ Q, χ c x ≤ 1 := by
    intro Q x
    have h1 : 0 ≤ ∏ c ∈ Q, (1 - χ c x) :=
      Finset.prod_nonneg fun c _ => sub_nonneg.mpr (h01 c x).2
    have h2 : ∏ c ∈ Q, (1 - χ c x) ≤ 1 :=
      Finset.prod_le_one₀ (fun c _ => sub_nonneg.mpr (h01 c x).2)
        (fun c _ => sub_le_self 1 (h01 c x).1)
    have h3 : 0 ≤ ∏ c ∈ C \ Q, χ c x := Finset.prod_nonneg fun c _ => (h01 c x).1
    have h4 : ∏ c ∈ C \ Q, χ c x ≤ 1 := Finset.prod_le_one₀ (fun c _ => (h01 c x).1)
      fun c _ => (h01 c x).2
    exact ⟨mul_nonneg h1 h3, by nlinarith⟩
  have hint : ∀ Q ∈ C.powerset, Integrable (fun x =>
      (((∏ c ∈ Q, (1 - χ c x)) * ∏ c ∈ C \ Q, χ c x : ℝ) : ℂ) * G x) μ := by
    intro Q _
    refine hG.norm.mono' ((Complex.measurable_ofReal.comp (hw Q)).aestronglyMeasurable.mul
      hG.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw1 Q x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw1 Q x).2
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show G x = ∑ Q ∈ C.powerset,
    (((∏ c ∈ Q, (1 - χ c x)) * ∏ c ∈ C \ Q, χ c x : ℝ) : ℂ) * G x
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_powerset_prod_eq_one C (fun c => χ c x)]
  simp

end Partition

section Instance

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- The fine set of the cubes `W ⊆ 𝕋_1` (here the `1`-blocks of `Torus d (1 * n * L ^ 1)`): the set
`Om = Ω₁` of the mixed data at `k = 0`. -/
noncomputable def baseOmegaFin (W : Set (Torus d n)) : Finset (Torus d (1 * n * L ^ (0 + 1))) :=
  cubePre 1 n L (0 + 1) (L ^ (0 + 1) * (1 * 1)) n W

theorem baseOmegaFin_blockUnion (W : Set (Torus d n)) :
    IsBlockUnion L (1 * n) (0 + 1) (0 + 1) (baseOmegaFin (L := L) W) :=
  (isCubeUnion_cubePre (M1 := 1) (N₁ := n) (L := L) (q := 0 + 1) (n := 0 + 1) (c := 1)
    (m := n) le_rfl (by simp) W).isBlockUnion le_rfl

/-- **`χ'_1(□')` at the first step** (P5 (2.13)–(2.14) at `k = 0`; LFR Definition II.3.2 item 3
with `lift_{0,1}(φ, θ)`): the landed `chiPrimeNew` at `k = 0` with `M₁ = 1`, `N₁ = n`, `c = 1`, the
set `Ω = Ω₁ = baseOmegaFin W`, the spins `baseSectorSpin φ` (layer `0`) and the coarse field
`baseSectorTheta θ` (layer `1`). -/
noncomputable def baseChiPrimeOne (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ) (W : Set (Torus d n))
    (y0 : Torus d n) (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) : ℝ :=
  chiPrimeNew (M1 := 1) (N₁ := n) (L := L) (N := N) (k := 0) a μ δ νk h (c := 1) (n := n)
    (by simp) y0 (baseOmegaFin W) (baseOmegaFin_blockUnion W)
    (baseSectorSpin φ, baseSectorTheta θ)

theorem baseChiPrimeOne_zero_or_one (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ)
    (W : Set (Torus d n)) (y0 : Torus d n) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) :
    0 ≤ baseChiPrimeOne a μ δ νk h W y0 θ φ ∧ baseChiPrimeOne a μ δ νk h W y0 θ φ ≤ 1 := by
  classical
  unfold baseChiPrimeOne chiPrimeNew
  rw [charFn_apply]
  split_ifs <;> norm_num

/-- `χ'_1(□')` is Borel in the spins (Lemma II.3.3). -/
theorem measurable_baseChiPrimeOne (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin N → ℝ)
    (H : BgHyp d L (0 + 1) (minSep L 1) a μ) (W : Set (Torus d n)) (y0 : Torus d n)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Measurable (baseChiPrimeOne (L := L) a μ δ νk h W y0 θ) := by
  have hm := measurable_chiPrimeNew (M1 := 1) (N₁ := n) (L := L) (N := N) (k := 0) (c := 1)
    (n := n) (by simp) y0 (baseOmegaFin W) (baseOmegaFin_blockUnion W) h a μ δ νk H
  have hs : Measurable (fun φ : CfgT d N L n => baseSectorSpin φ) :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => measurable_baseSectorSpin x i
  exact hm.comp (hs.prodMk measurable_const)

end Instance

end Balaban.LargeField
