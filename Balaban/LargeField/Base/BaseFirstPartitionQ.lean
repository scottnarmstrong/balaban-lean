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

section Identity

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

/-- The bare spin integrand `K(θ, φ) e^{-βH(φ) + ⟨g, φ⟩}` of the first density. -/
noncomputable def baseFirstF (β a ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : ℂ :=
  ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
    Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
      ∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))

omit [NeZero N] in
/-- A measurable weight in `[0, 1]` times the bare integrand is integrable (the integrand is
continuous on the compact configuration space). -/
theorem integrable_weight_mul_baseFirstF (β a ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (w : CfgT d N L n → ℝ) (hw : Measurable w) (hw1 : ∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) :
    Integrable (fun φ : CfgT d N L n => ((w φ : ℝ) : ℂ) * baseFirstF β a ν h g θ φ)
      (aprioriMeasure d N (L * n)) := by
  have hFcont : Continuous (baseFirstF β a ν h g θ) := by
    unfold baseFirstF
    dsimp [baseKernel, baseQ, gaussT, energy]
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hFcont.continuousOn
  refine Integrable.of_bound
    ((Complex.measurable_ofReal.comp hw).mul hFcont.measurable).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw1 φ).1]
  calc _ ≤ 1 * ‖baseFirstF β a ν h g θ φ‖ :=
        mul_le_mul_of_nonneg_right (hw1 φ).2 (norm_nonneg _)
    _ ≤ C := by rw [one_mul]; exact hC φ (Set.mem_univ _)

open Classical in
/-- **The exact identity for the cubes `𝖰₁`** (P5 (2.14) at `k = 0`; LFR Lemma II.7.2): for every
choice of the cube sets `C(𝖯₁) ⊆ 𝕋_1` (in particular `C = Ω₁(𝖯₁)^{∼3}`, `baseCubesQ`) and of the sets
`Ω(𝖯₁)` entering the mixed data,
`ρ₁(ψ; g) = z₁^{N|𝕋_n|} ∑_{𝖯₁} ∑_{𝖰₁ ⊆ C(𝖯₁)} ∫ [P-factors] ∏_{c ∈ 𝖰₁} (1 - χ'_1(c))
∏_{c ∈ C(𝖯₁) ∖ 𝖰₁} χ'_1(c) · K e^{-βH + ⟨g, φ⟩} dσ`, with `θ = z₁ψ`. -/
theorem baseRho1_eq_sum_firstP_Q
    (β a z ν : ℝ) (regimeB : Prop) (δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (aχ : ℕ → ℝ) (μχ δχ νχ : ℝ) (Hbg : BgHyp d L (0 + 1) (minSep L 1) aχ μχ)
    (Wset : Finset (Torus d n) → Set (Torus d n))
    (Cset : Finset (Torus d n) → Finset (Torus d n)) :
    baseRho1 d N L n β a z ν h ψ g =
      ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset,
          ∑ Q ∈ (Cset P).powerset,
            ∫ φ, ((((∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
                (fun i => h i) c (baseSectorSpin φ, baseSectorTheta (z • ψ)))) *
              ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
                chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
                  (baseSectorSpin φ, baseSectorTheta (z • ψ))) *
              ((∏ c ∈ Q, (1 - baseChiPrimeOne aχ μχ δχ νχ (fun i => h i) (Wset P) c (z • ψ) φ)) *
                ∏ c ∈ Cset P \ Q,
                  baseChiPrimeOne aχ μχ δχ νχ (fun i => h i) (Wset P) c (z • ψ) φ) : ℝ) : ℂ) *
              baseFirstF β a ν h g (z • ψ) φ ∂aprioriMeasure d N (L * n) := by
  rw [baseRho1_eq_sum_firstP β a z ν regimeB δ₀ h g ψ]
  congr 1
  refine Finset.sum_congr rfl fun P _ => ?_
  obtain ⟨hWm, hW0, hW1⟩ := baseFirstPhysicalP_weight_measurable_unit (d := d) (N := N) (L := L)
    (n := n) regimeB ν δ₀ h (z • ψ) P
  have hG := integrable_weight_mul_baseFirstF β a ν h g (z • ψ) _ hWm
    (fun φ => ⟨hW0 φ, hW1 φ⟩)
  refine (integral_partition_prod (aprioriMeasure d N (L * n)) (Cset P)
    (fun c φ => baseChiPrimeOne aχ μχ δχ νχ (fun i => h i) (Wset P) c (z • ψ) φ)
    (fun c => measurable_baseChiPrimeOne aχ μχ δχ νχ (fun i => h i) Hbg (Wset P) c (z • ψ))
    (fun c φ => baseChiPrimeOne_zero_or_one aχ μχ δχ νχ (fun i => h i) (Wset P) c (z • ψ) φ) _ hG).trans ?_
  refine Finset.sum_congr rfl fun Q _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [Complex.ofReal_mul]
  ring

end Identity

section Records

variable {d L n : ℕ} [NeZero L] [NeZero n]

open Classical in
/-- **The cube set of `𝖰₁`** (P5 (2.14) at `k = 0`; the record constraint `Q_sub`): the cubes of
`Ω₁(𝖯₁)^{∼3}`, `Ω₁ = Op_1(𝖯₁^{∼3}; 𝕋_1)`. -/
noncomputable def baseCubesQ (P : Finset (Torus d n)) : Finset (Torus d n) :=
  (Set.toFinite (nbhd 3 (Region.Omega L (P : Set (Torus d n)) Set.univ))).toFinset

/-- The narrower reading: the cubes of `Ω₁(𝖯₁)` only. -/
noncomputable def baseCubesOmega (P : Finset (Torus d n)) : Finset (Torus d n) :=
  (Set.toFinite (Region.Omega L (P : Set (Torus d n)) Set.univ)).toFinset

omit [NeZero L] in
theorem mem_baseCubesQ {P : Finset (Torus d n)} {c : Torus d n} :
    c ∈ baseCubesQ (L := L) P ↔ c ∈ nbhd 3 (Region.Omega L (P : Set (Torus d n)) Set.univ) := by
  classical
  simp [baseCubesQ]

omit [NeZero L] in
theorem mem_baseCubesOmega {P : Finset (Torus d n)} {c : Torus d n} :
    c ∈ baseCubesOmega (L := L) P ↔ c ∈ Region.Omega L (P : Set (Torus d n)) Set.univ := by
  classical
  simp [baseCubesOmega]

omit [NeZero L] in
theorem baseCubesOmega_subset (P : Finset (Torus d n)) :
    baseCubesOmega (L := L) P ⊆ baseCubesQ (L := L) P := fun _ hc =>
  mem_baseCubesQ.2 (subset_nbhd 3 _ (mem_baseCubesOmega.1 hc))

omit [NeZero L] in
/-- **The cubes `𝖰₁` of a base record lie in the cube set `C(𝖯₁)`** (the constraint `Q ⊆ Ω₁^{∼3}`
of Definition II.7.1). -/
theorem BaseRecord.Q_subset_cubesQ {Rk : ℝ} (br : BaseRecord d L n Rk) (P : Finset (Torus d n))
    (hP : br.P = (P : Set (Torus d n))) {c : Torus d n} (hc : c ∈ br.Q) :
    c ∈ baseCubesQ (L := L) P := by
  refine mem_baseCubesQ.2 ?_
  have := br.Q_sub hc
  rwa [hP] at this

omit [NeZero L] in
/-- The cubes `𝖰₁` lie in `F''_1`, hence the opening `Ω''_1` is built from them. -/
theorem BaseRecord.Q_subset_FDD {Rk : ℝ} (br : BaseRecord d L n Rk) {c : Torus d n}
    (hc : c ∈ br.Q) : c ∈ br.FDD :=
  Or.inl (subset_nbhd _ _ hc)

end Records

end Balaban.LargeField
