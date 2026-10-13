/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsTerms
public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Inhabited.HatExpansionWitnessLabels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The clipped coordinate marks: bounds and mean zero (OBSMARKS 8.4)

This is a routine leaf.  The observable marks family (`ObsMarks` for the physical zero-class step)
is NOT constructed here.

The first-order marks of the zero-class step are the fluctuation coordinates `ψ̂(z)_a`, clipped to
the cutoff ball: `clippedCoord N p a v = v_a` if `‖v‖ < p` and `0` otherwise.  We prove

* `norm_clippedCoord_le`: `|G v| ≤ p` for every `v`; `clippedCoord_ae_eq`: `G v = v_a`
  `fluctMeasure1 N p`-almost everywhere;
* `map_neg_fluctMeasure1`: the truncated Gaussian `fluctMeasure1 N p` is invariant under
  `v ↦ -v`; hence `integral_clippedCoord_fluctMeasure1`: `∫ G d(fluctMeasure1 N p) = 0`;
* the same on the site product `fluctMeasure U N p` (`siteMark`);
* through the landed block split `S.blockSplit m₀ hp`: the mark `blockMark` of a unit point `u`
  and a component `a` satisfies the four first-order fields of `ObsMarks`
  (`meas1`, `dep1`, `bound1`, `mean1`) literally (`blockMark_fields`);
* one instance at the landed witness step `Balaban.Inhabited.hatWitnessStep`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer

/-! ### One site -/

/-- The coordinate `v_a`, clipped to the open cutoff ball `‖v‖ < p` (and `0` outside it). -/
noncomputable def clippedCoord (N : ℕ) (p : ℝ) (a : Fin N) (v : Rn N) : ℂ :=
  open Classical in if ‖v‖ < p then ((v a : ℝ) : ℂ) else 0

theorem clippedCoord_of_lt {N : ℕ} {p : ℝ} (a : Fin N) {v : Rn N} (h : ‖v‖ < p) :
    clippedCoord N p a v = ((v a : ℝ) : ℂ) := by
  simp [clippedCoord, h]

/-- The clipped coordinate is bounded by the cutoff radius for **every** `v`. -/
theorem norm_clippedCoord_le {N : ℕ} {p : ℝ} (hp : 0 ≤ p) (a : Fin N) (v : Rn N) :
    ‖clippedCoord N p a v‖ ≤ p := by
  by_cases h : ‖v‖ < p
  · rw [clippedCoord_of_lt a h, Complex.norm_real, Real.norm_eq_abs]
    exact ((by simpa using PiLp.norm_apply_le v a : |v a| ≤ ‖v‖).trans h.le)
  · simp only [clippedCoord, h, ite_false, norm_zero]; exact hp

theorem measurable_clippedCoord (N : ℕ) (p : ℝ) (a : Fin N) :
    Measurable (clippedCoord N p a) := by
  unfold clippedCoord
  refine Measurable.ite (measurableSet_lt measurable_norm measurable_const) ?_ measurable_const
  exact Complex.measurable_ofReal.comp (EuclideanSpace.proj a).continuous.measurable

theorem clippedCoord_neg (N : ℕ) (p : ℝ) (a : Fin N) (v : Rn N) :
    clippedCoord N p a (-v) = - clippedCoord N p a v := by
  by_cases h : ‖v‖ < p
  · rw [clippedCoord_of_lt a (by simpa using h), clippedCoord_of_lt a h]
    simp
  · have h' : ¬ ‖-v‖ < p := by simpa using h
    simp [clippedCoord, h]

/-- The clipped coordinate is the coordinate, `fluctMeasure1`-almost everywhere. -/
theorem clippedCoord_ae_eq (N : ℕ) (p : ℝ) (a : Fin N) :
    ∀ᵐ v ∂fluctMeasure1 N p, clippedCoord N p a v = ((v a : ℝ) : ℂ) := by
  filter_upwards [ae_norm_lt_fluctMeasure1 N p] with v hv using clippedCoord_of_lt a hv

/-- **Evenness of the truncated Gaussian**: `fluctMeasure1 N p` is invariant under `v ↦ -v`. -/
theorem map_neg_fluctMeasure1 (N : ℕ) (p : ℝ) :
    Measure.map (Neg.neg : Rn N → Rn N) (fluctMeasure1 N p) = fluctMeasure1 N p := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  have hs' : MeasurableSet ((Neg.neg : Rn N → Rn N) ⁻¹' s) := measurable_neg hs
  set F : Rn N → ENNReal := fun x => ENNReal.ofReal (fluctDensity N p x) with hF
  have hFm : Measurable F := (measurable_fluctDensity N p).ennreal_ofReal
  have hFe : ∀ x, F (-x) = F x := fun x => by simp [hF, fluctDensity]
  unfold fluctMeasure1
  rw [Measure.smul_apply, Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs']
  congr 1
  rw [← lintegral_indicator hs, ← lintegral_indicator hs']
  have hmp : MeasurePreserving (Neg.neg : Rn N → Rn N) volume volume :=
    Measure.measurePreserving_neg volume
  have := hmp.lintegral_comp_emb (MeasurableEquiv.neg (Rn N)).measurableEmbedding
    (s.indicator F)
  rw [← this]
  refine lintegral_congr fun x => ?_
  by_cases hx : -x ∈ s
  · simp [Set.indicator_of_mem, hx, hF, fluctDensity]
  · simp [Set.indicator_of_notMem, hx]

/-- **Mean zero for one site**: an odd integrable function has integral zero under an even
probability measure. -/
theorem integral_clippedCoord_fluctMeasure1 (N : ℕ) (p : ℝ) (a : Fin N) :
    ∫ v, clippedCoord N p a v ∂fluctMeasure1 N p = 0 := by
  set I := ∫ v, clippedCoord N p a v ∂fluctMeasure1 N p with hI
  have h1 : I = ∫ v, clippedCoord N p a v ∂Measure.map (Neg.neg : Rn N → Rn N)
      (fluctMeasure1 N p) := by rw [map_neg_fluctMeasure1]
  rw [integral_map measurable_neg.aemeasurable
    ((measurable_clippedCoord N p a).aestronglyMeasurable)] at h1
  simp only [clippedCoord_neg, integral_neg] at h1
  rw [← hI] at h1
  have : I + I = 0 := by linear_combination h1
  have h2 : (2 : ℂ) * I = 0 := by linear_combination this
  simpa using h2

/-! ### The site product -/

section SiteProduct

variable {U : Type*} [Fintype U]

/-- The clipped coordinate at the site `z` and component `a` on the site product. -/
noncomputable def siteMark (N : ℕ) (p : ℝ) (z : U) (a : Fin N) (x : U → Rn N) : ℂ :=
  clippedCoord N p a (x z)

omit [Fintype U] in
theorem norm_siteMark_le {N : ℕ} {p : ℝ} (hp : 0 ≤ p) (z : U) (a : Fin N) (x : U → Rn N) :
    ‖siteMark N p z a x‖ ≤ p := norm_clippedCoord_le hp a (x z)

omit [Fintype U] in
theorem measurable_siteMark (N : ℕ) (p : ℝ) (z : U) (a : Fin N) :
    Measurable (siteMark N p z a) :=
  (measurable_clippedCoord N p a).comp (measurable_pi_apply z)

/-- The integral of a function of the coordinate at one site, in a product of probability
measures. -/
theorem integral_comp_eval_pi {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) {g : Ω i → ℂ}
    (hg : Measurable g) :
    ∫ x, g (x i) ∂Measure.pi μ = ∫ y, g y ∂μ i := by
  have := (measurePreserving_eval μ i).map_eq
  rw [← this, integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]

/-- **Mean zero on the site product**: `∫ siteMark z a d(fluctMeasure U N p) = 0`. -/
theorem integral_siteMark {N : ℕ} {p : ℝ} (hp : 0 < p) (z : U) (a : Fin N) :
    ∫ x, siteMark N p z a x ∂fluctMeasure U N p = 0 := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  unfold siteMark fluctMeasure
  rw [integral_comp_eval_pi (fun _ : U => fluctMeasure1 N p) z (measurable_clippedCoord N p a)]
  exact integral_clippedCoord_fluctMeasure1 N p a

end SiteProduct

/-! ### Through the landed block split -/

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

open Classical in
/-- **The clipped coordinate mark of a unit point `u` and a component `a`** on the block
configurations of the landed split `S.blockSplit m₀ hp`: it reads the fluctuation vector at `u`,
which sits in the block `S.cellOf m₀ u`. -/
noncomputable def blockMark (hp : 0 < S.p₁) (u : S.U) (a : Fin N)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  clippedCoord N S.p₁ a (Φ (S.cellOf m₀ u) ⟨u, rfl⟩)

/-- The mark as a function of the single block variable of `u`. -/
noncomputable def blockFiber (hp : 0 < S.p₁) (u : S.U) (a : Fin N)
    (y : (S.blockSplit m₀ hp).Ωb (S.cellOf m₀ u)) : ℂ :=
  clippedCoord N S.p₁ a (y ⟨u, rfl⟩)

theorem measurable_blockFiber (hp : 0 < S.p₁) (u : S.U) (a : Fin N) :
    Measurable (blockFiber S m₀ hp u a) :=
  (measurable_clippedCoord N S.p₁ a).comp
    (measurable_pi_apply (⟨u, rfl⟩ : {v : S.U // S.cellOf m₀ v = S.cellOf m₀ u}))

theorem norm_blockMark_le (hp : 0 < S.p₁) (u : S.U) (a : Fin N) (Φ) :
    ‖blockMark S m₀ hp u a Φ‖ ≤ S.p₁ :=
  norm_clippedCoord_le hp.le a _

theorem measurable_blockMark (hp : 0 < S.p₁) (u : S.U) (a : Fin N) :
    Measurable (blockMark S m₀ hp u a) :=
  (measurable_clippedCoord N S.p₁ a).comp
    ((measurable_pi_apply (⟨u, rfl⟩ : {v : S.U // S.cellOf m₀ v = S.cellOf m₀ u})).comp
      (measurable_pi_apply (S.cellOf m₀ u)))

/-- The mark depends only on the block of `u`: on every set of blocks containing it. -/
theorem depOn_blockMark (hp : 0 < S.p₁) (u : S.U) (a : Fin N)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT : S.cellOf m₀ u ∈ T) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) T (blockMark S m₀ hp u a) := by
  intro Φ Φ' h
  unfold blockMark
  rw [h _ hT]

/-- **Mean zero through the block split**: `∫ blockMark d(Measure.pi BS.μ) = 0`. -/
theorem integral_blockMark (hp : 0 < S.p₁) (u : S.U) (a : Fin N) :
    ∫ Φ, blockMark S m₀ hp u a Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0 := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  unfold blockMark
  have h1 := integral_comp_eval_pi (Ω := (S.blockSplit m₀ hp).Ωb) (S.blockSplit m₀ hp).μ
    (S.cellOf m₀ u) (g := blockFiber S m₀ hp u a) (measurable_blockFiber S m₀ hp u a)
  have h2 := integral_comp_eval_pi (fun _ => fluctMeasure1 N S.p₁)
    (⟨u, rfl⟩ : {v : S.U // S.cellOf m₀ v = S.cellOf m₀ u}) (measurable_clippedCoord N S.p₁ a)
  exact h1.trans (h2.trans (integral_clippedCoord_fluctMeasure1 N S.p₁ a))

/-- **The four first-order fields of `ObsMarks` for the clipped coordinate mark.**  Let `Lab` be a
label structure for the step, `y` one of its labels whose block set contains the block of `u`
and whose size `dl y` is `0` (the label of the single mark cube), `F₁ = p₁`.  Then
`meas1`, `dep1` (with the blocks of the label), `bound1` (for every block configuration) and
`mean1` hold literally; and `0 < F₁`. -/
theorem blockMark_fields (hp : 0 < S.p₁) (u : S.U) (a : Fin N) {Lb : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb) (y : Lb)
    (hy : S.cellOf m₀ u ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ (Lab.ysite y))
    (hdl : Lab.dl y = 0) (κG : ℝ) :
    Measurable (blockMark S m₀ hp u a) ∧
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ (Lab.ysite y)) (blockMark S m₀ hp u a) ∧
    0 < S.p₁ ∧
    (∀ Φ, ‖blockMark S m₀ hp u a Φ‖ ≤ S.p₁ * Real.exp (-κG * Lab.dl y)) ∧
    ∫ Φ, blockMark S m₀ hp u a Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0 := by
  refine ⟨measurable_blockMark S m₀ hp u a, depOn_blockMark S m₀ hp u a hy, hp, fun Φ => ?_,
    integral_blockMark S m₀ hp u a⟩
  rw [hdl]
  simpa using norm_blockMark_le S m₀ hp u a Φ

end Block

/-! ### One instance at a landed step -/

/-- **Non-vacuity**: at the landed witness step `Balaban.Inhabited.hatWitnessStep` (`d = L = 3`, `N₁ = 9`, `k = 1`,
any `N`, `m₀ = 1`, any cutoff radius `p₁ > 0`) and its block split `blockSplit 1`, the clipped mark
of every unit point and component is measurable, bounded by `p₁` everywhere, has integral zero,
and depends only on the block of its point. -/
theorem blockMark_witness (N m₁ : ℕ) {p₁ : ℝ} (hp : 0 < p₁)
    (u : (Balaban.Inhabited.hatWitnessStep N m₁ p₁).U) (a : Fin N) :
    ∃ hp' : 0 < (Balaban.Inhabited.hatWitnessStep N m₁ p₁).p₁,
      Measurable (blockMark (Balaban.Inhabited.hatWitnessStep N m₁ p₁) 1 hp' u a) ∧
      (∀ Φ, ‖blockMark (Balaban.Inhabited.hatWitnessStep N m₁ p₁) 1 hp' u a Φ‖ ≤ p₁) ∧
      DepOn (Ω := ((Balaban.Inhabited.hatWitnessStep N m₁ p₁).blockSplit 1 hp').Ωb)
        {(Balaban.Inhabited.hatWitnessStep N m₁ p₁).cellOf 1 u} (blockMark (Balaban.Inhabited.hatWitnessStep N m₁ p₁) 1 hp' u a) ∧
      ∫ Φ, blockMark (Balaban.Inhabited.hatWitnessStep N m₁ p₁) 1 hp' u a Φ
        ∂Measure.pi ((Balaban.Inhabited.hatWitnessStep N m₁ p₁).blockSplit 1 hp').μ = 0 := by
  have hp' : 0 < (Balaban.Inhabited.hatWitnessStep N m₁ p₁).p₁ := hp
  exact ⟨hp', measurable_blockMark _ 1 hp' u a, fun Φ => norm_blockMark_le _ 1 hp' u a Φ,
    depOn_blockMark _ 1 hp' u a (by simp), integral_blockMark _ 1 hp' u a⟩

end Balaban.Fluctuation
