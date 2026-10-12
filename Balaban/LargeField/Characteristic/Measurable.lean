module

public import Balaban.LargeField.Characteristic.MeasurableAux
import Mathlib.Tactic.Linarith

/-!
# Measurability of the regularity predicate for continuous families of real data

(Lemma II.3.3, first half.) Let `Y` be a measurable space with a topology
(`OpensMeasurableSpace`) and `D : Y → BgData G N` a family of real data with continuous
coordinates and `h̃ ≡ h` on `Ω₁`. Then `{y | Reg a μ G (D y) δ T S}` and
`{y | D y ∈ 𝒟_ℝ ∧ RegMixedIneq ...}` are measurable.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

set_option linter.unusedSectionVars false

section Domain

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

theorem measurableSet_forall_lt_meas {ι : Type*} [Finite ι] {f : ι → Y → ℝ}
    (hf : ∀ i, Measurable (f i)) (p : ι → Prop) (c : ι → ℝ) :
    MeasurableSet {y | ∀ i, p i → f i y < c i} := by
  have : {y | ∀ i, p i → f i y < c i} = ⋂ i, {y | p i → f i y < c i} := by
    ext y; simp
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hp : p i
  · simp only [hp, forall_true_left]
    exact measurableSet_lt (hf i) measurable_const
  · simp [hp]

theorem measurable_rn {v : Y → Fin N → ℝ} (hv : ∀ i, Measurable fun y => v y i) :
    Measurable fun y => rn (v y) :=
  Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => (hv i).pow_const 2)

variable {G : GeneratingSet d L N₀ q ϱ} {μ : ℝ} (D : Y → BgData G N)

/-- **The real domain is measurable** for a family of real data with `h̃ ≡ h` and continuous
coordinates. -/
theorem measurableSet_domR (hd : 0 < d) {h : Fin N → ℝ}
    (hΨ : ∀ y x i, ((D y).Ψ x i).im = 0) (hh : ∀ y, ∀ x ∈ G.Ω 1, ∀ i, (D y).h x i = (h i : ℂ))
    (hΨc : ∀ x i, Continuous fun y => (D y).Ψ x i) :
    MeasurableSet {y | InUnionDomainR G (bgC1 d L N) μ (D y)} := by
  classical
  by_cases hne : (G.Ω 1).Nonempty
  · have hc := bgC1_pos_of (L := L) (N := N) hd
    have hre : ∀ x i, Measurable fun y => ((D y).Ψ x i).re := fun x i =>
      (Complex.continuous_re.comp (hΨc x i)).measurable
    have hset : {y | InUnionDomainR G (bgC1 d L N) μ (D y)} =
        {y | (∀ p : Torus d (N₀ * L ^ q) × Torus d (N₀ * L ^ q), IsInterfacePair G p.1 p.2 →
            rn (fun i => ((D y).Ψ p.1 i).re - ((D y).Ψ p.2 i).re) < bgC1 d L N) ∧
          (∀ x : Torus d (N₀ * L ^ q), x ∈ dataSites G →
            |∑ i, ((D y).Ψ x i).re ^ 2 - 1| < bgC1 d L N) ∧
          (∀ x : Torus d (N₀ * L ^ q), x ∈ dataSites G →
            μ * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
              |1 - (∑ i, ((D y).Ψ x i).re * h i) / rn (fun i => ((D y).Ψ x i).re)| <
              bgC1 d L N ^ 2) ∧
          μ * ((L : ℝ) ^ q) ^ 2 * |∑ i, h i ^ 2 - 1| < bgC1 d L N ^ 2} := by
      ext y
      rw [Set.mem_ofPred_eq, inUnionDomainR_iff hc hne (hΨ y) (hh y)]
      constructor
      · intro P
        exact ⟨fun p hp => P.r1 p.1 p.2 hp, P.r2, P.r3, P.r4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨?_, fun x x' hx => h1 (x, x') hx, h2, h3, h4⟩
        intro n hn1 hnk x hx x' hx'
        simp only [(D y).Ψ_layerConst n hn1 hnk x hx x' hx']
    rw [hset]
    refine ((measurableSet_forall_lt_meas (ι := Torus d (N₀ * L ^ q) × Torus d (N₀ * L ^ q))
      (f := fun p y => rn (fun i => ((D y).Ψ p.1 i).re - ((D y).Ψ p.2 i).re))
      (fun p => measurable_rn fun i => (hre _ i).sub (hre _ i)) _ fun _ => bgC1 d L N)).inter
      ((measurableSet_forall_lt_meas (ι := Torus d (N₀ * L ^ q))
        (f := fun x y => |∑ i, ((D y).Ψ x i).re ^ 2 - 1|)
        (fun x => (continuous_abs.measurable.comp
          ((Finset.measurable_sum _ fun i _ => (hre x i).pow_const 2).sub_const 1))) _
        fun _ => bgC1 d L N).inter
      ((measurableSet_forall_lt_meas (ι := Torus d (N₀ * L ^ q))
        (f := fun x y => μ * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
          |1 - (∑ i, ((D y).Ψ x i).re * h i) / rn (fun i => ((D y).Ψ x i).re)|)
        (fun x => measurable_const.mul (continuous_abs.measurable.comp
          (measurable_const.sub
            ((Finset.measurable_sum _ fun i _ => (hre x i).mul_const (h i)).div
              (measurable_rn fun i => hre x i))))) _ fun _ => bgC1 d L N ^ 2).inter ?_))
    exact MeasurableSet.const _
  · have hemp : G.Ω 1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    by_cases hy : ∃ y₀, InUnionDomainR G (bgC1 d L N) μ (D y₀)
    · obtain ⟨y₀, hy₀⟩ := hy
      have : {y | InUnionDomainR G (bgC1 d L N) μ (D y)} = Set.univ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (inUnionDomainR_of_empty hemp (D y₀)).2 hy₀
      rw [this]; exact MeasurableSet.univ
    · push Not at hy
      have : {y | InUnionDomainR G (bgC1 d L N) μ (D y)} = ∅ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact hy y
      rw [this]; exact MeasurableSet.empty

end Domain


/-! ### The inequalities -/

section Ineq

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {G : GeneratingSet d L N₀ q ϱ} {D : Y → BgData G N} {E : Set Y} (hE : MeasurableSet E)
  {φ : Y → G.Ω 1 × Fin N → ℂ} {α : Y → G.Ω 1 → ℂ}
  (hφ : ContinuousOn φ E) (hα : ContinuousOn α E)
  (hΨ : ∀ x i, Continuous fun y => (D y).Ψ x i) (hh : ∀ x i, Continuous fun y => (D y).h x i)

include hE hφ hΨ in
theorem measurableSet_blockClose (T : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) :
    MeasurableSet {y | y ∈ E ∧ BlockClose G (D y) (φ y) T δ} :=
  measurableSet_forall_lt (ι := Torus d (N₀ * L ^ q)) (E := E)
    (f := fun x y => blockDev G (D y) (φ y) x) (p := fun x => x ∈ T) (c := fun _ => δ) hE
    fun x _ => contOn_blockDev hφ hΨ x

theorem gradClose_iff (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (ℓ δ : ℝ)
    (S : Finset (Torus d (N₀ * L ^ q))) :
    GradClose G D φ α ℓ S δ ↔
      (∀ p : G.Ω 1 × Fin d, (p.1 : Torus d (N₀ * L ^ q)) ∈ S →
          ℓ * vn (barVec G D φ ((p.1 : Torus d (N₀ * L ^ q)) + Pi.single p.2 1) -
            barVec G D φ p.1) < δ) ∧
      (∀ p : G.Ω 1 × Fin d, (p.1 : Torus d (N₀ * L ^ q)) ∈ S →
          ℓ * vn (barVec G D φ ((p.1 : Torus d (N₀ * L ^ q)) - Pi.single p.2 1) -
            barVec G D φ p.1) < δ) ∧
      (∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S → ℓ ^ 2 * vn (barLap G D φ x) < δ) ∧
      (∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S → ℓ ^ 2 * ‖α x‖ < δ) := by
  unfold GradClose
  constructor
  · intro h
    exact ⟨fun p hp => ((h p.1 hp).1 p.2).1, fun p hp => ((h p.1 hp).1 p.2).2,
      fun x hx => (h x hx).2.1, fun x hx => (h x hx).2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩ x hx
    exact ⟨fun μ => ⟨h1 (x, μ) hx, h2 (x, μ) hx⟩, h3 x hx, h4 x hx⟩

include hE hφ hα hΨ in
theorem measurableSet_gradClose (ℓ δ : ℝ) (S : Finset (Torus d (N₀ * L ^ q))) :
    MeasurableSet {y | y ∈ E ∧ GradClose G (D y) (φ y) (α y) ℓ S δ} := by
  have e : {y | y ∈ E ∧ GradClose G (D y) (φ y) (α y) ℓ S δ} =
      {y | y ∈ E ∧ ∀ p : G.Ω 1 × Fin d, (p.1 : Torus d (N₀ * L ^ q)) ∈ S →
          ℓ * vn (barVec G (D y) (φ y) ((p.1 : Torus d (N₀ * L ^ q)) + Pi.single p.2 1) -
            barVec G (D y) (φ y) p.1) < δ} ∩
      {y | y ∈ E ∧ ∀ p : G.Ω 1 × Fin d, (p.1 : Torus d (N₀ * L ^ q)) ∈ S →
          ℓ * vn (barVec G (D y) (φ y) ((p.1 : Torus d (N₀ * L ^ q)) - Pi.single p.2 1) -
            barVec G (D y) (φ y) p.1) < δ} ∩
      {y | y ∈ E ∧ ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S →
          ℓ ^ 2 * vn (barLap G (D y) (φ y) x) < δ} ∩
      {y | y ∈ E ∧ ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S → ℓ ^ 2 * ‖α y x‖ < δ} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [gradClose_iff]
    constructor
    · rintro ⟨hy, h1, h2, h3, h4⟩
      exact ⟨⟨⟨⟨hy, h1⟩, hy, h2⟩, hy, h3⟩, hy, h4⟩
    · rintro ⟨⟨⟨⟨hy, h1⟩, -, h2⟩, -, h3⟩, -, h4⟩
      exact ⟨hy, h1, h2, h3, h4⟩
  have m1 := measurableSet_forall_lt (ι := G.Ω 1 × Fin d) (E := E)
      (f := fun p y => ℓ * vn (barVec G (D y) (φ y) ((p.1 : Torus d (N₀ * L ^ q)) +
        Pi.single p.2 1) - barVec G (D y) (φ y) p.1))
      (p := fun p => (p.1 : Torus d (N₀ * L ^ q)) ∈ S) (c := fun _ => δ) hE
      fun p _ => contOn_gradDiff hφ hΨ ℓ (p.1 : Torus d (N₀ * L ^ q)) ((p.1 : Torus d (N₀ * L ^ q)) + Pi.single p.2 1)
  have m2 := measurableSet_forall_lt (ι := G.Ω 1 × Fin d) (E := E)
      (f := fun p y => ℓ * vn (barVec G (D y) (φ y) ((p.1 : Torus d (N₀ * L ^ q)) -
        Pi.single p.2 1) - barVec G (D y) (φ y) p.1))
      (p := fun p => (p.1 : Torus d (N₀ * L ^ q)) ∈ S) (c := fun _ => δ) hE
      fun p _ => contOn_gradDiff hφ hΨ ℓ (p.1 : Torus d (N₀ * L ^ q)) ((p.1 : Torus d (N₀ * L ^ q)) - Pi.single p.2 1)
  have m3 := measurableSet_forall_lt (ι := G.Ω 1) (E := E)
      (f := fun x y => ℓ ^ 2 * vn (barLap G (D y) (φ y) x))
      (p := fun x => (x : Torus d (N₀ * L ^ q)) ∈ S) (c := fun _ => δ) hE
      fun x _ => contOn_lapScaled hφ hΨ ℓ x
  have m4 := measurableSet_forall_lt (ι := G.Ω 1) (E := E)
      (f := fun x y => ℓ ^ 2 * ‖α y x‖)
      (p := fun x => (x : Torus d (N₀ * L ^ q)) ∈ S) (c := fun _ => δ) hE
      fun x _ => continuousOn_const.mul
        (continuous_norm.comp_continuousOn ((continuous_apply x).comp_continuousOn hα))
  rw [e]
  exact (((m1.inter m2).inter m3).inter m4)

include hE hφ hh in
theorem measurableSet_fieldClose (ν δ : ℝ) (S : Finset (Torus d (N₀ * L ^ q))) :
    MeasurableSet {y | y ∈ E ∧ FieldClose G (D y) (φ y) ν S δ} := by
  by_cases hν : 0 < ν
  · have e : {y | y ∈ E ∧ FieldClose G (D y) (φ y) ν S δ} =
        {y | y ∈ E ∧ ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S →
          vn (fun i => φ y (x, i) - (D y).h x i) < δ / Real.sqrt ν} ∩
        {y | y ∈ E ∧ ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S →
          ‖∑ i, (D y).h x i * (D y).h x i - 1‖ < δ ^ 2 / ν} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, FieldClose, hν, forall_true_left]
      constructor
      · rintro ⟨hy, h⟩
        exact ⟨⟨hy, fun x hx => (h x hx).1⟩, hy, fun x hx => (h x hx).2⟩
      · rintro ⟨⟨hy, h1⟩, -, h2⟩
        exact ⟨hy, fun x hx => ⟨h1 x hx, h2 x hx⟩⟩
    rw [e]
    refine (measurableSet_forall_lt (ι := G.Ω 1) (E := E)
      (f := fun x y => vn (fun i => φ y (x, i) - (D y).h x i))
      (p := fun x => (x : Torus d (N₀ * L ^ q)) ∈ S) (c := fun _ => δ / Real.sqrt ν) hE
      fun x _ => ContinuousOn.vn' fun i =>
        (contOn_coord hφ (x, i)).sub (hh x i).continuousOn).inter
      (measurableSet_forall_lt (ι := G.Ω 1) (E := E)
        (f := fun x y => ‖∑ i, (D y).h x i * (D y).h x i - 1‖)
        (p := fun x => (x : Torus d (N₀ * L ^ q)) ∈ S) (c := fun _ => δ ^ 2 / ν) hE
        fun x _ => continuous_norm.comp_continuousOn
          ((continuousOn_finsetSum _ fun i _ =>
            (hh x i).continuousOn.mul (hh x i).continuousOn).sub continuousOn_const))
  · have e : {y | y ∈ E ∧ FieldClose G (D y) (φ y) ν S δ} = E := by
      ext y
      simp only [Set.mem_ofPred_eq, FieldClose, hν, false_imp_iff, and_true]
    rw [e]; exact hE

end Ineq


/-! ### `Reg` and `RegMixedIneq` -/

section RegMeasurable

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {G : GeneratingSet d L N₀ q ϱ}

/-- A family of real data with continuous coordinates and `h̃ ≡ h` on `Ω₁`. -/
structure RealFamily (D : Y → BgData G N) (h : Fin N → ℝ) : Prop where
  real : ∀ y x i, ((D y).Ψ x i).im = 0
  hconst : ∀ y, ∀ x ∈ G.Ω 1, ∀ i, (D y).h x i = (h i : ℂ)
  Ψc : ∀ x i, Continuous fun y => (D y).Ψ x i
  hc : ∀ x i, Continuous fun y => (D y).h x i

variable {a : ℕ → ℝ} {μ : ℝ} {D : Y → BgData G N} {h : Fin N → ℝ}

/-- **Lemma II.3.3 (measurability), the regularity predicate**: for a family of real data with
continuous coordinates and `h̃ ≡ h`, the set where `Reg_q(G, D y, δ; T, S)` holds is Borel. -/
theorem measurableSet_reg (H : BgHyp d L q ϱ a μ) (F : RealFamily D h) (δ : ℝ)
    (T S : Finset (Torus d (N₀ * L ^ q))) :
    MeasurableSet {y | Reg G a μ (D y) δ T S} := by
  have hd : 0 < d := by have := H.hd; omega
  have hE := measurableSet_domR D (μ := μ) hd F.real F.hconst F.Ψc
  obtain ⟨hφ, hα⟩ := contOn_bg D H F.Ψc F.hc
  have m1 := measurableSet_blockClose hE hφ F.Ψc T δ
  have m2 := measurableSet_gradClose hE hφ hα F.Ψc ((L : ℝ) ^ q) δ S
  have m3 := measurableSet_fieldClose hE hφ F.hc (μ * ((L : ℝ) ^ q) ^ 2) δ S
  have e : {y | Reg G a μ (D y) δ T S} =
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        BlockClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y)) T δ} ∩
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        GradClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y))
          (bgMultC G a μ (bgC0 d L N) (D y)) ((L : ℝ) ^ q) S δ} ∩
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        FieldClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y)) (μ * ((L : ℝ) ^ q) ^ 2) S δ} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Reg, RegIneq]
    constructor
    · rintro ⟨hy, h1, h2, h3⟩
      exact ⟨⟨⟨hy, h1⟩, hy, h2⟩, hy, h3⟩
    · rintro ⟨⟨⟨hy, h1⟩, -, h2⟩, -, h3⟩
      exact ⟨hy, h1, h2, h3⟩
  rw [e]
  exact (m1.inter m2).inter m3

/-- The mixed inequalities of P5 (2.13) together with the domain conjunct are Borel. -/
theorem measurableSet_regMixed (H : BgHyp d L q ϱ a μ) (F : RealFamily D h) (ℓ νk δ : ℝ)
    (Tfar Tnear S : Finset (Torus d (N₀ * L ^ q))) :
    MeasurableSet {y | InUnionDomainR G (bgC1 d L N) μ (D y) ∧
      RegMixedIneq G a μ (D y) ℓ νk δ Tfar Tnear S} := by
  have hd : 0 < d := by have := H.hd; omega
  have hE := measurableSet_domR D (μ := μ) hd F.real F.hconst F.Ψc
  obtain ⟨hφ, hα⟩ := contOn_bg D H F.Ψc F.hc
  have m1 := measurableSet_blockClose hE hφ F.Ψc Tfar (3 / 4 * δ)
  have m2 := measurableSet_blockClose hE hφ F.Ψc Tnear (5 / 4 * δ)
  have m3 := measurableSet_gradClose hE hφ hα F.Ψc ℓ (3 / 4 * δ) S
  have m4 := measurableSet_fieldClose hE hφ F.hc νk (3 / 4 * δ) S
  have e : {y | InUnionDomainR G (bgC1 d L N) μ (D y) ∧
      RegMixedIneq G a μ (D y) ℓ νk δ Tfar Tnear S} =
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        BlockClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y)) Tfar (3 / 4 * δ)} ∩
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        BlockClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y)) Tnear (5 / 4 * δ)} ∩
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        GradClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y))
          (bgMultC G a μ (bgC0 d L N) (D y)) ℓ S (3 / 4 * δ)} ∩
      {y | y ∈ {y | InUnionDomainR G (bgC1 d L N) μ (D y)} ∧
        FieldClose G (D y) (bgFieldC G a μ (bgC0 d L N) (D y)) νk S (3 / 4 * δ)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, RegMixedIneq]
    constructor
    · rintro ⟨hy, h1, h2, h3, h4⟩
      exact ⟨⟨⟨⟨hy, h1⟩, hy, h2⟩, hy, h3⟩, hy, h4⟩
    · rintro ⟨⟨⟨⟨hy, h1⟩, -, h2⟩, -, h3⟩, -, h4⟩
      exact ⟨hy, h1, h2, h3, h4⟩
  rw [e]
  exact ((m1.inter m2).inter m3).inter m4

end RegMeasurable

end Balaban.LargeField
