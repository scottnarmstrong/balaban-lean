/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31Inhab

/-!
# The interpolation averages on a region (FLUCTUATION.md §3.5, P5 (3.2), P6 §4)

`Fluctuation/Thm31cde.lean` states Theorem 3.1 (c), (d), (e) for measures that are products over
the cubes of the whole torus (`ProdSplit`, `InterpMarks` over `CubeB m₀ K Set.univ`).  In the step on
a region the fluctuation variables live on the unit points of `Ω''_{k+1}` (P5 (2.48)), and the
measure is a product over the `π'_{k+1}`-cubes of `Ω''_{k+1}`; the cluster expansion of Theorem 3.4
(`marked_cubes_explicit`, `avg_integral_expansion`) is stated for the cubes of any `π'`-union `Ω`.
This file is the region-general form, with the whole-torus objects as the instance `Ω = univ`:

* `ProdSplitOn ν Ω`: the measure `ν` is the product of probability measures on the cubes of `Ω`;
  `ProdSplit.toOn`: the whole-torus split is the instance `Ω = univ`;
* `avgFun_eq_avgPi_on`: the expectation in `Z_s⁻¹ e^{W(s)} dν` is that of the product measure,
  when `W(s)` and the integrand are sums of terms of the cube variables;
* `InterpMarksOn`: Proposition 3.3 for an interpolation average on `Ω` (the localized exponent and
  marks with the hypotheses of Theorem 3.4); `InterpMarks.toOn`; `nonempty_interpMarksOn`;
* `interpTermOn`: the term `∫₀¹ ∑_i G*(Y₀ᵢ, S) du` of a set `S` of cubes of `Ω`;
* `interpAvg_eq_sum_interpTermOn`: **the localization expansion of the interpolation average**
  `∫₀¹ ⟨f(u)⟩_u du = ∑_S interpTermOn S`, with
  `|interpTermOn S| ≤ C_PE (∑_i F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) e^{-κ' d_Ω(S)}` (the common core of
  Theorem 3.1 (a), (c), (d), (e) on a region).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type*} [MeasurableSpace X]

/-- **The block structure of `ν` on a region**: the variable is the family of its restrictions to
the cubes (side `cellSide L m₀ m₁ K`) of `Ω`, and `ν` is the product of probability measures `ν_b`. -/
structure ProdSplitOn (ν : Measure X) (d L N₁ m₁ K m₀ : ℕ) [NeZero L] [NeZero N₁]
    (Ω : Set (CTorus d L N₁ m₁ K)) where
  /-- the variables of a cube -/
  Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Ω → Type
  [ms : ∀ b, MeasurableSpace (Ωb b)]
  /-- the measure of a cube -/
  μ : ∀ b, Measure (Ωb b)
  [prob : ∀ b, IsProbabilityMeasure (μ b)]
  /-- the restriction to the cubes -/
  restr : X → ∀ b, Ωb b
  meas : Measurable restr
  map_eq : Measure.map restr ν = Measure.pi μ

attribute [instance] ProdSplitOn.ms ProdSplitOn.prob

/-- The whole-torus split is the instance `Ω = univ`. -/
def ProdSplit.toOn {ν : Measure X} {m₀ : ℕ} (BS : ProdSplit ν d L N₁ m₁ K m₀) :
    ProdSplitOn ν d L N₁ m₁ K m₀ Set.univ where
  Ωb := BS.Ωb
  μ := BS.μ
  restr := BS.restr
  meas := BS.meas
  map_eq := BS.map_eq

/-- The expectation in `Z_s⁻¹ e^{W(s)} dν` is the expectation `avgPi` of the product measure, when
`W(s)` and the integrand are `ν`-a.e. sums of functions of the cube variables. -/
theorem avgFun_eq_avgPi_on {ν : Measure X} {m₀ : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
    (BS : ProdSplitOn ν d L N₁ m₁ K m₀ Ω) {Lb : Type*} [Fintype Lb] (W : ℝ → X → ℂ) (f : X → ℂ)
    (s : ℝ) (H : Lb → (∀ b, BS.Ωb b) → ℂ) (G : (∀ b, BS.Ωb b) → ℂ)
    (hHm : ∀ y, Measurable (H y)) (hGm : Measurable G)
    (hW : ∀ᵐ x ∂ν, W s x = ∑ y, H y (BS.restr x))
    (hf : ∀ᵐ x ∂ν, f x = G (BS.restr x)) :
    avgFun ν W f s = avgPi (K := K) (j := K) (Ω := Ω) BS.μ H G := by
  have hmeas : Measurable (fun Φ : ∀ b, BS.Ωb b => Complex.exp (∑ y, H y Φ)) :=
    Complex.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hHm y)
  have hZ : partFun ν W s = ∫ Φ, Complex.exp (∑ y, H y Φ) ∂(Measure.pi BS.μ) := by
    rw [← BS.map_eq, integral_map BS.meas.aemeasurable hmeas.aestronglyMeasurable]
    unfold partFun
    refine integral_congr_ae ?_
    filter_upwards [hW] with x hx
    rw [hx]
  have hN : ∫ x, f x * Complex.exp (W s x) ∂ν =
      ∫ Φ, G Φ * Complex.exp (∑ y, H y Φ) ∂(Measure.pi BS.μ) := by
    rw [← BS.map_eq, integral_map (f := fun Φ => G Φ * Complex.exp (∑ y, H y Φ))
      BS.meas.aemeasurable (hGm.mul hmeas).aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hW, hf] with x hx hfx
    rw [hx, hfx]
  unfold avgFun avgPi
  rw [hZ, hN]

/-- **Proposition 3.3 for an interpolation average on a region**: exponent `W(u)` and integrand
`f(u)` are, `ν`-a.e. and for `u ∈ [0,1]`, sums of terms of the cube variables of `Ω` (holomorphic in
`u` on an open `𝒰 ⊃ [0,1]`), with the numerical hypotheses of Theorem 3.4. -/
structure InterpMarksOn (ν : Measure X) {m₀ : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
    (BS : ProdSplitOn ν d L N₁ m₁ K m₀ Ω) (W : ℝ → X → ℂ) (f : ℝ → X → ℂ) where
  /-- the labels of the interaction -/
  Lb : Type
  [fin : Fintype Lb]
  /-- their sites and sizes -/
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Ω Lb
  /-- the indices of the marks -/
  ι : Type
  [finι : Fintype ι]
  nonempty : Nonempty ι
  εH : ℝ
  κH : ℝ
  κG : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  F0 : ι → ℝ
  hN : L ^ m₀ ∣ N₁
  𝒰 : Set ℂ
  isOpen : IsOpen 𝒰
  seg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰
  /-- the localized exponent -/
  A : ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc
  /-- the labels of the marks -/
  y0 : ι → Lb
  /-- the marks -/
  G : ι → ℂ → (∀ b, BS.Ωb b) → ℂ
  meas : ∀ i u, Measurable (G i u)
  dep : ∀ i u, DepOn (blocksOf m₀ K Ω (Lab.ysite (y0 i))) (G i u)
  bound : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i))
  holA : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰
  holG : ∀ i Φ, DifferentiableOn ℂ (fun u => G i u Φ) 𝒰
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 + 1 ≤ Kc
  hεpos : 0 < εH
  hF0 : ∀ i, 0 < F0 i
  hκ' : 0 ≤ κ'
  hκG : κH ≤ κG
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))
  hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    W s x = ∑ y, (A (s : ℂ)).H y (BS.restr x)
  hF : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    f s x = ∑ i, G i (s : ℂ) (BS.restr x)

attribute [instance] InterpMarksOn.fin InterpMarksOn.finι

/-- The whole-torus data are the instance `Ω = univ`. -/
def InterpMarks.toOn {ν : Measure X} {m₀ : ℕ} {BS : ProdSplit ν d L N₁ m₁ K m₀}
    {W : ℝ → X → ℂ} {f : ℝ → X → ℂ} (I : InterpMarks ν BS W f) :
    InterpMarksOn ν BS.toOn W f where
  Lb := I.Lb
  Lab := I.Lab
  ι := I.ι
  nonempty := I.nonempty
  εH := I.εH
  κH := I.κH
  κG := I.κG
  κ0 := I.κ0
  κ' := I.κ'
  Kc := I.Kc
  F0 := I.F0
  hN := I.hN
  𝒰 := I.𝒰
  isOpen := I.isOpen
  seg := I.seg
  A := I.A
  y0 := I.y0
  G := I.G
  meas := I.meas
  dep := I.dep
  bound := I.bound
  holA := I.holA
  holG := I.holG
  hκ0 := I.hκ0
  hKc := I.hKc
  hεpos := I.hεpos
  hF0 := I.hF0
  hκ' := I.hκ'
  hκG := I.hκG
  hκ := I.hκ
  hε := I.hε
  hW := I.hW
  hF := I.hF

/-- `InterpMarksOn` is inhabited (rule 10): the whole-torus witness `nonempty_interpMarks`. -/
theorem nonempty_interpMarksOn (d L N₁ m₁ K : ℕ) [NeZero L] [NeZero N₁] :
    ∃ (ν : Measure (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ → Unit))
      (BS : ProdSplitOn ν d L N₁ m₁ K 0 Set.univ) (W f : ℝ → _ → ℂ),
        Nonempty (InterpMarksOn ν BS W f) := by
  obtain ⟨ν, BS, W, f, ⟨I⟩⟩ := nonempty_interpMarks (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
  exact ⟨ν, BS.toOn, W, f, ⟨I.toOn⟩⟩

/-- **The term of a set `S` of cubes** of the localization expansion of an interpolation average:
`∫₀¹ ∑_i G*(Y₀ᵢ, S) du` (Theorem 3.4 at each `u`). -/
noncomputable def interpTermOn {ν : Measure X} {m₀ : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
    {BS : ProdSplitOn ν d L N₁ m₁ K m₀ Ω} {W : ℝ → X → ℂ} {f : ℝ → X → ℂ}
    (I : InterpMarksOn ν BS W f)
    (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Ω)) : ℂ :=
  ∫ s in (0 : ℝ)..1, Gsum BS.μ I.Lab (I.A (s : ℂ)).H I.y0 (fun i => I.G i (s : ℂ)) S

open Classical in
/-- **The localization expansion of an interpolation average on a region** (the common core of
Theorem 3.1 (a), (c), (d), (e); FLUCTUATION Theorem 3.4): for a `π'`-union `Ω`,
`∫₀¹ ⟨f(u)⟩_u du = ∑_S interpTermOn S` over the sets `S` of cubes of `Ω`, with
`|interpTermOn S| ≤ C_PE (∑_i F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) e^{-κ' d_Ω(S)}`; conditional on `InterpMarksOn`. -/
theorem interpAvg_eq_sum_interpTermOn {ν : Measure X} {m₀ : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
    (hΩ : IsPiUnion m₀ K Ω) {BS : ProdSplitOn ν d L N₁ m₁ K m₀ Ω} {W : ℝ → X → ℂ}
    {f : ℝ → X → ℂ} (I : InterpMarksOn ν BS W f) :
    interpAvg ν W f = ∑ S, interpTermOn I S ∧
      ∀ S, ‖interpTermOn I S‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt S) := by
  obtain ⟨-, hint, hbd⟩ := avg_integral_expansion BS.μ I.hN le_rfl hΩ
    I.isOpen I.seg I.A I.y0 I.G I.meas I.dep I.bound I.holA I.holG I.hκ0 I.hKc I.hεpos
    I.nonempty I.hF0 I.hκ' I.hκG I.hκ I.hε
  refine ⟨?_, hbd⟩
  unfold interpTermOn
  rw [← hint]
  unfold interpAvg
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact avgFun_eq_avgPi_on BS _ _ s (I.A (s : ℂ)).H (fun Φ => ∑ i, I.G i (s : ℂ) Φ)
    (I.A (s : ℂ)).meas (Finset.measurable_sum _ fun i _ => I.meas i _) (I.hW s hs) (I.hF s hs)

end Generic

end Balaban.Fluctuation
