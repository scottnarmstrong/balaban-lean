/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityHZero
public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Fluctuation.GsumActiveParam

/-!
# The first energy of a general class at a free datum: split of the exponent and the value

For a class member `C` the exponent of the step, as a function of the raw block datum `Θ` and the
hat variable, is the exponent of the zero class plus the increment of the inherited energy:
`W₁^C(Θ, ψ̂) = W₁^0(Θ, ψ̂) + (ℰ_k(Θ, ψ̂) - ℰ_k(Θ, 0))` (`W1_eq_zeroClass_add_EJ`), so that its
derivative in `ψ̂` is the derivative for the zero class plus the derivative of the inherited
energy (`fderiv_W1_eq_zeroClass_add_EJ`), wherever the old densities `ℰ^{(j)}` are analytic at
the composed pairs.  Consequently marks for `C` are the marks of the zero class together with marks
for the inherited energy (`fderiv_W1_eq_sum_elim`).

`E1locJ_eq_sum_gsumCoeff_of_marks`: at one raw datum `Θ`, if the class exponent `W₁^C(Θ, s ψ̂)` is
the label sum of an activity `A` and the localized derivative is the sum of marks `G`
(Theorem 3.1 (a) data, the record `InterpMarks`), then `ℰ₁^{(k+1)}(z)` at `Θ` (`E1locJ`) is
`∑_T gsumCoeff μ Lab A y0 G T`.

`paramMarkFamily_sum_elim`: the record `ParamMarkFamily` for an activity family and two families of
marks indexed by `ι₀ ⊕ ι₁`, from the fields of each.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Matrix Filter Topology MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The exponent of a class member split into the zero class and the inherited energy -/

/-- **`W₁^C = W₁^0 + (ℰ_k(·) - ℰ_k(·, 0))`** as functions of the raw block datum and the hat
variable. -/
theorem W1_eq_zeroClass_add_EJ (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    Jr.W1 C q = Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) q + (Jr.EJ C q - Jr.EJ C (q.1, 0)) := by
  rw [Jr.W1_zeroClass_eq_neg_beta_VJ]
  rfl

/-- **The derivative of `W₁^C` in the hat variable is that of `W₁^0` plus that of `ℰ_k`**, at a
chart datum `Θ` and a bounded hat variable `u`, where the old densities `ℰ^{(j)}` are analytic at
the composed pairs of `(Θ, u)`. -/
theorem fderiv_W1_eq_zeroClass_add_EJ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps) {u : S.EC} (hu : ∀ p, ‖u p‖ ≤ pp)
    (hE : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, u))) (v : S.EC) :
    fderiv ℂ (fun w : S.EC => Jr.W1 C (Θ, w)) u v =
      fderiv ℂ (fun w : S.EC => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (Θ, w)) u v +
        fderiv ℂ (fun w : S.EC => Jr.EJ C (Θ, w)) u v := by
  have hpair : DifferentiableAt ℂ (fun w : S.EC => (Θ, w)) u :=
    (differentiableAt_const _).prodMk differentiableAt_id
  have h0 : DifferentiableAt ℂ (fun w : S.EC => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (Θ, w)) u :=
    (Jr.analyticAt_W1 (zeroClass d L N₁ m₁ k N ϱ) hΘ hu
      (fun j _ => analyticAt_Edens_zeroClass j _)
      (fun j _ => analyticAt_Edens_zeroClass j _)).differentiableAt.comp u hpair
  have h1 : DifferentiableAt ℂ (fun w : S.EC => Jr.EJ C (Θ, w)) u :=
    (Jr.analyticAt_EJ C hΘ hu hE).differentiableAt.comp u hpair
  have hfun : (fun w : S.EC => Jr.W1 C (Θ, w)) =
      fun w => (Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (Θ, w) + Jr.EJ C (Θ, w)) - Jr.EJ C (Θ, 0) := by
    funext w
    rw [Jr.W1_eq_zeroClass_add_EJ C]
    ring
  rw [hfun, fderiv_sub_const, fderiv_fun_add h0 h1, _root_.add_apply]

/-- **Marks of a class member from marks of the zero class and marks of the inherited energy.**
If the derivative of `W₁^0` in the direction `v` is `∑ G₀` and that of `ℰ_k` is `∑ G₁`, the
derivative of `W₁^C` is the sum over `ι₀ ⊕ ι₁` of the joined marks. -/
theorem fderiv_W1_eq_sum_elim {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps) {u : S.EC} (hu : ∀ p, ‖u p‖ ≤ pp)
    (hE : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, u))) (v : S.EC) {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (G₀ : ι₀ → ℂ) (G₁ : ι₁ → ℂ)
    (h0 : fderiv ℂ (fun w : S.EC => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (Θ, w)) u v = ∑ i, G₀ i)
    (h1 : fderiv ℂ (fun w : S.EC => Jr.EJ C (Θ, w)) u v = ∑ j, G₁ j) :
    fderiv ℂ (fun w : S.EC => Jr.W1 C (Θ, w)) u v = ∑ i, Sum.elim G₀ G₁ i := by
  rw [Jr.fderiv_W1_eq_zeroClass_add_EJ C hΘ hu hE v, h0, h1, Fintype.sum_sum_type]
  rfl

/-! ### The value of `ℰ₁^{(k+1)}` at one raw datum from an activity and marks -/

open Classical in
/-- **`ℰ₁^{(k+1)}(z)` at a raw datum `Θ` as the sum of the Theorem 3.1 (a) coefficients.**  Let `A`
be an activity on the labels `Lab` whose label sum is the class exponent `W₁^C(Θ, s ψ̂)` and `G`
marks whose sum is the localized derivative `DW₁^C(Θ, s ψ̂)[C^{-1/2} 1_{B(z)} C^{1/2} ψ̂]`, for
`s ∈ [0, 1]`, almost surely, with the numerical hypotheses of Theorem 3.4.  Then
`E1locJ C z Θ = ∑_T gsumCoeff μ Lab A y0 G T`. -/
theorem E1locJ_eq_sum_gsumCoeff_of_marks {m₀ : ℕ} (hp : 0 < S.p₁)
    {Lb : Type} [Fintype Lb]
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ Lb)
    {ι : Type} [Fintype ι] (hι : Nonempty ι) (y0 : ι → Lb)
    {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ} (hN : L ^ m₀ ∣ N₁)
    {𝒰 : Set ℂ} (h𝒰 : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (A : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (G : ι → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (hmeas : ∀ i u, Measurable (G i u))
    (hdep : ∀ i u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i))) (G i u))
    (hbd : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (holA : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰)
    (holG : ∀ i Φ, DifferentiableOn ℂ (fun u => G i u Φ) 𝒰)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 C (Θ, (s : ℂ) • yhat x) = ∑ y, (A (s : ℂ)).H y ((S.blockSplit m₀ hp).restr x))
    (hF : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (fun w : S.EC => Jr.W1 C (Θ, w)) ((s : ℂ) • yhat x))
          ((Jr.Mx Θ)⁻¹ *ᵥ S.maskUC z (Jr.Mx Θ *ᵥ yhat x)) =
        ∑ i, G i (s : ℂ) ((S.blockSplit m₀ hp).restr x)) :
    Jr.E1locJ C z Θ = ∑ T, gsumCoeff (S.blockSplit m₀ hp).μ Lab A y0 G T := by
  let I : InterpMarks S.nuFl (S.blockSplit m₀ hp)
      (fun s x => Jr.W1 C (Θ, (s : ℂ) • yhat x))
      (fun s x => (fderiv ℂ (fun w : S.EC => Jr.W1 C (Θ, w)) ((s : ℂ) • yhat x))
        ((Jr.Mx Θ)⁻¹ *ᵥ S.maskUC z (Jr.Mx Θ *ᵥ yhat x))) :=
    { Lb := Lb
      Lab := Lab
      ι := ι
      nonempty := hι
      εH := εH
      κH := κH
      κG := κG
      κ0 := κ0
      κ' := κ'
      Kc := Kc
      F0 := F0
      hN := hN
      𝒰 := 𝒰
      isOpen := h𝒰
      seg := hseg
      A := A
      y0 := y0
      G := G
      meas := hmeas
      dep := hdep
      bound := hbd
      holA := holA
      holG := holG
      hκ0 := hκ0
      hKc := hKc
      hεpos := hεpos
      hF0 := hF0
      hκ' := hκ'
      hκG := hκG
      hκ := hκ
      hε := hε
      hW := hW
      hF := hF }
  exact (interpCoeff_spec I).1

end Balaban.Fluctuation.StepSetting.JointRep

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

/-! ### A parameter family of marks indexed by a sum -/

section SumElim

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb] {ι₀ ι₁ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **`ParamMarkFamily` for marks indexed by `ι₀ ⊕ ι₁`** from the analytic and continuity fields of
the activities and of each of the two families of marks. -/
theorem paramMarkFamily_sum_elim {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc κG : ℝ}
    {A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {y0 : ι₀ → Lb} {y1 : ι₁ → Lb}
    {G₀ : E → ι₀ → ℂ → (∀ b, Ωb b) → ℂ} {G₁ : E → ι₁ → ℂ → (∀ b, Ωb b) → ℂ}
    {F0 : ι₀ → ℝ} {F1 : ι₁ → ℝ} {V : Set E} {𝒰 : Set ℂ} {Q : Set (∀ b, Ωb b)}
    (hV : IsOpen V) (h𝒰 : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (hQ : IsCompact Q) (hQm : MeasurableSet Q) (hμQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (holA : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => (A p.1 p.2).H y Φ) (V ×ˢ 𝒰))
    (hcontA : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A θ u).H y) Q)
    (hmeas₀ : ∀ θ i u, Measurable (G₀ θ i u))
    (hbd₀ : ∀ θ i u Φ, ‖G₀ θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hol₀ : ∀ i, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => G₀ p.1 i p.2 Φ) (V ×ˢ 𝒰))
    (hcont₀ : ∀ i, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn (G₀ θ i u) Q)
    (hmeas₁ : ∀ θ i u, Measurable (G₁ θ i u))
    (hbd₁ : ∀ θ i u Φ, ‖G₁ θ i u Φ‖ ≤ F1 i * Real.exp (-κG * Lab.dl (y1 i)))
    (hol₁ : ∀ i, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => G₁ p.1 i p.2 Φ) (V ×ˢ 𝒰))
    (hcont₁ : ∀ i, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn (G₁ θ i u) Q) :
    ParamMarkFamily μ Lab A (Sum.elim y0 y1) (fun θ => Sum.elim (G₀ θ) (G₁ θ)) κG
      (Sum.elim F0 F1) V 𝒰 Q where
  isOpenV := hV
  isOpenU := h𝒰
  seg := hseg
  compact := hQ
  measQ := hQm
  carried := hμQ
  meas := fun θ i u => by
    cases i with
    | inl i => exact hmeas₀ θ i u
    | inr i => exact hmeas₁ θ i u
  bound := fun θ i u Φ => by
    cases i with
    | inl i => exact hbd₀ θ i u Φ
    | inr i => exact hbd₁ θ i u Φ
  holA := holA
  holG := fun i Φ hΦ => by
    cases i with
    | inl i => exact hol₀ i Φ hΦ
    | inr i => exact hol₁ i Φ hΦ
  contA := hcontA
  contG := fun i θ hθ u hu => by
    cases i with
    | inl i => exact hcont₀ i θ hθ u hu
    | inr i => exact hcont₁ i θ hθ u hu

end SumElim

end Balaban.Fluctuation
