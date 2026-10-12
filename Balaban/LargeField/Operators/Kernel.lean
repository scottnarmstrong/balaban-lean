module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Large-field kernels, operators and the bound (1.26) (Part II, Definition II.5.2)

A large-field kernel `(K, b)` has `K ≥ 0` Borel in the output and internal variables, independent
of `g`, and `b` analytic in `g` on the `ℓ¹` unit ball and real for real arguments; the operators
depend on `g` through `e^b` only (audit P2-04).  The variables are abstract: `O` (outputs),
`X` (internal variables, with a reference measure `μ`), `H` (the parameter `h`), `ι` (the index of
the coordinates of `g`).  `Bound126` is the bound (1.26) with the modulus inside, with the domain
indicator `dom` (`χ^dom`) and the support condition of Lemma II.5.9 (d).
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- The open `ℓ¹` unit ball `‖g‖_{ℓ¹} < 1`. -/
def l1Ball (ι : Type*) [Fintype ι] : Set (ι → ℂ) := {g | ∑ i, ‖g i‖ < 1}

/-- A large-field kernel (Definition II.5.2). -/
structure LFKernel (O X H ι : Type*) [MeasurableSpace O] [MeasurableSpace X] [Fintype ι] where
  /-- the non-negative kernel, independent of `g` -/
  K : O → X → H → ℝ
  /-- the exponent `b`, analytic in `g` -/
  b : O → X → H → (ι → ℂ) → ℂ
  K_nonneg : ∀ o x h, 0 ≤ K o x h
  measurable_K : ∀ h, Measurable fun p : O × X => K p.1 p.2 h
  measurable_b : ∀ h g, Measurable fun p : O × X => b p.1 p.2 h g
  analytic_b : ∀ o x h, AnalyticOnNhd ℂ (b o x h) (l1Ball ι)
  real_b : ∀ o x h g, g ∈ l1Ball ι → (∀ i, (g i).im = 0) → (b o x h g).im = 0

namespace LFKernel

variable {O X H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [Fintype ι]
  (T : LFKernel O X H ι)

/-- The complex weight `K e^b`. -/
noncomputable def w (o : O) (x : X) (h : H) (g : ι → ℂ) : ℂ := (T.K o x h : ℂ) * Complex.exp (T.b o x h g)

/-- The non-negative weight `K e^{Re b}` (as an extended real). -/
noncomputable def absW (o : O) (x : X) (h : H) (g : ι → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (T.K o x h * Real.exp (T.b o x h g).re)

theorem measurable_absW (h : H) (g : ι → ℂ) :
    Measurable fun p : O × X => T.absW p.1 p.2 h g :=
  ENNReal.measurable_ofReal.comp
    ((T.measurable_K h).mul (Real.measurable_exp.comp (Complex.measurable_re.comp
      (T.measurable_b h g))))

/-- The partial integral `x ↦ K e^b f`, integrated against `μ`, at fixed output. -/
noncomputable def pint (μ : Measure X) (h : H) (g : ι → ℂ) (o : O) (f : X → ℂ) : ℂ :=
  ∫ x, T.w o x h g * f x ∂μ

/-- The operator `𝕋 F (o) = ∫ K e^b F(o, x) μ(dx)`. -/
noncomputable def op (μ : Measure X) (h : H) (g : ι → ℂ) (F : O → X → ℂ) (o : O) : ℂ :=
  T.pint μ h g o (F o)

end LFKernel

/-- The bound (1.26) with exponent `κ`: the kernel vanishes off the domain `dom` and, for all
Borel `F` and all `g` in the `ℓ¹` ball,
`∫ dν ∫ μ(dx) K e^{Re b} |F| ≤ e^{-κ} sup {χ^dom |F|}`. -/
def Bound126 {O X H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [Fintype ι]
    (T : LFKernel O X H ι) (ν : Measure O) (μ : Measure X) (dom : O → X → H → Prop) (κ : ℝ) :
    Prop :=
  (∀ o x h, ¬ dom o x h → T.K o x h = 0) ∧
    ∀ h, ∀ g ∈ l1Ball ι, ∀ F : O → X → ℂ, Measurable (fun p : O × X => F p.1 p.2) →
      ∫⁻ o, ∫⁻ x, T.absW o x h g * ‖F o x‖ₑ ∂μ ∂ν ≤
        ENNReal.ofReal (Real.exp (-κ)) * ⨆ (p : O × X) (_ : dom p.1 p.2 h), ‖F p.1 p.2‖ₑ

section Basic

variable {O X H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [Fintype ι]
  {T : LFKernel O X H ι} {ν : Measure O} {μ : Measure X} {dom : O → X → H → Prop} {κ : ℝ}
  [SFinite ν] [SFinite μ]

omit [SFinite ν] in
/-- Reduction to `F ≡ 1` (audit P2-06). -/
theorem bound126_iff_one :
    Bound126 T ν μ dom κ ↔ (∀ o x h, ¬ dom o x h → T.K o x h = 0) ∧
      ∀ h, ∀ g ∈ l1Ball ι, ∫⁻ o, ∫⁻ x, T.absW o x h g ∂μ ∂ν ≤ ENNReal.ofReal (Real.exp (-κ)) := by
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun h g hg => ?_⟩
    have := hb h g hg (fun _ _ => 1) measurable_const
    simp only [enorm_one, mul_one] at this
    refine this.trans ?_
    calc _ ≤ ENNReal.ofReal (Real.exp (-κ)) * 1 :=
          by gcongr; exact iSup₂_le fun _ _ => le_rfl
      _ = _ := mul_one _
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun h g hg F hF => ?_⟩
    set Sup : ℝ≥0∞ := ⨆ (p : O × X) (_ : dom p.1 p.2 h), ‖F p.1 p.2‖ₑ with hSup
    have hpt : ∀ o x, T.absW o x h g * ‖F o x‖ₑ ≤ T.absW o x h g * Sup := by
      intro o x
      by_cases hd : dom o x h
      · gcongr
        exact le_iSup₂ (f := fun (p : O × X) (_ : dom p.1 p.2 h) => ‖F p.1 p.2‖ₑ) (o, x) hd
      · have : T.K o x h = 0 := hs o x h hd
        simp [LFKernel.absW, this]
    have hm1 : ∀ o, Measurable fun x => T.absW o x h g := fun o =>
      (T.measurable_absW h g).comp measurable_prodMk_left
    calc ∫⁻ o, ∫⁻ x, T.absW o x h g * ‖F o x‖ₑ ∂μ ∂ν
        ≤ ∫⁻ o, ∫⁻ x, T.absW o x h g * Sup ∂μ ∂ν :=
          lintegral_mono fun o => lintegral_mono fun x => hpt o x
      _ = (∫⁻ o, ∫⁻ x, T.absW o x h g ∂μ ∂ν) * Sup := by
          simp_rw [lintegral_mul_const _ (hm1 _)]
          rw [lintegral_mul_const _ (T.measurable_absW h g).lintegral_prod_right']
      _ ≤ ENNReal.ofReal (Real.exp (-κ)) * Sup := by gcongr; exact hb h g hg

end Basic

/-! ### Tensor products and compositions (Lemma II.5.3) -/

namespace LFKernel

variable {O X H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [Fintype ι]

section Tensor

variable {O₁ O₂ X₁ X₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]
  [MeasurableSpace X₁] [MeasurableSpace X₂]

/-- The kernel of the product of two operators with disjoint variables (Lemma II.5.3 (a)). -/
noncomputable def tensor (T₁ : LFKernel O₁ X₁ H ι) (T₂ : LFKernel O₂ X₂ H ι) :
    LFKernel (O₁ × O₂) (X₁ × X₂) H ι where
  K p x h := T₁.K p.1 x.1 h * T₂.K p.2 x.2 h
  b p x h g := T₁.b p.1 x.1 h g + T₂.b p.2 x.2 h g
  K_nonneg p x h := mul_nonneg (T₁.K_nonneg _ _ _) (T₂.K_nonneg _ _ _)
  measurable_K h :=
    ((T₁.measurable_K h).comp (by fun_prop : Measurable fun q : (O₁ × O₂) × (X₁ × X₂) =>
        (q.1.1, q.2.1))).mul
      ((T₂.measurable_K h).comp (by fun_prop : Measurable fun q : (O₁ × O₂) × (X₁ × X₂) =>
        (q.1.2, q.2.2)))
  measurable_b h g :=
    ((T₁.measurable_b h g).comp (by fun_prop : Measurable fun q : (O₁ × O₂) × (X₁ × X₂) =>
        (q.1.1, q.2.1))).add
      ((T₂.measurable_b h g).comp (by fun_prop : Measurable fun q : (O₁ × O₂) × (X₁ × X₂) =>
        (q.1.2, q.2.2)))
  analytic_b p x h := fun g hg =>
    AnalyticAt.add (T₁.analytic_b p.1 x.1 h g hg) (T₂.analytic_b p.2 x.2 h g hg)
  real_b p x h g hg hr := by
    simp [T₁.real_b _ _ _ g hg hr, T₂.real_b _ _ _ g hg hr]

theorem tensor_w (T₁ : LFKernel O₁ X₁ H ι) (T₂ : LFKernel O₂ X₂ H ι) (p : O₁ × O₂)
    (x : X₁ × X₂) (h : H) (g : ι → ℂ) :
    (tensor T₁ T₂).w p x h g = T₁.w p.1 x.1 h g * T₂.w p.2 x.2 h g := by
  simp only [w, tensor, Complex.exp_add, Complex.ofReal_mul]; ring

theorem tensor_absW (T₁ : LFKernel O₁ X₁ H ι) (T₂ : LFKernel O₂ X₂ H ι) (p : O₁ × O₂)
    (x : X₁ × X₂) (h : H) (g : ι → ℂ) :
    (tensor T₁ T₂).absW p x h g = T₁.absW p.1 x.1 h g * T₂.absW p.2 x.2 h g := by
  simp only [absW, tensor, Complex.add_re, Real.exp_add]
  rw [← ENNReal.ofReal_mul (mul_nonneg (T₁.K_nonneg _ _ _) (Real.exp_pos _).le)]
  congr 1; ring

/-- Operators with disjoint variables: the operator of the tensor kernel on a product function is
the product of the operators (Lemma II.5.3 (a)). -/
theorem op_tensor (T₁ : LFKernel O₁ X₁ H ι) (T₂ : LFKernel O₂ X₂ H ι) (μ₁ : Measure X₁)
    (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂] (h : H) (g : ι → ℂ)
    (F₁ : O₁ → X₁ → ℂ) (F₂ : O₂ → X₂ → ℂ) (p : O₁ × O₂) :
    (tensor T₁ T₂).op (μ₁.prod μ₂) h g (fun p x => F₁ p.1 x.1 * F₂ p.2 x.2) p =
      T₁.op μ₁ h g F₁ p.1 * T₂.op μ₂ h g F₂ p.2 := by
  simp only [op, pint, tensor_w]
  rw [← integral_prod_mul (μ := μ₁) (ν := μ₂)
    (fun x₁ => T₁.w p.1 x₁ h g * F₁ p.1 x₁) (fun x₂ => T₂.w p.2 x₂ h g * F₂ p.2 x₂)]
  congr 1; ext x; ring

/-- Operators commute: Fubini–Tonelli (Lemma II.5.3 (a)), on functions for which the joint
integral converges absolutely. -/
theorem op_comm (T₁ : LFKernel O₁ X₁ H ι) (T₂ : LFKernel O₂ X₂ H ι) (μ₁ : Measure X₁)
    (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂] (h : H) (g : ι → ℂ) (o₁ : O₁) (o₂ : O₂)
    (F : X₁ → X₂ → ℂ)
    (hint : Integrable (fun q : X₁ × X₂ => T₁.w o₁ q.1 h g * (T₂.w o₂ q.2 h g * F q.1 q.2))
      (μ₁.prod μ₂)) :
    T₁.pint μ₁ h g o₁ (fun x₁ => T₂.pint μ₂ h g o₂ (F x₁)) =
      T₂.pint μ₂ h g o₂ (fun x₂ => T₁.pint μ₁ h g o₁ (fun x₁ => F x₁ x₂)) := by
  simp only [pint]
  have h1 : ∀ x₁, T₁.w o₁ x₁ h g * ∫ x₂, T₂.w o₂ x₂ h g * F x₁ x₂ ∂μ₂ =
      ∫ x₂, T₁.w o₁ x₁ h g * (T₂.w o₂ x₂ h g * F x₁ x₂) ∂μ₂ := fun x₁ =>
    (integral_const_mul _ _).symm
  have h2 : ∀ x₂, T₂.w o₂ x₂ h g * ∫ x₁, T₁.w o₁ x₁ h g * F x₁ x₂ ∂μ₁ =
      ∫ x₁, T₁.w o₁ x₁ h g * (T₂.w o₂ x₂ h g * F x₁ x₂) ∂μ₁ := fun x₂ => by
    rw [← integral_const_mul]; congr 1; ext x₁; ring
  simp_rw [h1, h2]
  exact integral_integral_swap hint

end Tensor

section Comp

variable {I X₀ O₀ : Type*} [MeasurableSpace I] [MeasurableSpace X₀] [MeasurableSpace O₀]

/-- The composition `𝕋₁ ∘ 𝕋₀`: `𝕋₁` has internal variables `I`, of which `r i ∈ O₀` are the
outputs of the ancestor `𝕋₀` (Lemma II.5.3 (b)); the composed kernel has internal variables
`I × X₀` and kernel `K₁ e^{b₁} K₀ e^{b₀}`. -/
noncomputable def comp (T₁ : LFKernel O I H ι) (r : I → O₀) (hr : Measurable r)
    (T₀ : LFKernel O₀ X₀ H ι) : LFKernel O (I × X₀) H ι where
  K o q h := T₁.K o q.1 h * T₀.K (r q.1) q.2 h
  b o q h g := T₁.b o q.1 h g + T₀.b (r q.1) q.2 h g
  K_nonneg o q h := mul_nonneg (T₁.K_nonneg _ _ _) (T₀.K_nonneg _ _ _)
  measurable_K h :=
    ((T₁.measurable_K h).comp (by fun_prop : Measurable fun q : O × (I × X₀) => (q.1, q.2.1))).mul
      ((T₀.measurable_K h).comp ((hr.comp (by fun_prop : Measurable fun q : O × (I × X₀) =>
        q.2.1)).prodMk (by fun_prop : Measurable fun q : O × (I × X₀) => q.2.2)))
  measurable_b h g :=
    ((T₁.measurable_b h g).comp (by fun_prop : Measurable fun q : O × (I × X₀) => (q.1, q.2.1))).add
      ((T₀.measurable_b h g).comp ((hr.comp (by fun_prop : Measurable fun q : O × (I × X₀) =>
        q.2.1)).prodMk (by fun_prop : Measurable fun q : O × (I × X₀) => q.2.2)))
  analytic_b o q h := fun g hg =>
    AnalyticAt.add (T₁.analytic_b o q.1 h g hg) (T₀.analytic_b (r q.1) q.2 h g hg)
  real_b o q h g hg hr' := by
    simp [T₁.real_b _ _ _ g hg hr', T₀.real_b _ _ _ g hg hr']

theorem comp_w (T₁ : LFKernel O I H ι) (r : I → O₀) (hr : Measurable r)
    (T₀ : LFKernel O₀ X₀ H ι) (o : O) (q : I × X₀) (h : H) (g : ι → ℂ) :
    (comp T₁ r hr T₀).w o q h g = T₁.w o q.1 h g * T₀.w (r q.1) q.2 h g := by
  simp only [w, comp, Complex.exp_add, Complex.ofReal_mul]; ring

theorem comp_absW (T₁ : LFKernel O I H ι) (r : I → O₀) (hr : Measurable r)
    (T₀ : LFKernel O₀ X₀ H ι) (o : O) (q : I × X₀) (h : H) (g : ι → ℂ) :
    (comp T₁ r hr T₀).absW o q h g = T₁.absW o q.1 h g * T₀.absW (r q.1) q.2 h g := by
  simp only [absW, comp, Complex.add_re, Real.exp_add]
  rw [← ENNReal.ofReal_mul (mul_nonneg (T₁.K_nonneg _ _ _) (Real.exp_pos _).le)]
  congr 1; ring

/-- The operator of the composed kernel is the iterated operator `𝕋₁ ∘ 𝕋₀` (Lemma II.5.3 (b)),
for functions with absolutely convergent joint integral. -/
theorem op_comp (T₁ : LFKernel O I H ι) (r : I → O₀) (hr : Measurable r)
    (T₀ : LFKernel O₀ X₀ H ι) (μ₁ : Measure I) (μ₀ : Measure X₀) [SFinite μ₁] [SFinite μ₀]
    (h : H) (g : ι → ℂ) (F : O → I × X₀ → ℂ) (o : O)
    (hint : Integrable (fun q : I × X₀ => (comp T₁ r hr T₀).w o q h g * F o q) (μ₁.prod μ₀)) :
    (comp T₁ r hr T₀).op (μ₁.prod μ₀) h g F o =
      T₁.op μ₁ h g (fun o' i => T₀.op μ₀ h g (fun _ x => F o' (i, x)) (r i)) o := by
  simp only [op, pint]
  rw [integral_prod _ hint]
  congr 1; ext i
  rw [← integral_const_mul]
  congr 1; ext x
  rw [comp_w]; ring

end Comp

end LFKernel

/-! ### The bound (1.26) is preserved -/

section Bounds

variable {H ι : Type*} [Fintype ι]

/-- Tensor products preserve (1.26): exponents add. -/
theorem Bound126.tensor {O₁ O₂ X₁ X₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]
    [MeasurableSpace X₁] [MeasurableSpace X₂] {T₁ : LFKernel O₁ X₁ H ι}
    {T₂ : LFKernel O₂ X₂ H ι} {ν₁ : Measure O₁} {ν₂ : Measure O₂} {μ₁ : Measure X₁}
    {μ₂ : Measure X₂} [SFinite ν₁] [SFinite ν₂] [SFinite μ₁] [SFinite μ₂]
    {dom₁ : O₁ → X₁ → H → Prop} {dom₂ : O₂ → X₂ → H → Prop} {κ₁ κ₂ : ℝ}
    (h₁ : Bound126 T₁ ν₁ μ₁ dom₁ κ₁) (h₂ : Bound126 T₂ ν₂ μ₂ dom₂ κ₂) :
    Bound126 (LFKernel.tensor T₁ T₂) (ν₁.prod ν₂) (μ₁.prod μ₂)
      (fun p x h => dom₁ p.1 x.1 h ∧ dom₂ p.2 x.2 h) (κ₁ + κ₂) := by
  rw [bound126_iff_one] at h₁ h₂ ⊢
  obtain ⟨s₁, b₁⟩ := h₁
  obtain ⟨s₂, b₂⟩ := h₂
  refine ⟨fun p x h hn => ?_, fun h g hg => ?_⟩
  · by_cases h1 : dom₁ p.1 x.1 h
    · have h2 : ¬ dom₂ p.2 x.2 h := fun h2 => hn ⟨h1, h2⟩
      simp [LFKernel.tensor, s₂ _ _ _ h2]
    · simp [LFKernel.tensor, s₁ _ _ _ h1]
  · have hm : ∀ (o : O₁ × O₂), ∫⁻ x, (LFKernel.tensor T₁ T₂).absW o x h g ∂(μ₁.prod μ₂) =
        (∫⁻ x₁, T₁.absW o.1 x₁ h g ∂μ₁) * ∫⁻ x₂, T₂.absW o.2 x₂ h g ∂μ₂ := by
      intro o
      simp_rw [LFKernel.tensor_absW]
      exact lintegral_prod_mul
        ((T₁.measurable_absW h g).comp measurable_prodMk_left).aemeasurable
        ((T₂.measurable_absW h g).comp measurable_prodMk_left).aemeasurable
    simp_rw [hm]
    rw [lintegral_prod_mul
      ((T₁.measurable_absW h g).lintegral_prod_right').aemeasurable
      ((T₂.measurable_absW h g).lintegral_prod_right').aemeasurable,
      show -(κ₁ + κ₂) = -κ₁ + -κ₂ by ring, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' (b₁ h g hg) (b₂ h g hg)

end Bounds

end Balaban.LargeField
