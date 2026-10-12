module

public import Balaban.LargeField.Operators.Kernel

/-!
# Composition preserves the bound (1.26) (Lemma II.5.3 / II.5.13, order of integration of P2-06)

The step kernel `𝕋₁` has internal variables `O₀ × N`: the outputs `y` of the ancestors (the old
variables) and the remaining new variables `n`.  `StepBound` is the form (S1)–(S2) of version 1.2
(D-IV.3): the weight `K₁ e^{Re b₁}` is dominated by `∑_w G_w(o, y) S_w(n)`, where the Gaussian
factors `G_w(o,y) = ∏ z^N t_k(u_y) F^w_k(u)` of the witness functions `F^w_k` integrate over the
new top variables `o` to the numbers `m_w` whatever `y` is, and `∑_w m_w ∫ S_w ≤ e^{-κ}`.
Then `Bound126` holds for the composition with the ancestor `𝕋₀`, with exponent `κ₀ + κ`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- The one-step bound (S1)–(S2) with Gaussian witness factors, abstractly. -/
structure StepBound {O O₀ N H ι : Type*} [MeasurableSpace O] [MeasurableSpace O₀]
    [MeasurableSpace N] [Fintype ι] (T : LFKernel O (O₀ × N) H ι) (ν : Measure O)
    (μ' : Measure N) (κ : ℝ) where
  /-- the finite family of witnesses -/
  W : Type
  [fintypeW : Fintype W]
  /-- the Gaussian factors `G_w(o, y)` -/
  G : W → O → O₀ → ℝ≥0∞
  /-- the bounds `S_w(n)` of the remaining kernel -/
  S : W → N → H → (ι → ℂ) → ℝ≥0∞
  /-- the Gaussian measures `m_w` -/
  m : W → ℝ≥0∞
  measurable_G : ∀ w, Measurable fun p : O × O₀ => G w p.1 p.2
  measurable_S : ∀ w h g, Measurable fun n => S w n h g
  gauss : ∀ w y, ∫⁻ o, G w o y ∂ν = m w
  dominated : ∀ o y n h, ∀ g ∈ l1Ball ι, T.absW o (y, n) h g ≤ ∑ w, G w o y * S w n h g
  total : ∀ h, ∀ g ∈ l1Ball ι, ∑ w, m w * ∫⁻ n, S w n h g ∂μ' ≤ ENNReal.ofReal (Real.exp (-κ))

attribute [instance] StepBound.fintypeW

/-- **Lemma II.5.3 (bound preserved), in the integration order of P2-06.** If the ancestor
operator satisfies (1.26) with exponent `κ₀` and the step satisfies (S1)–(S2) with exponent `κ`
(and vanishes off its domain), the composition satisfies (1.26) with exponent `κ₀ + κ`. -/
theorem Bound126.comp {O O₀ N X₀ H ι : Type*} [MeasurableSpace O] [MeasurableSpace O₀]
    [MeasurableSpace N] [MeasurableSpace X₀] [Fintype ι]
    {T₁ : LFKernel O (O₀ × N) H ι} {T₀ : LFKernel O₀ X₀ H ι} {ν : Measure O}
    {ν₀ : Measure O₀} {μ' : Measure N} {μ₀ : Measure X₀} [SFinite ν] [SFinite ν₀]
    [SFinite μ'] [SFinite μ₀] {dom₁ : O → O₀ × N → H → Prop} {dom₀ : O₀ → X₀ → H → Prop}
    {κ₀ κ : ℝ} (hS₁ : ∀ o i h, ¬ dom₁ o i h → T₁.K o i h = 0)
    (hstep : StepBound T₁ ν μ' κ) (h₀ : Bound126 T₀ ν₀ μ₀ dom₀ κ₀) :
    Bound126 (LFKernel.comp T₁ Prod.fst measurable_fst T₀) ν ((ν₀.prod μ').prod μ₀)
      (fun o q h => dom₁ o q.1 h ∧ dom₀ q.1.1 q.2 h) (κ₀ + κ) := by
  rw [bound126_iff_one] at h₀ ⊢
  obtain ⟨s₀, b₀⟩ := h₀
  refine ⟨fun o q h hn => ?_, fun h g hg => ?_⟩
  · by_cases h1 : dom₁ o q.1 h
    · have h2 : ¬ dom₀ q.1.1 q.2 h := fun h2 => hn ⟨h1, h2⟩
      simp [LFKernel.comp, s₀ _ _ _ h2]
    · simp [LFKernel.comp, hS₁ _ _ _ h1]
  · -- notation
    set a₁ : O → O₀ × N → ℝ≥0∞ := fun o i => T₁.absW o i h g with ha₁
    set a₀ : O₀ → X₀ → ℝ≥0∞ := fun y x => T₀.absW y x h g with ha₀
    set B₀ : O₀ → ℝ≥0∞ := fun y => ∫⁻ x, a₀ y x ∂μ₀ with hB₀
    have hma₀ : Measurable fun p : O₀ × X₀ => a₀ p.1 p.2 := T₀.measurable_absW h g
    have hma₁ : Measurable fun p : O × (O₀ × N) => a₁ p.1 p.2 := T₁.measurable_absW h g
    have hmB₀ : Measurable B₀ := hma₀.lintegral_prod_right'
    have hBtot : ∫⁻ y, B₀ y ∂ν₀ ≤ ENNReal.ofReal (Real.exp (-κ₀)) := b₀ h g hg
    -- inner integral over the internal variables of the composition
    have hinner : ∀ o, ∫⁻ q, (LFKernel.comp T₁ Prod.fst measurable_fst T₀).absW o q h g
        ∂((ν₀.prod μ').prod μ₀) = ∫⁻ i, a₁ o i * B₀ i.1 ∂(ν₀.prod μ') := by
      intro o
      have hm : Measurable fun q : (O₀ × N) × X₀ => a₁ o q.1 * a₀ q.1.1 q.2 :=
        ((hma₁.comp (measurable_prodMk_left (x := o))).comp measurable_fst).mul
          (hma₀.comp (by fun_prop : Measurable fun q : (O₀ × N) × X₀ => (q.1.1, q.2)))
      simp_rw [LFKernel.comp_absW]
      rw [lintegral_prod _ hm.aemeasurable]
      refine lintegral_congr fun i => ?_
      have hm0 : Measurable fun x => a₀ i.1 x := hma₀.comp (measurable_prodMk_left (x := i.1))
      exact lintegral_const_mul (a₁ o i) hm0
    simp_rw [hinner]
    -- domination
    have hdom : ∀ o, ∫⁻ i, a₁ o i * B₀ i.1 ∂(ν₀.prod μ') ≤
        ∫⁻ y, ∫⁻ n, ∑ w, hstep.G w o y * hstep.S w n h g * B₀ y ∂μ' ∂ν₀ := by
      intro o
      have hm : Measurable fun i : O₀ × N => ∑ w, hstep.G w o i.1 * hstep.S w i.2 h g * B₀ i.1 :=
        Finset.measurable_sum _ fun w _ =>
          (((hstep.measurable_G w).comp (measurable_prodMk_left (x := o))).comp measurable_fst
            |>.mul ((hstep.measurable_S w h g).comp measurable_snd)).mul (hmB₀.comp measurable_fst)
      rw [← lintegral_prod (fun i : O₀ × N => ∑ w, hstep.G w o i.1 * hstep.S w i.2 h g * B₀ i.1)
        hm.aemeasurable] 
      refine lintegral_mono fun i => ?_
      calc a₁ o i * B₀ i.1 ≤ (∑ w, hstep.G w o i.1 * hstep.S w i.2 h g) * B₀ i.1 := by
            gcongr; exact hstep.dominated o i.1 i.2 h g hg
        _ = _ := Finset.sum_mul _ _ _
    -- the triple integrand, one witness at a time
    set f : hstep.W → O × O₀ × N → ℝ≥0∞ :=
      fun w p => hstep.G w p.1 p.2.1 * hstep.S w p.2.2 h g * B₀ p.2.1 with hf
    have hmf : ∀ w, Measurable (f w) := fun w =>
      (((hstep.measurable_G w).comp (by fun_prop : Measurable fun p : O × O₀ × N => (p.1, p.2.1)))
        |>.mul ((hstep.measurable_S w h g).comp (by fun_prop : Measurable fun p : O × O₀ × N =>
          p.2.2))).mul (hmB₀.comp (by fun_prop : Measurable fun p : O × O₀ × N => p.2.1))
    have hmf' : ∀ w, Measurable fun p : (O × O₀) × N => f w (p.1.1, p.1.2, p.2) := fun w =>
      (hmf w).comp (by fun_prop)
    have hper : ∀ w, ∫⁻ o, ∫⁻ y, ∫⁻ n, f w (o, y, n) ∂μ' ∂ν₀ ∂ν =
        hstep.m w * (∫⁻ n, hstep.S w n h g ∂μ') * ∫⁻ y, B₀ y ∂ν₀ := by
      intro w
      have e1 : ∀ o y, ∫⁻ n, f w (o, y, n) ∂μ' =
          (hstep.G w o y * B₀ y) * ∫⁻ n, hstep.S w n h g ∂μ' := by
        intro o y
        simp only [hf]
        rw [← lintegral_const_mul _ (hstep.measurable_S w h g)]
        refine lintegral_congr fun n => ?_
        ring
      simp_rw [e1]
      have hmm : Measurable fun p : O × O₀ =>
          (hstep.G w p.1 p.2 * B₀ p.2) * ∫⁻ n, hstep.S w n h g ∂μ' :=
        ((hstep.measurable_G w).mul (hmB₀.comp measurable_snd)).mul_const _
      rw [lintegral_lintegral_swap hmm.aemeasurable]
      have e2 : ∀ y, ∫⁻ o, (hstep.G w o y * B₀ y) * ∫⁻ n, hstep.S w n h g ∂μ' ∂ν =
          hstep.m w * (B₀ y * ∫⁻ n, hstep.S w n h g ∂μ') := by
        intro y
        have : ∀ o, (hstep.G w o y * B₀ y) * ∫⁻ n, hstep.S w n h g ∂μ' =
            hstep.G w o y * (B₀ y * ∫⁻ n, hstep.S w n h g ∂μ') := fun o => mul_assoc _ _ _
        simp_rw [this]
        have hmG : Measurable fun o => hstep.G w o y :=
          (hstep.measurable_G w).comp (measurable_prodMk_right (y := y))
        rw [lintegral_mul_const _ hmG, hstep.gauss]
      simp_rw [e2]
      rw [lintegral_const_mul _ (hmB₀.mul_const _), lintegral_mul_const _ hmB₀]
      ring
    have hsum : ∫⁻ o, ∫⁻ y, ∫⁻ n, ∑ w, f w (o, y, n) ∂μ' ∂ν₀ ∂ν =
        ∑ w, ∫⁻ o, ∫⁻ y, ∫⁻ n, f w (o, y, n) ∂μ' ∂ν₀ ∂ν := by
      have hk : ∀ w, Measurable fun x : O × O₀ => ∫⁻ n, f w (x.1, x.2, n) ∂μ' := fun w =>
        (hmf' w).lintegral_prod_right'
      have hk2 : ∀ w, Measurable fun x : O × O₀ => ∫⁻ n, f w (x.1, x.2, n) ∂μ' := hk
      have e1 : ∀ o y, ∫⁻ n, ∑ w, f w (o, y, n) ∂μ' = ∑ w, ∫⁻ n, f w (o, y, n) ∂μ' :=
        fun o y => lintegral_finsetSum _ fun w _ =>
          (hmf' w).comp (measurable_prodMk_left (x := (o, y)))
      have e2 : ∀ o, ∫⁻ y, ∑ w, ∫⁻ n, f w (o, y, n) ∂μ' ∂ν₀ =
          ∑ w, ∫⁻ y, ∫⁻ n, f w (o, y, n) ∂μ' ∂ν₀ := fun o =>
        lintegral_finsetSum _ fun w _ => (hk w).comp (measurable_prodMk_left (x := o))
      have e3 : ∫⁻ o, ∑ w, ∫⁻ y, ∫⁻ n, f w (o, y, n) ∂μ' ∂ν₀ ∂ν =
          ∑ w, ∫⁻ o, ∫⁻ y, ∫⁻ n, f w (o, y, n) ∂μ' ∂ν₀ ∂ν :=
        lintegral_finsetSum _ fun w _ => (hk w).lintegral_prod_right'
      simp_rw [e1, e2]
      exact e3
    calc ∫⁻ o, ∫⁻ i, a₁ o i * B₀ i.1 ∂(ν₀.prod μ') ∂ν
        ≤ ∫⁻ o, ∫⁻ y, ∫⁻ n, ∑ w, f w (o, y, n) ∂μ' ∂ν₀ ∂ν := lintegral_mono hdom
      _ = ∑ w, hstep.m w * (∫⁻ n, hstep.S w n h g ∂μ') * ∫⁻ y, B₀ y ∂ν₀ := by
          rw [hsum]; exact Finset.sum_congr rfl fun w _ => hper w
      _ = (∑ w, hstep.m w * ∫⁻ n, hstep.S w n h g ∂μ') * ∫⁻ y, B₀ y ∂ν₀ := by
          rw [Finset.sum_mul]
      _ ≤ ENNReal.ofReal (Real.exp (-κ)) * ENNReal.ofReal (Real.exp (-κ₀)) :=
          mul_le_mul' (hstep.total h g hg) hBtot
      _ = ENNReal.ofReal (Real.exp (-(κ₀ + κ))) := by
          rw [show -(κ₀ + κ) = -κ₀ + -κ by ring, Real.exp_add,
            ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

end Balaban.LargeField
