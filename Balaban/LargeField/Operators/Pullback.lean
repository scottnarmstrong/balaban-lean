module

public import Balaban.LargeField.Operators.Kernel

/-!
# Kernels multiplied by pulled-back kernels (the form of Definition II.5.8)

`LFKernel.mulPull T₀ s T fo fx` is the large-field kernel with
`K = K₀ · ∏_{j ∈ s} K_j(fo_j(x), fx_j(x))` and `b = b₀ + ∑_{j ∈ s} b_j(fo_j(x), fx_j(x))`: the
step kernel `T₀` times the ancestors' kernels `T_j`, evaluated at the ancestors' outputs
`fo_j(x)` (which are internal variables of the new component) and at the restrictions `fx_j(x)` of
the internal variables (Lemma II.5.3 (b), with the ancestors' variables identified inside the
variables of the component).
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory

namespace LFKernel

variable {O X X₀ H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [MeasurableSpace X₀]
  [Fintype ι] {J : Type*} {O' X' : J → Type*} [∀ j, MeasurableSpace (O' j)] [∀ j, MeasurableSpace (X' j)]

/-- The step kernel times the pulled-back kernels `T j` of the finite family `s`. -/
noncomputable def mulPull (T₀ : LFKernel O X₀ H ι) (f₀ : X → X₀) (hf₀ : Measurable f₀)
    (s : Finset J) (T : ∀ j, LFKernel (O' j) (X' j) H ι)
    (fo : ∀ j, X → O' j) (fx : ∀ j, X → X' j) (hfo : ∀ j, Measurable (fo j))
    (hfx : ∀ j, Measurable (fx j)) : LFKernel O X H ι where
  K o x h := T₀.K o (f₀ x) h * ∏ j ∈ s, (T j).K (fo j x) (fx j x) h
  b o x h g := T₀.b o (f₀ x) h g + ∑ j ∈ s, (T j).b (fo j x) (fx j x) h g
  K_nonneg o x h :=
    mul_nonneg (T₀.K_nonneg _ _ _) (Finset.prod_nonneg fun j _ => (T j).K_nonneg _ _ _)
  measurable_K h :=
    ((T₀.measurable_K h).comp (measurable_fst.prodMk (hf₀.comp measurable_snd))).mul
      (Finset.measurable_prod s fun j _ =>
      ((T j).measurable_K h).comp (((hfo j).comp measurable_snd).prodMk ((hfx j).comp measurable_snd)))
  measurable_b h g :=
    ((T₀.measurable_b h g).comp (measurable_fst.prodMk (hf₀.comp measurable_snd))).add
      (Finset.measurable_sum s fun j _ =>
      ((T j).measurable_b h g).comp (((hfo j).comp measurable_snd).prodMk ((hfx j).comp measurable_snd)))
  analytic_b o x h :=
    (T₀.analytic_b o (f₀ x) h).add (Finset.analyticOnNhd_fun_sum s fun j _ =>
      (T j).analytic_b (fo j x) (fx j x) h)
  real_b o x h g hg hr := by
    have h0 := T₀.real_b o (f₀ x) h g hg hr
    have hs : (∑ j ∈ s, (T j).b (fo j x) (fx j x) h g).im = 0 := by
      rw [Complex.im_sum]
      exact Finset.sum_eq_zero fun j _ => (T j).real_b _ _ _ g hg hr
    rw [Complex.add_im, h0, hs, add_zero]

theorem mulPull_K (T₀ : LFKernel O X₀ H ι) (f₀ : X → X₀) (hf₀ : Measurable f₀) (s : Finset J) (T : ∀ j, LFKernel (O' j) (X' j) H ι)
    (fo : ∀ j, X → O' j) (fx : ∀ j, X → X' j) (hfo : ∀ j, Measurable (fo j))
    (hfx : ∀ j, Measurable (fx j)) (o : O) (x : X) (h : H) :
    (T₀.mulPull f₀ hf₀ s T fo fx hfo hfx).K o x h = T₀.K o (f₀ x) h * ∏ j ∈ s, (T j).K (fo j x) (fx j x) h :=
  rfl

theorem mulPull_b (T₀ : LFKernel O X₀ H ι) (f₀ : X → X₀) (hf₀ : Measurable f₀) (s : Finset J) (T : ∀ j, LFKernel (O' j) (X' j) H ι)
    (fo : ∀ j, X → O' j) (fx : ∀ j, X → X' j) (hfo : ∀ j, Measurable (fo j))
    (hfx : ∀ j, Measurable (fx j)) (o : O) (x : X) (h : H) (g : ι → ℂ) :
    (T₀.mulPull f₀ hf₀ s T fo fx hfo hfx).b o x h g =
      T₀.b o (f₀ x) h g + ∑ j ∈ s, (T j).b (fo j x) (fx j x) h g :=
  rfl

end LFKernel

end Balaban.LargeField
