/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.KerBound

/-!
# The bound (1.26) at a complex source (ruling R2)

Ruling R2 (route R-YM′; `notes/phase1/Q13-YM.md` §5, `notes/phase1/astra/RADIUS.md` Part II §1):
the large-field kernels carry the external field in their weight, and the weight is continued to a
complex source in a thin tube around the real physical field, while the sharp characteristic
functions stay at the real field (they are never continued analytically).  The landed `KerBound`
quantifies over a real source `hv` and is a property of an `LFKernel`, whose exponent is real for a
real `g` (`LFKernel.real_b`); a genuinely complex source does not fit that type.  This file gives
the complex-source interface:

* `srcTube m β c hv`: the complex sources `h` around the real field `h_*` whose source increment
  `q = m (h - h_*)` satisfies `∑ |q_i|² ≤ c² m / β` (`RADIUS.md` (11));
* `KerBoundSrc a k Kc bc D κ`: the bound (1.26) for a sharp kernel `Kc` read at the real field and
  an exponent `bc` read at a source `s ∈ D h_*`, for every real field `h_*`;
* `kerBound_of_kerBoundSrc`: the real slice is the landed `KerBound` (for an `LFKernel` whose
  exponent at a real field is the complex exponent at a point of `D`);
* `kerBoundSrc_zero`: the bound holds for the zero kernel (it is satisfiable);
* `kerBoundSrc_mono`, `kerBoundSrc_le`: monotonicity in the source set and in the exponent;
* `lintegral_le_of_kerBoundSrc_budget`: the (1.31) integral bound for every complex source of the
  tube from a single-history Peierls budget (the complex-source form of
  `p5_kernel_integral_on_source_tube_of_physical_inputs`, without a family of real kernels).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Src

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The thin source tube** of route R-YM′ (`RADIUS.md` (11)): the complex sources `h` around the
real field `h_*` (`hv`) whose source increment `q = m (h - h_*)` (`m` the mass) satisfies
`∑ |q_i|² ≤ c² m / β`. -/
def srcTube (m β c : ℝ) (hv : EuclideanSpace ℝ (Fin N)) : Set (Fin N → ℂ) :=
  {h | ∑ i, ‖(m : ℂ) * (h i - (hv i : ℂ))‖ ^ 2 ≤ c ^ 2 * m / β}

/-- The real field lies in its own tube (for `c² m / β ≥ 0`). -/
theorem ofReal_mem_srcTube {m β c : ℝ} (hmβ : 0 ≤ c ^ 2 * m / β) (hv : EuclideanSpace ℝ (Fin N)) :
    (fun i => (hv i : ℂ)) ∈ srcTube m β c hv := by
  simp only [srcTube, Set.mem_ofPred_eq, sub_self, mul_zero, norm_zero]
  simpa using hmβ

/-- **The bound (1.26) at a complex source** (ruling R2): the integral of `Kc e^{Re bc}` over the
output variables on `Z` and the internal variables is at most `e^{-κ}`, for every real field `h_*`,
every source `s ∈ D h_*`, every `‖g‖_{ℓ¹} < 1` and every value of the parameters.  The sharp
kernel `Kc` is read at the real field `h_*`; only the exponent `bc` sees the source `s`. -/
def KerBoundSrc {Src : Type*} (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (Kc : OutT N R a k → SubCfg N a k A → EuclideanSpace ℝ (Fin N) → ℝ)
    (bc : OutT N R a k → SubCfg N a k A → Src → (GIdx S n M K N → ℂ) → ℂ)
    (D : EuclideanSpace ℝ (Fin N) → Set Src) (κ : ℝ) : Prop :=
  ∀ (hv : EuclideanSpace ℝ (Fin N)), ∀ s ∈ D hv, ∀ g : GIdx S n M K N → ℂ,
    g ∈ l1Ball (GIdx S n M K N) → ∀ par : OutPar N R a k,
      ∫⁻ oz, ∫⁻ x, ENNReal.ofReal (Kc (mergeOut a k oz par) x hv *
          Real.exp (bc (mergeOut a k oz par) x s g).re) ∂(subMeasure N a k A)
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤ ENNReal.ofReal (Real.exp (-κ))

variable {Src : Type*} {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}
  {Kc : OutT N R a k → SubCfg N a k A → EuclideanSpace ℝ (Fin N) → ℝ}
  {bc : OutT N R a k → SubCfg N a k A → Src → (GIdx S n M K N → ℂ) → ℂ}
  {D D' : EuclideanSpace ℝ (Fin N) → Set Src} {κ κ' : ℝ}

/-- **The real slice.**  If the weight `K e^{Re b}` of an `LFKernel` at a real field `h_*` is the
weight `Kc e^{Re bc}` at a source `ι h_* ∈ D h_*` (for the source tube, `ι h_* = h_*`; a factor may
move between the kernel and the exponent, as the physical action factor `e^{-𝒜}` does), the
complex-source bound gives the landed real-source `KerBound`. -/
theorem kerBound_of_kerBoundSrc
    (T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (ι : EuclideanSpace ℝ (Fin N) → Src) (hι : ∀ hv, ι hv ∈ D hv)
    (hw : ∀ o x hv g, T.K o x hv * Real.exp (T.b o x hv g).re =
      Kc o x hv * Real.exp (bc o x (ι hv) g).re)
    (h : KerBoundSrc a k Kc bc D κ) : KerBound a k T κ := by
  intro hv g hg par
  have := h hv (ι hv) (hι hv) g hg par
  simpa only [LFKernel.absW, hw] using this

/-- The bound is satisfiable: it holds for the zero kernel (every exponent). -/
theorem kerBoundSrc_zero : KerBoundSrc a k (fun _ _ _ => 0) bc D κ := by
  intro hv s hs g hg par
  simp

/-- Monotonicity in the source set. -/
theorem kerBoundSrc_mono (hD : ∀ hv, D' hv ⊆ D hv) (h : KerBoundSrc a k Kc bc D κ) :
    KerBoundSrc a k Kc bc D' κ :=
  fun hv s hs g hg par => h hv s (hD hv hs) g hg par

/-- Monotonicity in the exponent. -/
theorem kerBoundSrc_le (hκ : κ' ≤ κ) (h : KerBoundSrc a k Kc bc D κ) :
    KerBoundSrc a k Kc bc D κ' :=
  fun hv s hs g hg par => (h hv s hs g hg par).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith)))

/-- **P5 (1.31) at a complex source of the tube.**  The complex-source bound on the tube and the
single-history Peierls inequality (1.30) `ℓ P₂ + H W ≤ κ` give the (1.31) integral bound at every
real field and every complex source of its tube.  This replaces the family of real kernels of
`p5_kernel_integral_on_source_tube_of_physical_inputs` (whose members would need a real exponent
at a complex source). -/
theorem lintegral_le_of_kerBoundSrc_budget {m β c P2 H W ell : ℝ}
    {bt : OutT N R a k → SubCfg N a k A → (Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
    (hker : KerBoundSrc a k Kc bt (srcTube m β c) κ) (hbudget : ell * P2 + H * W ≤ κ)
    (hv : EuclideanSpace ℝ (Fin N)) {h : Fin N → ℂ} (hh : h ∈ srcTube m β c hv)
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) (par : OutPar N R a k) :
    ∫⁻ oz, ∫⁻ x, ENNReal.ofReal (Kc (mergeOut a k oz par) x hv *
        Real.exp (bt (mergeOut a k oz par) x h g).re) ∂(subMeasure N a k A)
      ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤
      ENNReal.ofReal (Real.exp (-(ell * P2) - H * W)) :=
  (hker hv h hh g hg par).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith)))

end Src

end Balaban.LargeField
