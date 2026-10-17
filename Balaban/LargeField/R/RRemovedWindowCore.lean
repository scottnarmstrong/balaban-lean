/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.CompBound
public import Balaban.LargeField.R.RRemovedWindowGen

/-!
# The window integral: the core (Lemma III.8.7 (4)) (W905)

`notes/phase1/LF4R-PLAN.md`, leaf 6, step (4).  For fixed window variables the core operators
`𝕋_{k₁}(C)`, `C ∈ 𝒞_*`, act on disjoint sets of variables, so the integral of the product of their
weights `K e^{Re b}` over the core variables (outputs `ψ_{k₁}` on `T^{(k₁)} ∩ C` and internal
variables of each `C`) is the product of the integrals, each at most `e^{-κ_{k₁}(C)}` by (D5)
(`PkgBound`, the bound (1.26) for the package of an operator, for every value of the parameters,
here the window variables through `par`).  `core_lintegral_le` is this statement; it is the
analogue of `inner_le` of `CompBound.lean` for a core family indexed by an arbitrary finite type.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory ENNReal

section Core

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **(D5) for the core** (step (4)): for a finite family `ι` of core operators `(P Y)` of
localized histories `a Y` at the scale `k₁` with `PkgBound … (κ Y)`, and any dependence `par` of
the parameters of the outputs on `V ∖ Z` on the window variables, the integral over the core
variables of `∏_Y K_Y e^{Re b_Y}` is at most `e^{-∑_Y κ Y}` for every window value. -/
theorem core_lintegral_le {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (k1 : ℕ)
    (P : ∀ Y, OpPkg N R (a Y) k1) (κ : ι → ℝ)
    (hanc : ∀ Y, PkgBound (a Y) k1 (P Y) (κ Y)) {Wd : Type*} (par : Wd → ∀ Y, OutPar N R (a Y) k1)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (w : Wd) :
    ∫⁻ c : (∀ Y, OutZ N R (a Y) k1 × SubCfg N (a Y) k1 (P Y).A),
        ∏ Y, (P Y).T.absW (mergeOut (a Y) k1 (c Y).1 (par w Y)) (c Y).2 hv g
      ∂(Measure.pi fun Y => (outPartMeasure N (Vblk R (a Y) k1) (ZBlk (a Y) k1)).prod
        (subMeasure N (a Y) k1 (P Y).A)) ≤
      ENNReal.ofReal (Real.exp (-∑ Y, κ Y)) := by
  classical
  set At : ∀ Y, (OutZ N R (a Y) k1 × SubCfg N (a Y) k1 (P Y).A) → ℝ≥0∞ := fun Y v =>
    (P Y).T.absW (mergeOut (a Y) k1 v.1 (par w Y)) v.2 hv g with hAt
  have hAtm : ∀ Y, Measurable (At Y) := fun Y =>
    ((P Y).T.measurable_absW hv g).comp
      (((measurable_mergeOut (a Y) k1 (par w Y)).comp measurable_fst).prodMk measurable_snd)
  refine (PiTools.lintegral_fintype_prod_eq_prod _ At hAtm
    (μ := fun Y => (outPartMeasure N (Vblk R (a Y) k1) (ZBlk (a Y) k1)).prod
      (subMeasure N (a Y) k1 (P Y).A))).le.trans ?_
  have h : ∀ Y, ∫⁻ v, At Y v ∂((outPartMeasure N (Vblk R (a Y) k1) (ZBlk (a Y) k1)).prod
      (subMeasure N (a Y) k1 (P Y).A)) ≤ ENNReal.ofReal (Real.exp (-κ Y)) := fun Y => by
    rw [lintegral_prod _ (hAtm Y).aemeasurable]
    exact hanc Y hv g hg (par w Y)
  refine (Finset.prod_le_prod fun Y _ => h Y).trans ?_
  rw [← ENNReal.ofReal_prod_of_nonneg (fun Y _ => (Real.exp_pos _).le), ← Real.exp_sum,
    Finset.sum_neg_distrib]

end Core

end Balaban.LargeField
