/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralClassMatch
public import Balaban.Fluctuation.StepComplexOutAnalytic
public import Balaban.Fluctuation.StepComplexOutWitness

/-!
# Path analyticity of the old terms of a general class (package `GeneralClassPathAnalytic`)

For a member of the class `IsSF2` the old energy, observable and source terms, evaluated at the
composed data `P_{j,D}(s, x)` of the complex path (`composedPairAtC` of the datum `S.dataUC
(S.psiAtC s x)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`, `1 ≤ j ≤ k`), are analytic in the pair of old fields at
the path point.  This is the three predicates `EdensAnalyticOnPath`, `MlocAnalyticOnPath`,
`FlocAnalyticOnPath` of `StepComplexOutAnalytic`.

* `OldXiDomC S C Dom`: the single open domain hypothesis (`GENERAL-OLD-XIDOM-C` of
  `notes/phase1/GENERAL.md`, restricted to the points the three predicates use).  For every path
  point, every scale `1 ≤ j ≤ k` and every old polymer `X` of scale `j`, the composed pair lies in
  the complex domain `Dom.dom j (C.Tm.gs j X)` of the class.
* `edensAnalyticOnPath_of_oldXiDomC`, `mlocAnalyticOnPath_of_oldXiDomC`,
  `flocAnalyticOnPath_of_oldXiDomC`: the three predicates, from the clauses `analyticE`,
  `analyticM` of `IsSF2`, `ClassParamMatch` and `OldXiDomC`.  The source condition `‖g‖₁ < 1` of
  `analyticM` is a premise on `g`, as in `GeneralClassMatch`.

Complex variables.  In each of the three theorems the analytic variable is the pair of old fields
`(ψ, h)` (the datum of the terms), at the point `composedPairAtC … (S.dataUC (S.psiAtC s x))`; the
source `g` is a fixed (real or complex) field and the interpolation parameter `s` and the
fluctuation variable `x` are fixed parameters selecting the point, exactly as in the predicates.
The consumers are the composition steps of `StepComplexExponent` (`exists_analytic_composedPairAtC_path`
makes the pair an analytic function of the raw block datum) and `StepComplexJoint`; analyticity in
the complex ray parameter `u` is obtained there from the analyticity of the path map composed with
these pair-analyticity statements, so these theorems give what the predicates ask and no more.

Not proved here.  `OldXiDomC` is not proved for the physical chart: it needs the class-radius
inequalities of `GENERAL.md` §1.  The regularity package (`ClassRegularLocC`), the identification
of the step exponent with the hat functionals, and the general-class activity bound are later
packages.  Nothing here depends on which generating set the class terms use: `C.Tm.gs j X` enters
only through the class `C`.  The old terms are taken on the step torus (index `k + 1`), as in
`GeneralClassMatch`; the lift of terms of index `k` is not used.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The domain hypothesis of the complex path** (`GENERAL-OLD-XIDOM-C`, open): for every point
`(s, ψ̂)` of the path (`s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`), every scale `1 ≤ j ≤ k` and every old polymer `X`
of scale `j`, the composed pair of old fields `P_{j,D}(s, ψ̂)` lies in the complex domain
`Dom.dom j (C.Tm.gs j X)` of the class. -/
def StepSetting.OldXiDomC (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
    ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))).2

/-- A finite sum over the polymers through a site of functions analytic at a point is analytic. -/
theorem analyticAt_finsum_polysAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (m₀ j : ℕ) (y : CTorus d L N₁ m₁ (k + 1)) (f : Set (CTorus d L N₁ m₁ (k + 1)) → E → F)
    {p₀ : E} (hf : ∀ X, IsPolyDom m₀ j X → y ∈ X → AnalyticAt ℂ (f X) p₀) :
    AnalyticAt ℂ (fun p => ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      m₀ j y, f X p) p₀ := by
  have hfin : (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ j y).Finite :=
    Set.toFinite _
  have : (fun p => ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      m₀ j y, f X p) = fun p => ∑ X ∈ hfin.toFinset, f X p :=
    funext fun p => finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun X hX =>
    hf X (hfin.mem_toFinset.1 hX).1 (hfin.mem_toFinset.1 hX).2

section Theorems

variable {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {P : Consts}
  {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
  {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
  {ρ : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ} {E : ℝ}

/-- **The densities `ℰ^{(j)}` of a general class are analytic at the composed data of the path**,
from `IsSF2` (clause `analyticE`), the parameter match and `OldXiDomC`.  The analytic variable is
the pair of old fields; `s`, `ψ̂` select the point. -/
theorem edensAnalyticOnPath_of_oldXiDomC (hm : ClassParamMatch S C P Rg a Tm)
    (h : IsSF2 P Rg β a Dom Tm ρ E) (hdom : S.OldXiDomC C Dom) :
    S.EdensAnalyticOnPath C := by
  intro s hs x hx j hj
  have hj' := Finset.mem_Icc.1 hj
  unfold Edens
  refine Finset.analyticAt_fun_sum _ fun y _ => ?_
  unfold Eloc
  refine analyticAt_finsum_polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) C.m₀ j y
    (fun X (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) => C.Tm.E j y X p.1 p.2) fun X hX hy => ?_
  have hX' : IsPolyDom P.m₀ j X := hm.m₀_eq ▸ hX
  have := h.terms.analyticE j hj'.1 (hj'.2.trans (Nat.le_succ k)) y X hX' hy
  rw [← hm.terms_eq] at this
  exact this _ (hdom s hs x hx j hj X hX)

/-- The vector `ℳ^{(j)}(y; ·, ·, g)` of a general class is analytic at the composed data of the path
(the analytic variable is the pair of old fields; the source `g` is fixed). -/
theorem analyticAt_Mloc_of_oldXiDomC (hm : ClassParamMatch S C P Rg a Tm)
    (h : IsSF2 P Rg β a Dom Tm ρ E) (hdom : S.OldXiDomC C Dom)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) (y : CTorus d L N₁ m₁ (k + 1))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 k) :
    AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Mloc C.m₀ C.Tm j y p.1 p.2 g)
      (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))) := by
  have hj' := Finset.mem_Icc.1 hj
  unfold Mloc
  refine analyticAt_finsum_polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) C.m₀ j y
    (fun X (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) => C.Tm.M j y X p.1 p.2 g) fun X hX hy => ?_
  have hX' : IsPolyDom P.m₀ j X := hm.m₀_eq ▸ hX
  have h1 := h.terms.analyticM j hj'.1 (hj'.2.trans (Nat.le_succ k)) y X hX' hy
  rw [← hm.terms_eq] at h1
  have h3 := h1 ((composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))).1,
    (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))).2, g)
    ⟨hdom s hs x hx j hj X hX, hg⟩
  have hmap : AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (q.1, q.2, g)) (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))) :=
    AnalyticAt.prod analyticAt_fst (AnalyticAt.prod analyticAt_snd analyticAt_const)
  exact h3.comp_of_eq hmap rfl

/-- **The components `ℳ^{(j)}(y; ·, ·, g)_i` of a general class are analytic at the composed data of
the path**, from `IsSF2` (clause `analyticM`), the parameter match, `OldXiDomC` and the source
condition `‖g‖₁ < 1`.  The analytic variable is the pair of old fields; the source `g` is fixed. -/
theorem mlocAnalyticOnPath_of_oldXiDomC (hm : ClassParamMatch S C P Rg a Tm)
    (h : IsSF2 P Rg β a Dom Tm ρ E) (hdom : S.OldXiDomC C Dom)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) (y : CTorus d L N₁ m₁ (k + 1))
    (i : Fin N) : S.MlocAnalyticOnPath C g y i := fun _ hs _ hx _ hj =>
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
    (analyticAt_Mloc_of_oldXiDomC hm h hdom hg y hs hx hj))

/-- **The terms `ℱ^{(j)}(·, ·, g)` of a general class are analytic at the composed data of the
path**, from `IsSF2` (clause `analyticM`), the parameter match, `OldXiDomC` and `‖g‖₁ < 1`.  The
analytic variable is the pair of old fields; the source `g` is fixed. -/
theorem flocAnalyticOnPath_of_oldXiDomC (hm : ClassParamMatch S C P Rg a Tm)
    (h : IsSF2 P Rg β a Dom Tm ρ E) (hdom : S.OldXiDomC C Dom)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1) : S.FlocAnalyticOnPath C g := by
  intro s hs x hx j hj
  unfold Floc
  refine Finset.analyticAt_fun_sum _ fun y _ => Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact analyticAt_const.mul (mlocAnalyticOnPath_of_oldXiDomC hm h hdom hg y i s hs x hx j hj)

end Theorems

/-- **`OldXiDomC` is inhabited** (rule 10), for the zero class at the zero-class witness step
`witnessSetting` of `StepRegWitness` (the step of `StepComplexOutWitness`): on the field domain
whose complex domain is everything.  This is trivial and says no more than that the hypothesis
is satisfiable: the zero class has no old terms, so no inclusion in a chart domain is tested.
(Inclusion in `completeXiDom` would need the class-radius inequalities and is not claimed.) -/
theorem nonempty_oldXiDomC_zeroClass (m₁ : ℕ) (β δ : ℝ) :
    ∃ Dom : FieldDom 3 3 6 m₁ (1 + 1) 2 (Balaban.Localization.I5Inhabited.rhoSep m₁),
      (witnessSetting m₁ β δ).OldXiDomC (zeroClass 3 3 6 m₁ 1 2 (Balaban.Localization.I5Inhabited.rhoSep m₁)) Dom :=
  ⟨⟨∅, fun _ _ _ _ => True⟩, fun _ _ _ _ _ _ _ _ => trivial⟩

end Balaban.Fluctuation
