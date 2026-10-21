/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfChi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Measurability of the small-field factor on the whole torus

A6-3 (a), item 1. On the `χ`-support `A = {χ_k(univ) ≠ 0}` all the building blocks of
`sfFactor2 C vc univ` are continuous in the block field (the terms `ℰ^{(j)}`, `ℳ^{(j)}`, `ℛ^{(k)}_n`
are analytic on the domains in which the fields lie, `Spine/FinalDomPsiJ.lean`), and off `A` the
factor is `0`; so it is Borel (`measurable_sfFactor2_univ`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Generic

/-- A finite sum over a finite index set of continuous functions. -/
theorem continuousOn_finsum_mem {α ι : Type*} [TopologicalSpace α] {E : Set α} {s : Set ι}
    (hs : s.Finite) {F : ι → α → ℂ} (hF : ∀ i ∈ s, ContinuousOn (F i) E) :
    ContinuousOn (fun a => ∑ᶠ i ∈ s, F i a) E := by
  classical
  have : (fun a => ∑ᶠ i ∈ s, F i a) = fun a => ∑ i ∈ hs.toFinset, F i a := by
    funext a; exact finsum_mem_eq_finite_toFinset_sum _ hs
  rw [this]
  exact continuousOn_finsetSum _ fun i hi => hF i (hs.mem_toFinset.1 hi)

/-- A finite sum over a finite index set of vector-valued continuous functions, read in a
coordinate. -/
theorem continuousOn_finsum_mem_apply {α ι κ : Type*} [TopologicalSpace α] {E : Set α}
    {s : Set ι} (hs : s.Finite) {F : ι → α → κ → ℂ} (k : κ)
    (hF : ∀ i ∈ s, ContinuousOn (fun a => F i a k) E) :
    ContinuousOn (fun a => (∑ᶠ i ∈ s, F i a) k) E := by
  classical
  have : (fun a => (∑ᶠ i ∈ s, F i a) k) = fun a => ∑ i ∈ hs.toFinset, F i a k := by
    funext a
    rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_apply]
  rw [this]
  exact continuousOn_finsetSum _ fun i hi => hF i (hs.mem_toFinset.1 hi)

/-- Composition with a function that is continuous at the points reached. -/
theorem continuousOn_comp_of_continuousAt {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {f : α → β} {g : β → γ} {s : Set α} (hf : ContinuousOn f s)
    (hg : ∀ a ∈ s, ContinuousAt g (f a)) : ContinuousOn (fun a => g (f a)) s :=
  fun a ha => (hg a ha).comp_continuousWithinAt (hf a ha)

end Generic

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N)) (vc : CorrCoef S.d)
  {P6 : Def6.Consts} {k0 : ℕ} (hm0 : P6.m₀ = C.m₀)
  (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
  (hTm : SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))

/-- The support of the characteristic function of the whole torus. -/
def Asupp : Set (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :=
  {ψk | C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv ≠ 0}

variable (hAD : Asupp C hv ⊆ DomSet C hv (C.cs.muBg (j + 1)))
  (hdomJ : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X, Def6.IsPolyDom C.m₀ jj X →
    (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X)
      (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Def6.constFld (hC hv)))
  (hslit : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
    ∀ x, dot (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)
      (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x) ∈ Complex.slitPlane)

include hm0 HB hTm hAD hdomJ in
/-- The localized terms `ℰ^{(j')}` at the inherited field are continuous on the support. -/
theorem continuousOn_EresJ2_terms {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      ∑ y ∈ C.alignedIn jj (Set.univ : Set (Torus S.d (n (j + 1)))),
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
          Def6.IsPolyDom C.m₀ jj X ∧ y ∈ X ∧ X ⊆ C.sset (thickY R (Set.univ : Set (Torus S.d (n (j + 1)))))},
          (C.sf.Tm C.N₁).E jj y X (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj)
            (Def6.constFld (hC hv))) (Asupp C hv) := by
  refine continuousOn_finsetSum _ fun y _ => continuousOn_finsum_mem (Set.toFinite _) fun X hX => ?_
  obtain ⟨hXp, hyX, -⟩ := hX
  have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
  have hAn := (hTm.analyticE jj hj1 hj y X hXp' hyX).continuousOn
  exact hAn.comp (((continuousOn_psiJ C hv HB hj1 hj).mono hAD).prodMk continuousOn_const)
    fun ψ hψ => hdomJ ψ hψ jj hj1 hj X hXp

include HB hAD in
/-- The inherited field at a site is continuous on the support. -/
theorem continuousOn_psiJ_site {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x) (Asupp C hv) :=
  (continuousOn_pi.2 fun i => (continuousOn_psiJ_coord C hv HB hj1 hj x i).mono hAD)

include HB hAD in
theorem continuousOn_dot_psiJ {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      dot (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)) (Asupp C hv) := by
  unfold dot
  exact continuousOn_finsetSum _ fun i _ =>
    (continuousOn_psiJ_coord C hv HB hj1 hj x i).mono hAD |>.mul
      ((continuousOn_psiJ_coord C hv HB hj1 hj x i).mono hAD)

include HB hAD hslit in
theorem continuousOn_dot_unitDir {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      dot (hC hv) (unitDirC (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)))
      (Asupp C hv) := by
  have hu : ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      unitDirC (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)) (Asupp C hv) :=
    continuousOn_comp_of_continuousAt (continuousOn_psiJ_site C hv HB hAD hj1 hj x)
      fun ψ hψ => (unitDirC_analyticAt (hslit ψ hψ jj hj1 hj x)).continuousAt
  unfold dot
  exact continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul ((continuousOn_pi.1 hu) i)

include HB hAD hslit in
/-- The correction `corrSum` of P5 (1.8) at the inherited field is continuous on the support. -/
theorem continuousOn_corrSum {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      corrSum (fun y x => vc.v1 jj (unlift jj (x - y))) (fun y x => vc.v2 jj (unlift jj (x - y)))
        (nuIdeal S.L (j + 1) (C.sf.ν (j + 1)) jj)
        (C.alignedIn jj (Set.univ : Set (Torus S.d (n (j + 1)))))
        (C.alignedIn jj (thickY R (Set.univ : Set (Torus S.d (n (j + 1))))))
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (hC hv)) (Asupp C hv) := by
  unfold corrSum corrPair
  refine continuousOn_finsetSum _ fun y _ => continuousOn_finsetSum _ fun x _ => ?_
  exact (continuousOn_const.mul ((continuousOn_dot_psiJ C hv HB hAD hj1 hj x).sub
      (continuousOn_dot_psiJ C hv HB hAD hj1 hj y))).add
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_dot_unitDir C hv HB hAD hslit hj1 hj x).sub
        (continuousOn_dot_unitDir C hv HB hAD hslit hj1 hj y))))

include hm0 HB hTm hAD hdomJ in
/-- The localized terms `ℳ^{(j')}` at the inherited field are continuous on the support. -/
theorem continuousOn_MresJ_coord (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) (i : Fin N) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.MresJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g jj x i) (Asupp C hv) := by
  unfold SFCtx.MresJ
  refine continuousOn_finsum_mem_apply (Set.toFinite _) i fun X hX => ?_
  obtain ⟨hXp, hxX, -⟩ := hX
  have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
  have hAn := (hTm.analyticM jj hj1 hj x X hXp' hxX).continuousOn
  have hcomp := hAn.comp
    (((continuousOn_psiJ C hv HB hj1 hj).mono hAD).prodMk
      (continuousOn_const.prodMk continuousOn_const))
    (fun ψ hψ => ⟨hdomJ ψ hψ jj hj1 hj X hXp, hg⟩)
  exact (continuousOn_pi.1 hcomp) i

include hm0 HB hTm hAD hdomJ in
/-- The source term `ℱ_k` of the whole torus is continuous on the support. -/
theorem continuousOn_Fres (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.Fres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) (Asupp C hv) := by
  classical
  unfold SFCtx.Fres
  have hφ := (continuousOn_phiBar C hv HB).mono hAD
  refine ContinuousOn.add (continuousOn_finsetSum _ fun x _ => continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj i).continuous.comp_continuousOn (continuousOn_pi.1 hφ x)))) ?_
  refine continuousOn_finsetSum _ fun jj hjj => continuousOn_finsetSum _ fun x _ => ?_
  by_cases hx : x ∈ C.sset (Set.univ : Set (Torus S.d (n (j + 1))))
  · simp only [hx, ↓reduceIte]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      (continuousOn_MresJ_coord C hv hm0 HB hTm hAD hdomJ g hg (Finset.mem_Icc.1 hjj).1
        (Finset.mem_Icc.1 hjj).2 x i)
  · simp only [hx, ↓reduceIte]
    exact continuousOn_const

include hm0 in
/-- The remainders `ℛ^{(k)}_n` at the lift of the block field are continuous on the support. -/
theorem continuousOn_Rres (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {fac : ℕ → ℝ}
    (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hdomR : ∀ ψk ∈ Asupp C hv, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv))) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.Rres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) (Asupp C hv) := by
  unfold SFCtx.Rres
  refine continuousOn_finsetSum _ fun nn hnn => continuousOn_finsum_mem (Set.toFinite _) fun X hX => ?_
  obtain ⟨hXp, -⟩ := hX
  have hXp' : Def6.IsPolyDom P6.m₀ (j + 1) X := by rw [hm0]; exact hXp
  have hnn' := Finset.mem_Icc.1 hnn
  have hAn := (hRt.analytic nn hnn'.1 (by rw [hm0]; exact hnn'.2) X hXp').continuousOn
  exact hAn.comp ((continuous_sfLiftK C).continuousOn.prodMk
    (continuousOn_const.prodMk continuousOn_const))
    fun ψ hψ => ⟨hdomR ψ hψ, fun _ => Set.mem_univ _, hg⟩

include hm0 HB hTm hAD hdomJ hslit in
/-- `ℰ^{(j')}` of the whole torus is continuous on the support. -/
theorem continuousOn_EresJ2 {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      EresJ2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Asupp C hv) := by
  unfold EresJ2
  exact (continuousOn_EresJ2_terms C hv hm0 HB hTm hAD hdomJ hj1 hj).sub
    (continuousOn_corrSum C hv vc HB hAD hslit hj1 hj)

include hm0 HB hTm hAD hdomJ hslit in
theorem continuousOn_EresK2 :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      EresK2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv) (Asupp C hv) := by
  unfold EresK2
  exact continuousOn_finsetSum _ fun jj hjj =>
    continuousOn_EresJ2 C hv vc hm0 HB hTm hAD hdomJ hslit (Finset.mem_Icc.1 hjj).1
      (Finset.mem_Icc.1 hjj).2

theorem continuous_psiLevelK :
    Continuous fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) => C.psiLevelK ψk := by
  refine continuous_pi fun m => continuous_pi fun y => ?_
  unfold SFCtx.psiLevelK
  by_cases hm : m ≤ j + 1
  · simp only [hm, ↓reduceDIte]
    unfold singleScale
    by_cases hmk : m = j + 1
    · simp only [hmk, ↓reduceDIte]
      exact continuous_apply _
    · simp only [hmk, ↓reduceDIte]
      exact continuous_const
  · simp only [hm, ↓reduceDIte]
    exact continuous_const

include HB hAD in
/-- The single-scale action `A*_k` of the whole torus is continuous on the support. -/
theorem continuousOn_actStar2 :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      actStar2 C (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv) (Asupp C hv) := by
  unfold actStar2
  have hφ := (continuousOn_phiBar C hv HB).mono hAD
  have hpair : ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      (C.psiLevelK ψk, C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv)) (Asupp C hv) :=
    (continuous_psiLevelK C).continuousOn.prodMk hφ
  exact ((continuous_actionG _ _ _ _ _).comp_continuousOn hpair).add
    (((continuous_starBondE _).comp_continuousOn hφ).const_mul _)

include hm0 HB hTm hAD hdomJ hslit in
/-- **`sfFactor2` of the whole torus is Borel in the block field** (A6-3 (a), item 1): on the support
`{χ_k(univ) ≠ 0}`, where the fields lie in the domains of the terms, every ingredient of the
exponent is continuous, and off the support the factor is `0`. -/
theorem measurable_sfFactor2_univ_of_dom (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {fac : ℕ → ℝ}
    (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hdomR : ∀ ψk ∈ Asupp C hv, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv)))
    (hmu : C.cs.mu (j + 1) = C.cs.muBg (j + 1)) :
    Measurable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g := by
  classical
  have HBmu : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)) := by
    rw [hmu]; exact HB
  have hchi := measurable_chiY C hv HBmu (Set.univ : Set (Torus S.d (n (j + 1))))
  have hA : MeasurableSet (Asupp C hv) :=
    (hchi (measurableSet_singleton (0 : ℝ))).compl
  have hExp : ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      Complex.exp (Ares2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv +
        C.Fres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g +
        C.Rres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g)) (Asupp C hv) := by
    refine Complex.continuous_exp.comp_continuousOn (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_)
    · unfold Ares2
      refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) continuousOn_const
      · exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_actStar2 C hv HB hAD))
      · exact continuousOn_EresK2 C hv vc hm0 HB hTm hAD hdomJ hslit
    · exact continuousOn_Fres C hv hm0 HB hTm hAD hdomJ g hg
    · exact continuousOn_Rres C hv hm0 g hg hRt hdomR
  have hE : Measurable ((Asupp C hv).piecewise (fun ψk : BlockAt S n M K (j + 1) →
      EuclideanSpace ℝ (Fin N) => Complex.exp (Ares2 C vc (Set.univ : Set (Torus S.d (n (j + 1))))
        ψk hv + C.Fres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g +
        C.Rres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g)) (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hExp continuousOn_const hA
  have : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) = fun ψk =>
      ((C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv : ℝ) : ℂ) *
        (Asupp C hv).piecewise (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
          Complex.exp (Ares2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv +
            C.Fres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g +
            C.Rres (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g)) (fun _ => 0) ψk := by
    funext ψk
    by_cases h : ψk ∈ Asupp C hv
    · rw [Set.piecewise_eq_of_mem _ _ _ h]; rfl
    · have h0 : C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv = 0 := by
        by_contra hne; exact h hne
      rw [Set.piecewise_eq_of_notMem _ _ _ h]
      unfold sfFactor2
      rw [h0]; simp
  rw [this]
  exact (Complex.measurable_ofReal.comp hchi).mul hE

end Ctx

end Balaban.RootFSpine
