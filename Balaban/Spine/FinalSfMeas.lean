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
# Measurability of the small-field factor of a cut

A6-3 (a), item 1, and its cut version (A6-4, `CutSfDomInput`). On the `χ`-support
`A = {χ_k(Y) ≠ 0}` of a cut `Y` all the building blocks of `sfFactor2 C vc Y` are continuous in the
block field, and off `A` the factor is `0`; so it is Borel (`measurable_sfFactor2_of_dom`).

The terms `ℰ^{(j)}(y, X)`, `ℳ^{(j)}(x, X)` read the inherited field only on the polymer
`X ⊆ Y^≈` (`localE`, `localM`) and the remainders `ℛ^{(k)}_n(X)` read the block field only on
`X ⊆ Y` (`RTermsH4.loc`): the hypotheses ask for replacement fields `Ψe`, `Ψr`, continuous on `A`,
equal to the inherited field on `Y^≈` (resp. to the lift of the block field on `Y`) and lying in
the domains of the terms. For the whole torus the replacement fields are the fields themselves
(`measurable_sfFactor2_univ_of_dom`).
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

/-- The support of the characteristic function of the cut `Y`. -/
def AsuppY (Y : Set (Torus S.d (n (j + 1)))) :
    Set (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :=
  {ψk | C.chiY Y ψk hv ≠ 0}

/-- The support of the characteristic function of the whole torus. -/
def Asupp : Set (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :=
  AsuppY C hv Set.univ

/-- The fine set of a cut lies in the fine set of its thickening `Y^≈`. -/
theorem sset_subset_sset_thickY (Y : Set (Torus S.d (n (j + 1)))) :
    C.sset Y ⊆ C.sset (thickY R Y) := fun _ hx => subset_nbhd _ _ hx

/-- The aligned sites of a set lie in its fine set. -/
theorem alignedIn_subset_sset (jj : ℕ) (A : Set (Torus S.d (n (j + 1)))) {x}
    (hx : x ∈ C.alignedIn jj A) : x ∈ C.sset A := by
  classical
  unfold SFCtx.alignedIn at hx
  exact (Finset.mem_filter.1 hx).2.2

variable (Y : Set (Torus S.d (n (j + 1))))
  (hAD : AsuppY C hv Y ⊆ DomSetY C hv Y (C.cs.muBg (j + 1)))
  (hrepJ : ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
    ∃ Ψe : (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) →
        Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N,
      ContinuousOn Ψe (AsuppY C hv Y) ∧ ∀ ψk ∈ AsuppY C hv Y,
        (∀ x ∈ C.sset (thickY R Y), Ψe ψk x = C.psiJ Y ψk hv jj x) ∧
        ∀ X, Def6.IsPolyDom C.m₀ jj X → X ⊆ C.sset (thickY R Y) →
          (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X) (Ψe ψk)
            (Def6.constFld (hC hv)))
  (hslit : ∀ ψk ∈ AsuppY C hv Y, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ x ∈ C.sset (thickY R Y),
    dot (C.psiJ Y ψk hv jj x) (C.psiJ Y ψk hv jj x) ∈ Complex.slitPlane)

include hm0 hTm hrepJ in
/-- The localized terms `ℰ^{(j')}` of the cut at the inherited field are continuous on the
support. -/
theorem continuousOn_EresJ2_terms {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      ∑ y ∈ C.alignedIn jj Y,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
          Def6.IsPolyDom C.m₀ jj X ∧ y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
          (C.sf.Tm C.N₁).E jj y X (C.psiJ Y ψk hv jj) (Def6.constFld (hC hv))) (AsuppY C hv Y) := by
  obtain ⟨Ψe, hcont, hrep⟩ := hrepJ jj hj1 hj
  refine continuousOn_finsetSum _ fun y _ => continuousOn_finsum_mem (Set.toFinite _) fun X hX => ?_
  obtain ⟨hXp, hyX, hXY⟩ := hX
  have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
  have hAn := (hTm.analyticE jj hj1 hj y X hXp' hyX).continuousOn
  refine (hAn.comp (hcont.prodMk continuousOn_const)
    fun ψ hψ => (hrep ψ hψ).2 X hXp hXY).congr fun ψ hψ => ?_
  exact hTm.localE jj y X _ _ _ _ fun x hx => ⟨((hrep ψ hψ).1 x (hXY hx)).symm, rfl⟩

include HB hAD in
/-- The inherited field of the cut at a site is continuous on the support. -/
theorem continuousOn_psiJ_site {jj : ℕ} (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.psiJ Y ψk hv jj x) (AsuppY C hv Y) :=
  (continuousOn_pi.2 fun i => (continuousOn_psiJ_coordY C hv Y HB hj x i).mono hAD)

include HB hAD in
theorem continuousOn_dot_psiJ {jj : ℕ} (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      dot (C.psiJ Y ψk hv jj x) (C.psiJ Y ψk hv jj x)) (AsuppY C hv Y) := by
  unfold dot
  exact continuousOn_finsetSum _ fun i _ =>
    (continuousOn_psiJ_coordY C hv Y HB hj x i).mono hAD |>.mul
      ((continuousOn_psiJ_coordY C hv Y HB hj x i).mono hAD)

include HB hAD hslit in
theorem continuousOn_dot_unitDir {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1)
    {x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)} (hx : x ∈ C.sset (thickY R Y)) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      dot (hC hv) (unitDirC (C.psiJ Y ψk hv jj x))) (AsuppY C hv Y) := by
  have hu : ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      unitDirC (C.psiJ Y ψk hv jj x)) (AsuppY C hv Y) :=
    continuousOn_comp_of_continuousAt (continuousOn_psiJ_site C hv HB Y hAD hj x)
      fun ψ hψ => (unitDirC_analyticAt (hslit ψ hψ jj hj1 hj x hx)).continuousAt
  unfold dot
  exact continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul ((continuousOn_pi.1 hu) i)

include HB hAD hslit in
/-- The correction `corrSum` of P5 (1.8) of the cut at the inherited field is continuous on the
support. -/
theorem continuousOn_corrSum {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      corrSum (fun y x => vc.v1 jj (unlift jj (x - y))) (fun y x => vc.v2 jj (unlift jj (x - y)))
        (nuIdeal S.L (j + 1) (C.sf.ν (j + 1)) jj)
        (C.alignedIn jj Y) (C.alignedIn jj (thickY R Y))
        (C.psiJ Y ψk hv jj) (hC hv)) (AsuppY C hv Y) := by
  unfold corrSum corrPair
  refine continuousOn_finsetSum _ fun y hy => continuousOn_finsetSum _ fun x hx => ?_
  have hy' : y ∈ C.sset (thickY R Y) :=
    sset_subset_sset_thickY C Y (alignedIn_subset_sset C jj Y hy)
  have hx' : x ∈ C.sset (thickY R Y) := alignedIn_subset_sset C jj _ hx
  exact (continuousOn_const.mul ((continuousOn_dot_psiJ C hv HB Y hAD hj x).sub
      (continuousOn_dot_psiJ C hv HB Y hAD hj y))).add
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_dot_unitDir C hv HB Y hAD hslit hj1 hj hx').sub
        (continuousOn_dot_unitDir C hv HB Y hAD hslit hj1 hj hy'))))

include hm0 hTm hrepJ in
/-- The aggregated terms `ℳ^{(j')}` of the cut at the inherited field are continuous on the
support. -/
theorem continuousOn_MresJ_coord (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) (i : Fin N) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.MresJ Y ψk hv g jj x i) (AsuppY C hv Y) := by
  obtain ⟨Ψe, hcont, hrep⟩ := hrepJ jj hj1 hj
  unfold SFCtx.MresJ
  refine continuousOn_finsum_mem_apply (Set.toFinite _) i fun X hX => ?_
  obtain ⟨hXp, hxX, hXY⟩ := hX
  have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
  have hAn := (hTm.analyticM jj hj1 hj x X hXp' hxX).continuousOn
  have hcomp := hAn.comp (hcont.prodMk (continuousOn_const.prodMk continuousOn_const))
    (fun ψ hψ => ⟨(hrep ψ hψ).2 X hXp hXY, hg⟩)
  refine (continuousOn_pi.1 hcomp i).congr fun ψ hψ => ?_
  show (C.sf.Tm C.N₁).M jj x X (C.psiJ Y ψ hv jj) (Def6.constFld (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g) i =
    (C.sf.Tm C.N₁).M jj x X (Ψe ψ) (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i
  rw [hTm.localM jj x X _ (Ψe ψ) _ _ _ _ fun z hz => ⟨((hrep ψ hψ).1 z (hXY hz)).symm, rfl, rfl⟩]

include hm0 HB hTm hAD hrepJ in
/-- The source term `ℱ_k` of the cut is continuous on the support. -/
theorem continuousOn_Fres (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.Fres Y ψk hv g) (AsuppY C hv Y) := by
  classical
  unfold SFCtx.Fres
  have hφ := (continuousOn_phiBarY C hv Y HB).mono hAD
  refine ContinuousOn.add (continuousOn_finsetSum _ fun x _ => continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj i).continuous.comp_continuousOn (continuousOn_pi.1 hφ x)))) ?_
  refine continuousOn_finsetSum _ fun jj hjj => continuousOn_finsetSum _ fun x _ => ?_
  by_cases hx : x ∈ C.sset Y
  · simp only [hx, ↓reduceIte]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      (continuousOn_MresJ_coord C hv hm0 hTm Y hrepJ g hg (Finset.mem_Icc.1 hjj).1
        (Finset.mem_Icc.1 hjj).2 x i)
  · simp only [hx, ↓reduceIte]
    exact continuousOn_const

include hm0 in
/-- The remainders `ℛ^{(k)}_n` of the cut at the lift of the block field are continuous on the
support. -/
theorem continuousOn_Rres (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {fac : ℕ → ℝ}
    (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hrepR : ∃ Ψr : (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) →
        Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N,
      ContinuousOn Ψr (AsuppY C hv Y) ∧ ∀ ψk ∈ AsuppY C hv Y,
        (∀ x ∈ C.sset Y, Ψr ψk x = sfLiftK C.geo C.hnn C.hkK C.hT ψk x) ∧
        Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
          (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
          (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
          (P6.eps S.d S.L (j + 1)) (Ψr ψk) (Def6.constFld (hC hv))) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      C.Rres Y ψk hv g) (AsuppY C hv Y) := by
  obtain ⟨Ψr, hcont, hrep⟩ := hrepR
  unfold SFCtx.Rres
  refine continuousOn_finsetSum _ fun nn hnn => continuousOn_finsum_mem (Set.toFinite _) fun X hX => ?_
  obtain ⟨hXp, hXY⟩ := hX
  have hXp' : Def6.IsPolyDom P6.m₀ (j + 1) X := by rw [hm0]; exact hXp
  have hnn' := Finset.mem_Icc.1 hnn
  have hAn := (hRt.analytic nn hnn'.1 (by rw [hm0]; exact hnn'.2) X hXp').continuousOn
  refine (hAn.comp (hcont.prodMk (continuousOn_const.prodMk continuousOn_const))
    fun ψ hψ => ⟨(hrep ψ hψ).2, fun _ => Set.mem_univ _, hg⟩).congr fun ψ hψ => ?_
  exact hRt.loc nn X _ _ _ _ _ _ fun z hz => ⟨((hrep ψ hψ).1 z (hXY hz)).symm, rfl, rfl⟩

include hm0 HB hTm hAD hrepJ hslit in
/-- `ℰ^{(j')}` of the cut is continuous on the support. -/
theorem continuousOn_EresJ2 {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      EresJ2 C vc Y ψk hv jj) (AsuppY C hv Y) := by
  unfold EresJ2
  exact (continuousOn_EresJ2_terms C hv hm0 hTm Y hrepJ hj1 hj).sub
    (continuousOn_corrSum C hv vc HB Y hAD hslit hj1 hj)

include hm0 HB hTm hAD hrepJ hslit in
theorem continuousOn_EresK2 :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      EresK2 C vc Y ψk hv) (AsuppY C hv Y) := by
  unfold EresK2
  exact continuousOn_finsetSum _ fun jj hjj =>
    continuousOn_EresJ2 C hv vc hm0 HB hTm Y hAD hrepJ hslit (Finset.mem_Icc.1 hjj).1
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
/-- The single-scale action `A*_k` of the cut is continuous on the support. -/
theorem continuousOn_actStar2 :
    ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      actStar2 C Y ψk hv) (AsuppY C hv Y) := by
  unfold actStar2
  have hφ := (continuousOn_phiBarY C hv Y HB).mono hAD
  have hpair : ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      (C.psiLevelK ψk, C.phiBar Y ψk hv)) (AsuppY C hv Y) :=
    (continuous_psiLevelK C).continuousOn.prodMk hφ
  exact ((continuous_actionG _ _ _ _ _).comp_continuousOn hpair).add
    (((continuous_starBondE _).comp_continuousOn hφ).const_mul _)

include hm0 HB hTm hAD hrepJ hslit in
/-- **`sfFactor2` of a cut is Borel in the block field** (A6-3 (a), item 1; A6-4): on the support
`{χ_k(Y) ≠ 0}`, where the replacement fields lie in the domains of the terms, every ingredient of
the exponent is continuous, and off the support the factor is `0`. -/
theorem measurable_sfFactor2_of_dom (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {fac : ℕ → ℝ}
    (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hrepR : ∃ Ψr : (BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) →
        Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N,
      ContinuousOn Ψr (AsuppY C hv Y) ∧ ∀ ψk ∈ AsuppY C hv Y,
        (∀ x ∈ C.sset Y, Ψr ψk x = sfLiftK C.geo C.hnn C.hkK C.hT ψk x) ∧
        Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
          (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
          (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
          (P6.eps S.d S.L (j + 1)) (Ψr ψk) (Def6.constFld (hC hv)))
    (hmu : C.cs.mu (j + 1) = C.cs.muBg (j + 1)) :
    Measurable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc Y ψk hv g := by
  classical
  have HBmu : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)) := by
    rw [hmu]; exact HB
  have hchi := measurable_chiY C hv HBmu Y
  have hA : MeasurableSet (AsuppY C hv Y) :=
    (hchi (measurableSet_singleton (0 : ℝ))).compl
  have hExp : ContinuousOn (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      Complex.exp (Ares2 C vc Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g)) (AsuppY C hv Y) := by
    refine Complex.continuous_exp.comp_continuousOn (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_)
    · unfold Ares2
      refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) continuousOn_const
      · exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_actStar2 C hv HB Y hAD))
      · exact continuousOn_EresK2 C hv vc hm0 HB hTm Y hAD hrepJ hslit
    · exact continuousOn_Fres C hv hm0 HB hTm Y hAD hrepJ g hg
    · exact continuousOn_Rres C hv hm0 Y g hg hRt hrepR
  have hE : Measurable ((AsuppY C hv Y).piecewise (fun ψk : BlockAt S n M K (j + 1) →
      EuclideanSpace ℝ (Fin N) => Complex.exp (Ares2 C vc Y ψk hv + C.Fres Y ψk hv g +
        C.Rres Y ψk hv g)) (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hExp continuousOn_const hA
  have : (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc Y ψk hv g) = fun ψk =>
      ((C.chiY Y ψk hv : ℝ) : ℂ) *
        (AsuppY C hv Y).piecewise (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
          Complex.exp (Ares2 C vc Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g))
          (fun _ => 0) ψk := by
    funext ψk
    by_cases h : ψk ∈ AsuppY C hv Y
    · rw [Set.piecewise_eq_of_mem _ _ _ h]; rfl
    · have h0 : C.chiY Y ψk hv = 0 := by
        by_contra hne; exact h hne
      rw [Set.piecewise_eq_of_notMem _ _ _ h]
      unfold sfFactor2
      rw [h0]; simp
  rw [this]
  exact (Complex.measurable_ofReal.comp hchi).mul hE

include hm0 HB hTm in
/-- **`sfFactor2` of the whole torus is Borel in the block field** (A6-3 (a), item 1): on the support
`{χ_k(univ) ≠ 0}`, where the fields lie in the domains of the terms, every ingredient of the
exponent is continuous, and off the support the factor is `0` (`measurable_sfFactor2_of_dom` with
the fields themselves as replacement fields). -/
theorem measurable_sfFactor2_univ_of_dom
    (hAD : Asupp C hv ⊆ DomSet C hv (C.cs.muBg (j + 1)))
    (hdomJ : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X, Def6.IsPolyDom C.m₀ jj X →
      (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Def6.constFld (hC hv)))
    (hslit : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      ∀ x, dot (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x) ∈ Complex.slitPlane)
    (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {fac : ℕ → ℝ}
    (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hdomR : ∀ ψk ∈ Asupp C hv, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv)))
    (hmu : C.cs.mu (j + 1) = C.cs.muBg (j + 1)) :
    Measurable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g :=
  measurable_sfFactor2_of_dom C hv vc hm0 HB hTm Set.univ hAD
    (fun jj hj1 hj => ⟨fun ψk => C.psiJ Set.univ ψk hv jj,
      (continuousOn_psiJY C hv Set.univ HB hj).mono hAD,
      fun ψk hψ => ⟨fun _ _ => rfl, fun X hX _ => hdomJ ψk hψ jj hj1 hj X hX⟩⟩)
    (fun ψk hψ jj hj1 hj x _ => hslit ψk hψ jj hj1 hj x) g hg hRt
    ⟨fun ψk => sfLiftK C.geo C.hnn C.hkK C.hT ψk, (continuous_sfLiftK C).continuousOn,
      fun ψk hψ => ⟨fun _ _ => rfl, hdomR ψk hψ⟩⟩ hmu

end Ctx

end Balaban.RootFSpine
