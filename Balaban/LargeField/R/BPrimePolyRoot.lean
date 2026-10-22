/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeRootForm
public import Balaban.LargeField.R.BPrimeCast
public import Balaban.Localization.DecoupledCompose
public import Balaban.LargeField.R.BPrimeDomainR
public import Balaban.SmallField.Def6v2Birth
public import Balaban.Fluctuation.LocalClassInherit

/-!
# The polymer roots of the residual of `R`: analyticity

The root of a polymer `X ∈ 𝒟_j` of the exponent of (D1) (`polyRoot`) reads the background field `φ`
of `𝔹_k(W)` and the field `ψ_k` through the composed field `ψ^{(j)} = composeField(𝔹_j(W), 𝔹_k(W);
φ, lift ψ_k)`, which is affine in `(ψ_k, φ)`; the class terms are analytic on their domains
(`SFTermClauses`).  Here the fields `φ` are those of the transported set `genWC Y` of the Def-6
torus (`castΩField`).

* `SFCtx.analyticAt_liftWC`: the coordinates of the transported lift of `ψ_k` are analytic in `ψ_k`;
* `SFCtx.analyticAt_psiJAt_cast`: `ψ^{(j)}` is analytic in `(ψ_k, φ)`;
* `SFCtx.analyticAt_polyRoot`: the root of a polymer is analytic at every point where the
  composed field lies in the domains of the class terms;
* `SFCtx.dom_psiJAt_of_near`: the composed field of a field near the approximate field lies in
  the birth domain of the class;
* `SFCtx.polyRoot_congr`: locality of the root;
* `SFCtx.norm_polyRoot_le`: the bound of the root on the domain.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7v2
  Balaban.SmallField.GsSpec

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

/-- The data of `𝔹_k(W)` of a complex field `ψ_k` on the `k`-blocks, transported to the Def-6
torus. -/
noncomputable def liftWC (ψC : BlockAt S n M K k → Fin N → ℂ) :
    Localization.CTorus S.d S.L C.N₁ m₁ k → Fin N → ℂ :=
  castTField C.coarseSide_eq (liftSingle (C.genW Y) (C.liftDataC ψC) (hC hv)).Ψ

/-- **The coordinates of the transported lift are analytic in `ψ_k`** (they are coordinates of
`ψ_k` or `0`). -/
theorem analyticAt_liftWC {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q₀ : Q}
    (ψ : Q → BlockAt S n M K k → Fin N → ℂ) (hψ : AnalyticAt ℂ ψ q₀)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (i : Fin N) :
    AnalyticAt ℂ (fun q => C.liftWC Y hv (ψ q) x i) q₀ := by
  classical
  unfold liftWC
  simp only [castTField_apply]
  unfold liftSingle BgData.clip
  by_cases hx : (GsSpec.torusCast x : BgT C.geo k) ∈ dataSites (C.genW Y)
  · simp only [hx, ↓reduceIte]
    unfold blockLift liftDataC
    exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hψ _) i
  · simp only [hx, ↓reduceIte]
    exact analyticAt_const

/-- **`ψ^{(j)}` is analytic in `(ψ_k, φ)`**: the composed field of a transported background field
`φ` of `genWC Y` and of the lift of `ψ_k`. -/
theorem analyticAt_psiJAt_cast {j : ℕ}
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ)) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j) q₀ := by
  rw [analyticAt_pi_iff]
  intro x
  rw [analyticAt_pi_iff]
  intro i
  by_cases hj : j ≤ k
  · have e : (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
        C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j x i) =
        fun q => composeField (C.genWCj hj Y) (C.genWC Y) C.weights q.2 (C.liftWC Y hv q.1) x i :=
      funext fun q => C.psiJAt_cast Y q.1 hv q.2 hj x i
    rw [e]
    refine analyticAt_composeField (G := C.genWCj hj Y) (G' := C.genWC Y) (q := q₀) C.weights
      (fun q => q.2) (fun q => C.liftWC Y hv q.1) (fun r => ?_) (fun y i' => ?_) x i
    · exact analyticAt_pi_iff.1 analyticAt_snd r
    · exact C.analyticAt_liftWC Y hv
        (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) => q.1)
        analyticAt_fst y i'
  · have e : (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
        C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j x i) = fun _ => 0 := by
      funext q; unfold psiJAt; simp [hj]
    rw [e]
    exact analyticAt_const

/-- **The root of a polymer is analytic** in `(ψ_k, φ)` at every point where the composed field
`ψ^{(j)}`, with the constant field `h`, lies in the domain of the class terms of `X` (when
`X ⊂ Y^≈`; otherwise the root vanishes), for a source `g` with `‖g‖₁ < 1`. -/
theorem analyticAt_polyRoot (g : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁))
    (hm0 : P.m₀ = C.m₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : IsPolyDom C.m₀ j X)
    (hg : l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1)
    (q₀ : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ))
    (hdom : X ⊆ C.sset (thickY R Y) → Dom.dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j)
      (constFld (hC hv))) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
      polyRoot C Y q.1 hv g (castΩField C.coarseSide_eq (C.genW Y) q.2) j X) q₀ := by
  classical
  have hX' : IsPolyDom P.m₀ j X := hm0 ▸ hX
  have hF := C.analyticAt_psiJAt_cast Y hv (j := j) q₀
  unfold polyRoot
  by_cases hXT : X ⊆ C.sset (thickY R Y)
  · simp only [hXT, ↓reduceIte]
    have hd := hdom hXT
    refine AnalyticAt.add (Finset.analyticAt_fun_sum _ fun y hy => ?_)
      (Finset.analyticAt_fun_sum _ fun x hx => Finset.analyticAt_fun_sum _ fun i _ => ?_)
    · have hyX : y ∈ X := (Finset.mem_filter.1 hy).2
      have hE := hT.analyticE j hj1 hjk y X hX' hyX
        (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j,
          constFld (hC hv)) hd
      have hpair : AnalyticAt ℂ
          (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
            (C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j,
              (constFld (hC hv) : Fld S.d S.L C.N₁ m₁ k N))) q₀ :=
        hF.prod analyticAt_const
      exact AnalyticAt.comp (g := fun p : Fld S.d S.L C.N₁ m₁ k N × Fld S.d S.L C.N₁ m₁ k N =>
        (C.sf.Tm C.N₁).E j y X p.1 p.2)
        (f := fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
            (C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j,
              (constFld (hC hv) : Fld S.d S.L C.N₁ m₁ k N))) (x := q₀) hE hpair
    · have hxX : x ∈ X := (Finset.mem_filter.1 hx).2.1
      have hM := hT.analyticM j hj1 hjk x X hX' hxX
        (C.psiJAt Y q₀.1 hv (castΩField C.coarseSide_eq (C.genW Y) q₀.2) j,
          constFld (hC hv), sfG C.geo C.hnn C.hkK C.hT g) ⟨hd, hg⟩
      have htriple : AnalyticAt ℂ
          (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
            (C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j,
              (constFld (hC hv) : Fld S.d S.L C.N₁ m₁ k N),
              (sfG C.geo C.hnn C.hkK C.hT g : Fld S.d S.L C.N₁ m₁ k N))) q₀ :=
        hF.prod (analyticAt_const.prod analyticAt_const)
      have hMc := AnalyticAt.comp (g := fun p : Fld S.d S.L C.N₁ m₁ k N ×
          Fld S.d S.L C.N₁ m₁ k N × Fld S.d S.L C.N₁ m₁ k N =>
        (C.sf.Tm C.N₁).M j x X p.1 p.2.1 p.2.2)
        (f := fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y).Ω 1 × Fin N → ℂ) =>
            (C.psiJAt Y q.1 hv (castΩField C.coarseSide_eq (C.genW Y) q.2) j,
              (constFld (hC hv) : Fld S.d S.L C.N₁ m₁ k N),
              (sfG C.geo C.hnn C.hkK C.hT g : Fld S.d S.L C.N₁ m₁ k N))) (x := q₀) hM htriple
      exact analyticAt_const.mul (analyticAt_pi_iff.1 hMc i)
  · simp only [hXT, ↓reduceIte]
    exact analyticAt_const

/-- The data of `𝔹_k(W)` of a complex field `ψ_k`, transported to the Def-6 torus. -/
noncomputable def dataWC (ψC : BlockAt S n M K k → Fin N → ℂ) : BgData (C.genWC Y) N :=
  castData C.coarseSide_eq (C.genW Y) (liftSingle (C.genW Y) (C.liftDataC ψC) (hC hv))

theorem dataWC_Ψ (ψC : BlockAt S n M K k → Fin N → ℂ) : (C.dataWC Y hv ψC).Ψ = C.liftWC Y hv ψC :=
  castData_Ψ _ _ _

theorem dataWC_h (ψC : BlockAt S n M K k → Fin N → ℂ) {x : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hx : x ∈ (C.genWC Y).Ω 1) (i : Fin N) : (C.dataWC Y hv ψC).h x i = ((hv i : ℝ) : ℂ) := by
  unfold dataWC
  rw [castData_h, castTField_apply]
  have hx' : (GsSpec.torusCast x : BgT C.geo k) ∈ (C.genW Y).Ω 1 := by
    have := (C.mem_genWC_Ω Y 1 x).1 hx
    rwa [sfToBg_eq_torusCast] at this
  rw [liftSingle_h _ _ _ hx']
  rfl

/-- **The composed field of a field near the approximate field lies in the class domain of the terms
of `R`** (the birth domain of the class, `birthXiDom`): the instance of
`sfTerm_nearCompose_xiDom` at the data of `ψ_k`, when the weights and the mass of the class at the
level `j` are those of the step (`hA`, `hμ`) and the radius fits (`(2 K₁ + 2) r ≤ ε_j`). -/
theorem dom_psiJAt_of_near {j : ℕ} (hj1 : 1 ≤ j) (hj : j < k) (hL : 3 ≤ S.L)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hX : X ⊆ C.sset (thickY R Y)) (hpoly : IsPolyDom C.m₀ j X) (hN : S.L ^ C.m₀ ∣ C.N₁)
    {P : Consts} {Rg : Regime S.L} {a : ℕ → ℝ}
    (hΩ : ∀ i, j < i → ((C.sf.Tm C.N₁).gs j X).Ω i = ∅)
    (hHat : HatSpec C.m₀ j X ((C.sf.Tm C.N₁).gs j X)) (hlt : hatScale S.L m₁ ϱ < C.m₀)
    (hsep : ϱ ≤ minSep S.L (S.L ^ (m₁ + hatScale S.L m₁ ϱ)))
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hm : m₁ + hatScale S.L m₁ ϱ + 3 ≤ C.m₀ + m₁)
    {a₁ ν c BG κ : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.selfKc S.d S.L) (Cchi S.d S.L) c BG)
    (SG : DGSetting (C.genWC Y) (compWeight S.L a₁) ν)
    (HB : BgHyp S.d S.L k (minSep S.L C.geo.M1) (compWeight S.L a₁) ν)
    (HBG : BgHyp S.d S.L k ϱ (compWeight S.L a₁) ν) (ha₁ : 0 < a₁) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁) {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ)
    (hδ73 : δ ≤ thm73C1 S.d S.L N) (hδc : δ + 5 * τ ≤ c7 S.d S.L N BG κ)
    (hrad : decDomRad S.d S.L N BG κ δ τ ≤ bgC1 S.d S.L N)
    (hw : C.weights = compWeight S.L a₁) (hA : aIdeal S.L k (a k) = compWeight S.L a₁)
    (hμ : physMass S.L j (Rg.ν j) = ν)
    (hε : (2 * bgK1 S.d S.L N + 2) * decDomRad S.d S.L N BG κ δ τ ≤ P.eps S.d S.L j)
    {Ψ₀ : Localization.CTorus S.d S.L C.N₁ m₁ k → Fin N → ℝ}
    (hP : InPsiTilde (C.genWC Y) ν δ Ψ₀ (fun i => hv i)) (ψC : BlockAt S n M K k → Fin N → ℂ)
    (hDΨ : ∀ x ∈ dataSites (C.genWC Y), vn (fun i => C.liftWC Y hv ψC x i - (Ψ₀ x i : ℂ)) ≤ τ)
    {φ : (C.genWC Y).Ω 1 × Fin N → ℂ}
    (hφ : NearApprox (C.genWC Y) (compWeight S.L a₁) ν (C.dataWC Y hv ψC)
      (cK2' S.d S.L N (famConst S.d S.L BG κ) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ) :
    (birthXiDom P Rg a C.N₁).dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j) (constFld (hC hv)) := by
  have hXi := C.sfTerm_nearCompose_xiDom Y hj1 hj hL hX hpoly hN hΩ hHat hlt hsep hMm hm hS SG HB
    HBG ha₁ hκ hM hδ0 hτ0 hδ73 hδc hrad hP (D := C.dataWC Y hv ψC)
    (fun x hx i => C.dataWC_h Y hv ψC hx i) (fun x hx => by rw [C.dataWC_Ψ]; exact hDΨ x hx) hφ
  rw [birthXiDom_dom_iff, hA, hμ]
  have e : (fun x i => composeField (C.genWCj hj.le Y) (C.genWC Y) (compWeight S.L a₁) φ
      (C.dataWC Y hv ψC).Ψ x i) = C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j := by
    funext x i
    rw [C.psiJAt_cast Y ψC hv φ hj.le x i, hw, C.dataWC_Ψ]
    rfl
  rw [e] at hXi
  obtain ⟨Ψ₀', h₀', Ψ'', h'', h1, h2, hXC⟩ := hXi
  exact ⟨Ψ₀', h₀', Ψ'', h'', h1, h2, Def6v2.xiC_mono_eps zero_le_one hε hXC⟩

/-- **Locality of the root of a polymer**: it depends on the background field only on the
dependency sets `composeDep(𝔹_j(W), 𝔹_k(W); x)`, `x ∈ X`, and on `ψ_k` only through its lift on
`X`. -/
theorem polyRoot_congr (g : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁)) {j : ℕ}
    (hj : j ≤ k) (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    {ψC ψC' : BlockAt S n M K k → Fin N → ℂ} {φ φ' : (C.genWC Y).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x ∈ X, ∀ u ∈ composeDep (C.genWCj hj Y) (C.genWC Y) x, ∀ i,
      svec (C.genWC Y) φ u i = svec (C.genWC Y) φ' u i)
    (hψ : ∀ x ∈ X, ∀ i, C.liftWC Y hv ψC x i = C.liftWC Y hv ψC' x i) :
    polyRoot C Y ψC hv g (castΩField C.coarseSide_eq (C.genW Y) φ) j X =
      polyRoot C Y ψC' hv g (castΩField C.coarseSide_eq (C.genW Y) φ') j X := by
  have hF : ∀ x ∈ X, C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j x =
      C.psiJAt Y ψC' hv (castΩField C.coarseSide_eq (C.genW Y) φ') j x := by
    intro x hx
    funext i
    rw [C.psiJAt_cast Y ψC hv φ hj x i, C.psiJAt_cast Y ψC' hv φ' hj x i]
    exact composeField_congr C.weights (hφ x hx) (hψ x hx) i
  unfold polyRoot
  split_ifs
  · congr 1
    · refine Finset.sum_congr rfl fun y _ => ?_
      exact hT.localE j y X _ _ _ _ fun x hx => ⟨hF x hx, rfl⟩
    · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hT.localM j x X _ _ _ _ _ _ fun z hz => ⟨hF z hz, rfl, rfl⟩]
  · rfl

open Classical in
/-- **The bound of the root of a polymer**: at a point where the composed field lies in the domain of
the class terms, `|root| ≤ ((#y) E₀ + c₉ L^{-j((d-2)/2 + γ - α₁)}) e^{-κ d_j(X)}` (`#y` the
aligned sites of `X ∩ Y`, `‖g‖₁ < 1`). -/
theorem norm_polyRoot_le (g : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁))
    (hm0 : P.m₀ = C.m₀) (hE₀ : 0 ≤ P.E₀) (hc₉ : 0 ≤ P.c₉) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : IsPolyDom C.m₀ j X)
    (hg : l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) (ψC : BlockAt S n M K k → Fin N → ℂ)
    (φ : (C.genWC Y).Ω 1 × Fin N → ℂ)
    (hdom : X ⊆ C.sset (thickY R Y) → Dom.dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j) (constFld (hC hv))) :
    ‖polyRoot C Y ψC hv g (castΩField C.coarseSide_eq (C.genW Y) φ) j X‖ ≤
      (((C.alignedIn j Y).filter (fun y => y ∈ X)).card * P.E₀ +
        P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
        Real.exp (-P.κ * sizeJ C.m₀ j X) := by
  classical
  have hX' : IsPolyDom P.m₀ j X := hm0 ▸ hX
  have hE0 := Real.exp_pos (-P.κ * sizeJ C.m₀ j X)
  have hLp : 0 ≤ ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁) :=
    Real.rpow_nonneg (by positivity) _
  set B := P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁) *
    Real.exp (-P.κ * sizeJ C.m₀ j X) with hB
  have hB0 : 0 ≤ B := by positivity
  have hsz : sizeJ C.m₀ j X = sizeJ P.m₀ j X := by rw [hm0]
  unfold polyRoot
  split_ifs with hXT
  · have hd := hdom hXT
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · refine (norm_sum_le _ _).trans ?_
      calc ∑ y ∈ (C.alignedIn j Y).filter (fun y => y ∈ X),
            ‖(C.sf.Tm C.N₁).E j y X (C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j)
              (constFld (hC hv))‖
          ≤ ∑ _y ∈ (C.alignedIn j Y).filter (fun y => y ∈ X),
              P.E₀ * Real.exp (-P.κ * sizeJ C.m₀ j X) :=
            Finset.sum_le_sum fun y hy => by
              rw [hsz]
              exact hT.boundE j hj1 hjk y X hX' (Finset.mem_filter.1 hy).2 _ _ hd
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    · rw [← hB]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ x ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
            (fun x => x ∈ X ∧ x ∈ C.sset Y),
            ‖∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * (C.sf.Tm C.N₁).M j x X
              (C.psiJAt Y ψC hv (castΩField C.coarseSide_eq (C.genW Y) φ) j)
              (constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i‖
          ≤ ∑ x ∈ (Finset.univ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)).filter
            (fun x => x ∈ X ∧ x ∈ C.sset Y), vn (sfG C.geo C.hnn C.hkK C.hT g x) * B := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hxX : x ∈ X := (Finset.mem_filter.1 hx).2.1
            refine (norm_sum_mul_le_vn _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (vn_nonneg _)
            have h2 := (hT.boundM j hj1 hjk x X hX' hxX _ _ _ hd hg).le
            rw [← hsz] at h2
            exact h2
        _ ≤ ∑ x, vn (sfG C.geo C.hnn C.hkK C.hT g x) * B :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun x _ _ => mul_nonneg (vn_nonneg _) hB0
        _ = l1 (sfG C.geo C.hnn C.hkK C.hT g) * B := by rw [← Finset.sum_mul]; rfl
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right hg.le hB0
        _ = B := one_mul B
  · simp only [norm_zero]
    have h1 : (0 : ℝ) ≤ ((C.alignedIn j Y).filter (fun y => y ∈ X)).card * P.E₀ :=
      mul_nonneg (Nat.cast_nonneg _) hE₀
    exact mul_nonneg (add_nonneg h1 (mul_nonneg hc₉ hLp)) hE0.le

end Def7.SFCtx

end Balaban.LargeField
