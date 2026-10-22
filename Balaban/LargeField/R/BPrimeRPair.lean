/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimePolyRoot
public import Balaban.LargeField.R.BPrimeRootGeom
public import Balaban.SmallField.XiPerturb
public import Balaban.Background.GenSetStabilityParts

/-!
# The pair functionals of the polymer roots of the residual of `R`

The residual of `R` compares the exponent of the old small-field region `Y₁` at the background field
of `genWC Y₁` with that of the new region `Y₂` at the background field of `genWC Y₂`.  The root of a
polymer `X ∈ 𝒟_j` contributes the pair functional `polyPair` (old minus new root,
`sfExp2At_sub_eq_roots`), a functional of the data `ψ_k` and of the two fields.  Here: its P3
premises in the form of `bPrime_pairs_aggregate_adm`, and the data domain.

* `composeDep_sameCell`: the composed field at `x` reads the fields in the `K`-block of `x`;
* `SFCtx.polyPair`, `SFCtx.liftAgree`; `SFCtx.polyRoot_loc`, `SFCtx.polyPair_loc` (a root and the
  pair read the fields, the lifts and the source only on a region `X₁` containing `X` and closed
  under the `k`-blocks), `SFCtx.analyticAt_polyPair`,
  `SFCtx.norm_polyPair_le` (at fields whose composed fields lie in the class domains);
* `SFCtx.RDataNear`, `SFCtx.isOpen_rDataNear`, `SFCtx.inDomainC_of_rDataNear`,
  `SFCtx.analyticAt_dataWC`: the data within `τ` of a real datum of `Ψ̃(genWC Y; δ)` form an open
  set, on which the data lie in `Ψ̃^c(δ + 5τ, δ + 5τ)`; the data are analytic in `ψ_k`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7v2

section Dep

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- **The composed field at `x` reads the fields in the `K`-block of `x`.** -/
theorem composeDep_sameCell {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}
    {x u : Torus d (N₀ * L ^ K)} (hu : u ∈ composeDep G G' x) : SameCell (L ^ K) u x := by
  classical
  unfold composeDep at hu
  split_ifs at hu with hx
  · rw [Finset.mem_insert, Finset.mem_union] at hu
    rcases hu with rfl | hb | hb
    · exact SameCell.refl _ _
    · exact (sameCell_of_jBlock_eq (Background.layerIndex_le_top G x) (GeneratingSet.mem_blk.1 hb)).mono
        (pow_dvd_pow L (Background.layerIndex_le_top G x))
    · exact (sameCell_of_jBlock_eq (Background.layerIndex_le_top G' x) (GeneratingSet.mem_blk.1 hb)).mono
        (pow_dvd_pow L (Background.layerIndex_le_top G' x))
  · rw [Finset.mem_singleton] at hu
    subst hu
    exact SameCell.refl _ _

/-- Fields agreeing on the sites of `A` in `Ω₁` have the same extensions on `A`. -/
theorem svec_eq_of_agree {N : ℕ} {G : GeneratingSet d L N₀ K ϱ} {φ φ' : G.Ω 1 × Fin N → ℂ}
    {A : Finset (Torus d (N₀ * L ^ K))}
    (h : ∀ y : G.Ω 1, (y : Torus d (N₀ * L ^ K)) ∈ A → ∀ i, φ (y, i) = φ' (y, i))
    {u : Torus d (N₀ * L ^ K)} (hu : u ∈ A) (i : Fin N) : svec G φ u i = svec G φ' u i := by
  classical
  unfold svec zeroExt
  split_ifs with hΩ
  · exact h ⟨u, hΩ⟩ hu i
  · rfl

end Dep

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y₁ Y₂ : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))

/-- **The pair functional of a polymer root of the residual of `R`**: the root of `X ∈ 𝒟_j` for
the old small-field region `Y₁` at a field of `genWC Y₁`, minus the one for the new region `Y₂` at a
field of `genWC Y₂`. -/
noncomputable def polyPair (g : GIdx S n M K N → ℂ) (j : ℕ)
    (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (u : BlockAt S n M K k → Fin N → ℂ)
    (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ) (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ) : ℂ :=
  polyRoot C Y₁ u hv g (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) j X -
    polyRoot C Y₂ u hv g (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) j X

/-- **The agreement of two data on a region** `A`: their lifts to the transported old and new sets
agree on `A`. -/
def liftAgree (A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (u u' : BlockAt S n M K k → Fin N → ℂ) : Prop :=
  ∀ x ∈ A, ∀ i, C.liftWC Y₁ hv u x i = C.liftWC Y₁ hv u' x i ∧
    C.liftWC Y₂ hv u x i = C.liftWC Y₂ hv u' x i

theorem liftAgree_refl (A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (u : BlockAt S n M K k → Fin N → ℂ) : C.liftAgree Y₁ Y₂ hv A u u :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem liftAgree_mono {A A' : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hA : A ⊆ A')
    {u u' : BlockAt S n M K k → Fin N → ℂ} (h : C.liftAgree Y₁ Y₂ hv A' u u') :
    C.liftAgree Y₁ Y₂ hv A u u' :=
  fun x hx => h x (hA hx)

/-- **Locality of a polymer root, with two sources**: for a region `X₁ ⊇ X` closed under the
`k`-blocks, the root of `X` for the region `Y` reads the field, the lift of the data and the source
`sfG g` only on `X₁`. -/
theorem polyRoot_loc (Y : Set (Torus S.d (n k))) (g g' : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁)) {j : ℕ}
    (hj : j ≤ k) {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {X₁f : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hXX : X ⊆ ↑X₁f)
    (hcell : ∀ x ∈ X₁f, ∀ y, SameCell (S.L ^ k) y x → y ∈ X₁f)
    (u u' : BlockAt S n M K k → Fin N → ℂ) (φ φ' : (C.genWC Y).Ω 1 × Fin N → ℂ)
    (hφ : ∀ y : (C.genWC Y).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f →
      ∀ i, φ (y, i) = φ' (y, i))
    (hu : ∀ x ∈ (X₁f : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)), ∀ i,
      C.liftWC Y hv u x i = C.liftWC Y hv u' x i)
    (hg : ∀ x ∈ (X₁f : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)), ∀ i,
      sfG C.geo C.hnn C.hkK C.hT g x i = sfG C.geo C.hnn C.hkK C.hT g' x i) :
    polyRoot C Y u hv g (castΩField C.coarseSide_eq (C.genW Y) φ) j X =
      polyRoot C Y u' hv g' (castΩField C.coarseSide_eq (C.genW Y) φ') j X :=
  C.polyRoot_congr_src Y hv g g' hT hj X
    (fun x hx y hy i => svec_eq_of_agree hφ (hcell x (hXX hx) y (composeDep_sameCell hy)) i)
    (fun x hx i => hu x (hXX hx) i) (fun x hx i => hg x (hXX hx) i)

/-- **Locality of the pair functional of a polymer root**: for a region `X₁ ⊇ X` closed under the
`k`-blocks, it reads the two fields and the lifts of the data only on `X₁` (two instances of
`polyRoot_loc`). -/
theorem polyPair_loc (g : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁)) {j : ℕ}
    (hj : j ≤ k) {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {X₁f : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hXX : X ⊆ ↑X₁f)
    (hcell : ∀ x ∈ X₁f, ∀ y, SameCell (S.L ^ k) y x → y ∈ X₁f)
    (u u' : BlockAt S n M K k → Fin N → ℂ) (φ₁ φ₁' : (C.genWC Y₁).Ω 1 × Fin N → ℂ)
    (φ₂ φ₂' : (C.genWC Y₂).Ω 1 × Fin N → ℂ)
    (h₁ : ∀ y : (C.genWC Y₁).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f →
      ∀ i, φ₁ (y, i) = φ₁' (y, i))
    (h₂ : ∀ y : (C.genWC Y₂).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ X₁f →
      ∀ i, φ₂ (y, i) = φ₂' (y, i))
    (hu : C.liftAgree Y₁ Y₂ hv ↑X₁f u u') :
    C.polyPair Y₁ Y₂ hv g j X u φ₁ φ₂ = C.polyPair Y₁ Y₂ hv g j X u' φ₁' φ₂' := by
  unfold polyPair
  rw [C.polyRoot_loc hv Y₁ g g hT hj hXX hcell u u' φ₁ φ₁' h₁ (fun x hx i => (hu x hx i).1)
      (fun _ _ _ => rfl),
    C.polyRoot_loc hv Y₂ g g hT hj hXX hcell u u' φ₂ φ₂' h₂ (fun x hx i => (hu x hx i).2)
      (fun _ _ _ => rfl)]

/-- **The pair functional of a polymer root is analytic** in `(ψ_k, φ₁, φ₂)` at every point where
the composed fields lie in the class domains of the terms of `X`. -/
theorem analyticAt_polyPair (g : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁))
    (hm0 : P.m₀ = C.m₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : IsPolyDom C.m₀ j X)
    (hg : l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) (u : BlockAt S n M K k → Fin N → ℂ)
    (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ) (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ)
    (hdom₁ : X ⊆ C.sset (thickY R Y₁) → Dom.dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y₁ u hv (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) j) (constFld (hC hv)))
    (hdom₂ : X ⊆ C.sset (thickY R Y₂) → Dom.dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y₂ u hv (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) j) (constFld (hC hv))) :
    AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y₁).Ω 1 × Fin N → ℂ) ×
        ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => C.polyPair Y₁ Y₂ hv g j X q.1 q.2.1 q.2.2)
      (u, φ₁, φ₂) := by
  have h1 := C.analyticAt_polyRoot Y₁ hv g hT hm0 hj1 hjk hX hg (u, φ₁) hdom₁
  have h2 := C.analyticAt_polyRoot Y₂ hv g hT hm0 hj1 hjk hX hg (u, φ₂) hdom₂
  have p1 : AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.1))
      (u, φ₁, φ₂) := analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have p2 : AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.2))
      (u, φ₁, φ₂) := analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have c1 := AnalyticAt.comp (g := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) =>
      polyRoot C Y₁ q.1 hv g (castΩField C.coarseSide_eq (C.genW Y₁) q.2) j X)
    (f := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.1))
    (x := (u, φ₁, φ₂)) h1 p1
  have c2 := AnalyticAt.comp (g := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₂).Ω 1 × Fin N → ℂ) =>
      polyRoot C Y₂ q.1 hv g (castΩField C.coarseSide_eq (C.genW Y₂) q.2) j X)
    (f := fun q : (BlockAt S n M K k → Fin N → ℂ) ×
      ((C.genWC Y₁).Ω 1 × Fin N → ℂ) × ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => (q.1, q.2.2))
    (x := (u, φ₁, φ₂)) h2 p2
  exact c1.sub c2

open Classical in
/-- The number of `L^j`-aligned sites of `X`. -/
noncomputable def alignedCount (j : ℕ) (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) : ℕ :=
  (Finset.univ.filter fun y : Localization.CTorus S.d S.L C.N₁ m₁ k =>
    Localization.Aligned (S.L ^ j) y ∧ y ∈ X).card

open Classical in
theorem card_alignedIn_le (j : ℕ) (A : Set (Torus S.d (n k)))
    (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    ((C.alignedIn j A).filter (fun y => y ∈ X)).card ≤ C.alignedCount j X := by
  unfold alignedCount alignedIn
  refine Finset.card_le_card fun y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact ⟨hy.1.1, hy.2⟩

/-- **The bound of the pair functional of a polymer root** at every point where the composed fields
lie in the class domains: `2 (#X_j E₀ + c₉ L^{-j((d-2)/2 + γ - α₁)}) e^{-κ d_j(X)}`, `#X_j` the
`L^j`-aligned sites of `X`. -/
theorem norm_polyPair_le (g : GIdx S n M K N → ℂ) {P : Consts}
    {Dom : FieldDom S.d S.L C.N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom (C.sf.Tm C.N₁))
    (hm0 : P.m₀ = C.m₀) (hE₀ : 0 ≤ P.E₀) (hc₉ : 0 ≤ P.c₉) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : IsPolyDom C.m₀ j X)
    (hg : l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) (u : BlockAt S n M K k → Fin N → ℂ)
    (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ) (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ)
    (hdom₁ : X ⊆ C.sset (thickY R Y₁) → Dom.dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y₁ u hv (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) j) (constFld (hC hv)))
    (hdom₂ : X ⊆ C.sset (thickY R Y₂) → Dom.dom j ((C.sf.Tm C.N₁).gs j X)
      (C.psiJAt Y₂ u hv (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) j) (constFld (hC hv))) :
    ‖C.polyPair Y₁ Y₂ hv g j X u φ₁ φ₂‖ ≤
      2 * ((C.alignedCount j X : ℝ) * P.E₀ +
        P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
        Real.exp (-P.κ * sizeJ C.m₀ j X) := by
  classical
  have hE := Real.exp_pos (-P.κ * sizeJ C.m₀ j X)
  have hb : ∀ A : Set (Torus S.d (n k)),
      ((((C.alignedIn j A).filter (fun y => y ∈ X)).card : ℝ) * P.E₀ +
        P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
        Real.exp (-P.κ * sizeJ C.m₀ j X) ≤
      ((C.alignedCount j X : ℝ) * P.E₀ +
        P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
        Real.exp (-P.κ * sizeJ C.m₀ j X) := by
    intro A
    refine mul_le_mul_of_nonneg_right ?_ hE.le
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ hE₀) le_rfl
    exact_mod_cast C.card_alignedIn_le j A X
  unfold polyPair
  refine (norm_sub_le _ _).trans ?_
  have h1 := C.norm_polyRoot_le Y₁ hv g hT hm0 hE₀ hc₉ hj1 hjk hX hg u φ₁ hdom₁
  have h2 := C.norm_polyRoot_le Y₂ hv g hT hm0 hE₀ hc₉ hj1 hjk hX hg u φ₂ hdom₂
  linarith [(h1.trans (hb Y₁)), (h2.trans (hb Y₂))]

/-! ### The data domain -/

/-- **The data near a real datum** of `Ψ̃(genWC Y; δ)` with the field `h`: the lift of `ψ_k` to
the data sites of `genWC Y` is within `τ` of it. -/
def RDataNear (Y : Set (Torus S.d (n k))) (ν δ τ : ℝ) (u : BlockAt S n M K k → Fin N → ℂ) : Prop :=
  ∃ Ψ₀ : Localization.CTorus S.d S.L C.N₁ m₁ k → Fin N → ℝ,
    InPsiTilde (C.genWC Y) ν δ Ψ₀ (fun i => hv i) ∧
      ∀ x ∈ dataSites (C.genWC Y), vn (fun i => C.liftWC Y hv u x i - (Ψ₀ x i : ℂ)) < τ

/-- The coordinates of the lift are continuous in `ψ_k`. -/
theorem continuous_liftWC (Y : Set (Torus S.d (n k)))
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (i : Fin N) :
    Continuous fun u : BlockAt S n M K k → Fin N → ℂ => C.liftWC Y hv u x i :=
  continuous_iff_continuousAt.2 fun u =>
    (C.analyticAt_liftWC Y hv (q₀ := u) id analyticAt_id x i).continuousAt

/-- **The data near a real datum form an open set.** -/
theorem isOpen_rDataNear (Y : Set (Torus S.d (n k))) (ν δ τ : ℝ) :
    IsOpen {u : BlockAt S n M K k → Fin N → ℂ | C.RDataNear hv Y ν δ τ u} := by
  classical
  have e : {u : BlockAt S n M K k → Fin N → ℂ | C.RDataNear hv Y ν δ τ u} =
      ⋃ Ψ₀ ∈ {Ψ₀ : Localization.CTorus S.d S.L C.N₁ m₁ k → Fin N → ℝ |
        InPsiTilde (C.genWC Y) ν δ Ψ₀ (fun i => hv i)},
        ⋂ x ∈ dataSites (C.genWC Y),
          {u | vn (fun i => C.liftWC Y hv u x i - (Ψ₀ x i : ℂ)) < τ} := by
    ext u
    simp only [RDataNear, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
  rw [e]
  refine isOpen_biUnion fun Ψ₀ _ => ?_
  refine isOpen_biInter_finset fun x _ => ?_
  have hc : Continuous fun u : BlockAt S n M K k → Fin N → ℂ =>
      (fun i => C.liftWC Y hv u x i - (Ψ₀ x i : ℂ)) :=
    continuous_pi fun i => (C.continuous_liftWC hv Y x i).sub continuous_const
  have hvn : Continuous fun v : Fin N → ℂ => vn v :=
    continuous_norm.comp (PiLp.continuous_toLp 2 _)
  exact isOpen_lt (hvn.comp hc) continuous_const

/-- **The data near a real datum lie in `Ψ̃^c(genWC Y; δ + 5τ, δ + 5τ)`.** -/
theorem inDomainC_of_rDataNear (Y : Set (Torus S.d (n k))) {ν δ τ : ℝ} (hδ0 : 0 < δ)
    (hδ14 : δ ≤ 1 / 4) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {u : BlockAt S n M K k → Fin N → ℂ}
    (hu : C.RDataNear hv Y ν δ τ u) :
    InDomainC (C.genWC Y) ν (δ + 5 * τ) (δ + 5 * τ) (C.dataWC Y hv u) := by
  obtain ⟨Ψ₀, hP, hD⟩ := hu
  set D := C.dataWC Y hv u with hDdef
  set δΨ : Localization.CTorus S.d S.L C.N₁ m₁ k → Fin N → ℂ :=
    fun x i => D.Ψ x i - (Ψ₀ x i : ℂ) with hδΨ
  have hδΨc : IsLayerConstant (C.genWC Y) δΨ := by
    intro m hm1 hmk x hx x' hx'
    funext i
    show D.Ψ x' i - (Ψ₀ x' i : ℂ) = D.Ψ x i - (Ψ₀ x i : ℂ)
    rw [congrFun (D.Ψ_layerConst m hm1 hmk x hx x' hx') i,
      congrFun (hP.layerConst m hm1 hmk x hx x' hx') i]
  have hDΨ : ∀ x ∈ dataSites (C.genWC Y), vn (δΨ x) ≤ τ := by
    intro x hx
    have := (hD x hx).le
    simpa [hδΨ, hDdef, C.dataWC_Ψ] using this
  have hPC := perturb_inPsiTildeC hδ14 hτ0 hτ1 (RootFSpine.inPsiTildeC_of_inPsiTilde hδ0 hP) hδΨc hDΨ
  refine ⟨Ψ₀, fun i => hv i, _, _, hPC, fun x _ i => by simp [hδΨ], fun x hx i => ?_⟩
  rw [hDdef, C.dataWC_h Y hv u hx i]
  simp

/-- **The data are analytic in `ψ_k`.** -/
theorem analyticAt_dataWC (Y : Set (Torus S.d (n k))) (u : BlockAt S n M K k → Fin N → ℂ) :
    AnalyticAt ℂ (fun u : BlockAt S n M K k → Fin N → ℂ =>
      ((C.dataWC Y hv u).Ψ, (C.dataWC Y hv u).h)) u := by
  refine AnalyticAt.prod ?_ ?_
  · rw [analyticAt_pi_iff]
    intro x
    rw [analyticAt_pi_iff]
    intro i
    simp only [C.dataWC_Ψ]
    exact C.analyticAt_liftWC Y hv id analyticAt_id x i
  · have e : (fun u : BlockAt S n M K k → Fin N → ℂ => (C.dataWC Y hv u).h) =
        fun _ => (C.dataWC Y hv u).h := by
      funext u'
      unfold dataWC
      rw [castData_h, castData_h]
      rfl
    rw [e]
    exact analyticAt_const

end Def7.SFCtx

end Balaban.LargeField
