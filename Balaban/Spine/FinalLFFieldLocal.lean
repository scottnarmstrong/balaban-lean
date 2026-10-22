/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFProduct
public import Balaban.Spine.FinalLFRegionLocal

/-!
# The fields of the boundary terms on a set of cubes are those of the records there (A6-4)

The boundary term `ℬ^{(k)}(X, 𝔸)` of a history reads the global multiscale field `gMulti` and the
global fluctuation field `gFluct` only on the blocks of the fine set of `X` (`D7` `loc_field`). For a
history of the large-field half, the configuration of its internal variables is read off one
configuration `z` of the global variables (`famEquiv`, `Spine/FinalLFProduct.lean`). This file proves
that on the blocks of the fine set of `X` these fields depend only on the records of the components
meeting `X`: two histories whose components meeting `X` have the same records have the same fields
there, at the configurations read off the same `z` (`gMulti_eq_on_of_corr`, `gFluct_eq_on_of_corr`).

* `subMultiscaleField_transport`, `subFluctField_transport`: the fields of a component read off `z`
  depend only on its localized history and the global image of its variables;
* `gMulti_eq_of_blockSub`, `gMulti_eq_zero_of_not`, `gFluct_eq_of_blockSub`, `gFluct_eq_zero_of_not`:
  the global fields on a block of a component;
* **`gMulti_eq_on_of_corr`**, **`gFluct_eq_on_of_corr`**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

section Transport

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ} {R : ℕ → ℝ}

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- **The multiscale field of a component read off a global configuration** depends only on its
localized history and on the global image of its variables. -/
theorem subMultiscaleField_transport {a a' : LocalHistory S n M K} (h : a = a')
    {A : Set (InternalVars a k)} {A' : Set (InternalVars a' k)} (hA : gImage A = gImage A')
    {W : Set (GVar S n M K k)} (h₁ : gImage A ⊆ W) (h₂ : gImage A' ⊆ W) (z : GCfgOn N W)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    subMultiscaleField N a k (Vblk R a k) ((subCfgEquiv A).symm (restrictOn h₁ z))
        (outOf R a k ψk) =
      subMultiscaleField N a' k (Vblk R a' k) ((subCfgEquiv A').symm (restrictOn h₂ z))
        (outOf R a' k ψk) := by
  subst h
  have e : A = A' := (Set.image_injective.2 Subtype.val_injective) hA
  subst e
  rfl

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- **The fluctuation field of a component read off a global configuration** depends only on its
localized history and on the global image of its variables. -/
theorem subFluctField_transport {a a' : LocalHistory S n M K} (h : a = a')
    {A : Set (InternalVars a k)} {A' : Set (InternalVars a' k)} (hA : gImage A = gImage A')
    {W : Set (GVar S n M K k)} (h₁ : gImage A ⊆ W) (h₂ : gImage A' ⊆ W) (z : GCfgOn N W) :
    subFluctField N a k ((subCfgEquiv A).symm (restrictOn h₁ z)) =
      subFluctField N a' k ((subCfgEquiv A').symm (restrictOn h₂ z)) := by
  subst h
  have e : A = A' := (Set.image_injective.2 Subtype.val_injective) hA
  subst e
  rfl

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- Restricting twice is restricting once. -/
theorem restrictOn_restrictOn {U V W : Set (GVar S n M K k)} (h₁ : U ⊆ V) (h₂ : V ⊆ W)
    (z : GCfgOn N W) : restrictOn h₁ (restrictOn h₂ z) = restrictOn (h₁.trans h₂) z := rfl

end Transport

section Eval

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N : ℕ} {R : ℕ → ℝ} {ι : Type} [Fintype ι] {a : ι → LocalHistory S n M K} {k : ℕ}
  {P : ∀ i, OpPkg N R (a i) k} {car : ι → Set (Torus S.d (M * n K * S.L ^ K))}
  (hcar : ∀ i i' x, x ∈ car i → x ∈ car i' → i = i')

omit [Fintype ι] in
include hcar in
/-- A block of scale `j ≤ K` in the fine sets of two members lies in one member. -/
theorem eq_of_blockSub_car {j : ℕ} (hjK : j ≤ K) {y : BlockAt S n M K j} {i i' : ι}
    (hi : BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i))
    (hi' : BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i')) : i = i' := by
  obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) (K := K) hjK y
  exact hcar i i' x (hi x hx) (hi' x hx)

include hcar in
/-- **The global multiscale field on a block of a member** (`j < k`) is the multiscale field of
the member. -/
theorem gMulti_eq_of_blockSub (Om : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (x : GCfg a k P) {j : ℕ} (hjk : j < k)
    (hjK : j ≤ K) {y : BlockAt S n M K j} (i : ι)
    (hi : BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i)) :
    gMulti a k P car Om ψk x j y =
      subMultiscaleField N (a i) k (Vblk R (a i) k) (x i) (outOf R (a i) k ψk) j y := by
  classical
  have hex : ∃ i, BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i) := ⟨i, hi⟩
  have hch : hex.choose = i := eq_of_blockSub_car hcar hjK hex.choose_spec hi
  unfold gMulti
  rw [ite_eq_left hjk, dite_eq_left hex]
  rw [hch]

/-- The global multiscale field vanishes on a block of scale `j < k` of no member. -/
theorem gMulti_eq_zero_of_not (Om : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (x : GCfg a k P) {j : ℕ} (hjk : j < k)
    {y : BlockAt S n M K j}
    (h : ¬ ∃ i, BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i)) :
    gMulti a k P car Om ψk x j y = 0 := by
  classical
  unfold gMulti
  rw [ite_eq_left hjk, dite_eq_right h]

open Classical in
/-- The global multiscale field at the scale `k` is `ψ_k` on the blocks of `Om`. -/
theorem gMulti_top (Om : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (x : GCfg a k P) (y : BlockAt S n M K k) :
    gMulti a k P car Om ψk x k y =
      if BlockSub (S := S) (n := n) (M := M) (K := K) k y Om then ψk y else 0 := by
  classical
  unfold gMulti
  rw [ite_eq_right (lt_irrefl k), dite_eq_left rfl]

/-- The global multiscale field vanishes above the scale `k`. -/
theorem gMulti_eq_zero_of_gt (Om : Set (Torus S.d (M * n K * S.L ^ K)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (x : GCfg a k P) {j : ℕ} (hkj : k < j)
    (y : BlockAt S n M K j) : gMulti a k P car Om ψk x j y = 0 := by
  classical
  unfold gMulti
  rw [ite_eq_right (by omega), dite_eq_right (by omega)]

include hcar in
/-- **The global fluctuation field on a block of a member** is the fluctuation field of the
member. -/
theorem gFluct_eq_of_blockSub (x : GCfg a k P) {j : ℕ} (hjK : j ≤ K) {y : BlockAt S n M K j}
    (i : ι) (hi : BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i)) :
    gFluct a k P car x j y = subFluctField N (a i) k (x i) j y := by
  classical
  have hex : ∃ i, BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i) := ⟨i, hi⟩
  have hch : hex.choose = i := eq_of_blockSub_car hcar hjK hex.choose_spec hi
  unfold gFluct
  rw [dite_eq_left hex, hch]

/-- The global fluctuation field vanishes on a block of no member. -/
theorem gFluct_eq_zero_of_not (x : GCfg a k P) {j : ℕ} {y : BlockAt S n M K j}
    (h : ¬ ∃ i, BlockSub (S := S) (n := n) (M := M) (K := K) j y (car i)) :
    gFluct a k P car x j y = 0 := by
  classical
  unfold gFluct
  rw [dite_eq_right h]

end Eval

section Corr

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

omit [NeZero M] [NeZero S.L] in
/-- The fine sets of distinct post components are disjoint. -/
theorem postComp_eq_of_mem_fineSet (A : LabHist S n R k0 K) (c c' : PostComp A k)
    (x : Torus S.d (M * n K * S.L ^ K))
    (hc : x ∈ fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
    (hc' : x ∈ fineSet (S := S) (n := n) M K k (c'.1.1 : Set (Torus S.d (n k)))) : c = c' :=
  Subtype.ext (Subtype.ext (comp_eq_of_mem c.1.2 c'.1.2 hc hc'))

/-- **A block of a component meeting `X` is a block of a corresponding component**: for a block of
scale `j ≤ K` in the fine set of `X` and in the fine set of a post component `c` of `𝔸`, the
component meets `X`; if its record is the record of a component `c'` of `𝔸'` (without removals up
to the scale `k`), the block lies in the fine set of `c'`. -/
theorem exists_corr_of_blockSub {A A' : LabHist S n R k0 K} (hA' : ∀ i, i ≤ k → A'.H.rem i = ∅)
    {X : Finset (Torus S.d (n k))}
    (hAB : ∀ c : A.H.Comp k, (c.1 ∩ X).Nonempty →
      ∃ c' : A'.H.Comp k, compRec M A' c' = compRec M A c)
    {j : ℕ} (hjK : j ≤ K) {y : BlockAt S n M K j}
    (hy : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))))
    (c : PostComp A k)
    (hc : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))) :
    ∃ c' : PostComp A' k, compRec M A' c'.1 = compRec M A c.1 ∧
      BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K k (c'.1.1 : Set (Torus S.d (n k)))) := by
  obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) (K := K) hjK y
  have hxc : cubeMap n S.L M K k x ∈ c.1.1 := hc x hx
  have hxX : cubeMap n S.L M K k x ∈ X := hy x hx
  obtain ⟨c', hc'⟩ := hAB c.1 ⟨_, Finset.mem_inter.2 ⟨hxc, hxX⟩⟩
  have h1 : c'.1 = c.1.1 := congrArg Prod.fst hc'
  refine ⟨⟨c', by rw [hA' k le_rfl]; exact Finset.notMem_empty _⟩, hc', fun x' hx' => ?_⟩
  change cubeMap n S.L M K k x' ∈ c'.1
  rw [h1]
  exact hc x' hx'

/-- **The fields of corresponding components read off one configuration agree**: for a post
component `c` of a history of the large-field half and a post component `c'` of a second history
with the same record, the multiscale and fluctuation fields of the components at the configurations
read off one configuration `z` of the global variables are equal. -/
theorem subFields_eq_of_compRec {A A' : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k)
    (c : PostComp A k) (c' : PostComp A' k) (hrec : compRec M A' c'.1 = compRec M A c.1)
    {W : Set (GVar S n M K k)}
    (hU : (⋃ c : PostComp A k, gImage (postOp geo cs rep.SD rep.KD A hkK c).A) ⊆ W)
    (hU' : (⋃ c : PostComp A' k, gImage (postOp geo cs rep.SD rep.KD A' hkK c).A) ⊆ W)
    (z : GCfgOn N W) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    subMultiscaleField N (A.H.localHistory M K k c.1) k (Vblk R (A.H.localHistory M K k c.1) k)
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
          (pairwise_disjoint_postOp rep hkK A)).symm (restrictOn hU z) c)
        (outOf R (A.H.localHistory M K k c.1) k ψk) =
      subMultiscaleField N (A'.H.localHistory M K k c'.1) k
        (Vblk R (A'.H.localHistory M K k c'.1) k)
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A' hkK c).A)
          (pairwise_disjoint_postOp rep hkK A')).symm (restrictOn hU' z) c')
        (outOf R (A'.H.localHistory M K k c'.1) k ψk) ∧
    subFluctField N (A.H.localHistory M K k c.1) k
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
          (pairwise_disjoint_postOp rep hkK A)).symm (restrictOn hU z) c) =
      subFluctField N (A'.H.localHistory M K k c'.1) k
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A' hkK c).A)
          (pairwise_disjoint_postOp rep hkK A')).symm (restrictOn hU' z) c') := by
  have hlh : A.H.localHistory M K k c.1 = A'.H.localHistory M K k c'.1 :=
    (congrArg (fun r : CRec S n M K k => r.2.1) hrec).symm
  have hr : (recOfComp rep hA c).1 = compRec M A' c'.1 := hrec.symm
  have hI : gImage (postOp geo cs rep.SD rep.KD A hkK c).A =
      gImage (postOp geo cs rep.SD rep.KD A' hkK c').A :=
    (gImage_postOp_eq rep hkK c (recOfComp rep hA c) rfl).trans
      (gImage_postOp_eq rep hkK c' _ hr).symm
  rw [famEquiv_symm_apply, famEquiv_symm_apply, restrictOn_restrictOn, restrictOn_restrictOn]
  exact ⟨subMultiscaleField_transport hlh hI _ _ z ψk, subFluctField_transport hlh hI _ _ z⟩

/-- **The global fields of two histories of the large-field half agree on the fine set of `X`** when
the records of their components meeting `X` correspond, at the configurations read off one
configuration `z` of the global variables: on every block of scale `j ≤ K` in the fine set of `X`,
the global multiscale fields (the multiscale fields of the components below the scale `k`, `ψ_k` on
`Ω_k` at the scale `k`) and the global fluctuation fields are equal (the hypothesis of `D7`
`loc_field`). -/
theorem fields_eq_on_of_corr {A A' : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k)
    (hA' : A' ∈ lfHist rep.hist k) {X : Finset (Torus S.d (n k))}
    (hAB : ∀ c : A.H.Comp k, (c.1 ∩ X).Nonempty →
      ∃ c' : A'.H.Comp k, compRec M A' c' = compRec M A c)
    (hBA : ∀ c' : A'.H.Comp k, (c'.1 ∩ X).Nonempty →
      ∃ c : A.H.Comp k, compRec M A c = compRec M A' c')
    {W : Set (GVar S n M K k)}
    (hU : (⋃ c : PostComp A k, gImage (postOp geo cs rep.SD rep.KD A hkK c).A) ⊆ W)
    (hU' : (⋃ c : PostComp A' k, gImage (postOp geo cs rep.SD rep.KD A' hkK c).A) ⊆ W)
    (z : GCfgOn N W) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) {j : ℕ} (hjK : j ≤ K)
    (y : BlockAt S n M K j)
    (hy : BlockSub (S := S) (n := n) (M := M) (K := K) j y
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))))) :
    gMulti (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A hkK)
        (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
        (fineSet (S := S) (n := n) M K k (OmegaCube A.H k)) ψk
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
          (pairwise_disjoint_postOp rep hkK A)).symm (restrictOn hU z)) j y =
      gMulti (fun c : PostComp A' k => A'.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A' hkK)
        (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
        (fineSet (S := S) (n := n) M K k (OmegaCube A'.H k)) ψk
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A' hkK c).A)
          (pairwise_disjoint_postOp rep hkK A')).symm (restrictOn hU' z)) j y ∧
    gFluct (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A hkK)
        (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
          (pairwise_disjoint_postOp rep hkK A)).symm (restrictOn hU z)) j y =
      gFluct (fun c : PostComp A' k => A'.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A' hkK)
        (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A' hkK c).A)
          (pairwise_disjoint_postOp rep hkK A')).symm (restrictOn hU' z)) j y := by
  have hremA := (mem_lfHist.1 hA).2.2
  have hremA' := (mem_lfHist.1 hA').2.2
  have hcar := postComp_eq_of_mem_fineSet (M := M) (k := k) A
  have hcar' := postComp_eq_of_mem_fineSet (M := M) (k := k) A'
  -- the two cases of a block: of a component of both histories, or of a component of neither
  have hcases : (∃ (c : PostComp A k) (c' : PostComp A' k), compRec M A' c'.1 = compRec M A c.1 ∧
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) ∧
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (c'.1.1 : Set (Torus S.d (n k))))) ∨
      ((¬ ∃ c : PostComp A k, BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))) ∧
        ¬ ∃ c' : PostComp A' k, BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (c'.1.1 : Set (Torus S.d (n k))))) := by
    by_cases hex : ∃ c : PostComp A k, BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
    · obtain ⟨c, hc⟩ := hex
      obtain ⟨c', hrec, hc'⟩ := exists_corr_of_blockSub hremA' hAB hjK hy c hc
      exact Or.inl ⟨c, c', hrec, hc, hc'⟩
    · refine Or.inr ⟨hex, fun ⟨c', hc'⟩ => hex ?_⟩
      obtain ⟨c, -, hc⟩ := exists_corr_of_blockSub hremA hBA hjK hy c' hc'
      exact ⟨c, hc⟩
  have hfl : gFluct (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A hkK)
        (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
          (pairwise_disjoint_postOp rep hkK A)).symm (restrictOn hU z)) j y =
      gFluct (fun c : PostComp A' k => A'.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A' hkK)
        (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k))))
        ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A' hkK c).A)
          (pairwise_disjoint_postOp rep hkK A')).symm (restrictOn hU' z)) j y := by
    rcases hcases with ⟨c, c', hrec, hc, hc'⟩ | ⟨hn, hn'⟩
    · rw [gFluct_eq_of_blockSub hcar _ hjK c hc, gFluct_eq_of_blockSub hcar' _ hjK c' hc']
      exact congrFun (congrFun (subFields_eq_of_compRec rep hkK hA c c' hrec hU hU' z
        (fun _ => 0)).2 j) y
    · rw [gFluct_eq_zero_of_not _ hn, gFluct_eq_zero_of_not _ hn']
  refine ⟨?_, hfl⟩
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · rcases hcases with ⟨c, c', hrec, hc, hc'⟩ | ⟨hn, hn'⟩
    · rw [gMulti_eq_of_blockSub hcar _ _ _ hjk hjK c hc,
        gMulti_eq_of_blockSub hcar' _ _ _ hjk hjK c' hc']
      exact congrFun (congrFun (subFields_eq_of_compRec rep hkK hA c c' hrec hU hU' z ψk).1 j) y
    · rw [gMulti_eq_zero_of_not _ _ _ hjk hn, gMulti_eq_zero_of_not _ _ _ hjk hn']
  · have hAB₀ : ∀ c : A.H.Comp j, (c.1 ∩ X).Nonempty → ∃ c' : A'.H.Comp j, c'.1 = c.1 ∧
        A'.H.localHistory M K j c' = A.H.localHistory M K j c := fun c hc => by
      obtain ⟨c', h⟩ := hAB c hc
      exact ⟨c', congrArg Prod.fst h, congrArg (fun r : CRec S n M K j => r.2.1) h⟩
    have hBA₀ : ∀ c' : A'.H.Comp j, (c'.1 ∩ X).Nonempty → ∃ c : A.H.Comp j, c.1 = c'.1 ∧
        A.H.localHistory M K j c = A'.H.localHistory M K j c' := fun c' hc' => by
      obtain ⟨c, h⟩ := hBA c' hc'
      exact ⟨c, congrArg Prod.fst h, congrArg (fun r : CRec S n M K j => r.2.1) h⟩
    have hΩ := ((regionData_eq_on_of_corr hkK hremA hremA' hAB₀ hBA₀).1 j le_rfl).1
    have hiff : BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K j (OmegaCube A.H j)) ↔
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K j (OmegaCube A'.H j)) := by
      constructor
      · intro h x hx
        have hx' : x ∈ fineSet (S := S) (n := n) M K j (OmegaCube A.H j) ∩
            fineSet (S := S) (n := n) M K j (X : Set (Torus S.d (n j))) := ⟨h x hx, hy x hx⟩
        rw [hΩ] at hx'
        exact hx'.1
      · intro h x hx
        have hx' : x ∈ fineSet (S := S) (n := n) M K j (OmegaCube A'.H j) ∩
            fineSet (S := S) (n := n) M K j (X : Set (Torus S.d (n j))) := ⟨h x hx, hy x hx⟩
        rw [← hΩ] at hx'
        exact hx'.1
    rw [gMulti_top, gMulti_top]
    by_cases h : BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (fineSet (S := S) (n := n) M K j (OmegaCube A.H j))
    · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
    · rw [ite_eq_right h, ite_eq_right (mt hiff.2 h)]
  · rw [gMulti_eq_zero_of_gt _ _ _ hkj, gMulti_eq_zero_of_gt _ _ _ hkj]

end Corr

end Balaban.RootFSpine
