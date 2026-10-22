/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFKerLocal
public import Balaban.Spine.FinalLFWeight
public import Balaban.LargeField.Operators.PiTools

/-!
# The product form of the operators of a history over its component records (A6-4)

The operator `𝕋_k(Z_k(𝔸), 𝔸)` of a history (`gOp`) integrates the internal variables of its
components against the product of their reference measures, with the product of their kernels. The
internal variables of a localized history are a subset of one global index set (`GVar`: a scale
`j < k`, a kind and a `j`-block), with a reference measure depending only on the index. This file
moves `gOp` to the configurations of the union of the variable sets of the components (`famEquiv`,
measure preserving when the variable sets are disjoint), and, for the histories of the large-field
half, writes the kernel of each component as the canonical weight of its record (`recW`, the weight
of the source of the record, `Spine/FinalLFWeight.lean`), by the kernel locality
(`locOp_corr_of_compRec_eq`):

* `GVar`, `gIsSpin`, `GCfgOn`, `gcfgMeasure`: the global variables, configurations on a set of them,
  and the product of the reference measures;
* `gImage`, `subCfgEquiv`, `measurePreserving_subCfgEquiv`: the configurations of a variable set of a
  localized history are the configurations of its global image;
* `restrictOn`, `famEquiv`, `measurePreserving_famEquiv`, `famEquiv_symm_apply`: for disjoint images,
  the configurations of a family are the configurations of the union;
* **`gOp_eq_integral_gcfg`**: `gOp` as an integral over the configurations of the union;
* `varSet_localHistory_subset`, `gImage_disjoint`: the variables of distinct components are distinct;
* `symVar_refl_val`, `relVal_refl_subCfgEquiv`, `relOut_refl_outOf`, `relG_refl`: the identity
  correspondence of configurations read off one global configuration;
* `recPkg`, `recVars`, `recW`: the operator, the variables and the weight of a realized record (those of
  its source); `gImage_postOp_eq`, `postOp_w_eq_recW`: the variables and the kernel of a component
  are those of its record;
* `compRec_mem_lfAllRecs`, `recOfComp`, `recOfComp_injective`, `pairwise_disjoint_postOp`,
  `recVars_recOfComp_subset`;
* **`gOp_postOp_eq_prod_recW`**: the operator of a history of the large-field half is the integral,
  over the configurations of the variables of its components, of the product of the weights of its
  records.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

section Global

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ}

/-- **The global index of the internal variables of scale `< k`**: a scale `j < k`, a kind and a
`j`-block. The index set `InternalVars a k` of a localized history is a subtype of it. -/
abbrev GVar (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) : Type :=
  (j : Fin k) × VarKind × BlockAt S n M K j

/-- Is the global variable a spin (a large-field variable of scale `0`)? -/
def gIsSpin (q : GVar S n M K k) : Bool := decide (q.1.val = 0 ∧ q.2.1 = VarKind.large)

/-- Configurations of a set of global variables. -/
abbrev GCfgOn (N : ℕ) (U : Set (GVar S n M K k)) : Type := (q : ↥U) → VarVal N (gIsSpin q.1)

noncomputable instance (U : Set (GVar S n M K k)) : Fintype ↥U := by
  haveI : Finite (GVar S n M K k) := by unfold GVar; infer_instance
  exact Fintype.ofFinite _

/-- The product of the reference measures on the configurations of a set of global variables. -/
noncomputable def gcfgMeasure (N : ℕ) (U : Set (GVar S n M K k)) : Measure (GCfgOn N U) :=
  Measure.pi fun q => varMeasure N (gIsSpin q.1)

instance (U : Set (GVar S n M K k)) : SigmaFinite (gcfgMeasure N U) := by
  unfold gcfgMeasure; infer_instance

/-- The global image of a set of internal variables of a localized history. -/
def gImage {a : LocalHistory S n M K} (A : Set (InternalVars a k)) : Set (GVar S n M K k) :=
  Subtype.val '' A

/-- **The configurations of a variable set are the configurations of its global image.** -/
noncomputable def subCfgEquiv {a : LocalHistory S n M K} (A : Set (InternalVars a k)) :
    SubCfg N a k A ≃ᵐ GCfgOn N (gImage A) :=
  MeasurableEquiv.piCongrLeft (fun q : ↥(gImage A) => VarVal N (gIsSpin q.1))
    (Equiv.Set.image Subtype.val A Subtype.val_injective)

theorem measurePreserving_subCfgEquiv {a : LocalHistory S n M K} (A : Set (InternalVars a k)) :
    MeasurePreserving (subCfgEquiv (N := N) A) (subMeasure N a k A) (gcfgMeasure N (gImage A)) := by
  have h := measurePreserving_piCongrLeft (ι' := ↥A)
    (fun q : ↥(gImage A) => varMeasure N (gIsSpin q.1))
    (Equiv.Set.image Subtype.val A Subtype.val_injective)
  exact h

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem subCfgEquiv_symm_apply {a : LocalHistory S n M K} (A : Set (InternalVars a k))
    (z : GCfgOn N (gImage A)) (p : ↥A) :
    (subCfgEquiv A).symm z p = z ⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ := rfl

/-- The restriction of a configuration to a subset of the variables. -/
def restrictOn {U W : Set (GVar S n M K k)} (h : U ⊆ W) (z : GCfgOn N W) : GCfgOn N U :=
  fun q => z ⟨q.1, h q.2⟩

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem measurable_restrictOn {U W : Set (GVar S n M K k)} (h : U ⊆ W) :
    Measurable (restrictOn (N := N) h) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

variable {ι : Type*} [Fintype ι] {a : ι → LocalHistory S n M K}
  (A : ∀ i, Set (InternalVars (a i) k))
  (hdisj : Pairwise (Function.onFun Disjoint fun i => gImage (A i)))

/-- **The configurations of a family of variable sets with disjoint images are the configurations
of the union of the images.** -/
noncomputable def famEquiv :
    ((i : ι) → SubCfg N (a i) k (A i)) ≃ᵐ GCfgOn N (⋃ i, gImage (A i)) :=
  (MeasurableEquiv.piCongrRight fun i => subCfgEquiv (N := N) (A i)).trans
    ((MeasurableEquiv.piCurry fun i (q : ↥(gImage (A i))) => VarVal N (gIsSpin q.1)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun q : ↥(⋃ i, gImage (A i)) => VarVal N (gIsSpin q.1))
        (Set.unionEqSigmaOfDisjoint hdisj).symm))

theorem measurePreserving_famEquiv :
    MeasurePreserving (famEquiv (N := N) A hdisj)
      (Measure.pi fun i => subMeasure N (a i) k (A i)) (gcfgMeasure N (⋃ i, gImage (A i))) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun i => subCfgEquiv (N := N) (A i))
      (Measure.pi fun i => subMeasure N (a i) k (A i))
      (Measure.pi fun i => gcfgMeasure N (gImage (A i))) :=
    measurePreserving_pi _ _ fun i => measurePreserving_subCfgEquiv (A i)
  have h2 := (PiTools.measurePreserving_piCurry
    (fun i (q : ↥(gImage (A i))) => VarVal N (gIsSpin q.1))
    (fun i q => varMeasure N (gIsSpin q.1))).symm
  have h3 := measurePreserving_piCongrLeft
    (fun q : ↥(⋃ i, gImage (A i)) => varMeasure N (gIsSpin q.1))
    (Set.unionEqSigmaOfDisjoint hdisj).symm
  exact (h3.comp h2).comp h1

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] [Fintype ι] in
theorem famEquiv_symm_apply (z : GCfgOn N (⋃ i, gImage (A i))) (i : ι) :
    (famEquiv A hdisj).symm z i =
      (subCfgEquiv (A i)).symm (restrictOn (Set.subset_iUnion (fun i => gImage (A i)) i) z) := by
  rfl

end Global

section Op

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N : ℕ} {R : ℕ → ℝ} {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (k : ℕ)
  (P : ∀ i, OpPkg N R (a i) k)
  (hdisj : Pairwise (Function.onFun Disjoint fun i => gImage (P i).A))

/-- **The operator of a family as an integral over the configurations of the union of the variable
sets** (for disjoint variable sets): the reference measure of the family is carried to the product of
the reference measures of the union (`measurePreserving_famEquiv`). -/
theorem gOp_eq_integral_gcfg (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (F : GCfg a k P → ℂ) :
    gOp a k P ψk hv g F =
      ∫ z, gWeight a k P ψk hv g ((famEquiv (fun i => (P i).A) hdisj).symm z) *
          F ((famEquiv (fun i => (P i).A) hdisj).symm z)
        ∂(gcfgMeasure N (⋃ i, gImage (P i).A)) := by
  unfold gOp gMeasure
  have hmp := measurePreserving_famEquiv (N := N) (fun i => (P i).A) hdisj
  rw [← hmp.integral_comp' (g := fun z => gWeight a k P ψk hv g
    ((famEquiv (fun i => (P i).A) hdisj).symm z) *
      F ((famEquiv (fun i => (P i).A) hdisj).symm z))]
  simp only [MeasurableEquiv.symm_apply_apply]

end Op

section Refl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ} {R : ℕ → ℝ} {a a' : LocalHistory S n M K}

/-- The identity symmetry does not move the global index of a variable. -/
theorem symVar_refl_val (hI : HistImage (LatTorusSym.refl S n M K).toTorusSym a a') (hk : k ≤ K)
    (p : InternalVars a k) : (symVar hI hk p).1 = p.1 := rfl

/-- Configurations of two variable sets read off one configuration of the global variables
correspond under the identity symmetry. -/
theorem relVal_refl_subCfgEquiv (hI : HistImage (LatTorusSym.refl S n M K).toTorusSym a a')
    (hk : k ≤ K) {A : Set (InternalVars a k)} {A' : Set (InternalVars a' k)}
    {W : Set (GVar S n M K k)} (h₁ : gImage A ⊆ W) (h₂ : gImage A' ⊆ W) (z : GCfgOn N W) :
    RelVal hI hk ((subCfgEquiv A).symm (restrictOn h₁ z)) ((subCfgEquiv A').symm (restrictOn h₂ z)) :=
  fun _ _ _ => rfl

/-- The outputs read off one field `ψ_k` by two equal localized histories correspond under the
identity symmetry. -/
theorem relOut_refl_outOf (h : a = a') (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    RelOut (LatTorusSym.refl S n M K).toTorusSym (outOf R a k ψk) (outOf R a' k ψk) := by
  subst h
  intro y
  rfl

/-- The sources correspond under the identity symmetry. -/
theorem relG_refl (g : GIdx S n M K N → ℂ) : RelG (LatTorusSym.refl S n M K).toTorusSym g g :=
  fun _ _ => rfl

end Refl

section Records

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

omit [NeZero M] [NeZero S.L] in
/-- The variable sets of the localized history of a component lie in the fine set of the
component. -/
theorem varSet_localHistory_subset (H : RegionHistory S n R k0 K) {k : ℕ} (c : H.Comp k) (j : ℕ)
    (κ : VarKind) : varSet (H.localHistory M K k c) j κ ⊆
      fineSet (S := S) (n := n) M K k (c.1 : Set (Torus S.d (n k))) := by
  cases κ
  · exact fun x hx => hx.1.2
  · exact fun x hx => hx.1.2

/-- **The variables of distinct components are distinct** (Lemma II.5.9 (b)): their blocks lie in the
fine sets of the components, which are disjoint. -/
theorem gImage_disjoint (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k ≤ K) {c c' : H.Comp k}
    (hne : c ≠ c') (A : Set (InternalVars (H.localHistory M K k c) k))
    (A' : Set (InternalVars (H.localHistory M K k c') k)) : Disjoint (gImage A) (gImage A') := by
  rw [Set.disjoint_left]
  rintro q ⟨⟨q₀, hq₀⟩, -, rfl⟩ ⟨⟨q₁, hq₁⟩, -, h⟩
  change q₁ = q₀ at h
  subst h
  obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) (K := K) (j := q₁.1)
    (by have := q₁.1.2; omega) q₁.2.2
  have h1 : cubeMap n S.L M K k x ∈ c.1 := varSet_localHistory_subset H c _ _ (hq₀ x hx)
  have h2 : cubeMap n S.L M K k x ∈ c'.1 := varSet_localHistory_subset H c' _ _ (hq₁ x hx)
  exact hne (Subtype.ext (comp_eq_of_mem c.2 c'.2 h1 h2))

variable {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

/-- **The operator of a realized record**: the operator of its source (`lfSrc`). -/
noncomputable def recPkg (r : ↥(lfAllRecs (M := M) rep.hist k)) :
    OpPkg N R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k :=
  locOp geo cs rep.SD rep.KD (lfSrc r).1.adm (fun i c => (lfSrc r).1.lab i c.1) k hkK (lfSrc r).2

/-- The global variables of a realized record. -/
def recVars (r : ↥(lfAllRecs (M := M) rep.hist k)) : Set (GVar S n M K k) :=
  gImage (recPkg rep hkK r).A

/-- **The weight of a realized record**: the kernel `K e^b` of its operator, as a function of the
field `ψ_k` and of the configuration of its global variables. -/
noncomputable def recW (r : ↥(lfAllRecs (M := M) rep.hist k))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (z : GCfgOn N (recVars rep hkK r)) : ℂ :=
  (recPkg rep hkK r).T.w (outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ψk)
    ((subCfgEquiv (recPkg rep hkK r).A).symm z) hv g

/-- **The variables of a component are those of its record** (kernel locality). -/
theorem gImage_postOp_eq {A : LabHist S n R k0 K} (c : PostComp A k)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hr : r.1 = compRec M A c.1) :
    gImage (postOp geo cs rep.SD rep.KD A hkK c).A = recVars rep hkK r := by
  obtain ⟨hI, hcorr, -⟩ := locOp_corr_of_compRec_eq M geo cs rep.SD rep.KD hkK c.1 (lfSrc r).2
    (hr.symm.trans (compRec_lfSrc r).symm)
  have hval : ∀ p : InternalVars (A.H.localHistory M K k c.1) k, (symVar hI hkK p).1 = p.1 :=
    fun p => symVar_refl_val hI hkK p
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨symVar hI hkK p, ?_, hval p⟩
    exact (hcorr p).1 hp
  · rintro ⟨p', hp', rfl⟩
    obtain ⟨p, rfl⟩ := symVar_surjective hI hkK p'
    refine ⟨p, ?_, (hval p).symm⟩
    exact (hcorr p).2 hp'

/-- **The kernel of a component is the weight of its record** (kernel locality,
`locOp_corr_of_compRec_eq`), on any configuration containing the variables of the component. -/
theorem postOp_w_eq_recW {A : LabHist S n R k0 K} (c : PostComp A k)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hr : r.1 = compRec M A c.1)
    {W : Set (GVar S n M K k)} (h₁ : gImage (postOp geo cs rep.SD rep.KD A hkK c).A ⊆ W)
    (z : GCfgOn N W) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (postOp geo cs rep.SD rep.KD A hkK c).T.w (outOf R (A.H.localHistory M K k c.1) k ψk)
        ((subCfgEquiv _).symm (restrictOn h₁ z)) hv g =
      recW rep hkK r ψk hv g (restrictOn (Set.Subset.trans (gImage_postOp_eq rep hkK c r hr).symm.subset h₁) z) := by
  have hcr : compRec M A c.1 = compRec M (lfSrc r).1 (lfSrc r).2 :=
    hr.symm.trans (compRec_lfSrc r).symm
  have hlh : A.H.localHistory M K k c.1 = (lfSrc r).1.H.localHistory M K k (lfSrc r).2 :=
    congrArg (fun r : CRec S n M K k => r.2.1) hcr
  obtain ⟨hI, -, hval⟩ := locOp_corr_of_compRec_eq M geo cs rep.SD rep.KD hkK c.1 (lfSrc r).2 hcr
  have hOut := relOut_refl_outOf (R := R) hlh ψk
  obtain ⟨hK, hb⟩ := hval _ _ ((subCfgEquiv _).symm (restrictOn h₁ z))
    ((subCfgEquiv _).symm (restrictOn (Set.Subset.trans (gImage_postOp_eq rep hkK c r hr).symm.subset h₁) z)) hv g g hOut
    (relVal_refl_subCfgEquiv hI hkK _ _ z) (relG_refl g)
  unfold recW recPkg LFKernel.w
  exact (congrArg₂ (fun (x : ℝ) (y : ℂ) => (x : ℂ) * Complex.exp y) hK hb).symm

/-- A record of a component of a history of the large-field half is realized. -/
theorem compRec_mem_lfAllRecs {A : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k)
    (c : A.H.Comp k) : compRec M A c ∈ lfAllRecs (M := M) rep.hist k := by
  classical
  unfold lfAllRecs
  exact Finset.mem_biUnion.2 ⟨lfRecs M k A, Finset.mem_image_of_mem _ hA, (mem_lfRecs M).2 ⟨c, rfl⟩⟩

/-- The record of a post component of a history of the large-field half, as a realized record. -/
noncomputable def recOfComp {A : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k) (c : PostComp A k) :
    ↥(lfAllRecs (M := M) rep.hist k) :=
  ⟨compRec M A c.1, compRec_mem_lfAllRecs rep hA c.1⟩

/-- Distinct components have distinct records. -/
theorem recOfComp_injective {A : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k) :
    Function.Injective (recOfComp rep hA) := by
  intro c c' h
  have h1 : c.1.1 = c'.1.1 := congrArg (fun r : ↥(lfAllRecs (M := M) rep.hist k) => r.1.1) h
  exact Subtype.ext (Subtype.ext h1)

/-- The variable sets of the post components of a history are pairwise disjoint. -/
theorem pairwise_disjoint_postOp (A : LabHist S n R k0 K) :
    Pairwise (Function.onFun Disjoint
      fun c : PostComp A k => gImage (postOp geo cs rep.SD rep.KD A hkK c).A) :=
  fun _ _ hne => gImage_disjoint A.H hkK (fun h => hne (Subtype.ext h)) _ _

/-- The variables of the record of a post component lie in the union of the variables of the
components. -/
theorem recVars_recOfComp_subset {A : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k)
    (c : PostComp A k) : recVars rep hkK (recOfComp rep hA c) ⊆
      ⋃ c' : PostComp A k, gImage (postOp geo cs rep.SD rep.KD A hkK c').A :=
  Set.Subset.trans (gImage_postOp_eq rep hkK c (recOfComp rep hA c) rfl).symm.subset
    (Set.subset_iUnion (fun c' : PostComp A k => gImage (postOp geo cs rep.SD rep.KD A hkK c').A) c)

/-- **The product form of the operator of a history of the large-field half over its records**: the
operator integrates the configurations of the union of the variables of its components against the
product of the reference measures, with the product over the components of the weights of their
records (`recW`, functions of the records only). -/
theorem gOp_postOp_eq_prod_recW {A : LabHist S n R k0 K} (hA : A ∈ lfHist rep.hist k)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (F : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A hkK) → ℂ) :
    gOp (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A hkK) ψk hv g F =
      ∫ z, (∏ c : PostComp A k, recW rep hkK (recOfComp rep hA c) ψk hv g
          (restrictOn (recVars_recOfComp_subset rep hkK hA c) z)) *
          F ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
            (pairwise_disjoint_postOp rep hkK A)).symm z)
        ∂(gcfgMeasure N (⋃ c : PostComp A k, gImage (postOp geo cs rep.SD rep.KD A hkK c).A)) := by
  rw [gOp_eq_integral_gcfg _ k _ (pairwise_disjoint_postOp rep hkK A)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine congrArg (· * _) ?_
  unfold gWeight
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [famEquiv_symm_apply]
  exact postOp_w_eq_recW rep hkK c (recOfComp rep hA c) rfl _ z ψk hv g

end Records

end Balaban.RootFSpine
