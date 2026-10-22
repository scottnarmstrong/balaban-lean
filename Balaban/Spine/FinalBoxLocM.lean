/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocE

/-!
# The top-level source terms `⟨g, ℳ^{(k)}(x, X)⟩` as polymer terms of the block field (A6-3, (L3))

The part `j = k` of the source term `ℱ_k` of the class, `∑_x ⟨g(x), ℳ^{(k)}(x; ψ^{(k)}_k, h, g)⟩`,
reads the block field on the blocks of the polymers `X ∋ x` (`ψ^{(k)}_k = lift ψ_k`,
`psiJC_univ_top`).  The amplitude of the label `(x, X)` is `|g(x)|₁ · c₉ L^{-k((d-2)/2 + γ - α₁)}`
(the bound `boundM` of the class), so the labels of a polymer carry at most `c₉ L^{…} ‖g‖₁`
(`λ = 0`).

* `MIdx C`, `mTerm`, `sum_mTerm` (the part `j = k` of `ℱ_k` on the whole torus);
* `mPolyTerms`, `mPolyTerms_count`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.Localization Balaban.Green Balaban.SmallField Balaban.Background Finset

section TopM

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- **The labels of the top-level source terms**: `x ∈ X`, `X ∈ 𝒟_k`. -/
abbrev MIdx : Type :=
  {p : Localization.CTorus S.d S.L C.N₁ m₁ k ×
      {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) // Def6.IsPolyDom C.m₀ k X} //
    p.1 ∈ p.2.1}

open Classical in
noncomputable instance : Fintype (MIdx C) := inferInstance

/-- **The top-level source term `⟨g(x), ℳ^{(k)}(x, X; lift ψ, h, g)⟩`.** -/
noncomputable def mTerm (g : GIdx S n M K N → ℂ) (t : MIdx C)
    (ψ : BlockAt S n M K k × Fin N → ℂ) : ℂ :=
  ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g t.1.1 i *
    (C.sf.Tm C.N₁).M k t.1.1 t.1.2.1 (C.sfLiftKC (fun b i => ψ (b, i))) (Def6.constFld (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g) i

open Classical in
/-- **The sum of the top-level source terms is the part `j = k` of `ℱ_k`** on the whole torus (at a
real block field). -/
theorem sum_mTerm (hk : 1 ≤ k) (ha : C.weights k ≠ 0)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (ψ : BlockAt S n M K k × Fin N → ℂ) (hψ : ∀ b i, ψ (b, i) = ((ψk b i : ℝ) : ℂ)) :
    ∑ t : MIdx C, mTerm C hv g t ψ =
      ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Set.univ then
          ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * C.MresJ Set.univ ψk hv g k x i
        else 0) := by
  have hpsi : C.psiJ Set.univ ψk hv k = C.sfLiftKC (fun b i => ψ (b, i)) := by
    rw [SFCtx.psiJ_eq, psiJC_univ_top C hv hk ha]
    congr 1
    funext b i
    rw [hψ]
    rfl
  unfold mTerm
  rw [sum_pairSubtype (fun X => Def6.IsPolyDom C.m₀ k X) (fun x X => x ∈ X)
    (fun x X => ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i *
      (C.sf.Tm C.N₁).M k x X (C.sfLiftKC (fun b i => ψ (b, i))) (Def6.constFld (hC hv))
        (sfG C.geo C.hnn C.hkK C.hT g) i)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sset_univ]
  simp only [Set.mem_univ, ↓reduceIte]
  unfold SFCtx.MresJ
  rw [thickY_univ, sset_univ, hpsi]
  have hset : {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | Def6.IsPolyDom C.m₀ k X ∧ x ∈ X ∧
      X ⊆ Set.univ} = {X | Def6.IsPolyDom C.m₀ k X ∧ x ∈ X} := by
    ext X; simp
  rw [hset, finsum_mem_def, finsum_eq_sum_of_fintype]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← Finset.sum_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum]

variable {C hv} {P6 : Def6.Consts} {k0 : ℕ} {δ r : ℝ}

/-- The amplitude of the top-level source terms: `c₉ L^{-k((d-2)/2 + γ - α₁)}`. -/
noncomputable def mAmp (P6 : Def6.Consts) (d L k : ℕ) : ℝ :=
  max 0 (P6.c₉ * ((L : ℝ) ^ k)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁))

/-- **The top-level source terms as a family of polymer terms of the block field.** -/
noncomputable def mPolyTerms
    (hE : Def6v2.SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    (hm₀ : P6.m₀ = C.m₀) (hk : 1 ≤ k)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k)) (Def6v2.physMass S.L k (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r) :
    PolyTerms C hv r P6.κ (MIdx C) where
  X := fun t => t.1.2.1
  isPoly := fun t => t.1.2.2
  τ := mTerm C hv
  amp := fun g t => (∑ i, ‖sfG C.geo C.hnn C.hkK C.hT g t.1.1 i‖) * mAmp P6 S.d S.L k
  amp_nonneg := fun _ _ => mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (le_max_left _ _)
  reads := fun g t ψ ψ' hψ => by
    have h := hE.localM k t.1.1 t.1.2.1 (C.sfLiftKC fun b i => ψ (b, i))
      (C.sfLiftKC fun b i => ψ' (b, i))
      (Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (hC hv))
      (Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g) (sfG C.geo C.hnn C.hkK C.hT g) fun z hz => ⟨by
        funext i'
        rw [sfLiftKC_apply, sfLiftKC_apply]
        exact hψ (sfBlockOf C z, i') ((mem_blocksOf C).2 ⟨z, hz, rfl⟩), rfl, rfl⟩
    unfold mTerm
    rw [h]
  congr_g := fun t g g' hgg ψ => by
    have hsf : ∀ z ∈ t.1.2.1, sfG C.geo C.hnn C.hkK C.hT g z = sfG C.geo C.hnn C.hkK C.hT g' z := by
      intro z hz
      funext i
      exact hgg _ ((mem_blocksOf C).2 ⟨z, hz, rfl⟩) i
    have h := hE.localM k t.1.1 t.1.2.1 (C.sfLiftKC fun b i => ψ (b, i))
      (C.sfLiftKC fun b i => ψ (b, i))
      (Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (hC hv))
      (Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT g) (sfG C.geo C.hnn C.hkK C.hT g') fun z hz =>
        ⟨rfl, rfl, hsf z hz⟩
    unfold mTerm
    rw [h, hsf t.1.1 t.2]
  analytic := fun t p hp => by
    have hX : Def6.IsPolyDom P6.m₀ k t.1.2.1 := by rw [hm₀]; exact t.1.2.2
    have hdom := eTerm_dom hE hm₀ hk H hunit hD t.1.2.2 hp.2
    have hA := hE.analyticM k hk le_rfl t.1.1 t.1.2.1 hX t.2
      (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁)
        (m₁ := m₁) (k := k) (hC hv), sfG C.geo C.hnn C.hkK C.hT p.1)
      ⟨hdom, (l1_sfG_le C p.1).trans_lt hp.1⟩
    have hM : AnalyticAt ℂ (fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
        (C.sf.Tm C.N₁).M k t.1.1 t.1.2.1 (C.sfLiftKC (fun b i => p.2 (b, i)))
          (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT p.1)) p :=
      AnalyticAt.comp (g := fun q : Def6.Fld S.d S.L C.N₁ m₁ k N × Def6.Fld S.d S.L C.N₁ m₁ k N ×
          Def6.Fld S.d S.L C.N₁ m₁ k N => (C.sf.Tm C.N₁).M k t.1.1 t.1.2.1 q.1 q.2.1 q.2.2)
        (f := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
          (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁)
            (m₁ := m₁) (k := k) (hC hv), sfG C.geo C.hnn C.hkK C.hT p.1))
        hA (analyticAt_rData C hv p)
    unfold mTerm
    refine Finset.analyticAt_fun_sum _ fun i _ => AnalyticAt.mul ?_ ?_
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : GIdx S n M K N => ℂ)
        (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT t.1.1), i)).comp
          (ContinuousLinearMap.fst ℂ (GIdx S n M K N → ℂ)
            (BlockAt S n M K k × Fin N → ℂ))).analyticAt p
    · exact (analyticAt_pi_iff.1 hM) i
  bound := fun t p hp => by
    have hX : Def6.IsPolyDom P6.m₀ k t.1.2.1 := by rw [hm₀]; exact t.1.2.2
    have hdom := eTerm_dom hE hm₀ hk H hunit hD t.1.2.2 hp.2
    have hB := hE.boundM k hk le_rfl t.1.1 t.1.2.1 hX t.2 (C.sfLiftKC (fun b i => p.2 (b, i)))
      (Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (hC hv))
      (sfG C.geo C.hnn C.hkK C.hT p.1) hdom ((l1_sfG_le C p.1).trans_lt hp.1)
    rw [hm₀] at hB
    set Mv := (C.sf.Tm C.N₁).M k t.1.1 t.1.2.1 (C.sfLiftKC (fun b i => p.2 (b, i)))
      (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT p.1) with hMv
    have hMle : vn Mv ≤ mAmp P6 S.d S.L k * Real.exp (-P6.κ * Def6.sizeJ C.m₀ k t.1.2.1) :=
      hB.le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    unfold mTerm
    calc ‖∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT p.1 t.1.1 i * Mv i‖
        ≤ ∑ i : Fin N, ‖sfG C.geo C.hnn C.hkK C.hT p.1 t.1.1 i‖ * vn Mv := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_le_vn Mv i) (norm_nonneg _)
      _ = (∑ i : Fin N, ‖sfG C.geo C.hnn C.hkK C.hT p.1 t.1.1 i‖) * vn Mv := by
          rw [Finset.sum_mul]
      _ ≤ (∑ i : Fin N, ‖sfG C.geo C.hnn C.hkK C.hT p.1 t.1.1 i‖) *
            (mAmp P6 S.d S.L k * Real.exp (-P6.κ * Def6.sizeJ C.m₀ k t.1.2.1)) :=
          mul_le_mul_of_nonneg_left hMle (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = _ := by ring

open Classical in
/-- **The label count of the top-level source terms**: for `‖g‖₁ < 1` the labels of a polymer carry
at most `c₉ L^{-k(…)}` (`λ = 0`). -/
theorem mPolyTerms_count
    (hE : Def6v2.SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    (hm₀ : P6.m₀ = C.m₀) (hk : 1 ≤ k)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k)) (Def6v2.physMass S.L k (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r)
    {g : GIdx S n M K N → ℂ} (hg : ∑ q, ‖g q‖ < 1)
    (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    ∑ t ∈ Finset.univ.filter (fun t => (mPolyTerms hE hm₀ hk H hunit hD).X t = X),
        (mPolyTerms hE hm₀ hk H hunit hD).amp g t ≤
      mAmp P6 S.d S.L k * Real.exp (0 * Def6.sizeJ C.m₀ k X) := by
  rw [zero_mul, Real.exp_zero, mul_one]
  simp only [mPolyTerms]
  rw [← Finset.sum_mul, mul_comm]
  refine mul_le_of_le_one_right (le_max_left _ _) ?_
  set f : Localization.CTorus S.d S.L C.N₁ m₁ k → ℝ :=
    fun x => ∑ i, ‖sfG C.geo C.hnn C.hkK C.hT g x i‖ with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hinj : Set.InjOn (fun t : MIdx C => t.1.1)
      (Finset.univ.filter (fun t : MIdx C => t.1.2.1 = X) : Set (MIdx C)) := by
    intro t₁ ht₁ t₂ ht₂ h
    have e₁ : t₁.1.2.1 = X := (Finset.mem_filter.1 ht₁).2
    have e₂ : t₂.1.2.1 = X := (Finset.mem_filter.1 ht₂).2
    exact Subtype.ext (Prod.ext h (Subtype.ext (e₁.trans e₂.symm)))
  calc ∑ t ∈ Finset.univ.filter (fun t : MIdx C => t.1.2.1 = X), f t.1.1
      = ∑ x ∈ (Finset.univ.filter (fun t : MIdx C => t.1.2.1 = X)).image (fun t => t.1.1), f x :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun x _ _ => hf0 x
    _ = ∑ q, ‖g q‖ := sum_norm_sfG_eq C g
    _ ≤ 1 := hg.le

end TopM

end Balaban.RootFSpine
