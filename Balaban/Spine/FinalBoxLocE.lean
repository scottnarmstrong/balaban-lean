/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocRForm
public import Balaban.Spine.FinalBoxLocCorr
public import Balaban.Spine.FinalSfConst
public import Balaban.LargeField.History.TopBlockTransport
public import Balaban.Fluctuation.CriticalPoint
public import Balaban.Fluctuation.StepRegDomain
public import Balaban.Green.FinalCountPolymers

/-!
# The top-level terms `ℰ^{(k)}(y, X)` as polymer terms of the block field (A6-3, (L3))

At the top level the composed field is the datum itself: `ψ^{(k)}_k = lift ψ_k` on the whole torus
(`psiJC_univ_top`, `composeField_self`), so the terms `ℰ^{(k)}(y, X; ψ^{(k)}_k, h)` of the class
read the block field on the blocks of `X` and need no localization of the background.

* `EIdx C`: the labels `(y, X)`, `y ∈ X` aligned to `L^k`, `X ∈ 𝒟_k`; `eTerm`; `sum_eTerm`: the sum
  is `ℰ^{(k)}` of the whole torus (`EresJ2_univ_eq_Edens`, finding (C));
* `ePolyTerms`: the family of polymer terms (amplitude `max 0 E₀`, decay `κ`) under the clauses
  `SFTermClauses` of the class on the birth domain, `BgHyp` at the physical mass and `RDomConsts`;
* `ePolyTerms_count`: the labels of `X` carry `max 0 E₀ · L^{(m₀+m₁)d} c₁ e^{d_k(X)}`
  (`card_aligned_polyDom_le`), so `λ = 1`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.Localization Balaban.Green Balaban.SmallField Balaban.Background Finset

section Pairs

open Classical in
/-- A sum over the labels `{(a, b) : P b ∧ Q a b}` as an iterated sum. -/
theorem sum_pairSubtype {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (P : β → Prop) (Q : α → β → Prop) [inst : Fintype {p : α × {b // P b} // Q p.1 p.2.1}]
    (f : α → β → M) :
    ∑ t : {p : α × {b // P b} // Q p.1 p.2.1}, f t.1.1 t.1.2.1 =
      ∑ a, ∑ b ∈ Finset.univ.filter (fun b => P b ∧ Q a b), f a b := by
  obtain rfl : inst = Subtype.fintype _ := Subsingleton.elim _ _
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : α × {b // P b} => Q p.1 p.2.1)
    (p := fun p : α × {b // P b} => Q p.1 p.2.1) (fun p => by simp)
    (fun p => f p.1 p.2.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_subtype (Finset.univ.filter P) (p := P) (fun b => by simp)
    (fun b => if Q a b then f a b else 0)]
  rw [← Finset.sum_filter, Finset.filter_filter]

end Pairs

section Top

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))

/-- The level-`k` set of the whole torus is of level `k`. -/
theorem isLevel_genW_univ (hk : 1 ≤ k) :
    Fluctuation.IsLevel (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c)
      (n := n k) (le_refl k) (W2 R (Set.univ : Set (Torus S.d (n k))))) k := by
  intro x
  have h1 := genSF_Ω_univ_of_le C (le_refl k) hk
  have hk' := genSF_Ω_univ_of_le C (le_refl k) (le_refl k)
  refine ⟨by rw [h1]; exact Finset.mem_univ _, ?_⟩
  refine GeneratingSet.layerIndex_eq _ hk le_rfl ?_
  rw [GeneratingSet.mem_layer, hk', GeneratingSet.top]
  exact ⟨Finset.mem_univ _, Finset.notMem_empty _⟩

/-- **At the top level the composed field is the lifted block field**:
`ψ^{(k)}_k = lift ψ_k` on the whole torus (`k ≥ 1`, `a_k ≠ 0`). -/
theorem psiJC_univ_top (hk : 1 ≤ k) (ha : C.weights k ≠ 0) (ψC : BlockAt S n M K k → Fin N → ℂ) :
    C.psiJC Set.univ ψC hv k = C.sfLiftKC ψC := by
  funext x i
  show (if hj : k ≤ k then sfPull C.geo C.hT (psiSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k)
      (L := S.L) (c := C.geo.c) (n := n k) C.weights (C.cs.muBg k) (bgC0 S.d S.L N) hj
      (W2 R Set.univ) (C.liftDataC ψC) (hC hv)) else 0) x i = _
  simp only [le_refl, ↓reduceDIte]
  unfold sfPull psiSF
  rw [Fluctuation.composeField_self (isLevel_genW_univ C hk) C.weights ha]
  have hds : sfToBg C.geo C.hT x ∈ dataSites (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k)
      (L := S.L) (c := C.geo.c) (n := n k) (le_refl k) (W2 R (Set.univ : Set (Torus S.d (n k))))) :=
    (mem_dataSites _).2 (Or.inl (by rw [genSF_Ω_univ_of_le C (le_refl k) hk]; exact Finset.mem_univ _))
  rw [liftSingle_Ψ _ _ _ hds, sfLiftKC_apply]
  unfold SFCtx.liftDataC sfBlockOf
  rw [jBlock_bgToFine_gen C.geo C.hnn C.hkK (le_refl k)]

/-- **The labels of the top-level terms `ℰ^{(k)}(y, X)`**: `y ∈ X` aligned to `L^k`, `X ∈ 𝒟_k`. -/
abbrev EIdx : Type :=
  {p : Localization.CTorus S.d S.L C.N₁ m₁ k ×
      {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) // Def6.IsPolyDom C.m₀ k X} //
    Aligned (S.L ^ k) p.1 ∧ p.1 ∈ p.2.1}

open Classical in
noncomputable instance : Fintype (EIdx C) := inferInstance

/-- **The top-level term `ℰ^{(k)}(y, X; lift ψ, h)`** as a function of the block field. -/
noncomputable def eTerm (_g : GIdx S n M K N → ℂ) (t : EIdx C)
    (ψ : BlockAt S n M K k × Fin N → ℂ) : ℂ :=
  (C.sf.Tm C.N₁).E k t.1.1 t.1.2.1 (C.sfLiftKC (fun b i => ψ (b, i))) (Def6.constFld (hC hv))

open Classical in
/-- **The sum of the top-level terms is `ℰ^{(k)}` of the whole torus** (at a real block field). -/
theorem sum_eTerm (vc : CorrCoef S.d) (hk : 1 ≤ k) (ha : C.weights k ≠ 0)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (ψ : BlockAt S n M K k × Fin N → ℂ) (hψ : ∀ b i, ψ (b, i) = ((ψk b i : ℝ) : ℂ)) :
    ∑ t : EIdx C, eTerm C hv g t ψ = EresJ2 C vc Set.univ ψk hv k := by
  rw [EresJ2_univ_eq_Edens C vc ψk hv (le_refl k)]
  have hpsi : C.psiJ Set.univ ψk hv k = C.sfLiftKC (fun b i => ψ (b, i)) := by
    rw [SFCtx.psiJ_eq, psiJC_univ_top C hv hk ha]
    congr 1
    funext b i
    rw [hψ]
    rfl
  rw [hpsi]
  unfold Def6.Edens Def6.Eloc eTerm
  rw [sum_pairSubtype (fun X => Def6.IsPolyDom C.m₀ k X)
    (fun y X => Aligned (S.L ^ k) y ∧ y ∈ X)
    (fun y X => (C.sf.Tm C.N₁).E k y X (C.sfLiftKC (fun b i => ψ (b, i)))
      (Def6.constFld (hC hv)))]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  by_cases hy : Aligned (S.L ^ k) y
  · simp only [hy, true_and, ↓reduceIte, Set.indicator_apply, Def6.polysAt, Set.mem_ofPred_eq]
    rw [← Finset.sum_filter]
  · simp [hy]

variable {C hv} {P6 : Def6.Consts} {k0 : ℕ} {δ r : ℝ}

/-- The data of the top-level terms lie in their analyticity domain (the birth domain of the class
at the level `k`), for block fields within `r` of `h`. -/
theorem eTerm_dom
    (hE : Def6v2.SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    (hm₀ : P6.m₀ = C.m₀) (hk : 1 ≤ k)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k)) (Def6v2.physMass S.L k (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX' : Def6.IsPolyDom C.m₀ k X)
    {ψ : BlockAt S n M K k × Fin N → ℂ} (hψ : ψ ∈ Metric.ball (hvField hv) r) :
    (sfDom P6 k0 C.sf C.N₁).dom k ((C.sf.Tm C.N₁).gs k X)
      (C.sfLiftKC (fun b i => ψ (b, i))) (Def6.constFld (hC hv)) := by
  have hX : Def6.IsPolyDom P6.m₀ k X := by rw [hm₀]; exact hX'
  have hΩ := (hE.gs_spec k hk le_rfl X hX).2
  have hu := sum_sq_eq_one_of_norm_eq_one hv hunit
  have hball : ∀ q, ‖ψ q - hvField hv q‖ < r := by
    intro q
    have := (dist_pi_lt_iff hD.hr0).1 (Metric.mem_ball.1 hψ) q
    rwa [dist_eq_norm] at this
  show Def6.XiDom _ _ _ k _ _ _
  refine Def6.xiDom_of_close_unit H hΩ le_rfl (u := fun i => hv i) hu hD.hδ0 hD.hδc0 hD.hδc1
    hD.hr0 hD.hr hD.hε _ (hC hv) (fun x i => ?_) (fun x x' hxx => ?_) (fun i => ?_)
  · rw [sfLiftKC_apply]
    exact (hball (sfBlockOf C x, i)).le
  · funext i
    rw [sfLiftKC_apply, sfLiftKC_apply, sfBlockOf_eq_of_jBlock C hxx]
  · have : hC hv i - ((hv i : ℝ) : ℂ) = 0 := sub_self _
    rw [this, norm_zero, mul_zero]
    exact hD.hr0.le

/-- **The top-level terms `ℰ^{(k)}(y, X)` as a family of polymer terms of the block field.** -/
noncomputable def ePolyTerms
    (hE : Def6v2.SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    (hm₀ : P6.m₀ = C.m₀) (hk : 1 ≤ k)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k)) (Def6v2.physMass S.L k (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r) :
    PolyTerms C hv r P6.κ (EIdx C) where
  X := fun t => t.1.2.1
  isPoly := fun t => t.1.2.2
  τ := eTerm C hv
  amp := fun _ _ => max 0 P6.E₀
  amp_nonneg := fun _ _ => le_max_left _ _
  reads := fun g t ψ ψ' hψ => by
    unfold eTerm
    refine hE.localE k t.1.1 t.1.2.1 _ _ _ _ fun z hz => ⟨?_, rfl⟩
    funext i
    rw [sfLiftKC_apply, sfLiftKC_apply]
    exact hψ (sfBlockOf C z, i) ((mem_blocksOf C).2 ⟨z, hz, rfl⟩)
  congr_g := fun _ _ _ _ _ => rfl
  analytic := fun t p hp => by
    have hX : Def6.IsPolyDom P6.m₀ k t.1.2.1 := by rw [hm₀]; exact t.1.2.2
    have hA := hE.analyticE k hk le_rfl t.1.1 t.1.2.1 hX t.2.2
      (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁)
        (m₁ := m₁) (k := k) (hC hv))
      (eTerm_dom hE hm₀ hk H hunit hD t.1.2.2 hp.2)
    refine AnalyticAt.comp (g := fun q : Def6.Fld S.d S.L C.N₁ m₁ k N ×
        Def6.Fld S.d S.L C.N₁ m₁ k N => (C.sf.Tm C.N₁).E k t.1.1 t.1.2.1 q.1 q.2)
      (f := fun p : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℂ) =>
        (C.sfLiftKC (fun b i => p.2 (b, i)), Def6.constFld (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁)
          (k := k) (hC hv))) hA ?_
    have h := analyticAt_rData C hv p
    exact (analyticAt_fst.comp h).prod (analyticAt_fst.comp (analyticAt_snd.comp h))
  bound := fun t p hp => by
    have hX : Def6.IsPolyDom P6.m₀ k t.1.2.1 := by rw [hm₀]; exact t.1.2.2
    have := hE.boundE k hk le_rfl t.1.1 t.1.2.1 hX t.2.2 _ _
      (eTerm_dom hE hm₀ hk H hunit hD t.1.2.2 hp.2)
    rw [hm₀] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

open Classical in
/-- **The label count of the top-level terms**: the labels of a polymer `X` carry at most
`max 0 E₀ · L^{(m₀+m₁)d} c₁ e^{d_k(X)}` (`card_aligned_polyDom_le`, `1 + s ≤ e^s`). -/
theorem ePolyTerms_count
    (hE : Def6v2.SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    (hm₀ : P6.m₀ = C.m₀) (hk : 1 ≤ k)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k)) (Def6v2.physMass S.L k (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r)
    (hN : S.L ^ C.m₀ ∣ C.N₁) (g : GIdx S n M K N → ℂ)
    (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    ∑ t ∈ Finset.univ.filter (fun t => (ePolyTerms hE hm₀ hk H hunit hD).X t = X),
        (ePolyTerms hE hm₀ hk H hunit hD).amp g t ≤
      (max 0 P6.E₀ * ((S.L : ℝ) ^ ((C.m₀ + m₁) * S.d) * Fluctuation.c1 S.d S.L)) *
        Real.exp (1 * Def6.sizeJ C.m₀ k X) := by
  classical
  set B := (S.L : ℝ) ^ ((C.m₀ + m₁) * S.d) * Fluctuation.c1 S.d S.L with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; unfold Fluctuation.c1; positivity
  have hs : 0 ≤ Def6.sizeJ C.m₀ k X := treeLenCovOne_nonneg (m₀ := C.m₀) _ _
  have hE0 : 0 ≤ max 0 P6.E₀ := le_max_left _ _
  simp only [ePolyTerms]
  rw [Finset.sum_const, nsmul_eq_mul, one_mul]
  have hcard : ((Finset.univ.filter fun t : EIdx C => t.1.2.1 = X).card : ℝ) ≤
      B * (1 + Def6.sizeJ C.m₀ k X) := by
    by_cases hX : Def6.IsPolyDom C.m₀ k X
    · have h1 : (Finset.univ.filter fun t : EIdx C => t.1.2.1 = X).card ≤
          (Finset.univ.filter fun y : Localization.CTorus S.d S.L C.N₁ m₁ k =>
            Aligned (S.L ^ k) y ∧ y ∈ X).card := by
        refine Finset.card_le_card_of_injOn (fun t => t.1.1) (fun t ht => ?_) ?_
        · have htX : t.1.2.1 = X := (Finset.mem_filter.1 ht).2
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, t.2.1, ?_⟩
          rw [← htX]; exact t.2.2
        · intro t₁ ht₁ t₂ ht₂ h
          have e₁ : t₁.1.2.1 = X := (Finset.mem_filter.1 ht₁).2
          have e₂ : t₂.1.2.1 = X := (Finset.mem_filter.1 ht₂).2
          exact Subtype.ext (Prod.ext h (Subtype.ext (e₁.trans e₂.symm)))
      refine (Nat.cast_le.2 h1).trans ?_
      exact Green.card_aligned_polyDom_le (le_refl k) hN hX
    · have h0 : (Finset.univ.filter fun t : EIdx C => t.1.2.1 = X) = ∅ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h
        exact hX (h ▸ t.1.2.2)
      rw [h0, Finset.card_empty, Nat.cast_zero]
      positivity
  have hexp : 1 + Def6.sizeJ C.m₀ k X ≤ Real.exp (Def6.sizeJ C.m₀ k X) := by
    have := Real.add_one_le_exp (Def6.sizeJ C.m₀ k X); linarith
  calc ((Finset.univ.filter fun t : EIdx C => t.1.2.1 = X).card : ℝ) * max 0 P6.E₀
      ≤ (B * (1 + Def6.sizeJ C.m₀ k X)) * max 0 P6.E₀ := mul_le_mul_of_nonneg_right hcard hE0
    _ ≤ (B * Real.exp (Def6.sizeJ C.m₀ k X)) * max 0 P6.E₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hB0) hE0
    _ = _ := by ring

end Top

end Balaban.RootFSpine
