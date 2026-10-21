/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KeptCoherence
public import Balaban.Spine.KappaLocal

/-!
# `KeptScaleData` from the kernels of the five outcomes at the scale `k`

The kept data of the output of `R` (`KeptScaleData`) are, below the scale `k`, those of the input
(`R` does not change the kept components below `k`), at the scale `k` the kept kernels of the five
outcomes `ϰ₁, …, ϰ₅` (LFR Lemma III.5.3), and zero above.  The costs are the constants
`C_dec = 5`, `γ_i = log 5 + A'₃ λ̂_i^{p_R}`.  So the only content of `KeptScaleData` besides the
constants is the structure `KeptScaleKernels` of the kernels at the scale `k`:

* the five kernels `(I'', K'', b'')_ϰ` of every localized history (`datum`), each an `LFKernel`;
* (S0) the support of `b''` in `g|_V` (`b_supp`);
* the `O(N)`-covariance (`rot_K`, `rot_b`) and the covariance under the lattice symmetries that
  preserve the localized history (`euclid_I`, `euclid_K`, `euclid_b`);
* the bound (1.26) with the exponent `κ^pre_k - C_R λ̂_k^{2d+1} + γ_k` (`pinnedExp`) and the
  vanishing off `χ^dom_k` for the localized histories of ripe kept components (`bound`).

`KeptScaleData.ofKernels` assembles `KeptScaleData` from them, for an input whose kept costs below
`k` are the constants (the class invariant); `keptDatumCoh_of_kernels` assembles the datum
coherence from that of the input and of the kernels at the scale `k`.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory MeasureTheory

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

section Zero

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The zero kernel. -/
noncomputable def zeroKernel (a : LocalHistory S n M K) (j : ℕ) :
    LFKernel (OutT N R a j) (SubCfg N a j (Set.univ : Set (InternalVars a j)))
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N) where
  K := fun _ _ _ => 0
  b := fun _ _ _ _ => 0
  K_nonneg := fun _ _ _ => le_rfl
  measurable_K := fun _ => measurable_const
  measurable_b := fun _ _ => measurable_const
  analytic_b := fun _ _ _ => analyticOnNhd_const
  real_b := fun _ _ _ _ _ _ => by simp

/-- The zero kept datum. -/
noncomputable def zeroDatum (a : LocalHistory S n M K) (j : ℕ) : KeptDatum (S := S) N R a j where
  Ikeep := Set.univ
  contains := fun _ _ => Set.mem_univ _
  ker := zeroKernel a j

theorem zeroKernel_kerBound (a : LocalHistory S n M K) (j : ℕ) (κ : ℝ) :
    KerBound a j (zeroKernel (N := N) (R := R) a j) κ := by
  intro hv g hg par
  simp [LFKernel.absW, zeroKernel]



end Zero

section Parts

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **The kept kernels of the five outcomes of `R` at the scale `k`** (LFR Lemma III.5.3): for every
localized history `a` and label `ϰ` the kept datum `(I'', K'', b'')` of the outcome `ϰ`, with the
support of `b''` in `g|_V` (S0), the `O(N)`-covariance and the covariance under the lattice
symmetries that preserve the localized history, and, for the localized histories of ripe kept
components of admissible region histories, the bound (1.26) at the pinned exponent
`κ^pre_k - C_R λ̂_k^{2d+1} + γ_k` with `γ_k = log 5 + A'₃ λ̂_k^{p_R}`, and the vanishing off the
domain `χ^dom_k`.  This is the only content of `KeptScaleData` besides the constants; the lower
scales are the kept data of the input and the higher scales are zero. -/
structure KeptScaleKernels (r₀ : Rep S n R k0 K M N geo cs P k) where
  datum : ∀ (a : LocalHistory S n M K), Fin 5 → KeptDatum (S := S) N R a k
  b_supp : ∀ a ϰ o x hv (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a k → g i = g' i) →
      (datum a ϰ).ker.b o x hv g = (datum a ϰ).ker.b o x hv g'
  rot_K : ∀ a ϰ (ρ : OrthN N) o x hv,
    (datum a ϰ).ker.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (datum a ϰ).ker.K o x hv
  rot_b : ∀ a ϰ (ρ : OrthN N) o x hv g,
    (datum a ϰ).ker.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = (datum a ϰ).ker.b o x hv g
  euclid_I : ∀ (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ.toTorusSym a a') (hk : k ≤ K) (ϰ : Fin 5) (p : InternalVars a k),
    p ∈ (datum a ϰ).Ikeep ↔ symVar hI hk p ∈ (datum a' ϰ).Ikeep
  euclid_K : ∀ (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ.toTorusSym a a') (hk : k ≤ K) (ϰ : Fin 5) o o' x x' hv,
    RelOut σ.toTorusSym o o' → RelSub hI hk x x' →
      (datum a' ϰ).ker.K o' x' hv = (datum a ϰ).ker.K o x hv
  euclid_b : ∀ (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ.toTorusSym a a') (hk : k ≤ K) (ϰ : Fin 5) o o' x x' hv g g',
    RelOut σ.toTorusSym o o' → RelSub hI hk x x' → RelG σ.toTorusSym g g' →
      (datum a' ϰ).ker.b o' x' hv g' = (datum a ϰ).ker.b o x hv g
  bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z : H.Comp k), 1 ≤ k → k ≤ k0 →
    S.Ripe k (H.bk k Z) → ∀ ϰ : Fin 5,
    (∀ o x hv, ¬ ChiDomAt geo cs H k Z o x →
      (datum (H.localHistory M K k Z) ϰ).ker.K o x hv = 0) ∧
    KerBound (H.localHistory M K k Z) k (datum (H.localHistory M K k Z) ϰ).ker
      (pinnedExp r₀ (canonHist S n R k0 K k (k + 1)) k (H.localHistory M K k Z) -
        S.CR * S.lam k ^ (2 * S.d + 1) + (Real.log 5 + S.A3' * S.lam k ^ S.pR))



open Classical in
/-- The kept data of the output of `R`: those of the input below the scale `k`, the kernels of the
five outcomes at the scale `k`, zero above. -/
noncomputable def mixDatum (r₀ : Rep S n R k0 K M N geo cs P k) (Ks : KeptScaleKernels r₀) (j : ℕ)
    (a : LocalHistory S n M K) (ϰ : Fin 5) : KeptDatum (S := S) N R a j :=
  if j < k then r₀.KD.datum j a ϰ else if hk : j = k then hk ▸ Ks.datum a ϰ else zeroDatum a j

theorem mixDatum_lt (r₀ : Rep S n R k0 K M N geo cs P k) (Ks : KeptScaleKernels r₀) {j : ℕ}
    (hj : j < k) (a : LocalHistory S n M K) (ϰ : Fin 5) :
    mixDatum r₀ Ks j a ϰ = r₀.KD.datum j a ϰ := by
  simp [mixDatum, hj]

theorem mixDatum_self (r₀ : Rep S n R k0 K M N geo cs P k) (Ks : KeptScaleKernels r₀)
    (a : LocalHistory S n M K) (ϰ : Fin 5) : mixDatum r₀ Ks k a ϰ = Ks.datum a ϰ := by
  simp [mixDatum]

theorem mixDatum_gt (r₀ : Rep S n R k0 K M N geo cs P k) (Ks : KeptScaleKernels r₀) {j : ℕ}
    (hj : k < j) (a : LocalHistory S n M K) (ϰ : Fin 5) :
    mixDatum r₀ Ks j a ϰ = zeroDatum a j := by
  have _ := hj
  have h1 : ¬ j < k := by omega
  have h2 : ¬ j = k := by omega
  simp [mixDatum, h1, h2]



/-- **`KeptScaleData` from the kernels of the five outcomes at the scale `k`.**  For an input whose
kept costs below `k` are the constants `γ_i = log 5 + A'₃ λ̂_i^{p_R}` (the invariant of the class;
`gam_eq`), the kept data of the output are those of the input below `k`, the five kernels at `k`,
and zero above; `C_dec = 5`, `γ_i` the constants. -/
noncomputable def KeptScaleData.ofKernels (r₀ : Rep S n R k0 K M N geo cs P k)
    (hγ : ∀ i, i < k → ∀ l, r₀.KD.gam i l = Real.log 5 + S.A3' * S.lam i ^ S.pR)
    (Ks : KeptScaleKernels r₀) : KeptScaleData r₀ where
  KD :=
    { datum := mixDatum r₀ Ks
      Cdec := fun _ => 5
      gam := fun i _ => Real.log 5 + S.A3' * S.lam i ^ S.pR
      one_le_Cdec := fun _ => by norm_num
      sum_inv_Cdec := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      gam_ge := fun i _ => by simp
      b_supp := fun j a ϰ o x hv g g' h => by
        revert x
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj]; intro x; exact r₀.KD.b_supp j a ϰ o x hv g g' h
        · rw [mixDatum_self]; intro x; exact Ks.b_supp a ϰ o x hv g g' h
        · rw [mixDatum_gt r₀ Ks hj]; intro x; rfl
      rot_K := fun j a ϰ ρ o x hv => by
        revert x
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj]; intro x; exact r₀.KD.rot_K j a ϰ ρ o x hv
        · rw [mixDatum_self]; intro x; exact Ks.rot_K a ϰ ρ o x hv
        · rw [mixDatum_gt r₀ Ks hj]; intro x; rfl
      rot_b := fun j a ϰ ρ o x hv g => by
        revert x
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj]; intro x; exact r₀.KD.rot_b j a ϰ ρ o x hv g
        · rw [mixDatum_self]; intro x; exact Ks.rot_b a ϰ ρ o x hv g
        · rw [mixDatum_gt r₀ Ks hj]; intro x; rfl
      euclid_I := fun j σ a a' hI hk ϰ p => by
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj, mixDatum_lt r₀ Ks hj]; exact r₀.KD.euclid_I j σ a a' hI hk ϰ p
        · rw [mixDatum_self, mixDatum_self]; exact Ks.euclid_I σ a a' hI hk ϰ p
        · rw [mixDatum_gt r₀ Ks hj, mixDatum_gt r₀ Ks hj]; exact Iff.rfl
      euclid_K := fun j σ a a' hI hk ϰ o o' x x' hv ho hx => by
        revert x x' hx
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj, mixDatum_lt r₀ Ks hj]
          intro x x' hx
          exact r₀.KD.euclid_K j σ a a' hI hk ϰ o o' x x' hv ho hx
        · rw [mixDatum_self, mixDatum_self]
          intro x x' hx
          exact Ks.euclid_K σ a a' hI hk ϰ o o' x x' hv ho hx
        · rw [mixDatum_gt r₀ Ks hj, mixDatum_gt r₀ Ks hj]; intro x x' hx; rfl
      euclid_b := fun j σ a a' hI hk ϰ o o' x x' hv g g' ho hx hg => by
        revert x x' hx
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj, mixDatum_lt r₀ Ks hj]
          intro x x' hx
          exact r₀.KD.euclid_b j σ a a' hI hk ϰ o o' x x' hv g g' ho hx hg
        · rw [mixDatum_self, mixDatum_self]
          intro x x' hx
          exact Ks.euclid_b σ a a' hI hk ϰ o o' x x' hv g g' ho hx hg
        · rw [mixDatum_gt r₀ Ks hj, mixDatum_gt r₀ Ks hj]; intro x x' hx; rfl
      bound := fun H hH j Z h1 h2 hr ϰ => by
        rcases lt_trichotomy j k with hj | rfl | hj
        · rw [mixDatum_lt r₀ Ks hj]
          have := r₀.KD.bound H hH j Z h1 h2 hr ϰ
          rw [hγ j hj ϰ] at this
          refine ⟨this.1, ?_⟩
          have hk' : keptExpOut r₀ (canonHist S n R k0 K k (k + 1)) k j (H.localHistory M K j Z) =
              r₀.κK j (H.localHistory M K j Z) := by
            simp [keptExpOut, hj.ne]
          simpa [hk'] using this.2
        · rw [mixDatum_self]
          have := Ks.bound H hH Z h1 h2 hr ϰ
          refine ⟨this.1, ?_⟩
          simpa [keptExpOut] using this.2
        · rw [mixDatum_gt r₀ Ks hj]
          exact ⟨fun _ _ _ _ => rfl, zeroKernel_kerBound _ _ _⟩ }
  gam_eq := fun i hi l => (hγ i hi l).symm
  gam_val := fun _ _ => rfl



theorem KeptScaleData.ofKernels_datum (r₀ : Rep S n R k0 K M N geo cs P k)
    (hγ : ∀ i, i < k → ∀ l, r₀.KD.gam i l = Real.log 5 + S.A3' * S.lam i ^ S.pR)
    (Ks : KeptScaleKernels r₀) (j : ℕ) (a : LocalHistory S n M K) (ϰ : Fin 5) :
    (KeptScaleData.ofKernels r₀ hγ Ks).KD.datum j a ϰ = mixDatum r₀ Ks j a ϰ := rfl

/-- **The kernels at the scale `k` are inhabited**: the zero kernels satisfy every clause of
`KeptScaleKernels` (support, covariances, the bound (1.26) at every exponent, the vanishing). -/
noncomputable def KeptScaleKernels.zero (r₀ : Rep S n R k0 K M N geo cs P k) :
    KeptScaleKernels r₀ where
  datum := fun a _ => zeroDatum a k
  b_supp := fun _ _ _ _ _ _ _ _ => rfl
  rot_K := fun _ _ _ _ _ _ => rfl
  rot_b := fun _ _ _ _ _ _ _ => rfl
  euclid_I := fun _ _ _ _ _ _ _ => Iff.rfl
  euclid_K := by intros; rfl
  euclid_b := by intros; rfl
  bound := fun _ _ _ _ _ _ _ => ⟨fun _ _ _ _ => rfl, zeroKernel_kerBound _ _ _⟩

end Parts

section Coh

variable {S : Setting} [NeZero S.L] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {k m₁ : ℕ} {ϱ : ℝ}

/-- **The datum coherence of the output kept data from that of the input and of the kernels at the
scale `k`.** -/
theorem keptDatumCoh_of_kernels {F : RepFam S R k0 K M N geo cs P k m₁ ϱ} (hin : LFCoherent F)
    (hγ : ∀ (nK : ℕ) [NeZero nK] (i : ℕ), i < k → ∀ l,
      (F.lf nK).KD.gam i l = Real.log 5 + S.A3' * S.lam i ^ S.pR)
    (Ks : ∀ (nK : ℕ) [NeZero nK], KeptScaleKernels (F.lf nK))
    (hKs : KeptDatumCohAt (K := K) (M := M) (R := R) (k0 := k0) k
      (fun nK _ a ϰ => (Ks nK).datum a ϰ)) :
    KeptDatumCoh (K := K) (M := M) (R := R) (geo := geo) (cs := cs) (k0 := k0)
      (fun nK _ => keptExpOut (F.lf nK) (canonHist S (sides S.L K nK) R k0 K k (k + 1)) k)
      (fun nK _ => (KeptScaleData.ofKernels (F.lf nK) (hγ nK) (Ks nK)).KD) := by
  intro j
  rcases lt_trichotomy j k with hj | rfl | hj
  · have e : (fun (nK : ℕ) [inst : NeZero nK] (a : LocalHistory S (sides S.L K nK) M K) (ϰ : Fin 5) =>
        (KeptScaleData.ofKernels (F.lf nK) (hγ nK) (Ks nK)).KD.datum j a ϰ) =
        fun nK [inst : NeZero nK] a ϰ => (F.lf nK).KD.datum j a ϰ := by
      funext nK inst a ϰ
      exact mixDatum_lt (F.lf nK) (Ks nK) hj a ϰ
    rw [e]
    intro nK₁ nK₂ _ _ c H₁ H₂ ad₁ ad₂ Z₁ Z₂ hH hV ϰ
    exact ((hin nK₁ nK₂ c).2.1 H₁ H₂ ad₁ ad₂ j Z₁ Z₂ hH hV).2 ϰ
  · have e : (fun (nK : ℕ) [inst : NeZero nK] (a : LocalHistory S (sides S.L K nK) M K) (ϰ : Fin 5) =>
        (KeptScaleData.ofKernels (F.lf nK) (hγ nK) (Ks nK)).KD.datum j a ϰ) =
        fun nK [inst : NeZero nK] a ϰ => (Ks nK).datum a ϰ := by
      funext nK inst a ϰ
      exact mixDatum_self (F.lf nK) (Ks nK) a ϰ
    rw [e]
    exact hKs
  · have e : (fun (nK : ℕ) [inst : NeZero nK] (a : LocalHistory S (sides S.L K nK) M K) (ϰ : Fin 5) =>
        (KeptScaleData.ofKernels (F.lf nK) (hγ nK) (Ks nK)).KD.datum j a ϰ) =
        fun nK [inst : NeZero nK] a ϰ => zeroDatum a j := by
      funext nK inst a ϰ
      exact mixDatum_gt (F.lf nK) (Ks nK) hj a ϰ
    rw [e]
    intro nK₁ nK₂ _ _ c H₁ H₂ ad₁ ad₂ Z₁ Z₂ hH hV ϰ
    refine ⟨fun _ _ _ => Iff.rfl, ?_⟩
    intro o₁ o₂ x₁ x₂ hv g₁ g₂ ho hx hg
    exact ⟨rfl, rfl⟩

end Coh

end Balaban.RootFSpine
