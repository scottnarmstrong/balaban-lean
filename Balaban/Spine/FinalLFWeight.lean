/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFHistFactorSurj
public import Balaban.LargeField.Budget.Labelled

/-!
# The weights of the component records: the bound (IV.4.1) for the inherited operators (A6-4)

The heavy objects of the last integral are the realized component records (`lfAllRecs`,
`Spine/FinalLFHistFactorSurj.lean`). Each record has a source in the large-field half of the complete
set (`lfSrc`), whose operator carries the bound (1.26) with the exponent `κ_k(Z, 𝔸 ∩ Z)`
(`D5Bound`). This file proves the summed form of the exponents that (IV.4.1) needs: for every set `Y`
of cubes of scale `k`,
`∑_{records r of cubes Y} e^{-κ(r)} ≤ e^{-A₂ λ_{k₀}^{p₂} - H_k |Y|_k}`,
from the flat budget (`D6Flat`: `G_k ≥ A₂ λ_{k₀}^{p₂} + 2σ_k ℓ + W_{k+1}(k̂)`, `G = κ - log C - H|Z|`)
and Lemma II.5.15 with labels (`sum_inv_logC_labelled_canonical`).

* `keptSum_eq_sum_keptPos`: the label costs of the kept ancestors are a sum over the kept positions;
* `image_fst_labSet`, `sum_labSet`: the positions and the label sum of the labelled kept positions;
* `exists_src_of_mem_lfAllRecs`, `lfSrc`, `lfSrc_mem`, `compRec_lfSrc`: the source of a realized
  record in the large-field half;
* `kappaH_ge_of_D6Flat`: `κ_k(Z, 𝔸 ∩ Z) ≥ A₂ λ_{k₀}^{p₂} + H_k |Z|_k + log C_k(a) + ∑ log C_dec(ϰ)`;
* `pkgBound_lfSrc`: the operator of the source of a record satisfies (1.26) with the exponent `κ`;
* **`sum_exp_neg_kappa_lfSrc_le`**: the summed bound (the inherited part of (IV.4.1)).
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

section KeptSum

variable (H : RegionHistory S n R k0 K)

/-- **The label costs of the kept ancestors are a sum over the kept positions**: for costs that are
functions of the scale and the cube set, `keptSum` is the sum over `keptPos`. -/
theorem keptSum_eq_sum_keptPos (f : ∀ j, Finset (Torus S.d (n j)) → ℝ) :
    ∀ (k : ℕ) (c : H.Comp k),
      H.keptSum (fun j c => f j c.1) k c = ∑ p ∈ H.keptPos k c, f p.1 p.2 := by
  classical
  intro k
  induction k with
  | zero => intro c; exact (H.F.isEmpty_comp_zero.false c).elim
  | succ k ih =>
    intro Z'
    have hdisj : ((H.parts k Z' : Finset (H.Comp k)) : Set (H.Comp k)).PairwiseDisjoint
        (fun c => H.keptPos k c) := by
      intro c₁ _ c₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨Y₁, hd₁, hY₁, -⟩ := exists_of_mem_keptPos H k c₁ p hp₁
      obtain ⟨Y₂, hd₂, hY₂, -⟩ := exists_of_mem_keptPos H k c₂ p hp₂
      have hY : Y₁ = Y₂ := Subtype.ext (hY₁.trans hY₂.symm)
      subst hY
      exact hne (hd₁.unique hd₂)
    have htop : ∀ p ∈ (H.parts k Z').biUnion (fun c => H.keptPos k c), p.1 ≤ k := by
      intro p hp
      obtain ⟨c, -, hpc⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨Y, hd, -, -⟩ := exists_of_mem_keptPos H k c p hpc
      exact hd.le
    rw [keptPos_succ]
    simp only [keptSum]
    by_cases hk : H.IsKeptEvent (k + 1) Z'
    · rw [ite_eq_left hk, ite_eq_left hk, Finset.sum_union, Finset.sum_biUnion hdisj, Finset.sum_singleton]
      · exact congrArg (· + f (k + 1) Z'.1) (Finset.sum_congr rfl fun c _ => ih c)
      · rw [Finset.disjoint_singleton_right]
        intro hp
        have := htop _ hp
        simp at this
    · rw [ite_eq_right hk, ite_eq_right hk, Finset.union_empty, Finset.sum_biUnion hdisj, add_zero]
      exact Finset.sum_congr rfl fun c _ => ih c

end KeptSum

section LabSet

variable {A : LabHist S n R k0 K} {k : ℕ} (c : A.H.Comp k)

/-- The positions of the labelled kept positions are the kept positions. -/
theorem image_fst_labSet : (labSet A c).image Prod.fst = A.H.keptPos k c := by
  unfold labSet
  rw [Finset.image_image]
  exact Finset.image_id'

/-- A sum over the labelled kept positions is a sum over the kept positions. -/
theorem sum_labSet (g : Fin 5 → ℝ) :
    ∑ t ∈ labSet A c, g t.2 = ∑ p ∈ A.H.keptPos k c, g (A.lab p.1 p.2) := by
  classical
  unfold labSet
  rw [Finset.sum_image]
  intro p _ q _ h
  exact congrArg Prod.fst h

end LabSet

section Src

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
/-- A realized record of the large-field half has a source in the large-field half. -/
theorem exists_src_of_mem_lfAllRecs {hist : Finset (LabHist S n R k0 K)} {k : ℕ}
    {r : CRec S n M K k} (hr : r ∈ lfAllRecs (M := M) hist k) :
    ∃ s : (Σ A : LabHist S n R k0 K, A.H.Comp k), s.1 ∈ lfHist hist k ∧ compRec M s.1 s.2 = r := by
  classical
  unfold lfAllRecs at hr
  obtain ⟨Γ, hΓ, hrΓ⟩ := Finset.mem_biUnion.1 hr
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hΓ
  obtain ⟨c, hc⟩ := (mem_lfRecs M).1 hrΓ
  exact ⟨⟨A, c⟩, hA, hc⟩

/-- **The source of a realized record**: a history of the large-field half and a component of it with
this record. -/
noncomputable def lfSrc {hist : Finset (LabHist S n R k0 K)} {k : ℕ}
    (r : ↥(lfAllRecs (M := M) hist k)) : Σ A : LabHist S n R k0 K, A.H.Comp k :=
  (exists_src_of_mem_lfAllRecs r.2).choose

omit [NeZero M] in
theorem lfSrc_mem {hist : Finset (LabHist S n R k0 K)} {k : ℕ} (r : ↥(lfAllRecs (M := M) hist k)) :
    (lfSrc r).1 ∈ lfHist hist k :=
  (exists_src_of_mem_lfAllRecs r.2).choose_spec.1

omit [NeZero M] in
theorem compRec_lfSrc {hist : Finset (LabHist S n R k0 K)} {k : ℕ}
    (r : ↥(lfAllRecs (M := M) hist k)) : compRec M (lfSrc r).1 (lfSrc r).2 = r.1 :=
  (exists_src_of_mem_lfAllRecs r.2).choose_spec.2

end Src

section Kappa

variable {M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {P : BudgetConsts} {k : ℕ}

/-- **The exponent of a component from the flat budget** (`D6Flat`; `G_k = κ - log C - H_k |Z|_k`,
`log C = log C_k(a) + ∑ log C_dec(ϰ)`, `logC_eq_record`, and `σ_k, ℓ, W ≥ 0`). -/
theorem kappaH_ge_of_D6Flat (rep : Rep S n R k0 K M N geo cs P k) {khat : ℕ}
    (hD6 : D6Flat khat rep) {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (hkK : k ≤ K)
    (c : A.H.Comp k) (hc : c.1 ∉ A.H.rem k) :
    S.A2 * S.lam k0 ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S c.1.card +
        ((A.H.localHistory M K k c).logC k +
          ∑ t ∈ labSet A c, Real.log (rep.KD.Cdec t.2)) ≤ rep.kappaH A k c := by
  have ok := A.H.F.ok
  have h6 := hD6 A hA ⟨c, hc⟩
  have hσ : 0 ≤ 2 * S.sigma k * (A.H.bk k c).len := by
    have := ok.sigma_nonneg k
    have : 0 ≤ (A.H.bk k c).len := by rw [bk_len]; exact Spine.length_nonneg _
    positivity
  have hW := ok.W_nonneg (k + 1) khat
  have hG : rep.Gpost A k c = rep.kappaH A k c - A.H.logC (rep.decor A) k c -
      HRun P.H0 P.beta k * BudgetConsts.cubeVol S c.1.card := rfl
  have hlog : A.H.logC (rep.decor A) k c = (A.H.localHistory M K k c).logC k +
      ∑ t ∈ labSet A c, Real.log (rep.KD.Cdec t.2) := by
    rw [A.H.logC_eq_record (M := M) _ k hkK c, sum_labSet c (fun ϰ => Real.log (rep.KD.Cdec ϰ))]
    congr 1
    exact keptSum_eq_sum_keptPos A.H (fun j c => Real.log (rep.KD.Cdec (A.lab j c))) k c
  rw [hG] at h6
  linarith

/-- **The bound (1.26) of the operator of the source of a record** (`D5Bound` at the scale `k`, the
source having no removal). -/
theorem pkgBound_lfSrc (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)
    (hD5 : D5Bound (k + 1) hkK rep) (r : ↥(lfAllRecs (M := M) rep.hist k)) :
    PkgBound ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k
      (locOp geo cs rep.SD rep.KD (lfSrc r).1.adm (fun i c => (lfSrc r).1.lab i c.1) k hkK
        (lfSrc r).2)
      (rep.kappaH (lfSrc r).1 k (lfSrc r).2) := by
  obtain ⟨hA, -, hrem⟩ := mem_lfHist.1 (lfSrc_mem r)
  exact (hD5 _ hA k le_rfl).1 (Nat.lt_succ_self k) (lfSrc r).2 (by
    rw [hrem k le_rfl]; exact Finset.notMem_empty _)

open Classical in
/-- **The inherited part of (IV.4.1)**: for a complete set satisfying the flat budget `D6Flat`, the
exponents `κ` of the sources of the realized records with the cubes `Y` satisfy
`∑_r e^{-κ(r)} ≤ e^{-A₂ λ_{k₀}^{p₂} - H_k |Y|_k}` (Lemma II.5.15 with labels for the records). -/
theorem sum_exp_neg_kappa_lfSrc_le (rep : Rep S n R k0 K M N geo cs P k) {khat : ℕ}
    (hD6 : D6Flat khat rep) (hkK : k ≤ K) (Y : Finset (Torus S.d (n k))) :
    ∑ r ∈ (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter (fun r => r.1.1 = Y),
        Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) ≤
      Real.exp (-(S.A2 * S.lam k0 ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S Y.card)) := by
  set T := (Finset.univ : Finset ↥(lfAllRecs (M := M) rep.hist k)).filter (fun r => r.1.1 = Y)
    with hT
  rcases T.eq_empty_or_nonempty with hT0 | ⟨r₀, -⟩
  · rw [hT0, Finset.sum_empty]; exact (Real.exp_pos _).le
  have ok := (lfSrc r₀).1.H.F.ok
  have hLd : 8 ≤ S.L ^ S.d :=
    le_trans (by norm_num : (8 : ℕ) ≤ 2 ^ 3) ((Nat.pow_le_pow_left ok.two_le_L 3).trans
      (Nat.pow_le_pow_right (by have := ok.two_le_L; omega) ok.three_le_d))
  set E := S.A2 * S.lam k0 ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S Y.card with hE
  let cdec : Fin 5 → ℝ := fun ϰ => Real.log (rep.KD.Cdec ϰ)
  let w : ↥(lfAllRecs (M := M) rep.hist k) → ℝ := fun r =>
    Real.exp (-((r.1.2.1).logC k + ∑ t ∈ r.1.2.2, cdec t.2))
  -- each source satisfies the flat budget
  have hsrc : ∀ r ∈ T, Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2) ≤ Real.exp (-E) * w r := by
    intro r hr
    have hrY : r.1.1 = Y := (Finset.mem_filter.1 hr).2
    obtain ⟨hA, -, hrem⟩ := mem_lfHist.1 (lfSrc_mem r)
    have hcr := compRec_lfSrc r
    have hk := kappaH_ge_of_D6Flat rep hD6 hA hkK (lfSrc r).2 (by
      rw [hrem k le_rfl]; exact Finset.notMem_empty _)
    have h1 : (lfSrc r).2.1 = Y := (congrArg Prod.fst hcr).trans hrY
    have h2 : (lfSrc r).1.H.localHistory M K k (lfSrc r).2 = r.1.2.1 :=
      congrArg (fun r : CRec S n M K k => r.2.1) hcr
    have h3 : labSet (lfSrc r).1 (lfSrc r).2 = r.1.2.2 :=
      congrArg (fun r : CRec S n M K k => r.2.2) hcr
    rw [h1, h2, h3] at hk
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by simp only [cdec, hE]; linarith)
  -- Lemma II.5.15 on the records with cubes `Y`
  have hlab : ∀ F : Finset (Fin 5), ∑ ϰ ∈ F, Real.exp (-cdec ϰ) ≤ 1 := by
    intro F
    have e : ∀ ϰ, Real.exp (-cdec ϰ) = (rep.KD.Cdec ϰ)⁻¹ := fun ϰ => by
      simp only [cdec]
      rw [Real.exp_neg, Real.exp_log (lt_of_lt_of_le one_pos (rep.KD.one_le_Cdec ϰ))]
    simp only [e]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F) fun ϰ _ _ => ?_)
      rep.KD.sum_inv_Cdec
    exact inv_nonneg.2 (le_trans zero_le_one (rep.KD.one_le_Cdec ϰ))
  let f : ↥(lfAllRecs (M := M) rep.hist k) → LocalHistory S n M K × Finset (KeptPos S n × Fin 5) :=
    fun r => (r.1.2.1, r.1.2.2)
  have hinj : Set.InjOn f T := by
    intro r hr r' hr' h
    have hY : r.1.1 = r'.1.1 :=
      (Finset.mem_filter.1 hr).2.trans (Finset.mem_filter.1 hr').2.symm
    exact Subtype.ext (Prod.ext hY h)
  have hII : ∑ x ∈ T.image f, Real.exp (-(x.1.logC k + ∑ t ∈ x.2, cdec t.2)) ≤ 1 := by
    refine sum_inv_logC_labelled_canonical (R := R) (k0 := k0) ?_ hkK Y cdec hlab (T.image f)
      ?_ ?_
    · exact hLd
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      have hrY : r.1.1 = Y := (Finset.mem_filter.1 hr).2
      have hcr := compRec_lfSrc r
      have h1 : (lfSrc r).2.1 = Y := (congrArg Prod.fst hcr).trans hrY
      have hYc : Y ∈ comps (S.omega k) ((lfSrc r).1.H.Zp k) := h1 ▸ (lfSrc r).2.2
      have e : (⟨Y, hYc⟩ : (lfSrc r).1.H.Comp k) = (lfSrc r).2 := Subtype.ext h1.symm
      refine ⟨(lfSrc r).1.H, hYc, ?_, ?_⟩
      · rw [e]; exact (congrArg (fun r : CRec S n M K k => r.2.1) hcr).symm
      · rw [e, ← image_fst_labSet]
        exact congrArg (fun T => Finset.image Prod.fst T)
          (congrArg (fun r : CRec S n M K k => r.2.2) hcr).symm
    · intro x hx p ϰ ϰ' h h'
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
      have hcr := compRec_lfSrc r
      have h3 : labSet (lfSrc r).1 (lfSrc r).2 = r.1.2.2 :=
        congrArg (fun r : CRec S n M K k => r.2.2) hcr
      rw [← h3] at h h'
      exact (mem_labSet.1 h).2.symm.trans (mem_labSet.1 h').2
  rw [Finset.sum_image hinj] at hII
  calc ∑ r ∈ T, Real.exp (-rep.kappaH (lfSrc r).1 k (lfSrc r).2)
      ≤ ∑ r ∈ T, Real.exp (-E) * w r := Finset.sum_le_sum hsrc
    _ = Real.exp (-E) * ∑ r ∈ T, w r := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (-E) * 1 := by gcongr
    _ = Real.exp (-E) := mul_one _

end Kappa

end Balaban.RootFSpine
