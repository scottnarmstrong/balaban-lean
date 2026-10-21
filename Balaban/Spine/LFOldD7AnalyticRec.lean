/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7AnalyticLoc

/-!
# The old term is analytic at the composed field, from the record (the input `hB`)

`oldTermLF_analytic_of_record`: for finite-scale parameter fields `ψf e`, `ψ'f e`, sources `gxE e`
depending analytically on `e`, and a set `Dm` of fields on which the record's old term is analytic
(the clause `analytic` at the external field `hC hv`, `Dm` the H7 domain), the old term
`oldTermLF … (extK (ψf e)) (extK (ψ'f e)) hv (gxE e)` is analytic jointly in `(e, comp)` at every
point whose multiscale triple lies in `Dm`.  This is the input `hB` of
`oldCoefLoc_analytic_family`, with the membership in `Dm` the H7 condition of the local pair.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Localization Matrix Balaban.LargeField

namespace Balaban.RootFSpine

open Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

section Rec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem composedMulti_extK_coord_analytic {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    {ψf : E → FinFieldC S n M K N} {Pset : Set E}
    (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψf e j y i) Pset)
    {e₀ : E} (he₀ : e₀ ∈ Pset) (c₀ : unitPts G' → Fin N → ℂ) (j : ℕ) (hj : j ≤ K)
    (y : Torus S.d (M * n K * S.L ^ (K - j))) (i : Fin N) :
    AnalyticAt ℂ (fun q : E × (unitPts G' → Fin N → ℂ) =>
      composedMulti g hnn hM1 hk G' (extK (ψf q.1)) q.2 j y i) (e₀, c₀) := by
  classical
  unfold composedMulti extK
  by_cases h1 : j < k
  · simp only [h1, ↓reduceIte, hj, dite_true]
    exact (hψ _ _ _ e₀ he₀).comp_of_eq analyticAt_fst rfl
  · by_cases h2 : j = k
    · subst h2
      simp only [h1, ↓reduceIte, dite_true, hj]
      by_cases h3 : unitOfBlock g hnn hM1 hk y ∈ unitPts G'
      · simp only [h3, dite_true]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : unitPts G' => Fin N → ℂ)
            ⟨unitOfBlock g hnn hM1 hk y, h3⟩)).analyticAt _ |>.comp analyticAt_snd
      · simp only [h3, dite_false]
        exact (hψ _ _ _ e₀ he₀).comp_of_eq analyticAt_fst rfl
    · simp only [h1, h2, ↓reduceIte, dite_false]
      exact analyticAt_const

theorem composedMulti_extK_eq {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : FinFieldC S n M K N) (c : unitPts G' → Fin N → ℂ) :
    extK (fun (j : Fin (K + 1)) y => composedMulti g hnn hM1 hk G' (extK ψ) c j.val y) =
      composedMulti g hnn hM1 hk G' (extK ψ) c := by
  funext j y
  unfold extK
  by_cases hj : j ≤ K
  · simp only [hj, dite_true]
  · simp only [hj, dite_false]
    unfold composedMulti
    have h1 : ¬ j < k := by omega
    have h2 : ¬ j = k := by omega
    simp only [h1, h2, ↓reduceIte, dite_false]

/-- **The input `hB` of `oldCoefLoc_analytic_family`, from the record**: `Dm` is a set of triples
`(ψ, ψ', g)` of finite fields on which the record's old term at the external field `hC hv` is
analytic (`hanR`); if the multiscale triple of `(e, comp)` lies in `Dm` (`hdom`, the H7 condition of
the local pair), the old term is analytic jointly in `(e, comp)` there. -/
theorem oldTermLF_analytic_of_record {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    {k : ℕ} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (hv : EuclideanSpace ℝ (Fin N))
    (Dm : Set (FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ)))
    (hanR : AnalyticOnNhd ℂ (fun p : FinFieldC S n M K N × FinFieldC S n M K N ×
      (GIdx S n M K N → ℂ) => rep.B A X (extK p.1) (extK p.2.1) (hC hv) p.2.2) Dm)
    {ψf ψ'f : E → FinFieldC S n M K N} {gxE : E → GIdx S n M K N → ℂ} {Pset : Set E}
    (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψf e j y i) Pset)
    (hψ' : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψ'f e j y i) Pset)
    (hgx : ∀ p, AnalyticOnNhd ℂ (fun e => gxE e p) Pset)
    {e₀ : E} (he₀ : e₀ ∈ Pset) (c₀ : unitPts G' → Fin N → ℂ)
    (hdom : ((fun (j : Fin (K + 1)) y => composedMulti g hnn hM1 hk G' (extK (ψf e₀)) c₀ j.val y),
      ψ'f e₀, gxE e₀) ∈ Dm) :
    AnalyticAt ℂ (fun q : E × (unitPts G' → Fin N → ℂ) =>
      oldTermLF g hnn hM1 rep A X hk G' (extK (ψf q.1)) (extK (ψ'f q.1)) hv (gxE q.1) q.2)
      (e₀, c₀) := by
  have hP : AnalyticAt ℂ (fun q : E × (unitPts G' → Fin N → ℂ) =>
      ((fun (j : Fin (K + 1)) y => composedMulti g hnn hM1 hk G' (extK (ψf q.1)) q.2 j.val y),
        ψ'f q.1, gxE q.1)) (e₀, c₀) := by
    refine AnalyticAt.prod ?_ (AnalyticAt.prod ?_ ?_)
    · exact analyticAt_pi_iff.2 fun j => analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i =>
        composedMulti_extK_coord_analytic g hnn hM1 hk G' hψ he₀ c₀ j.val
          (Nat.lt_succ_iff.1 j.2) y i
    · exact analyticAt_pi_iff.2 fun j => analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i =>
        (hψ' j y i e₀ he₀).comp_of_eq analyticAt_fst rfl
    · exact analyticAt_pi_iff.2 fun p => (hgx p e₀ he₀).comp_of_eq analyticAt_fst rfl
  have h := (hanR _ hdom).comp_of_eq hP rfl
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp_def, oldTermLF]
  rw [composedMulti_extK_eq g hnn hM1 hk G' (ψf q.1) q.2]

end Rec

end Balaban.RootFSpine
