/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelCastAvg

/-!
# Analyticity across the reindexing of fields (`LocalClassDensityLevelCastAnalytic`)

Reindexing the coordinates of fields along a map `σ` is a continuous linear map, so it preserves
analyticity of functions of one, two or three fields, on the preimage of the domain.
-/

@[expose] public section

namespace Balaban.Fluctuation

section Analytic

variable {α β : Type} [Fintype α] [Fintype β] {N : ℕ}

omit [Fintype α] in
theorem analyticAt_eval_castEquiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (π : E →L[ℂ] (α → Fin N → ℂ)) (x : α) (i : Fin N) (p : E) :
    AnalyticAt ℂ (fun q : E => π q x i) p :=
  (((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.proj x : (α → Fin N → ℂ) →L[ℂ] (Fin N → ℂ))).comp π).analyticAt p

omit [Fintype α] in
theorem analyticAt_reindex {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (π : E →L[ℂ] (α → Fin N → ℂ)) (σ : β → α) (p : E) :
    AnalyticAt ℂ (fun q : E => (fun x : β => π q (σ x))) p :=
  analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => analyticAt_eval_castEquiv π (σ x) i p

/-- Analyticity of a function of two fields is preserved by reindexing. -/
theorem analyticOnNhd_pull2 {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (σ : β → α)
    {G : (β → Fin N → ℂ) × (β → Fin N → ℂ) → F}
    {t : Set ((β → Fin N → ℂ) × (β → Fin N → ℂ))} (hG : AnalyticOnNhd ℂ G t) :
    AnalyticOnNhd ℂ (fun p : (α → Fin N → ℂ) × (α → Fin N → ℂ) =>
      G (fun x => p.1 (σ x), fun x => p.2 (σ x)))
      {p | ((fun x => p.1 (σ x), fun x => p.2 (σ x)) :
        (β → Fin N → ℂ) × (β → Fin N → ℂ)) ∈ t} := by
  have hf : AnalyticOnNhd ℂ (fun p : (α → Fin N → ℂ) × (α → Fin N → ℂ) =>
      ((fun x => p.1 (σ x), fun x => p.2 (σ x)) : (β → Fin N → ℂ) × (β → Fin N → ℂ)))
      Set.univ := fun p _ =>
    AnalyticAt.prod (analyticAt_reindex (ContinuousLinearMap.fst ℂ _ _) σ p)
      (analyticAt_reindex (ContinuousLinearMap.snd ℂ _ _) σ p)
  exact hG.comp (hf.mono (Set.subset_univ _)) (fun p hp => hp)

/-- Analyticity of a function of three fields is preserved by reindexing. -/
theorem analyticOnNhd_pull3 {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (σ : β → α)
    {G : (β → Fin N → ℂ) × (β → Fin N → ℂ) × (β → Fin N → ℂ) → F}
    {t : Set ((β → Fin N → ℂ) × (β → Fin N → ℂ) × (β → Fin N → ℂ))}
    (hG : AnalyticOnNhd ℂ G t) :
    AnalyticOnNhd ℂ (fun p : (α → Fin N → ℂ) × (α → Fin N → ℂ) × (α → Fin N → ℂ) =>
      G (fun x => p.1 (σ x), fun x => p.2.1 (σ x), fun x => p.2.2 (σ x)))
      {p | ((fun x => p.1 (σ x), fun x => p.2.1 (σ x), fun x => p.2.2 (σ x)) :
        (β → Fin N → ℂ) × (β → Fin N → ℂ) × (β → Fin N → ℂ)) ∈ t} := by
  have hf : AnalyticOnNhd ℂ
      (fun p : (α → Fin N → ℂ) × (α → Fin N → ℂ) × (α → Fin N → ℂ) =>
        ((fun x => p.1 (σ x), fun x => p.2.1 (σ x), fun x => p.2.2 (σ x)) :
          (β → Fin N → ℂ) × (β → Fin N → ℂ) × (β → Fin N → ℂ))) Set.univ := fun p _ =>
    AnalyticAt.prod (analyticAt_reindex (ContinuousLinearMap.fst ℂ _ _) σ p)
      (AnalyticAt.prod
        (analyticAt_reindex ((ContinuousLinearMap.fst ℂ (α → Fin N → ℂ) (α → Fin N → ℂ)).comp
            (ContinuousLinearMap.snd ℂ (α → Fin N → ℂ) ((α → Fin N → ℂ) × (α → Fin N → ℂ))))
          σ p)
        (analyticAt_reindex ((ContinuousLinearMap.snd ℂ (α → Fin N → ℂ) (α → Fin N → ℂ)).comp
            (ContinuousLinearMap.snd ℂ (α → Fin N → ℂ) ((α → Fin N → ℂ) × (α → Fin N → ℂ))))
          σ p))
  exact hG.comp (hf.mono (Set.subset_univ _)) (fun p hp => hp)

/-- Analyticity of a function of `((Ψ, h), g)` is preserved by reindexing. -/
theorem analyticOnNhd_pullSrc {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (σ : β → α)
    {G : ((β → Fin N → ℂ) × (β → Fin N → ℂ)) × (β → Fin N → ℂ) → F}
    {t : Set (((β → Fin N → ℂ) × (β → Fin N → ℂ)) × (β → Fin N → ℂ))}
    (hG : AnalyticOnNhd ℂ G t) :
    AnalyticOnNhd ℂ (fun p : ((α → Fin N → ℂ) × (α → Fin N → ℂ)) × (α → Fin N → ℂ) =>
      G ((fun x => p.1.1 (σ x), fun x => p.1.2 (σ x)), fun x => p.2 (σ x)))
      {p | (((fun x => p.1.1 (σ x), fun x => p.1.2 (σ x)), fun x => p.2 (σ x)) :
        ((β → Fin N → ℂ) × (β → Fin N → ℂ)) × (β → Fin N → ℂ)) ∈ t} := by
  have hf : AnalyticOnNhd ℂ
      (fun p : ((α → Fin N → ℂ) × (α → Fin N → ℂ)) × (α → Fin N → ℂ) =>
        (((fun x => p.1.1 (σ x), fun x => p.1.2 (σ x)), fun x => p.2 (σ x)) :
          ((β → Fin N → ℂ) × (β → Fin N → ℂ)) × (β → Fin N → ℂ))) Set.univ := fun p _ =>
    AnalyticAt.prod
      (AnalyticAt.prod
        (analyticAt_reindex ((ContinuousLinearMap.fst ℂ (α → Fin N → ℂ) (α → Fin N → ℂ)).comp
            (ContinuousLinearMap.fst ℂ ((α → Fin N → ℂ) × (α → Fin N → ℂ)) (α → Fin N → ℂ)))
          σ p)
        (analyticAt_reindex ((ContinuousLinearMap.snd ℂ (α → Fin N → ℂ) (α → Fin N → ℂ)).comp
            (ContinuousLinearMap.fst ℂ ((α → Fin N → ℂ) × (α → Fin N → ℂ)) (α → Fin N → ℂ)))
          σ p))
      (analyticAt_reindex (ContinuousLinearMap.snd ℂ _ _) σ p)
  exact hG.comp (hf.mono (Set.subset_univ _)) (fun p hp => hp)

end Analytic

end Balaban.Fluctuation
