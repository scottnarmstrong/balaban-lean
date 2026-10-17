/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassExtend

/-!
# The completion of a term in a larger field domain

The completion `cpl` of `LocalClassExtend.lean` chooses, for a pair of fields, a pair of a field
domain equal on `Y` to its projection `Q (Ψ, h)`.  Here the completion is taken in a field domain
`Dom₂` containing the domain `Dom₁` on which the term is analytic; the term is assumed local on
`Dom₂` only.  At `Dom₂ = Dom₁` these are `fieldDom_completion_analytic_param` and
`fieldDom_completion_extension`.

* `eventually_exists_completion_witness`: near a point of `Dom₁` every projection `Q p` has a
  witness in `Dom₁`;
* `fieldDom_completion_analytic_param_of_sub`, `fieldDom_completion_extension_of_sub`: the completed
  term equals the term on `Dom₂`, is local in `Y` for all pairs, and is analytic on `Dom₁`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.LargeField Balaban.Fluctuation Filter Topology

/-! ### The completion in a larger field domain -/

section Completion

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Near a point of a field domain open relative to the layer-constant pairs, every projection
`Q p` has a witness in the domain**: `p₀ + Q p - Q p₀` lies in the domain for `p` near `p₀`, and it
equals `Q p` on `Y`. -/
theorem eventually_exists_completion_witness (Dom : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom.dom j G q.1 q.2)
    {p₀ : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N} (hp₀ : Dom.dom j G p₀.1 p₀.2) :
    ∀ᶠ p in 𝓝 p₀, ∃ q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom.dom j G q.1 q.2 ∧
      ∀ z ∈ Y, q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z := by
  obtain ⟨hQU, -, hQid⟩ := Classical.choose_spec (exists_layerProj (N := N) G Y)
  set Q := Classical.choose (exists_layerProj (N := N) G Y) with hQ
  have hQc : Continuous Q := LinearMap.continuous_of_finiteDimensional Q
  have hφ : Tendsto (fun p => p₀ + (Q p - Q p₀)) (𝓝 p₀) (𝓝[layerSub G] p₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun p =>
      add_sub_mem_layerSub (hDL p₀ hp₀) (hQU p) (hQU p₀)⟩
    have hφc : Continuous (fun p => p₀ + (Q p - Q p₀)) :=
      continuous_const.add (hQc.sub continuous_const)
    have h := hφc.tendsto p₀
    simp only [sub_self, add_zero] at h
    exact h
  filter_upwards [hφ.eventually (hDo p₀ hp₀)] with p hp
  refine ⟨_, hp, fun z hz => ?_⟩
  obtain ⟨e1, e2⟩ := hQid p₀ (hDL p₀ hp₀) z hz
  simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, Pi.add_apply,
    Pi.sub_apply, e1, e2]
  exact ⟨by abel, by abel⟩

/-- **The completion in a larger domain, with a parameter**: let `Dom₁ ⊆ Dom₂` be field domains
in the layer-constant pairs, `Dom₁` open relative to them, `cpl` the completion in `Dom₂`
(`fieldDom_completion_spec`), `T` analytic on `Dom₁ × Sp` and depending only on the restriction to
`Y` for pairs of `Dom₂`.  Then `(p, g) ↦ T (cpl p, g)` equals `T` on `Dom₂` and is analytic on
`Dom₁ × Sp`.  Near a point of `Dom₁` the completion in `Dom₁` exists, and the two completions give
the same value by the locality on `Dom₂`. -/
theorem fieldDom_completion_analytic_param_of_sub {S F : Type*} [NormedAddCommGroup S]
    [NormedSpace ℂ S] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Dom₁ Dom₂ : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₂.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (h12 : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      Dom₂.dom j G p.1 p.2)
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom₁.dom j G q.1 q.2)
    {Sp : Set S} (T : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × S → F)
    (hT : AnalyticOnNhd ℂ T ({p | Dom₁.dom j G p.1 p.2} ×ˢ Sp))
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 →
      Dom₂.dom j G p'.1 p'.2 → (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) →
      ∀ g, T (p, g) = T (p', g)) :
    (∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → ∀ g,
      T (c p, g) = T (p, g)) ∧
    AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × S => T (c q.1, q.2))
      ({p | Dom₁.dom j G p.1 p.2} ×ˢ Sp) := by
  obtain ⟨-, c2⟩ := fieldDom_completion_spec Dom₂ j G Y c hc hDL
  refine ⟨fun p hp g => hloc _ _ (c2 p hp).1 hp (c2 p hp).2 g, ?_⟩
  -- the completion in `Dom₁`
  set c₁ : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N :=
    fun p => Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₁.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z) with hc₁
  have hA := fieldDom_completion_analytic_param Dom₁ j G Y c₁ (fun _ => rfl)
    (fun p hp => hDL p (h12 p hp)) hDo T hT
    (fun p p' hp hp' hY g => hloc p p' (h12 _ hp) (h12 _ hp') hY g)
  rintro ⟨p₀, g₀⟩ ⟨hp₀, hg₀⟩
  refine (hA (p₀, g₀) ⟨hp₀, hg₀⟩).congr ?_
  have hev := (continuous_fst.tendsto (p₀, g₀)).eventually
    (eventually_exists_completion_witness Dom₁ j G Y (fun p hp => hDL p (h12 p hp)) hDo hp₀)
  filter_upwards [hev] with q hq
  obtain ⟨d1, d2⟩ := Classical.epsilon_spec hq
  obtain ⟨w, hw1, hw2⟩ := hq
  obtain ⟨e1, e2⟩ := Classical.epsilon_spec (p := fun q' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₂.dom j G q'.1 q'.2 ∧ ∀ z ∈ Y,
        q'.1 z = (Classical.choose (exists_layerProj (N := N) G Y) q.1).1 z ∧
        q'.2 z = (Classical.choose (exists_layerProj (N := N) G Y) q.1).2 z)
    ⟨w, h12 w hw1, hw2⟩
  rw [← hc] at e1 e2
  exact hloc _ _ (h12 _ d1) e1 (fun z hz => ⟨(d2 z hz).1.trans (e2 z hz).1.symm,
    (d2 z hz).2.trans (e2 z hz).2.symm⟩) q.2

/-- **The completion in a larger domain** (`fieldDom_completion_analytic_param_of_sub` for a
function of the pair alone): `T ∘ cpl` depends only on the restriction to `Y` for all pairs, equals
`T` on `Dom₂` and is analytic on `Dom₁`. -/
theorem fieldDom_completion_extension_of_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Dom₁ Dom₂ : FieldDom d L N₁ m₁ K N ϱ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Set (CTorus d L N₁ m₁ K))
    (c : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N)
    (hc : ∀ p, c p = Classical.epsilon (fun q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N =>
      Dom₂.dom j G q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) G Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) G Y) p).2 z))
    (h12 : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      Dom₂.dom j G p.1 p.2)
    (hDL : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → p ∈ layerSub G)
    (hDo : ∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₁.dom j G p.1 p.2 →
      ∀ᶠ q in 𝓝[layerSub G] p, Dom₁.dom j G q.1 q.2)
    (T : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → F)
    (hT : AnalyticOnNhd ℂ T {p | Dom₁.dom j G p.1 p.2})
    (hloc : ∀ p p' : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 →
      Dom₂.dom j G p'.1 p'.2 → (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T p = T p') :
    (∀ Ψ Ψ' h h' : Fld d L N₁ m₁ K N, (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      T (c (Ψ, h)) = T (c (Ψ', h'))) ∧
    (∀ p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, Dom₂.dom j G p.1 p.2 → T (c p) = T p) ∧
    AnalyticOnNhd ℂ (fun p => T (c p)) {p | Dom₁.dom j G p.1 p.2} := by
  obtain ⟨c1, -⟩ := fieldDom_completion_spec Dom₂ j G Y c hc hDL
  obtain ⟨e, ha⟩ := fieldDom_completion_analytic_param_of_sub (S := ℂ) (Sp := Set.univ)
    Dom₁ Dom₂ j G Y c hc h12 hDL hDo (fun q => T q.1)
    (fun q hq => (hT q.1 hq.1).comp_of_eq analyticAt_fst rfl)
    (fun p p' hp hp' hY _ => hloc p p' hp hp' hY)
  refine ⟨fun Ψ Ψ' h h' hY => by rw [c1 Ψ Ψ' h h' hY], fun p hp => e p hp 0, ?_⟩
  intro p₀ hp₀
  exact (ha (p₀, 0) ⟨hp₀, Set.mem_univ _⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl

end Completion

end Balaban.Localization
