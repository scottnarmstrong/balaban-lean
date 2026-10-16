/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassAssembleE
public import Balaban.Fluctuation.LocalClassM

/-!
# The M-part of the local successor class at the new level: the assembly

The source terms of the local successor class at the level `k + 1` (blocker 6) are indexed by a
site `x` and a polymer `Y ∈ 𝒟_{k+1}`: the site sums `TM x Y = Σ_{τ, y_τ = x} T_τ Y` of the recomputed
source terms `T_τ` of the old labels on `𝔹_{k+1}(Y⁺)` (`localB_mTermHat_evTerm_*`, vectors of
`ℂ^N`, functions of the pair of fields and of the source), completed off the class domain and
averaged over the paving group, the site being transported with the polymer.  This file composes
the landed clauses into the fields at `j = k + 1` of `SFTermClausesStrong` for the source terms
(`LocalClassAssembleE.lean` for the energy terms).

* `l1_actField`, `analyticAt_actTriple`: the `ℓ¹` norm of a source is invariant under the
  permutations of the torus, which act linearly on triples;
* `localClass_termClausesM`: from per-polymer hypotheses on `TM` (analytic on the domain times
  `{‖g‖₁ < 1}`, local in the pair on the domain and in the source everywhere, bounded by
  `B_M e^{-κ d_{k+1}(Y)}` with `B_M < c₉ ξ_{k+1}^{(d-2)/2 + γ - α₁}`, equivariant under real rotations),
  the slices at `j = k + 1` of `analyticM`, `eucM`, `localM`, `boundM`, and `rotM` for the real
  matrices of `IsRot` and the sources of `ℓ¹` norm `< 1`;
* `localClass_termClausesM_of_labels`: the same for the site sums over the labels, from per-label
  hypotheses in the form of the landed per-label theorems; the bound is resummed per site (no volume
  factor) and needs `√N γ ρ_M < c₉ ξ_{k+1}^{(d-2)/2 + γ - α₁}`;
* `localClass_avgM_eq_of_cov`: the averaged completed term equals `TM` on the class domain if `TM`
  is covariant under the paving group there.

Not covered: complex rotations, sources of `ℓ¹` norm `≥ 1` in `rotM` (the per-label rotation
theorem needs the analyticity of the old term in the fields at the source), `eucMloc`, and the
per-label paving covariance of the source terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

section AssembleM

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- The `ℓ¹` norm of a source is invariant under the permutations of the torus. -/
theorem l1_actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) (g : Fld d L N₁ m₁ (k + 1) N) :
    Def6.l1 (actField s g) = Def6.l1 g := by
  unfold Def6.l1 actField
  exact Equiv.sum_comp s.symm (fun x => vn (g x))

/-- The action of a permutation on triples (pair of fields, source) is analytic (it is linear). -/
theorem analyticAt_actTriple (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
    (q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N) :
    AnalyticAt ℂ (fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) ×
        Fld d L N₁ m₁ (k + 1) N =>
      ((actField s q.1.1, actField s q.1.2), actField s q.2)) q := by
  let ℓ : Fld d L N₁ m₁ (k + 1) N →ₗ[ℂ] Fld d L N₁ m₁ (k + 1) N :=
    LinearMap.funLeft ℂ (Fin N → ℂ) s.symm
  have h := (LinearMap.toContinuousLinearMap
    (LinearMap.prodMap (LinearMap.prodMap ℓ ℓ) ℓ)).analyticAt q
  convert h using 1
  funext q
  rfl

open Classical in
/-- **The M-fields of the local successor class at the new level `k + 1`** (the analogue of
`localClass_termClausesE` for the source terms).  Let `TM x Y` be the recomputed source term of the
site `x` and the polymer `Y` (a vector of `ℂ^N`, a function of the pair of fields and of the
source), with, for polymers `Y ∈ 𝒟_{k+1}`, on the class domain of `𝔹_{k+1}(Y⁺)`:
* `hTMan`: analyticity jointly in the pair and the source on the domain times `{‖g‖₁ < 1}`;
* `hTMloc`: dependence on the restriction of the pair to `Y` only, for every source;
* `hTMsrc`: dependence on the restriction of the source to `Y` only (all pairs, all sets);
* `hTMbd`: `vn (TM x Y) ≤ B_M e^{-κ d_{k+1}(Y)}` for `x ∈ Y`, `‖g‖₁ < 1`, with
  `B_M < c₉ ξ_{k+1}^{(d-2)/2 + γ - α₁}` (`hBM`);
* `hTMrot`: equivariance under real orthogonal `Q` for `‖g‖₁ < 1`.
Let `AM x Y` be the average over the paving group of `(p, g) ↦ TM (s⁻¹ x) (s⁻¹ Y) (cpl (s⁻¹ Y)
(s⁻¹ p), s⁻¹ g)` and the class term `M (k + 1) x Y = AM x Y`.  Then the slices at `j = k + 1` of the
clauses `analyticM`, `eucM`, `localM`, `boundM` hold, and `rotM` for the real matrices of `IsRot`
and the sources of `ℓ¹` norm `< 1`.  As for `ℰ`, no paving covariance of `TM` is used. -/
theorem localClass_termClausesM {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ Y z, z ∈ Yp Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (hgs : ∀ Y, Tm.gs (k + 1) Y =
      localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMan : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TM x Y)
      ({p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2} ×ˢ
        {g | Def6.l1 g < 1}))
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (hTMsrc : ∀ x Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ z ∈ Y, g z = g' z) → TM x Y (p, g) = TM x Y (p, g'))
    {BM : ℝ}
    (hBM : BM < P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hTMbd : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 → vn (TM x Y (p, g)) ≤ BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTMrot : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 →
      TM x Y ((rotField (cmat Q) p.1, rotField (cmat Q) p.2), rotField (cmat Q) g) =
        (cmat Q) *ᵥ TM x Y (p, g))
    (AM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hAM : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g)) :
    -- `analyticM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => Tm.M (k + 1) x X p.1 p.2.1 p.2.2)
        {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}) ∧
    -- `rotM`, real matrices, sources of `ℓ¹` norm `< 1`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h g, Def6.l1 g < 1 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.M (k + 1) x X (rotField R Ψ) (rotField R h) (rotField R g) =
        R *ᵥ Tm.M (k + 1) x X Ψ h g) ∧
    -- `eucM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.M (k + 1) (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) =
        Tm.M (k + 1) x X Ψ h g) ∧
    -- `localM`
    (∀ x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      Tm.M (k + 1) x X Ψ h g = Tm.M (k + 1) x X Ψ' h' g') ∧
    -- `boundM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ Ψ h g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h → Def6.l1 g < 1 →
      vn (Tm.M (k + 1) x X Ψ h g) <
        P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) := by
  set D : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom
      (k + 1) (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2
    with hD
  have hDL : ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      p ∈ layerSub (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) :=
    fun Y p hp => xiDom_mem_layerSub hp
  have hdom : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      D (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    localB_collar_xiDom_act (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp Y)
      (hYp (r '' Y)) hp
  set f : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N →
      Fin N → ℂ := fun x Y q => TM x Y (cpl Y q.1, q.2) with hf
  have hAM' : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2) := hAM
  -- the completed terms equal the terms on the domain, are analytic there, and are local
  have hfT : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g, D Y p →
      f x Y (p, g) = TM x Y (p, g) := fun x Y hY p g hp => by
    obtain ⟨-, c2⟩ := fieldDom_completion_spec _ (k + 1) _ Y (cpl Y) (hcpl Y) (hDL Y)
    exact hTMloc x Y hY _ _ (c2 p hp).1 hp (c2 p hp).2 g
  have hfan : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      AnalyticOnNhd ℂ (f x Y) ({p | D Y p} ×ˢ {g | Def6.l1 g < 1}) := fun x Y hY =>
    fieldDom_completion_analytic_param _ (k + 1) _ Y (cpl Y) (hcpl Y) (hDL Y)
      (fun _ hp => xiDom_eventually HB hp) (TM x Y) (hTMan x Y hY)
      (fun p p' hp hp' hpp g => hTMloc x Y hY p p' hp hp' hpp g)
  have hfloc : ∀ x Y
      (q q' : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N),
      (∀ z ∈ Y, q.1.1 z = q'.1.1 z ∧ q.1.2 z = q'.1.2 z ∧ q.2 z = q'.2 z) →
      f x Y q = f x Y q' := fun x Y q q' hqq => by
    obtain ⟨c1, -⟩ := fieldDom_completion_spec _ (k + 1) _ Y (cpl Y) (hcpl Y) (hDL Y)
    have e := c1 q.1.1 q'.1.1 q.1.2 q'.1.2 fun z hz => ⟨(hqq z hz).1, (hqq z hz).2.1⟩
    simp only [Prod.mk.eta] at e
    simp only [hf]
    rw [e]
    exact hTMsrc x Y _ _ _ fun z hz => (hqq z hz).2.2
  -- covariance of the average for all triples
  have hAMcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ x Y (q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N),
      AM (r x) (r '' Y) ((actField r q.1.1, actField r q.1.2), actField r q.2) = AM x Y q := by
    intro r hr x Y q
    rw [hAM', hAM']
    congr 1
    refine (Fintype.sum_equiv (Equiv.mulLeft (⟨r, hr⟩ :
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))) _ _
      fun t => ?_).symm
    have ht : ((Equiv.mulLeft (⟨r, hr⟩ :
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) t :
          pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
          Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) = r * (t : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) :=
      rfl
    simp only [ht, _root_.mul_inv_rev, actField_mul_perm, actField_inv_actField]
    congr 1
    · simp [Equiv.Perm.inv_def]
    · simp [Set.image_image, Equiv.Perm.inv_def]
  have hAMloc : ∀ x Y
      (q q' : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N),
      (∀ z ∈ Y, q.1.1 z = q'.1.1 z ∧ q.1.2 z = q'.1.2 z ∧ q.2 z = q'.2 z) →
      AM x Y q = AM x Y q' := fun x Y q q' hqq => by
    rw [hAM', hAM']
    congr 1
    refine Finset.sum_congr rfl fun s _ => hfloc _ _ _ _ fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [actField, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact hqq y hy
  have hinv : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
    fun s => inv_mem s.2
  refine ⟨fun x X hX hx => ?_, fun x X hX hx R hR hre Ψ h g hg h1 h2 => ?_,
    fun x X hX hx r hr Ψ h g _ _ => ?_, fun x X Ψ Ψ' h h' g g' hX => ?_,
    fun x X hX hx Ψ h g h1 hg => ?_⟩
  · -- `analyticM`
    rw [hgs]
    intro p hp
    have hq : AnalyticAt ℂ (AM x X) ((p.1, p.2.1), p.2.2) := by
      have hAf : AM x X = fun q => ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (d := d) L P.m₀ (k + 1)) : ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁)
          (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
          f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
            (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
            ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2) :=
        funext (hAM' x X)
      rw [hAf]
      refine AnalyticAt.fun_const_smul ?_
      have hs : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
          AnalyticAt ℂ (fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) ×
              Fld d L N₁ m₁ (k + 1) N =>
            f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
                Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
              (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
                Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
              ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
                  actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
            ((p.1, p.2.1), p.2.2) := fun s =>
        AnalyticAt.comp_of_eq
          (g := f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
                Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
              (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
                Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X))
          (f := fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) ×
              Fld d L N₁ m₁ (k + 1) N =>
            ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
          (y := ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2.1),
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2.2))
          (hfan _ _ ((isPolyDom_image_iff hN (hinv s) X).2 hX) _
            ⟨hdom _ (hinv s) X (p.1, p.2.1) hp.1,
              show Def6.l1 (actField _ p.2.2) < 1 by rw [l1_actField]; exact hp.2⟩)
          (analyticAt_actTriple _ _) rfl
      have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := ((p.1, p.2.1), p.2.2)) Finset.univ
        fun s _ => hs s
      convert h using 1
      funext q
      simp [Finset.sum_apply]
    have hφ : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
        Fld d L N₁ m₁ (k + 1) N => ((p.1, p.2.1), p.2.2)) p :=
      (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
        (analyticAt_snd.comp analyticAt_snd)
    have e : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
        Fld d L N₁ m₁ (k + 1) N => Tm.M (k + 1) x X p.1 p.2.1 p.2.2) =
        fun p => AM x X ((p.1, p.2.1), p.2.2) := funext fun p => hM _ _ _ _ _
    rw [e]
    exact hq.comp_of_eq hφ rfl
  · -- `rotM`
    obtain ⟨Q, hQ, rfl⟩ := exists_cmat_of_isRot_real hR hre
    rw [hgs] at h1 h2
    rw [hM, hM, hAM', hAM', Matrix.mulVec_smul, Matrix.mulVec_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' X) := (isPolyDom_image_iff hN (hinv s) X).2 hX
    have hp1 := hdom _ (hinv s) X (Ψ, h) h1
    have hp2 := hdom _ (hinv s) X (rotField (cmat Q) Ψ, rotField (cmat Q) h) h2
    simp only at hp1 hp2
    rw [actField_rotField, actField_rotField] at hp2 ⊢
    rw [actField_rotField, hfT _ _ hY' _ _ hp2, hfT _ _ hY' _ _ hp1]
    exact hTMrot _ _ hY' Q hQ _ _ hp1 (by rw [l1_actField]; exact hg)
  · -- `eucM`
    rw [hM, hM]
    exact hAMcov r hr x X ((Ψ, h), g)
  · -- `localM`
    rw [hM, hM]
    exact hAMloc x X _ _ hX
  · -- `boundM`
    rw [hgs] at h1
    rw [hM, hAM']
    refine (le_of_eq (vn_smul_complex _ _)).trans_lt ?_
    have hc : (0 : ℝ) < Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d)
        L P.m₀ (k + 1)) := by exact_mod_cast Fintype.card_pos
    have hterm : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        vn (f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
            (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
            ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ Ψ,
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ h),
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g)) ≤
          BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X) := fun s => by
      have hY' : IsPolyDom P.m₀ (k + 1)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
            '' X) := (isPolyDom_image_iff hN (hinv s) X).2 hX
      have hp1 := hdom _ (hinv s) X (Ψ, h) h1
      rw [hfT _ _ hY' _ _ hp1, ← sizeJ_image hN (hinv s) X]
      exact hTMbd _ _ hY' (Set.mem_image_of_mem _ hx) _ _ hp1 (by rw [l1_actField]; exact hg)
    have hsum := (vn_sum_le Finset.univ fun s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (d := d) L P.m₀ (k + 1) =>
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ Ψ,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ h),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g)).trans
      (Finset.sum_le_sum fun s _ => hterm s)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hsum' : vn (∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ Ψ,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ h),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g)) ≤
        Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) *
          (BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) := by
      convert hsum using 2
      funext i
      simp [Finset.sum_apply]
    have hle : ‖((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
        (k + 1)) : ℂ))⁻¹‖ * vn (∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d)
          L P.m₀ (k + 1),
        f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ Ψ,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ h),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g)) ≤
        BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X) := by
      rw [norm_inv, Complex.norm_natCast]
      calc _ ≤ ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
            (k + 1)) : ℝ))⁻¹ * (Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1)
              (d := d) L P.m₀ (k + 1)) * (BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X))) :=
            mul_le_mul_of_nonneg_left hsum' (inv_nonneg.2 hc.le)
        _ = _ := by field_simp
    exact hle.trans_lt (mul_lt_mul_of_pos_right hBM (Real.exp_pos _))


open Classical in
/-- **The M-fields of the local successor class from the per-label source terms**
(`localClass_termClausesM` for the site sums `TM x Y = Σ_{τ ∈ 𝒯M, y_τ = x} T_τ Y` of the recomputed
source terms of the old labels, vectors of `ℂ^N`).  Per-label hypotheses, for polymers
`Y ∈ 𝒟_{k+1}` and on the class domain of `𝔹_{k+1}(Y⁺)`, in the form of the landed per-label
theorems (componentwise for `T_τ Y (p, g) i = evTerm … (Fi i) Y (clipRaw 𝔹_{k+1}(Y⁺) p, g)`):
* `hTlan`: analyticity jointly in the pair and the source (`localB_mTermHat_evTerm_xiFieldDom`,
  clause 1, componentwise);
* `hTlloc`: locality in the pair on the domain, every source (`localB_mTermHat_evTerm_local`);
* `hTlsrc`: locality in the source, all pairs (`evTerm_source_congr`);
* `hTlbd`: the per-label bound of every component (`localB_mTermHat_evTerm_xiFieldDom`, clause 2);
* `hTlrot`: equivariance under real orthogonal `Q` (`localB_mTermHat_evTerm_rot`).
The bound is resummed per site, with no volume factor: per-site sums of `Eb_τ e^{-κ₀ d_{j_τ}(X_τ)}`
at most `ρ_M` (`classM_siteSum_le` for the class labels), `κ ≤ 2 κ_dec`, and the numerical
hypothesis `√N γ ρ_M < c₉ ξ_{k+1}^{(d-2)/2 + γ - α₁}` (`hBM`), the prefactor of the clause
`boundM`. -/
theorem localClass_termClausesM_of_labels {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (HB : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ Y z, z ∈ Yp Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (hgs : ∀ Y, Tm.gs (k + 1) Y =
      localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    {τι : Type*} [DecidableEq τι] (𝒯M : Finset τι) (yM : τι → CTorus d L N₁ m₁ (k + 1))
    (Tl : τι → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTlan : ∀ τ ∈ 𝒯M, ∀ Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (Tl τ Y)
      ({p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2} ×ˢ
        {g | Def6.l1 g < 1}))
    (hTlloc : ∀ τ ∈ 𝒯M, ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, Tl τ Y (p, g) = Tl τ Y (p', g))
    (hTlsrc : ∀ τ ∈ 𝒯M, ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ z ∈ Y, g z = g' z) → Tl τ Y (p, g) = Tl τ Y (p, g'))
    {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} (hGa : IsLevel Ga (k + 1))
    (jM : τι → ℕ) (XM : τι → Set (CTorus d L N₁ m₁ (k + 1)))
    (EbM : τι → ℝ) (hEb0 : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {κ₀ ρM : ℝ}
    (hρM : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯M.filter (fun τ => yM τ = x),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ)) ≤ ρM)
    {γ κdec : ℝ} (hγ : 0 ≤ γ) (hκ : P.κ ≤ 2 * κdec)
    (hBM : Real.sqrt N * (γ * ρM) <
      P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hTlbd : ∀ τ ∈ 𝒯M, ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 → ∀ i, ‖Tl τ Y (p, g) i‖ ≤ EbM τ * γ *
        Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ) - 2 * κdec * treeLenCov Ga P.m₀ Y))
    (hTlrot : ∀ τ ∈ 𝒯M, ∀ Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ,
      Qᵀ * Q = 1 →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 →
      Tl τ Y ((rotField (cmat Q) p.1, rotField (cmat Q) p.2), rotField (cmat Q) g) =
        (cmat Q) *ᵥ Tl τ Y (p, g))
    (AM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hAM : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        ∑ τ ∈ 𝒯M.filter (fun τ => yM τ = (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)), Tl τ
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g)) :
    -- `analyticM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => Tm.M (k + 1) x X p.1 p.2.1 p.2.2)
        {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}) ∧
    -- `rotM`, real matrices, sources of `ℓ¹` norm `< 1`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h g, Def6.l1 g < 1 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.M (k + 1) x X (rotField R Ψ) (rotField R h) (rotField R g) =
        R *ᵥ Tm.M (k + 1) x X Ψ h g) ∧
    -- `eucM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.M (k + 1) (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) =
        Tm.M (k + 1) x X Ψ h g) ∧
    -- `localM`
    (∀ x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      Tm.M (k + 1) x X Ψ h g = Tm.M (k + 1) x X Ψ' h' g') ∧
    -- `boundM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ Ψ h g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h → Def6.l1 g < 1 →
      vn (Tm.M (k + 1) x X Ψ h g) <
        P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) := by
  have hρM0 : ∀ x : CTorus d L N₁ m₁ (k + 1), ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 →
      vn (∑ τ ∈ 𝒯M.filter (fun τ => yM τ = x), Tl τ Y (p, g)) ≤
        Real.sqrt N * (γ * ρM) * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by
    intro x Y hY p g hp hg
    set t := treeLenCovOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) P.m₀ (k + 1) Y with ht
    have ht0 : 0 ≤ t := treeLenCovOne_nonneg _ _ _
    have hconv : treeLenCov Ga P.m₀ Y = t := treeLenCov_eq_treeLenCovOne hGa P.m₀ Y
    have hvn : ∀ τ ∈ 𝒯M.filter (fun τ => yM τ = x), vn (Tl τ Y (p, g)) ≤
        Real.sqrt N * (EbM τ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ)) *
          (γ * Real.exp (-2 * κdec * t))) := by
      intro τ hτ
      have hτ' := (Finset.mem_filter.1 hτ).1
      have hb := hTlbd τ hτ' Y hY p g hp hg
      have e : EbM τ * γ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ) -
          2 * κdec * treeLenCov Ga P.m₀ Y) =
          EbM τ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ)) *
            (γ * Real.exp (-2 * κdec * t)) := by
        rw [hconv, sub_eq_add_neg, Real.exp_add]
        ring_nf
      have h0 : 0 ≤ EbM τ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ)) *
          (γ * Real.exp (-2 * κdec * t)) :=
        mul_nonneg (mul_nonneg (hEb0 τ hτ') (Real.exp_pos _).le)
          (mul_nonneg hγ (Real.exp_pos _).le)
      exact vn_le_sqrt_mul h0 fun i => (hb i).trans (le_of_eq e)
    have hq : 0 ≤ γ * Real.exp (-2 * κdec * t) := mul_nonneg hγ (Real.exp_pos _).le
    rw [Finset.sum_fn]
    refine (vn_sum_le _ _).trans ((Finset.sum_le_sum hvn).trans ?_)
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hexp : Real.exp (-2 * κdec * t) ≤ Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by
      refine Real.exp_le_exp.2 ?_
      unfold sizeJ
      rw [← ht]
      nlinarith
    calc Real.sqrt N * ((∑ τ ∈ 𝒯M.filter (fun τ => yM τ = x),
          EbM τ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jM τ) (XM τ))) *
          (γ * Real.exp (-2 * κdec * t)))
        ≤ Real.sqrt N * (ρM * (γ * Real.exp (-2 * κdec * t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hρM x) hq)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt N * (γ * ρM) * Real.exp (-2 * κdec * t) := by ring
      _ ≤ Real.sqrt N * (γ * ρM) * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by
          refine mul_le_mul_of_nonneg_left hexp ?_
          have : 0 ≤ ρM := le_trans (Finset.sum_nonneg fun τ hτ => mul_nonneg
            (hEb0 τ (Finset.mem_filter.1 hτ).1) (Real.exp_pos _).le) (hρM x)
          positivity
  exact localClass_termClausesM hN HB Yp hYp Tm hgs cpl hcpl
    (fun x Y q => ∑ τ ∈ 𝒯M.filter (fun τ => yM τ = x), Tl τ Y q)
    (fun x Y hY q hq => Finset.analyticAt_fun_sum _ fun τ hτ =>
      hTlan τ (Finset.mem_filter.1 hτ).1 Y hY q hq)
    (fun x Y hY p p' hp hp' hpp g => Finset.sum_congr rfl fun τ hτ =>
      hTlloc τ (Finset.mem_filter.1 hτ).1 Y hY p p' hp hp' hpp g)
    (fun x Y p g g' hgg => Finset.sum_congr rfl fun τ hτ =>
      hTlsrc τ (Finset.mem_filter.1 hτ).1 Y p g g' hgg)
    hBM (fun x Y hY _ p g hp hg => hρM0 x Y hY p g hp hg)
    (fun x Y hY Q hQ p g hp hg => by
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun τ hτ => hTlrot τ (Finset.mem_filter.1 hτ).1 Y hY Q hQ p g hp hg)
    AM hAM hM


/-- **The averaged completed source term is the recomputed source term on the class domain** if the
recomputed source terms are covariant under the paving group on the class domains (the analogue of
`localClass_avg_eq_of_cov`; not used by the term clauses of `localClass_termClausesM`). -/
theorem localClass_avgM_eq_of_cov {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ Y z, z ∈ Yp Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y) p).2 z))
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (hTMcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      TM (r x) (r '' Y) ((actField r p.1, actField r p.2), actField r g) = TM x Y (p, g))
    (AM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hAM : ∀ x Y q, AM x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ q.2))
    {x : CTorus d L N₁ m₁ (k + 1)} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsPolyDom P.m₀ (k + 1) Y)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N} (g : Fld d L N₁ m₁ (k + 1) N)
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2) :
    AM x Y (p, g) = TM x Y (p, g) := by
  have hc : (Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
      (k + 1)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g) = TM x Y (p, g) := by
    intro s
    have hs : ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) := inv_mem s.2
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' Y) := (isPolyDom_image_iff hN hs Y).2 hY
    have hp' : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom
        (k + 1) (localB (k + 1) (le_refl (k + 1))
          (Yp (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)) (le_refl (minSep L (L ^ m₁))))
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) :=
      localB_collar_xiDom_act (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hs (hYp Y)
        (hYp (_ '' Y)) hp
    obtain ⟨-, c2⟩ := fieldDom_completion_spec
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))) (k + 1)
      (localB (k + 1) (le_refl (k + 1))
          (Yp (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)) (le_refl (minSep L (L ^ m₁))))
      (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
      (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
        Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)) (hcpl _) (fun q hq => xiDom_mem_layerSub hq)
    rw [hTMloc _ _ hY' _ _ (c2 _ hp').1 hp' (c2 _ hp').2]
    exact hTMcov _ hs x Y hY p g hp
  have hAM' := hAM x Y (p, g)
  simp only at hAM'
  rw [hAM', Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

end AssembleM

end Balaban.Localization
