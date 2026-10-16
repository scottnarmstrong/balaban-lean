/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassAssembly
public import Balaban.Fluctuation.LocalClassSum

/-!
# The E-part of the local successor class at the new level: the assembly

The new energy terms of the local successor class at the level `k + 1` (blocker 6) are built from
the recomputed terms `T_τ(Y)` of the old labels `τ` on the local generating sets
`𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺` of the polymers `Y ∈ 𝒟_{k+1}` (`localB_eTermHat_evTerm_*`), in
three steps: the sum over the labels `T(Y) = Σ_τ T_τ(Y)`, the completion off the class domain and
the average over the paving group (`localB_avg_completion`), and the uniform distribution over the
`L^{k+1}`-aligned sites of `Y` (`LocalClassAssembly.lean`).  This file composes the landed clauses
of the three steps into the fields at `j = k + 1` of `SFTermClausesStrong`.

* `exists_cmat_of_isRot_real`: a real matrix with `IsRot` is the complexification of a real
  orthogonal matrix (the real half of the clause `rotE`);
* `localClass_termClausesE`: from the per-polymer hypotheses on `T` (analytic, local and bounded on
  the class domain, invariant under real rotations there), the slices at `j = k + 1` of `gs_spec`,
  `gsStrong`, `pavingGS`, `analyticE`, `rotE` (real matrices), `eucE`, `localE`, `boundE` for the
  averaged, completed, distributed terms.  The paving covariance of `T` is not needed: the average
  is covariant for all pairs of fields, and the rotation clause compares points of the domain, where
  each completed term equals `T`;
* `localClass_avg_eq_of_cov`: the averaged completed term equals `T` on the class domain if `T` is
  covariant under the paving group on the class domains (needed for the density, not for the term
  clauses);
* `localClass_termClausesE_of_labels`, `localClass_avg_eq_sum_of_cov`: the same for
  `T(Y) = Σ_{τ ∈ 𝒯E} T_τ(Y)`, from per-label hypotheses in the form of the landed per-label
  theorems (`localB_eTermHat_evTerm_xiFieldDom`, `localB_eTermHat_evTerm_local`,
  `localB_eTermHat_evTerm_rot`, `localB_eTermHat_evTerm_paving_tau` with a relabelling of the old
  labels) and the resummation of `norm_sum_rooted_le_boundE`.

Not covered here: the complex rotations of `rotE` (`SO(N, ℂ)`), the density covariance `eucEloc`,
the levels `j ≤ k` (inherited terms), and the M-part.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

section Rot

variable {N : ℕ}

/-- A real matrix of `IsRot` is the complexification of a real orthogonal matrix. -/
theorem exists_cmat_of_isRot_real {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    (hre : ∀ i j, (R i j).im = 0) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 ∧ R = cmat Q := by
  have hRQ : R = cmat (R.map Complex.re) := by
    ext i j
    exact Complex.ext (by simp [cmat]) (by simp [cmat, hre i j])
  refine ⟨R.map Complex.re, ?_, hRQ⟩
  have h1 : cmat ((R.map Complex.re)ᵀ * R.map Complex.re) = cmat 1 := by
    have e : cmat ((R.map Complex.re)ᵀ * R.map Complex.re) =
        (cmat (R.map Complex.re))ᵀ * cmat (R.map Complex.re) := by
      simp only [cmat]
      rw [← Matrix.transpose_map]
      exact Matrix.map_mul (f := Complex.ofRealHom)
    rw [e, ← hRQ, hR.1]
    ext i j
    by_cases h : i = j <;> simp [cmat, Matrix.one_apply, h]
  ext i j
  have := congrFun (congrFun h1 i) j
  simpa [cmat] using this

end Rot

section AssembleE

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
/-- Rotations act pointwise and commute with the action of permutations of the torus. -/
theorem actField_rotField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
    (R : Matrix (Fin N) (Fin N) ℂ) (Ψ : Fld d L N₁ m₁ (k + 1) N) :
    actField s (rotField R Ψ) = rotField R (actField s Ψ) := rfl


open Classical in
/-- **The E-fields of the local successor class at the new level `k + 1`** (blocker 6, the
assembly).  Setting: the class index `5 L M₁ = minSep L (L ^ m₁)`, the generating set of a polymer
`Y ∈ 𝒟_{k+1}` is `𝔹_{k+1}(Y⁺) = localB (k + 1) … (Yp Y)` (`hgs`, `Y⁺` the collar `hYp`), the class
domain is `xiFieldDom a ν εseq`.  Let `T Y` be the recomputed term of the polymer `Y` (in the
application the sum over the old labels, `localClass_termClausesE_of_labels`), with, for polymers
`Y ∈ 𝒟_{k+1}` and on the class domain of `𝔹_{k+1}(Y⁺)`:
* `hTan`: analyticity;
* `hTloc`: dependence on the restriction to `Y` only;
* `hTbd`: the bound `E₀ e^{-κ d_{k+1}(Y)}` of the class;
* `hTrot`: invariance under real orthogonal `Q`.
Let `A Y` be the average over the paving group of the completed terms `T (s⁻¹ Y) ∘ cpl (s⁻¹ Y) ∘ s⁻¹`
(`localB_avg_completion`) and let the class term be `A Y` distributed uniformly over the `L^{k+1}`-
aligned sites of `Y` (`hE`, `LocalClassAssembly.lean`).  Then the slices at `j = k + 1` of the
clauses `gs_spec`, `gsStrong`, `pavingGS`, `analyticE`, `rotE` (for the real matrices of `IsRot`),
`eucE`, `localE` and `boundE` of `SFTermClausesStrong` hold.  The paving covariance of `T` is not
needed for these clauses (it identifies `A Y` with `T Y` on the class domain:
`localClass_avg_eq_of_cov`). -/
theorem localClass_termClausesE {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    (T : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTan : ∀ Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (T Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTloc : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T Y p = T Y p')
    (hTbd : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖T Y p‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTrot : ∀ Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      T Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = T Y p)
    (A : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hA : ∀ Y p, A Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        T (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ (k + 1)) z)).card : ℕ) : ℂ)⁻¹ * A Y (Ψ, h) else 0) :
    -- `gs_spec`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      X ⊆ ↑((Tm.gs (k + 1) X).Ω 1) ∧ ∀ i, k + 1 < i → (Tm.gs (k + 1) X).Ω i = ∅) ∧
    -- `gsStrong`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      GsSpecStrong (k + 1) (le_refl (k + 1)) X (Tm.gs (k + 1) X)) ∧
    -- `pavingGS`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ i,
        (((Tm.gs (k + 1) (r '' X)).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1))) =
          r '' (((Tm.gs (k + 1) X).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1)))) ∧
    -- `analyticE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      AnalyticOnNhd ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Tm.E (k + 1) y X p.1 p.2)
        {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2}) ∧
    -- `rotE`, real matrices
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.E (k + 1) y X (rotField R Ψ) (rotField R h) = Tm.E (k + 1) y X Ψ h) ∧
    -- `eucE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.E (k + 1) (blockBase L (k + 1) (r y)) (r '' X) (actField r Ψ) (actField r h) =
        Tm.E (k + 1) y X Ψ h) ∧
    -- `localE`
    (∀ y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      Tm.E (k + 1) y X Ψ h = Tm.E (k + 1) y X Ψ' h') ∧
    -- `boundE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      ‖Tm.E (k + 1) y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) := by
  set G : Set (CTorus d L N₁ m₁ (k + 1)) → GeneratingSet d L (N₁ * L ^ m₁) (k + 1)
    (minSep L (L ^ m₁)) :=
    fun Y => localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))) with hG
  set D : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom
      (k + 1) (G Y) p.1 p.2 with hD
  have hDL : ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      p ∈ layerSub (G Y) := fun Y p hp => xiDom_mem_layerSub hp
  have hdom : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      D (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    localB_collar_xiDom_act (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp Y)
      (hYp (r '' Y)) hp
  set f : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      ℂ := fun Y p => T Y (cpl Y p) with hf
  have hA' : ∀ Y p, A Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
          Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) := hA
  -- the completion facts at a polymer
  have hext : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N, D Y p → f Y p = T Y p) ∧
      AnalyticOnNhd ℂ (f Y) {p | D Y p} := fun Y hY => by
    obtain ⟨-, e2, e3⟩ := xiFieldDom_completion_extension HB (k + 1) (G Y) Y (cpl Y) (hcpl Y)
      (T Y) (hTan Y hY) (hTloc Y hY)
    exact ⟨e2, e3⟩
  -- locality of the completed terms, all sets
  have hfloc : ∀ Y (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → f Y p = f Y p' := fun Y p p' hpp => by
    obtain ⟨c1, -⟩ := fieldDom_completion_spec _ (k + 1) (G Y) Y (cpl Y) (hcpl Y) (hDL Y)
    simp only [hf]
    rw [c1 p.1 p'.1 p.2 p'.2 hpp]
  -- the polymer domain family, carried into itself by the paving group
  set D' : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => IsPolyDom P.m₀ (k + 1) Y ∧ D Y p with hD'
  have hdom' : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D' Y p →
      D' (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    ⟨(isPolyDom_image_iff hN hr Y).2 hp.1, hdom r hr Y p hp.2⟩
  have hfan : ∀ Y, AnalyticOnNhd ℂ (f Y) {p | D' Y p} := fun Y p hp =>
    (hext Y hp.1).2 p hp.2
  have hAcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      A (r '' Y) (actField r p.1, actField r p.2) = A Y p := fun r hr =>
    avgTerm_act (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f A
      hA' hr
  have hAloc := avgTerm_local (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f A hA' hfloc
  have hAan := avgTerm_analytic (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f A hA' D' hdom' hfan
  have hAbd := avgTerm_bound (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f A hA' D' hdom'
    (fun Y => P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y)) (boundE_paving_invariant hN P.E₀ P.κ)
    (fun Y p hp => by rw [(hext Y hp.1).1 p hp.2]; exact hTbd Y hp.1 p hp.2)
  refine ⟨fun X _ => ?_, fun X _ => ?_, fun X _ r hr i => ?_, fun y X hX hy => ?_,
    fun y X hX hy R hR hre Ψ h h1 h2 => ?_, fun y X hX hy r hr Ψ h _ _ => ?_,
    fun y X Ψ Ψ' h h' hX => ?_, fun y X hX hy Ψ h h1 => ?_⟩
  · rw [hgs]
    exact localB_collar_gs_spec (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) (hYp X)
  · rw [hgs]
    exact localB_collar_gsSpecStrong_of_subset (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁)))
      (hYp X)
  · rw [hgs, hgs]
    exact localB_collar_pavingGS (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp X)
      (hYp (r '' X)) i
  · have hEf : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Tm.E (k + 1) y X p.1 p.2) = fun p => ((((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
          (fun z => z ∈ X ∧ Aligned (L ^ (k + 1)) z)).card : ℕ) : ℂ)⁻¹ * A X p := by
      funext p
      rw [hE]
      simp [hy]
    rw [hEf, hgs]
    intro p hp
    exact analyticAt_const.mul (hAan X p ⟨hX, hp⟩)
  · obtain ⟨Q, hQ, rfl⟩ := exists_cmat_of_isRot_real hR hre
    rw [hE, hE]
    simp only [hy, ↓reduceIte]
    congr 1
    rw [hgs] at h1 h2
    rw [hA', hA']
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hs : ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
      inv_mem s.2
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' X) := (isPolyDom_image_iff hN hs X).2 hX
    have hp1 := hdom _ hs X (Ψ, h) h1
    have hp2 := hdom _ hs X (rotField (cmat Q) Ψ, rotField (cmat Q) h) h2
    simp only at hp1 hp2
    rw [actField_rotField, actField_rotField] at hp2 ⊢
    rw [(hext _ hY').1 _ hp2, (hext _ hY').1 _ hp1]
    exact hTrot _ hY' Q hQ _ hp1
  · exact assembly_eucE hN (fun Y p => A Y p) hAcov (Tm.E (k + 1)) hE
      hr hX hy Ψ h
  · exact assembly_local (fun Y p => A Y p) (fun Y Ψ Ψ' h h' hY => hAloc Y _ _ hY)
      (Tm.E (k + 1)) hE y X Ψ Ψ' h h' hX
  · refine (assembly_norm_le (fun Y p => A Y p) (Tm.E (k + 1)) hE y X Ψ h).trans ?_
    rw [hgs] at h1
    exact hAbd X (Ψ, h) ⟨hX, h1⟩


/-- **The averaged completed term is the recomputed term on the class domain** if the recomputed
terms of the polymers are covariant under the paving group on the class domains (item 5 of
`localB_avg_completion`, with the hypotheses on polymers only).  This identification is not used by
the term clauses of `localClass_termClausesE`; it is what makes the class terms the terms of the
renormalization step (the density (H.1)). -/
theorem localClass_avg_eq_of_cov {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    (T : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTan : ∀ Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (T Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTloc : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T Y p = T Y p')
    (hTcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ Y, IsPolyDom P.m₀ (k + 1) Y → ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      T (r '' Y) (actField r p.1, actField r p.2) = T Y p)
    (A : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hA : ∀ Y p, A Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        T (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : IsPolyDom P.m₀ (k + 1) Y)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2) :
    A Y p = T Y p := by
  set D : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => IsPolyDom P.m₀ (k + 1) Y ∧
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 with hD
  set f : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      ℂ := fun Y p => T Y (cpl Y p) with hf
  have he : ∀ Y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y q → f Y q = T Y q :=
    fun Y q hq => (xiFieldDom_completion_extension HB (k + 1)
      (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) Y (cpl Y) (hcpl Y)
      (T Y) (hTan Y hq.1) (hTloc Y hq.1)).2.1 q hq.2
  have hcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ Y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y q →
      f (r '' Y) (actField r q.1, actField r q.2) = f Y q := fun r hr Y q hq => by
    have hq' : D (r '' Y) (actField r q.1, actField r q.2) :=
      ⟨(isPolyDom_image_iff hN hr Y).2 hq.1,
        localB_collar_xiDom_act (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp Y)
          (hYp (r '' Y)) hq.2⟩
    rw [he _ _ hq', he _ _ hq]
    exact hTcov r hr Y hq.1 q hq.2
  rw [avgTerm_eq_of_cov (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))
    f A hA D hcov Y p ⟨hY, hp⟩]
  exact he Y p ⟨hY, hp⟩


open Classical in
/-- **The E-fields of the local successor class from the per-label terms** (`localClass_termClausesE`
for the sum `T Y = Σ_{τ ∈ 𝒯E} T_τ Y` of the recomputed terms of the old labels).  Per-label
hypotheses, for polymers `Y ∈ 𝒟_{k+1}` and on the class domain of `𝔹_{k+1}(Y⁺)`, in the form of the
landed per-label theorems (for the term `T_τ Y p = evTerm … Y (clipRaw 𝔹_{k+1}(Y⁺) p)`):
* `hTlan`: analyticity (`localB_eTermHat_evTerm_xiFieldDom`, clause 1);
* `hTlloc`: locality on the domain (`localB_eTermHat_evTerm_local`);
* `hTlbd`: the per-label bound `Eb_τ γ e^{-κ₀ d_{j_τ}(X_τ) - 2 κ_dec d̃^cov(Y)}`
  (`localB_eTermHat_evTerm_xiFieldDom`, clause 2);
* `hTl0`: the term vanishes unless its root lies in `Y` (`evTerm_eq_zero_of_not_subset`, roots in
  `X₁(τ)`);
* `hTlrot`: invariance under real orthogonal `Q` (`localB_eTermHat_evTerm_rot`).
Numerical hypotheses of the resummation (`norm_sum_rooted_le_boundE`): the ambient generating set
`Ga` of level `k + 1`, per-site sums of `Eb_τ e^{-κ₀ d_{j_τ}(X_τ)}` at most `ρ_E`
(`classE_siteSum_le` for the class labels), `γ ρ_E c₁ (L^{k+1} L^{m₀+m₁})^d ≤ E₀` and
`κ ≤ 2 κ_dec - 1` for the constants `E₀`, `κ` of the class. -/
theorem localClass_termClausesE_of_labels {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι)
    (Tl : τι → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTlan : ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (Tl τ Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTlloc : ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → Tl τ Y p = Tl τ Y p')
    {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} (hGa : IsLevel Ga (k + 1))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (jE : τι → ℕ) (XE : τι → Set (CTorus d L N₁ m₁ (k + 1)))
    (EbE : τι → ℝ) (hEb0 : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {κ₀ ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jE τ) (XE τ)) ≤ ρE)
    {γ κdec : ℝ} (hγ : 0 ≤ γ) (hκ : P.κ ≤ 2 * κdec - 1)
    (hE₀ : γ * ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d ≤ P.E₀)
    (hTlbd : ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖Tl τ Y p‖ ≤ EbE τ * γ * Real.exp (-κ₀ * treeLenCovOne P.m₀ (jE τ) (XE τ) -
        2 * κdec * treeLenCov Ga P.m₀ Y))
    (hTl0 : ∀ τ ∈ 𝒯E, ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      rE τ ∉ Y → Tl τ Y p = 0)
    (hTlrot : ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ,
      Qᵀ * Q = 1 → ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Tl τ Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = Tl τ Y p)
    (A : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hA : ∀ Y p, A Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        ∑ τ ∈ 𝒯E, Tl τ (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ (k + 1)) z)).card : ℕ) : ℂ)⁻¹ * A Y (Ψ, h) else 0) :
    -- `gs_spec`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      X ⊆ ↑((Tm.gs (k + 1) X).Ω 1) ∧ ∀ i, k + 1 < i → (Tm.gs (k + 1) X).Ω i = ∅) ∧
    -- `gsStrong`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      GsSpecStrong (k + 1) (le_refl (k + 1)) X (Tm.gs (k + 1) X)) ∧
    -- `pavingGS`
    (∀ X, IsPolyDom P.m₀ (k + 1) X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ i,
        (((Tm.gs (k + 1) (r '' X)).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1))) =
          r '' (((Tm.gs (k + 1) X).Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) :
            Set (CTorus d L N₁ m₁ (k + 1)))) ∧
    -- `analyticE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      AnalyticOnNhd ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Tm.E (k + 1) y X p.1 p.2)
        {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2}) ∧
    -- `rotE`, real matrices
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.E (k + 1) y X (rotField R Ψ) (rotField R h) = Tm.E (k + 1) y X Ψ h) ∧
    -- `eucE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.E (k + 1) (blockBase L (k + 1) (r y)) (r '' X) (actField r Ψ) (actField r h) =
        Tm.E (k + 1) y X Ψ h) ∧
    -- `localE`
    (∀ y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      Tm.E (k + 1) y X Ψ h = Tm.E (k + 1) y X Ψ' h') ∧
    -- `boundE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      ‖Tm.E (k + 1) y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) :=
  localClass_termClausesE hN HB Yp hYp Tm hgs cpl hcpl (fun Y p => ∑ τ ∈ 𝒯E, Tl τ Y p)
    (fun Y hY => fun p hp => Finset.analyticAt_fun_sum _ fun τ hτ => hTlan τ hτ Y hY p hp)
    (fun Y hY p p' hp hp' hpp => Finset.sum_congr rfl fun τ hτ => hTlloc τ hτ Y hY p p' hp hp' hpp)
    (fun Y hY p hp => norm_sum_rooted_le_boundE 𝒯E hGa hN hY rE jE XE EbE hEb0 hρE0 hρE hγ hκ hE₀
      (fun τ p => Tl τ Y p) p (fun τ hτ => hTlbd τ hτ Y hY p hp) (fun τ hτ hn => hTl0 τ hτ Y p hn))
    (fun Y hY Q hQ p hp => Finset.sum_congr rfl fun τ hτ => hTlrot τ hτ Y hY Q hQ p hp)
    A hA hE

/-- **The averaged completed sum is the sum of the recomputed terms on the class domain**, from the
per-label paving covariance with a relabelling of the labels (`localClass_avg_eq_of_cov`).  For
every paving symmetry `r` a bijection `π` of the label set with `T_{π τ}(r Y)(r p) = T_τ(Y)(p)` on
the class domain (`localB_eTermHat_evTerm_paving_tau`, the old label `(j, y, X)` going to
`(j, r y, r X)`). -/
theorem localClass_avg_eq_sum_of_cov {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι)
    (Tl : τι → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTlan : ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (Tl τ Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTlloc : ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → Tl τ Y p = Tl τ Y p')
    (hTlcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∃ π : τι → τι, Set.BijOn π ↑𝒯E ↑𝒯E ∧ ∀ τ ∈ 𝒯E, ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
        ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
        Tl (π τ) (r '' Y) (actField r p.1, actField r p.2) = Tl τ Y p)
    (A : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hA : ∀ Y p, A Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        ∑ τ ∈ 𝒯E, Tl τ (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : IsPolyDom P.m₀ (k + 1) Y)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2) :
    A Y p = ∑ τ ∈ 𝒯E, Tl τ Y p :=
  localClass_avg_eq_of_cov (T := fun Y p => ∑ τ ∈ 𝒯E, Tl τ Y p) hN HB Yp hYp cpl hcpl
    (fun Y hY => fun p hp => Finset.analyticAt_fun_sum _ fun τ hτ => hTlan τ hτ Y hY p hp)
    (fun Y hY p p' hp hp' hpp => Finset.sum_congr rfl fun τ hτ => hTlloc τ hτ Y hY p p' hp hp' hpp)
    (fun r hr Y hY q hq => by
      obtain ⟨π, hπ, hcov⟩ := hTlcov r hr
      exact (Finset.sum_nbij π (fun τ hτ => hπ.mapsTo hτ) hπ.injOn hπ.surjOn
        (fun τ hτ => (hcov τ hτ Y hY q hq).symm)).symm)
    A hA hY hp

end AssembleE

end Balaban.Localization
