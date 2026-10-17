/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityCentre
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source terms of the new level, completed in the larger local chart

The source terms of the new level (`localClass_termClausesM`, `localClass_site_Mloc_eq`,
`localClass_eucMloc_site`) with the completion taken in the larger local chart
`Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, εL_{k+1})`, `ε_{k+1} ≤ εL_{k+1}` (`LocalClassDensityChart.lean`).  The term
`TM x Y` is analytic and bounded and equivariant under real rotations on the class chart (radius
`ε`), and depends only on the restriction of the pair to `Y` on the larger chart (radius `εL`).

* `mloc_eq_of_avg_terms`: the combinatorial core of the per-site identity;
* `localClass_termClausesM_chart`: the slices at `j = k + 1` of `analyticM`, `rotM` (real
  matrices, sources of `ℓ¹` norm `< 1`), `eucM`, `localM`, `boundM`;
* `localClass_site_Mloc_eq_chart`: `Mloc_{k+1}(x) = 𝒟_M(x)` on the whole-level domain at the class
  radius (inputs `hchart` into the larger charts, `hDM`, `hDMcov`);
* `localClass_eucMloc_site_chart`: `eucMloc` at `j = k + 1` for `fullJSymGroup L (k + 1)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **Averaged source terms whose polymer sums give a covariant density sum to the density** (the
analogue of `eloc_eq_of_avg_terms` for `Mloc`, with a source `g`). -/
theorem mloc_eq_of_avg_terms {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))] {ϱ : ℝ}
    (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (S : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop)
    (hS : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N, S q →
        S (actField r q.1, actField r q.2))
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g, S q →
      ∑ᶠ Y ∈ polysAt m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g, S q →
        S (actField r q.1, actField r q.2) →
        DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g))
    (x : CTorus d L N₁ m₁ (k + 1)) {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : S p) (g : Fld d L N₁ m₁ (k + 1) N)
    (hterm : ∀ Y ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) x,
      Tm.M (k + 1) x Y p.1 p.2 g =
        ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀
          (k + 1)) : ℂ))⁻¹ •
        ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
          TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
            (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
                actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g)) :
    Mloc m₀ Tm (k + 1) x p.1 p.2 g = DM x (p, g) := by
  have hfin : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) x).Finite :=
    Set.toFinite _
  have hinner : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∑ Y ∈ hfin.toFinset,
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g) = DM x (p, g) := by
    intro s
    set t : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)) := (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹
      with ht
    have hts : t ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1) :=
      inv_mem s.2
    have hti : t⁻¹ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1) :=
      inv_mem hts
    have hq := hS t hts p hp
    have hbij : Set.BijOn (fun Y => (⇑t) '' Y)
        (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) x)
        (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) (t x)) := by
      refine ⟨fun Y hY => ⟨(isPolyDom_image_iff hN hts Y).2 hY.1, Set.mem_image_of_mem _ hY.2⟩,
        fun Y _ Y' _ hYY => Set.image_injective.2 t.injective hYY, fun Y' hY' => ?_⟩
      refine ⟨(⇑(t⁻¹)) '' Y', ⟨(isPolyDom_image_iff hN hti Y').2 hY'.1,
        ⟨t x, hY'.2, by simp [Equiv.Perm.inv_def]⟩⟩, ?_⟩
      simp only
      rw [Set.image_image]
      simp [Equiv.Perm.inv_def]
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_of_bijOn
        (g := fun Y' => TM (t x) Y' ((actField t p.1, actField t p.2), actField t g))
        (fun Y => (⇑t) '' Y) hbij fun Y _ => rfl,
      hDM _ _ _ hq]
    exact hDMcov t hts x p g hp hq
  have hc : (Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀
      (k + 1)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Mloc
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.smul_sum,
    Finset.sum_comm]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

open Classical in
/-- **The M-fields of the new level, completed in the larger local chart** (the analogue of
`localClass_termClausesM` with the completion `cpl` in `xiFieldDom a ν εL`, `ε_{k+1} ≤ εL_{k+1}`):
analyticity (`hTMan`), the bound (`hTMbd`, `B_M < c₉ ξ_{k+1}^{(d-2)/2 + γ - α₁}`) and the
equivariance under real orthogonal `Q` (`hTMrot`) on the class chart, the locality in the pair
(`hTMloc`) on the larger chart, the locality in the source (`hTMsrc`) for all pairs.  Then the
slices at `j = k + 1` of `analyticM`, `rotM` (real matrices, `‖g‖₁ < 1`), `eucM`, `localM`, `boundM`
hold for `Tm.M (k + 1) x Y = AM x Y`. -/
theorem localClass_termClausesM_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq εL : ℕ → ℝ} (hεL : εseq (k + 1) ≤ εL (k + 1))
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
        (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
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
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
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
  set G : Set (CTorus d L N₁ m₁ (k + 1)) → GeneratingSet d L (N₁ * L ^ m₁) (k + 1)
    (minSep L (L ^ m₁)) :=
    fun Y => localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁))) with hG
  set D : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom
      (k + 1) (G Y) p.1 p.2 with hD
  have hDL₂ : ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (G Y) p.1 p.2 → p ∈ layerSub (G Y) := fun Y p hp => xiDom_mem_layerSub hp
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
  -- the completed terms: equal to the terms on the class domain, analytic there, local
  have hcomp : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g, D Y p →
        f x Y (p, g) = TM x Y (p, g)) ∧
      AnalyticOnNhd ℂ (f x Y) ({p | D Y p} ×ˢ {g | Def6.l1 g < 1}) := fun x Y hY => by
    obtain ⟨e, ha⟩ := fieldDom_completion_analytic_param_of_sub
      (xiFieldDom a ν εseq) (xiFieldDom a ν εL) (k + 1) (G Y) Y (cpl Y) (hcpl Y)
      (fun p hp => xiFieldDom_dom_of_eps_le hεL hp) (hDL₂ Y) (fun _ hp => xiDom_eventually HB hp)
      (TM x Y) (hTMan x Y hY) (hTMloc x Y hY)
    exact ⟨fun p g hp => e p (xiFieldDom_dom_of_eps_le hεL hp) g, ha⟩
  have hfloc : ∀ x Y
      (q q' : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N),
      (∀ z ∈ Y, q.1.1 z = q'.1.1 z ∧ q.1.2 z = q'.1.2 z ∧ q.2 z = q'.2 z) →
      f x Y q = f x Y q' := fun x Y q q' hqq => by
    obtain ⟨c1, -⟩ := fieldDom_completion_spec _ (k + 1) _ Y (cpl Y) (hcpl Y) (hDL₂ Y)
    have e := c1 q.1.1 q'.1.1 q.1.2 q'.1.2 fun z hz => ⟨(hqq z hz).1, (hqq z hz).2.1⟩
    simp only [Prod.mk.eta] at e
    simp only [hf]
    rw [e]
    exact hTMsrc x Y _ _ _ fun z hz => (hqq z hz).2.2
  have hinv : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
    fun s => inv_mem s.2
  -- the term of one element of the group, at a pair of the class domain
  have hterm : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ x X, IsPolyDom P.m₀ (k + 1) X → ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
        (g : Fld d L N₁ m₁ (k + 1) N), D X p →
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g) =
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g) :=
    fun s x X hX p g hp => (hcomp _ _ ((isPolyDom_image_iff hN (hinv s) X).2 hX)).1 _ _
      (hdom _ (hinv s) X p hp)
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
          ((hcomp _ _ ((isPolyDom_image_iff hN (hinv s) X).2 hX)).2 _
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
    rw [hterm s x X hX (rotField (cmat Q) Ψ, rotField (cmat Q) h) _ h2,
      hterm s x X hX (Ψ, h) g h1]
    simp only at hp1 ⊢
    rw [actField_rotField, actField_rotField, actField_rotField]
    exact hTMrot _ _ hY' Q hQ _ _ hp1 (by rw [l1_actField]; exact hg)
  · -- `eucM`
    rw [hM, hM]
    exact avgTermM_act _ f AM hAM' hr x X ((Ψ, h), g)
  · -- `localM`
    rw [hM, hM, hAM', hAM']
    congr 1
    refine Finset.sum_congr rfl fun s _ => hfloc _ _ _ _ fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [actField, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact hX y hy
  · -- `boundM`
    rw [hgs] at h1
    rw [hM, hAM']
    refine (le_of_eq (vn_smul_complex _ _)).trans_lt ?_
    have hc : (0 : ℝ) < Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d)
        L P.m₀ (k + 1)) := by exact_mod_cast Fintype.card_pos
    have hb : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
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
      rw [hterm s x X hX (Ψ, h) g h1, ← sizeJ_image hN (hinv s) X]
      exact hTMbd _ _ hY' (Set.mem_image_of_mem _ hx) _ _ (hdom _ (hinv s) X (Ψ, h) h1)
        (by rw [l1_actField]; exact hg)
    have hsum := (vn_sum_le Finset.univ fun s : pavingSymGroup (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (d := d) L P.m₀ (k + 1) =>
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' X)
          ((actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ Ψ,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ h),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ g)).trans
      (Finset.sum_le_sum fun s _ => hb s)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hsum' : vn (∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
        (k + 1),
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
    rw [norm_inv, Complex.norm_natCast]
    have hle := mul_le_mul_of_nonneg_left hsum' (inv_nonneg.2 hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hle
    exact hle.trans_lt (mul_lt_mul_of_pos_right hBM (Real.exp_pos _))

open Classical in
/-- **The per-site identity of the source terms, with the completion in the larger chart**: for
the class terms of `localClass_termClausesM_chart`, at every pair `p` of the whole-level domain at
the class radius and every source, `Mloc_{k+1}(x)(p, g) = 𝒟_M(x)(p, g)`, from the inclusion
`hchart` of that domain in the larger charts, the expansion `hDM` and the paving covariance
`hDMcov`. -/
theorem localClass_site_Mloc_eq_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq εL : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
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
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
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
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g))
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g))
    (x : CTorus d L N₁ m₁ (k + 1)) {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      p.1 p.2) (g : Fld d L N₁ m₁ (k + 1) N) :
    Mloc P.m₀ Tm (k + 1) x p.1 p.2 g = DM x (p, g) := by
  refine mloc_eq_of_avg_terms hN Tm (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2) (fun r hr q hq => xiFieldDom_levelGS_act hr hq) TM DM hDM hDMcov x hp g
    fun Y hY => ?_
  rw [hM, hAM]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs : ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) := inv_mem s.2
  have hY' : IsPolyDom P.m₀ (k + 1)
      (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
        '' Y) := (isPolyDom_image_iff hN hs Y).2 hY.1
  have hq := hchart _ hY' (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
    actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) (xiFieldDom_levelGS_act hs hp)
  obtain ⟨-, c2⟩ := fieldDom_completion_spec _ (k + 1) _ _ _ (hcpl _)
    (fun q hq => xiDom_mem_layerSub hq)
  exact hTMloc _ _ hY' _ _ (c2 _ hq).1 hq (c2 _ hq).2 _

open Classical in
/-- **`eucMloc` at `j = k + 1` for `fullJSymGroup L (k + 1)`, with the completion in the larger
chart**: from `localClass_site_Mloc_eq_chart` and the covariance of the per-site density `𝒟_M`
under the full group (`hDMfull`, P4 (H.7)). -/
theorem localClass_eucMloc_site_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ} {εseq εL : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (Tm : Terms d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁)))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p = Classical.epsilon
      (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
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
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
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
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g))
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g)) :
    ∀ hjk : k + 1 ≤ k + 1, ∀ x,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Mloc P.m₀ Tm (k + 1) (r x) (actField r Ψ) (actField r h) (actField r g) =
        Mloc P.m₀ Tm (k + 1) x Ψ h g := by
  intro _ x r hr Ψ h g h1 h2
  have hle : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) ≤
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) :=
    symGroupBy_le_of_dvd pow_dvd_cellSide (cellSide_pos (L := L) P.m₀ m₁ (k + 1))
  have e1 := localClass_site_Mloc_eq_chart hN Yp Tm cpl hcpl TM hTMloc AM hAM hM hchart DM hDM
    (fun r hr' => hDMfull r (hle hr')) (r x) (p := (actField r Ψ, actField r h)) h2 (actField r g)
  have e2 := localClass_site_Mloc_eq_chart hN Yp Tm cpl hcpl TM hTMloc AM hAM hM hchart DM hDM
    (fun r hr' => hDMfull r (hle hr')) x (p := (Ψ, h)) h1 g
  simp only at e1 e2
  rw [e1, e2]
  exact hDMfull r hr x (Ψ, h) g h1 h2

end Balaban.Localization
