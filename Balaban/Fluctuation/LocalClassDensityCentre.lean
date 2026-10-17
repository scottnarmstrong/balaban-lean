/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityChart
public import Balaban.Fluctuation.LocalClassInherit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The energy terms of the new level with centre labels, completed in the larger local chart

The centre-labelled energy terms of `LocalClassCentre.lean` (decisions D1(a), D5(a)), with the
completion taken in the **larger** local chart `Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, εL_{k+1})`,
`ε_{k+1} ≤ εL_{k+1}`, instead of the class chart `Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, ε_{k+1})`
(`LocalClassDensityChart.lean`: the inclusion `hchart` of the whole-level domain in the class chart
of a polymer at the same radius is not derivable; with the loss `K_loc` it holds for the larger
chart, `levelGS_xiFieldDom_sub_localB`).  The term `TE z Y` of the centre `z` and the polymer `Y`:

* is analytic, bounded and invariant under real rotations on the **class** chart (radius `ε`);
* depends only on the restriction to `Y` on the **larger** chart (radius `εL`).

The class term is `Tm.E (k + 1) y Y = AE y Y` for `y ∈ Y`, `AE` the average over the paving group of
the completed terms `TE (s⁻¹ z) (s⁻¹ Y) (cpl (s⁻¹ Y) (s⁻¹ p))`, `cpl` the completion in the larger
chart.  At `εL = ε` all statements are those of `LocalClassCentre.lean`.

* `eloc_eq_of_avg_terms`: the combinatorial core of the per-centre identity (averages over the
  paving group of terms whose sums over the polymers of a site give a covariant density);
* `localClass_termClausesE_centre_chart`: the slices at `j = k + 1` of `gs_spec`, `gsStrong`,
  `pavingGS`, `analyticE`, `rotE`, `eucE`, `localE`, `boundE`;
* `localClass_centre_Eloc_eq_chart`: `Eloc_{k+1}(y) = 𝒟(y)` on the whole-level domain at the class
  radius, from the inclusion of that domain in the **larger** charts (`hchart`), the expansion
  identity `hDz` and the paving covariance `hDzcov` of `𝒟`;
* `localClass_eucEloc_centre_chart`: `eucEloc` at `j = k + 1` for `fullJSymGroup L (k + 1)`;
* `localClass_centre_Edens_eq_chart`: `Edens_{k+1} = Σ_{z ∈ Λ_{k+1}} 𝒟(z)` (P4 (4.22)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-! ### The combinatorial core of the per-centre identity -/

open Classical in
/-- **Averaged terms whose polymer sums give a covariant density sum to the density.**  Let `S` be
a set of pairs carried into itself by the paving group, `Dz` covariant under the paving group on
`S`, `Σ_{Y ∋ y} TE y Y q = Dz y q` on `S`, and let the class terms of the polymers of `y` at a pair
`p ∈ S` be the averages `|H|⁻¹ Σ_{s ∈ H} TE (s⁻¹ y) (s⁻¹ Y) (s⁻¹ p)`.  Then
`Eloc_{k+1}(y)(p) = Dz y p`: for each `s` the polymers `s⁻¹ Y ∋ s⁻¹ y` are all the polymers of
`s⁻¹ y`, so the inner sum is `Dz (s⁻¹ y) (s⁻¹ p) = Dz y p`. -/
theorem eloc_eq_of_avg_terms {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))] {ϱ : ℝ}
    (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (S : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop)
    (hS : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N, S q →
        S (actField r q.1, actField r q.2))
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), S q →
      ∑ᶠ Y ∈ polysAt m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), S q →
        S (actField r q.1, actField r q.2) → Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    (y : CTorus d L N₁ m₁ (k + 1)) {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : S p)
    (hterm : ∀ Y ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) y,
      Tm.E (k + 1) y Y p.1 p.2 =
        ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀
          (k + 1)) : ℂ))⁻¹ •
        ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
          TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) y)
            (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)) :
    Eloc m₀ Tm (k + 1) y p.1 p.2 = Dz y p := by
  have hfin : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) y).Finite :=
    Set.toFinite _
  -- for one element `t = s⁻¹` of the group, the polymers of `y` are carried onto those of `t y`
  have hinner : ∀ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1),
      ∑ Y ∈ hfin.toFinset,
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) y)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) = Dz y p := by
    intro s
    set t : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)) := (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹
      with ht
    have hts : t ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1) :=
      inv_mem s.2
    have hti : t⁻¹ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1) :=
      inv_mem hts
    have hq := hS t hts p hp
    have hbij : Set.BijOn (fun Y => (⇑t) '' Y)
        (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) y)
        (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ (k + 1) (t y)) := by
      refine ⟨fun Y hY => ⟨(isPolyDom_image_iff hN hts Y).2 hY.1, Set.mem_image_of_mem _ hY.2⟩,
        fun Y _ Y' _ hYY => Set.image_injective.2 t.injective hYY, fun Y' hY' => ?_⟩
      refine ⟨(⇑(t⁻¹)) '' Y', ⟨(isPolyDom_image_iff hN hti Y').2 hY'.1,
        ⟨t y, hY'.2, by simp [Equiv.Perm.inv_def]⟩⟩, ?_⟩
      simp only
      rw [Set.image_image]
      simp [Equiv.Perm.inv_def]
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_of_bijOn (g := fun Y' => TE (t y) Y' (actField t p.1, actField t p.2))
        (fun Y => (⇑t) '' Y) hbij fun Y _ => rfl,
      hDz _ _ hq]
    exact hDzcov t hts y p hp hq
  have hc : (Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀
      (k + 1)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Eloc
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.smul_sum,
    Finset.sum_comm]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

/-! ### The clauses of the energy terms -/

open Classical in
/-- **The E-fields of the new level with centre labels, completed in the larger local chart.**
Setting of `localClass_termClausesE_centre`, with two radius sequences `ε ≤ εL` at `k + 1`: the
class domain is `xiFieldDom a ν ε`, the completion `cpl` is taken in `xiFieldDom a ν εL`.  For
polymers `Y ∈ 𝒟_{k+1}`:
* `hTEan`, `hTEbd`, `hTErot`: analyticity, the bound `E₀ e^{-κ d_{k+1}(Y)}` (`z ∈ Y`) and the
  invariance under real orthogonal `Q`, on the class chart of `𝔹_{k+1}(Y⁺)`;
* `hTEloc`: dependence on the restriction to `Y` only, on the larger chart of `𝔹_{k+1}(Y⁺)`;
* `hTEblock`: dependence on the centre through its block.
Then the slices at `j = k + 1` of `gs_spec`, `gsStrong`, `pavingGS`, `analyticE`, `rotE`, `eucE`,
`localE`, `boundE` hold for `Tm.E (k + 1) y Y = AE y Y` (`y ∈ Y`). -/
theorem localClass_termClausesE_centre_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEblock : ∀ z z' Y p, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' → TE z Y p = TE z' Y p)
    (hTEan : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TE z Y)
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2})
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (hTEbd : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖TE z Y p‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTErot : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      TE z Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = TE z Y p)
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0) :
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
    -- `rotE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      ∀ Ψ h,
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
  -- the class domain `D` and the larger chart `D₂` of the completion
  set D : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom
      (k + 1) (G Y) p.1 p.2 with hD
  have hDL₂ : ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (G Y) p.1 p.2 → p ∈ layerSub (G Y) := fun Y p hp => xiDom_mem_layerSub hp
  have hdom : ∀ r ∈ (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D Y p →
      D (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    localB_collar_xiDom_act (le_refl (k + 1)) (le_refl (minSep L (L ^ m₁))) hr (hYp Y)
      (hYp (r '' Y)) hp
  set f : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ :=
    fun z Y p => TE z Y (cpl Y p) with hf
  have hAE' : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀
        (k + 1)) : ℂ))⁻¹ •
      ∑ s : (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      f (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
          Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
        (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
          actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2) := hAE
  -- the completed terms: equal to the terms on the class domain, analytic there, local
  have hext : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N, D Y p → f z Y p = TE z Y p) ∧
      AnalyticOnNhd ℂ (f z Y) {p | D Y p} := fun z Y hY => by
    obtain ⟨-, e2, e3⟩ := fieldDom_completion_extension_of_sub
      (xiFieldDom a ν εseq) (xiFieldDom a ν εL) (k + 1) (G Y) Y (cpl Y) (hcpl Y)
      (fun p hp => xiFieldDom_dom_of_eps_le hεL hp) (hDL₂ Y) (fun _ hp => xiDom_eventually HB hp)
      (TE z Y) (hTEan z Y hY) (hTEloc z Y hY)
    exact ⟨fun p hp => e2 p (xiFieldDom_dom_of_eps_le hεL hp), e3⟩
  have hfloc : ∀ z Y (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → f z Y p = f z Y p' := fun z Y p p' hpp => by
    obtain ⟨c1, -⟩ := fieldDom_completion_spec _ (k + 1) (G Y) Y (cpl Y) (hcpl Y) (hDL₂ Y)
    simp only [hf]
    rw [c1 p.1 p'.1 p.2 p'.2 hpp]
  -- the polymer domain family, carried into itself by the paving group
  set D' : Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Prop :=
    fun Y p => IsPolyDom P.m₀ (k + 1) Y ∧ D Y p with hD'
  have hdom' : ∀ r ∈ (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      ∀ Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), D' Y p →
      D' (r '' Y) (actField r p.1, actField r p.2) := fun r hr Y p hp =>
    ⟨(isPolyDom_image_iff hN hr Y).2 hp.1, hdom r hr Y p hp.2⟩
  have hfan : ∀ z Y, AnalyticOnNhd ℂ (f z Y) {p | D' Y p} := fun z Y p hp =>
    (hext z Y hp.1).2 p hp.2
  have hAcov : ∀ r ∈ (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)),
      ∀ z Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      AE (r z) (r '' Y) (actField r p.1, actField r p.2) = AE z Y p := fun r hr z Y p =>
    avgTermC_act
      (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
      hAE' hr z Y p
  have hAblock : ∀ z z' Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' →
      AE z Y p = AE z' Y p := fun z z' Y p hzz =>
    avgTermC_block
      (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) le_rfl f AE
      hAE' (fun w w' Y p hww => by simp only [hf]; exact hTEblock w w' _ _ hww) hzz Y p
  have hAloc := avgTermC_local
    (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
    hAE' hfloc
  have hAan := avgTermC_analytic
    (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
    hAE' D' hdom' hfan
  have hAbd : ∀ z Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N), z ∈ Y → D' Y p →
      ‖AE z Y p‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := fun z Y p hz hp =>
    avgTermC_bound (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) f AE
      hAE' D' hdom' (fun Y => P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
      (boundE_paving_invariant hN P.E₀ P.κ)
      (fun z Y p hz hp => by rw [(hext z Y hp.1).1 p hp.2]; exact hTEbd z Y hp.1 hz p hp.2) hz hp
  refine ⟨fun X _ => ?_, fun X _ => ?_, fun X _ r hr i => ?_, fun y X hX hy => ?_,
    fun y X hX hy R hR Ψ h h1 h2 => ?_, fun y X hX hy r hr Ψ h _ _ => ?_,
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
        Tm.E (k + 1) y X p.1 p.2) = fun p => AE y X p := by
      funext p
      rw [hE]
      simp [hy]
    rw [hEf, hgs]
    intro p hp
    exact hAan y X p ⟨hX, hp⟩
  · obtain ⟨Q, hQ, rfl⟩ := exists_cmat_of_isRot_real hR hR.2
    rw [hE, hE]
    simp only [hy, ↓reduceIte]
    rw [hgs] at h1 h2
    rw [hAE', hAE']
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    have hs : ((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹) ∈
        (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) := inv_mem s.2
    have hY' : IsPolyDom P.m₀ (k + 1)
        (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
          '' X) := (isPolyDom_image_iff hN hs X).2 hX
    have hp1 := hdom _ hs X (Ψ, h) h1
    have hp2 := hdom _ hs X (rotField (cmat Q) Ψ, rotField (cmat Q) h) h2
    simp only at hp1 hp2
    rw [actField_rotField, actField_rotField] at hp2 ⊢
    rw [(hext _ _ hY').1 _ hp2, (hext _ _ hY').1 _ hp1]
    exact hTErot _ _ hY' Q hQ _ hp1
  · have hmem := blockBase_mem_image hr (blockUnion_of_isPolyDom hN hX) hy
    rw [hE, hE]
    simp only [hmem, hy, ↓reduceIte]
    rw [hAblock _ (r y) _ _ (cbase_eq_self_of_aligned (aligned_cbase _))]
    exact hAcov r hr y X (Ψ, h)
  · rw [hE, hE, hAloc y X (Ψ, h) (Ψ', h') hX]
  · rw [hE]
    simp only [hy, ↓reduceIte]
    rw [hgs] at h1
    exact hAbd y X (Ψ, h) hy ⟨hX, h1⟩

/-! ### The per-centre identity, `eucEloc` for the full group, the density -/

open Classical in
/-- **The per-centre identity with the completion in the larger chart**: for the class terms of
`localClass_termClausesE_centre_chart`, at every pair `p` of the whole-level domain at the class
radius, `Eloc_{k+1}(y)(p) = 𝒟(y)(p)`.  Inputs, on the whole-level domain at the class radius:
* `hchart`: it lies in the **larger** chart of every polymer (`levelGS_xiFieldDom_sub_localB`, with
  the loss `K_loc`), where the completion does not change the values of the terms (`hTEloc`);
* `hDz`: the localization expansion of the density, `Σ_{Y ∋ y} TE y Y = 𝒟(y)`;
* `hDzcov`: the covariance of the density under the paving group. -/
theorem localClass_centre_Eloc_eq_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    (y : CTorus d L N₁ m₁ (k + 1)) {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      p.1 p.2) :
    Eloc P.m₀ Tm (k + 1) y p.1 p.2 = Dz y p := by
  refine eloc_eq_of_avg_terms hN Tm (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2) (fun r hr q hq => xiFieldDom_levelGS_act hr hq) TE Dz hDz hDzcov y hp
    fun Y hY => ?_
  rw [hE]
  simp only [hY.2, ↓reduceIte]
  rw [hAE]
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
  exact hTEloc _ _ hY' _ _ (c2 _ hq).1 hq (c2 _ hq).2

open Classical in
/-- **`eucEloc` at `j = k + 1` for `fullJSymGroup L (k + 1)`, with the completion in the larger
chart**: from `localClass_centre_Eloc_eq_chart` and the covariance of the per-block density `𝒟`
under the full group (`hDzfull`), `𝒟` depending on the centre through its block (`hDzblock`). -/
theorem localClass_eucEloc_centre_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzblock : ∀ y y' q, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' → Dz y q = Dz y' q)
    (hDzfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q) :
    ∀ hjk : k + 1 ≤ k + 1, ∀ y,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Eloc P.m₀ Tm (k + 1) (blockBase L (k + 1) (r y)) (actField r Ψ) (actField r h) =
        Eloc P.m₀ Tm (k + 1) y Ψ h := by
  intro _ y r hr Ψ h h1 h2
  have hle : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) ≤
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) :=
    symGroupBy_le_of_dvd pow_dvd_cellSide (cellSide_pos (L := L) P.m₀ m₁ (k + 1))
  have e1 := localClass_centre_Eloc_eq_chart hN Yp Tm cpl hcpl TE hTEloc AE hAE hE hchart Dz hDz
    (fun r hr' => hDzfull r (hle hr')) (blockBase L (k + 1) (r y))
    (p := (actField r Ψ, actField r h)) h2
  have e2 := localClass_centre_Eloc_eq_chart hN Yp Tm cpl hcpl TE hTEloc AE hAE hE hchart Dz hDz
    (fun r hr' => hDzfull r (hle hr')) y (p := (Ψ, h)) h1
  simp only at e1 e2
  rw [e1, e2, hDzblock _ (r y) _ (cbase_eq_self_of_aligned (aligned_cbase _))]
  exact hDzfull r hr y (Ψ, h) h1 h2

open Classical in
/-- **The density of the new level is the sum of the per-block densities, with the completion in the
larger chart** (P4 (4.22)): `Edens_{k+1} = Σ_{z ∈ Λ_{k+1}} 𝒟(z)` on the whole-level domain at the
class radius (inputs of `localClass_centre_Eloc_eq_chart`). -/
theorem localClass_centre_Edens_eq_chart {P : Consts} (hN : L ^ P.m₀ ∣ N₁)
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
    (TE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTEloc : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → TE z Y p = TE z Y p')
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        TE (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hchart : ∀ Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εL : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) q.1 q.2)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, TE y Y q = Dz y q)
    (hDzcov : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
      p.1 p.2) :
    Edens P.m₀ Tm (k + 1) p.1 p.2 =
      ∑ z ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter (Aligned (L ^ (k + 1))),
        Dz z p := by
  unfold Edens
  exact Finset.sum_congr rfl fun z _ => localClass_centre_Eloc_eq_chart hN Yp Tm cpl hcpl TE
    hTEloc AE hAE hE hchart Dz hDz hDzcov z hp

end Balaban.Localization
