/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelCastAnalytic

/-!
# The new level of the successor class at the cast local sets (`LocalClassDensityLevelCast`)

`localClass_newLevel_of_expansion_rho` needs `ϱ ≤ minSep L (L ^ m₁)` on the torus
`CTorus d L N₁ m₁ (k + 1)`.  At the tower's separation `ϱ = rhoSep m` this fails on the tower's own
torus (`not_rhoSep_le_minSep`); it holds on a finer torus `(N₁', m₁')` with
`N₁' L ^ m₁' = N₁ L ^ m₁` and `ϱ ≤ minSep L (L ^ m₁')` (`rhoSep_le_minSep_of_four`, `m₁' = m₁ + 4`).
The generating sets of the new level are then the sets `castG hc (localB …)` of that finer torus,
as for the label sets of the chain.

`localClass_newLevel_of_expansion_cast` has the hypotheses of `localClass_newLevel_of_expansion_rho`
on the torus `(N₁, m₁)` (the terms `Tl`, `TM`, the densities `Dz`, `DM`, the averages `hAE`, `hAM`,
the domains of the terms read through `castG`), and the conclusions of the latter on `(N₁, m₁)`.
The plus-sets `Yp'` and the local projection `cpl'` are those of the finer torus (`hYp'`, `hcpl'`
are the hypotheses `hYp`, `hcpl` of the landed theorem there); `Yp`, `cpl` are their transports to
the sets and fields of `(N₁, m₁)` (`hYp`, `hcpl`).

**Proof.**  The block index shifts to `m₀' = m₀ + m₁ - m₁'`, so that the cell sides
`cellSide L m₀' m₁' j = cellSide L m₀ m₁ j` agree; hence the polymers of `𝒟_j`, their sizes, the
`M`-paving group and the full level group correspond under the cast `e` of the two tori
(`LocalClassDensityLevelCastGeom`, `…Sym`).  The terms are moved to the finer torus along `e`, the
chart domains by `xiDom_castG_iff` (`…Dom`), the group averages by `AE_castEquiv`, `AM_castEquiv`
(`…Avg`) and the analyticity by reindexing (`…Analytic`).  The landed theorem is applied there with
`hsep`, and its conclusions are carried back.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

section NewLevelCast

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **The new level of the successor class at the cast local sets.**  The hypotheses and
conclusions of `localClass_newLevel_of_expansion_rho` on the torus `(N₁, m₁)`, with the generating
sets of the new level the sets `castG hc (localB …)` of the finer torus `(N₁', m₁')`,
`N₁' L ^ m₁' = N₁ L ^ m₁`, `m₁' ≤ m₀ + m₁`, `ϱ ≤ minSep L (L ^ m₁')`. -/
theorem localClass_newLevel_of_expansion_cast {N₁' m₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) {ϱ : ℝ} (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {P : Consts} (hm : m₁' ≤ P.m₀ + m₁) (hN : L ^ P.m₀ ∣ N₁)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    {a : ℕ → ℝ} {ν : ℝ}
    (HB : BgHyp d L (k + 1) ϱ a ν) (hα₀ : 0 ≤ P.α₀) (hα : 0 ≤ P.alpha d)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (3 * P.α₀)) ≤ 1)
    (hc0 : xiC1 d * (3 * P.α₀) ≤ bgC0 d L N) (hc1 : xiC1 d * (3 * P.α₀) ≤ bgC1 d L N)
    -- the plus-sets of the finer torus
    (Yp' : Set (CTorus d L N₁' m₁' (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (hYp' : ∀ Y z, z ∈ Yp' Y ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁' m₁' (k + 1),
      fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁'))
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (hYp : ∀ Y, Yp Y = Yp' {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y})
    -- the terms and their generating sets: the local sets of the finer torus, cast
    (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (hgs : ∀ Y, Tm.gs (k + 1) Y =
      castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep))
    -- the local projection of the finer torus, and its transport
    (cpl' : Set (CTorus d L N₁' m₁' (k + 1)) →
      Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N →
      Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N)
    (hcpl' : ∀ Y p, cpl' Y p = Classical.epsilon
      (fun q : Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N =>
        (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁' m₁' (k + 1) N ϱ).dom (k + 1)
          (localB (k + 1) (le_refl (k + 1)) (Yp' Y) hsep) q.1 q.2 ∧
        ∀ z ∈ Y,
          q.1 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp' Y) hsep) Y) p).1 z ∧
          q.2 z = (Classical.choose (exists_layerProj (N := N)
            (localB (k + 1) (le_refl (k + 1)) (Yp' Y) hsep) Y) p).2 z))
    (cpl : Set (CTorus d L N₁ m₁ (k + 1)) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ Y p, cpl Y p =
      (fun x => (cpl' {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y}
          (fun x' => p.1 (torusCast x'), fun x' => p.2 (torusCast x'))).1 (torusCast x),
        fun x => (cpl' {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y}
          (fun x' => p.1 (torusCast x'), fun x' => p.2 (torusCast x'))).2 (torusCast x)))
    -- the energy terms, per label
    {τι : Type*} (𝒯E : Finset τι)
    (Tl : τι → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTlblock : ∀ τ ∈ 𝒯E, ∀ z z' Y p,
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) z' →
      Tl τ z Y p = Tl τ z' Y p)
    (hTlan : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (Tl τ z Y)
      {p | (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2})
    (hTlloc : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p'.1 p'.2 →
      (∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → Tl τ z Y p = Tl τ z Y p')
    (EbE : τι → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hTlbd : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      ‖Tl τ z Y p‖ ≤ EbE τ z Y)
    (hsum : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∑ τ ∈ 𝒯E, EbE τ z Y ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTlrot : ∀ τ ∈ 𝒯E, ∀ z Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      Tl τ z Y (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = Tl τ z Y p)
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        ∑ τ ∈ 𝒯E, Tl τ (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    -- the energy density: expansion identity and covariance (remaining inputs)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hDz : ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) y, ∑ τ ∈ 𝒯E, Tl τ y Y q = Dz y q)
    (hDzblock : ∀ y y' q, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' → Dz y q = Dz y' q)
    (hDzfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Dz (r y) (actField r q.1, actField r q.2) = Dz y q)
    -- the source terms
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMan : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TM x Y)
      ({p | (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2} ×ˢ
        {g | Def6.l1 g < 1}))
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      (xiFieldDom a ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (hTMsrc : ∀ x Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ z ∈ Y, g z = g' z) → TM x Y (p, g) = TM x Y (p, g'))
    {BM : ℝ}
    (hBM : BM < P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hTMbd : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      Def6.l1 g < 1 → vn (TM x Y (p, g)) ≤ BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTMrot : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
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
    (hM : ∀ x Y Ψ h g, Tm.M (k + 1) x Y Ψ h g = AM x Y ((Ψ, h), g))
    -- the source density: expansion identity and covariance (remaining inputs)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hDM : ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom a ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g)) :
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
        {p | (xiFieldDom a ν (P.eps d L) :
          FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2}) ∧
    -- `rotE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.E (k + 1) y X (rotField R Ψ) (rotField R h) = Tm.E (k + 1) y X Ψ h) ∧
    -- `eucE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.E (k + 1) (blockBase L (k + 1) (r y)) (r '' X) (actField r Ψ) (actField r h) =
        Tm.E (k + 1) y X Ψ h) ∧
    -- `localE`
    (∀ y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      Tm.E (k + 1) y X Ψ h = Tm.E (k + 1) y X Ψ' h') ∧
    -- `boundE`
    (∀ y X, IsPolyDom P.m₀ (k + 1) X → y ∈ X → ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      ‖Tm.E (k + 1) y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) ∧
    -- `eucEloc`, full group
    (∀ hjk : k + 1 ≤ k + 1, ∀ y,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Eloc P.m₀ Tm (k + 1) (blockBase L (k + 1) (r y)) (actField r Ψ) (actField r h) =
        Eloc P.m₀ Tm (k + 1) y Ψ h) ∧
    -- the density (P4 (4.22))
    (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        p.1 p.2 →
      Edens P.m₀ Tm (k + 1) p.1 p.2 =
        ∑ z ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter (Aligned (L ^ (k + 1))),
          Dz z p) ∧
    -- `analyticM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => Tm.M (k + 1) x X p.1 p.2.1 p.2.2)
        {p | (xiFieldDom a ν (P.eps d L) :
          FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
          (Tm.gs (k + 1) X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}) ∧
    -- `rotM`, real matrices
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R →
      (∀ i j, (R i j).im = 0) → ∀ Ψ h g, Def6.l1 g < 1 →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.M (k + 1) x X (rotField R Ψ) (rotField R h) (rotField R g) =
        R *ᵥ Tm.M (k + 1) x X Ψ h g) ∧
    -- `eucM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X →
      ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) (r '' X)) (actField r Ψ) (actField r h) →
      Tm.M (k + 1) (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) =
        Tm.M (k + 1) x X Ψ h g) ∧
    -- `localM`
    (∀ x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
      Tm.M (k + 1) x X Ψ h g = Tm.M (k + 1) x X Ψ' h' g') ∧
    -- `boundM`
    (∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ Ψ h g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (Tm.gs (k + 1) X) Ψ h → Def6.l1 g < 1 →
      vn (Tm.M (k + 1) x X Ψ h g) <
        P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ (k + 1) X)) ∧
    -- `eucMloc`, full group
    (∀ hjk : k + 1 ≤ k + 1, ∀ x,
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1), ∀ Ψ h g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk) Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) hjk)
        (actField r Ψ) (actField r h) →
      Mloc P.m₀ Tm (k + 1) (r x) (actField r Ψ) (actField r h) (actField r g) =
        Mloc P.m₀ Tm (k + 1) x Ψ h g) ∧
    -- the per-site identity of the source terms
    (∀ x (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        p.1 p.2 →
      Mloc P.m₀ Tm (k + 1) x p.1 p.2 g = DM x (p, g)) := by
  obtain ⟨e, he⟩ := exists_castEquiv (d := d) (L := L) hc (k + 1)
  obtain ⟨m₀', hm₀'⟩ : ∃ m₀', m₀' + m₁' = P.m₀ + m₁ := ⟨P.m₀ + m₁ - m₁', by omega⟩
  let P' : Consts := { P with m₀ := m₀' }
  have hN' : L ^ P'.m₀ ∣ N₁' := by
    show L ^ m₀' ∣ N₁'
    have hpos : 0 < L ^ m₁' := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    refine Nat.dvd_of_mul_dvd_mul_right hpos ?_
    rw [hc, ← pow_add, hm₀', pow_add]
    exact Nat.mul_dvd_mul_right hN _
  classical
  have : Fintype (pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀ (k + 1)) :=
    Fintype.ofFinite _
  obtain ⟨Tm', hTE, hTM, hTgs⟩ : ∃ Tm' : Terms d L N₁' m₁' (k + 1) N ϱ,
      (∀ j y Y Ψ h, Tm'.E j y Y Ψ h =
        Tm.E j (e y) (e '' Y) (fun x => Ψ (e.symm x)) (fun x => h (e.symm x))) ∧
      (∀ j x Y Ψ h g, Tm'.M j x Y Ψ h g =
        Tm.M j (e x) (e '' Y) (fun z => Ψ (e.symm z)) (fun z => h (e.symm z))
          (fun z => g (e.symm z))) ∧
      (∀ j Y, Tm'.gs j Y = localB (k + 1) (le_refl (k + 1)) (Yp' Y) hsep) :=
    ⟨{ E := fun j y Y Ψ h =>
          Tm.E j (e y) (e '' Y) (fun x => Ψ (e.symm x)) (fun x => h (e.symm x))
       M := fun j x Y Ψ h g =>
          Tm.M j (e x) (e '' Y) (fun z => Ψ (e.symm z)) (fun z => h (e.symm z))
            (fun z => g (e.symm z))
       gs := fun _ Y => localB (k + 1) (le_refl (k + 1)) (Yp' Y) hsep },
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨Tl', hTl'⟩ : ∃ Tl' : τι → CTorus d L N₁' m₁' (k + 1) → Set (CTorus d L N₁' m₁' (k + 1)) →
      Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N → ℂ,
      ∀ τ z Y q, Tl' τ z Y q = Tl τ (e z) (e '' Y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)) :=
    ⟨fun τ z Y q => Tl τ (e z) (e '' Y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)),
      fun _ _ _ _ => rfl⟩
  obtain ⟨EbE', hEbE'⟩ : ∃ EbE' : τι → CTorus d L N₁' m₁' (k + 1) →
      Set (CTorus d L N₁' m₁' (k + 1)) → ℝ, ∀ τ z Y, EbE' τ z Y = EbE τ (e z) (e '' Y) :=
    ⟨fun τ z Y => EbE τ (e z) (e '' Y), fun _ _ _ => rfl⟩
  obtain ⟨AE', hAE'⟩ : ∃ AE' : CTorus d L N₁' m₁' (k + 1) → Set (CTorus d L N₁' m₁' (k + 1)) →
      Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N → ℂ,
      ∀ z Y p, AE' z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀
          (k + 1)) : ℂ))⁻¹ •
        ∑ s : pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀ (k + 1),
        ∑ τ ∈ 𝒯E, Tl' τ (((s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) '' Y)
          (cpl' (((s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ p.2)) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨Dz', hDz'⟩ : ∃ Dz' : CTorus d L N₁' m₁' (k + 1) →
      Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N → ℂ,
      ∀ y q, Dz' y q = Dz (e y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)) :=
    ⟨fun y q => Dz (e y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)), fun _ _ => rfl⟩
  obtain ⟨TM', hTM'⟩ : ∃ TM' : CTorus d L N₁' m₁' (k + 1) → Set (CTorus d L N₁' m₁' (k + 1)) →
      (Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N) × Fld d L N₁' m₁' (k + 1) N →
        Fin N → ℂ,
      ∀ x Y q, TM' x Y q = TM (e x) (e '' Y)
        ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z)) :=
    ⟨fun x Y q => TM (e x) (e '' Y)
        ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z)),
      fun _ _ _ => rfl⟩
  obtain ⟨AM', hAM'⟩ : ∃ AM' : CTorus d L N₁' m₁' (k + 1) → Set (CTorus d L N₁' m₁' (k + 1)) →
      (Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N) × Fld d L N₁' m₁' (k + 1) N →
        Fin N → ℂ,
      ∀ x Y q, AM' x Y q =
      ((Fintype.card (pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀
          (k + 1)) : ℂ))⁻¹ •
        ∑ s : pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀ (k + 1),
        TM' (((s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) x)
          (((s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) '' Y)
          (cpl' (((s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))⁻¹ q.2) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨DM', hDM'⟩ : ∃ DM' : CTorus d L N₁' m₁' (k + 1) →
      (Fld d L N₁' m₁' (k + 1) N × Fld d L N₁' m₁' (k + 1) N) × Fld d L N₁' m₁' (k + 1) N →
        Fin N → ℂ,
      ∀ x q, DM' x q = DM (e x)
        ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z)) :=
    ⟨fun x q => DM (e x)
        ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z)),
      fun _ _ => rfl⟩
  have hSY := preimage_image_castEquiv (d := d) (L := L) hc he
  have hYe : ∀ Y' : Set (CTorus d L N₁' m₁' (k + 1)), Yp (e '' Y') = Yp' Y' := fun Y' => by
    rw [hYp, hSY]
  have hpoly : ∀ Y' : Set (CTorus d L N₁' m₁' (k + 1)),
      IsPolyDom (L := L) (N₁ := N₁') (m₁ := m₁') (k := k + 1) m₀' (k + 1) Y' ↔
        IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) (e '' Y') :=
    fun Y' => isPolyDom_castEquiv_iff hc hm₀' he Y'
  have hsz : ∀ Y' : Set (CTorus d L N₁' m₁' (k + 1)),
      sizeJ (L := L) (N₁ := N₁') (m₁ := m₁') (k := k + 1) m₀' (k + 1) Y' =
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) (e '' Y') :=
    fun Y' => sizeJ_castEquiv hc hm₀' he Y'
  have hmem : ∀ (y : CTorus d L N₁' m₁' (k + 1)) (Y : Set (CTorus d L N₁' m₁' (k + 1))),
      e y ∈ e '' Y ↔ y ∈ Y := fun y Y => e.injective.mem_set_image
  have domc : ∀ (ε : ℕ → ℝ) (G' : GeneratingSet d L (N₁' * L ^ m₁') (k + 1) ϱ)
      (Ψ h : Fld d L N₁' m₁' (k + 1) N),
      (xiFieldDom a ν ε : FieldDom d L N₁' m₁' (k + 1) N ϱ).dom (k + 1) G' Ψ h ↔
        (xiFieldDom a ν ε : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) (castG hc G')
          (fun x => Ψ (e.symm x)) (fun x => h (e.symm x)) := by
    intro ε G' Ψ h
    rw [xiFieldDom_dom_castG_iff hc he]
    simp only [Equiv.symm_apply_apply]
  have domL : ∀ (ε : ℕ → ℝ) (Ψ h : Fld d L N₁' m₁' (k + 1) N),
      (xiFieldDom a ν ε : FieldDom d L N₁' m₁' (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁') (m₁ := m₁') (k + 1) (le_refl (k + 1))) Ψ h ↔
        (xiFieldDom a ν ε : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
          (fun x => Ψ (e.symm x)) (fun x => h (e.symm x)) := by
    intro ε Ψ h
    rw [domc ε _ Ψ h, castG_levelGS hc he]
  have hS : Subgroup.map e.permCongrHom
      (pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀ (k + 1)) =
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1) :=
    castEquiv_pavingSymGroup hc he hm₀' (k + 1)
  have key := localClass_newLevel_of_expansion_rho (ϱ := ϱ) (N₁ := N₁') (m₁ := m₁') (k := k)
    (N := N) hsep (P := P') hN' HB hα₀ hα hsmall hc0 hc1 Yp' hYp' Tm' (fun Y => hTgs _ Y) cpl'
    hcpl' 𝒯E Tl'
    -- hTlblock
    (fun τ hτ z z' Y p h => by
      rw [hTl', hTl']
      exact hTlblock τ hτ (e z) (e z') (e '' Y) _ (by
        rw [← castEquiv_blockBase hc he (k + 1) z, ← castEquiv_blockBase hc he (k + 1) z', h]))
    -- hTlan
    (fun τ hτ z Y hY => by
      have h := hTlan τ hτ (e z) (e '' Y) ((hpoly Y).1 hY)
      rw [hYe] at h
      rw [show Tl' τ z Y = fun p => Tl τ (e z) (e '' Y)
          (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) from funext fun p => hTl' τ z Y p]
      exact (analyticOnNhd_pull2 e.symm h).mono (fun p hp => (domc _ _ p.1 p.2).1 hp))
    -- hTlloc
    (fun τ hτ z Y hY p p' hp hp' hpp => by
      have h := hTlloc τ hτ (e z) (e '' Y) ((hpoly Y).1 hY)
      rw [hYe] at h
      rw [hTl', hTl']
      refine h (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) (fun x => p'.1 (e.symm x), fun x => p'.2 (e.symm x)) ((domc _ _ p.1 p.2).1 hp) ((domc _ _ p'.1 p'.2).1 hp') ?_
      rintro _ ⟨x, hx, rfl⟩
      simpa only [Equiv.symm_apply_apply] using hpp x hx)
    EbE'
    -- hTlbd
    (fun τ hτ z Y hY hz p hp => by
      have h := hTlbd τ hτ (e z) (e '' Y) ((hpoly Y).1 hY) ((hmem z Y).2 hz)
      rw [hYe] at h
      rw [hTl', hEbE']
      exact h (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) ((domc _ _ p.1 p.2).1 hp))
    -- hsum
    (fun z Y hY hz => by
      have h := hsum (e z) (e '' Y) ((hpoly Y).1 hY) ((hmem z Y).2 hz)
      rw [Finset.sum_congr rfl (fun τ _ => hEbE' τ z Y)]
      rw [← hsz Y] at h
      exact h)
    -- hTlrot
    (fun τ hτ z Y hY Q hQ p hp => by
      have h := hTlrot τ hτ (e z) (e '' Y) ((hpoly Y).1 hY) Q hQ
      rw [hYe] at h
      rw [hTl', hTl']
      exact h (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) ((domc _ _ p.1 p.2).1 hp))
    AE' hAE'
    -- hE
    (fun y Y Ψ h => by
      rw [hTE, hE]
      by_cases hy : y ∈ Y
      · have h1 := (hmem y Y).2 hy
        simp only [h1, hy, ↓reduceIte]
        exact AE_castEquiv hc he 𝒯E hcpl hS hTl' hAE hAE' y Y (Ψ, h)
      · have h1 : e y ∉ e '' Y := fun h' => hy ((hmem y Y).1 h')
        simp only [h1, hy, ↓reduceIte])
    Dz'
    -- hDz
    (fun y q hq => by
      have h := hDz (e y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x))
        ((domL _ q.1 q.2).1 hq)
      refine (finsum_mem_congr rfl fun Y _ => Finset.sum_congr rfl fun τ _ =>
        hTl' τ y Y q).trans ?_
      rw [hDz']
      exact (finsum_polysAt_castEquiv hc hm₀' he (k + 1) y
        (fun Y => ∑ τ ∈ 𝒯E, Tl τ (e y) Y (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)))).symm.trans h)
    -- hDzblock
    (fun y y' q hyy => by
      rw [hDz', hDz']
      exact hDzblock (e y) (e y') _ (by
        rw [← castEquiv_blockBase hc he (k + 1) y, ← castEquiv_blockBase hc he (k + 1) y', hyy]))
    -- hDzfull
    (fun r hr y q hq hq' => by
      rw [hDz', hDz']
      have hr' : e.permCongrHom r ∈
          fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) := by
        rw [← castEquiv_fullJSymGroup hc he (k + 1)]
        exact Subgroup.mem_map_of_mem _ hr
      have h := hDzfull (e.permCongrHom r) hr' (e y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x))
        ((domL _ q.1 q.2).1 hq) (by
          rw [actField_castEquiv, actField_castEquiv]
          exact (domL _ _ _).1 hq')
      rw [permCongrHom_apply', actField_castEquiv, actField_castEquiv] at h
      exact h)
    TM'
    -- hTMan
    (fun x Y hY => by
      have h := hTMan (e x) (e '' Y) ((hpoly Y).1 hY)
      rw [hYe] at h
      rw [show TM' x Y = fun q => TM (e x) (e '' Y)
          ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z))
          from funext fun q => hTM' x Y q]
      refine (analyticOnNhd_pullSrc e.symm h).mono ?_
      rintro q ⟨hq1, hq2⟩
      refine ⟨(domc _ _ q.1.1 q.1.2).1 hq1, ?_⟩
      show Def6.l1 (fun z => q.2 (e.symm z)) < 1
      rw [l1_castEquiv]
      exact hq2)
    -- hTMloc
    (fun x Y hY p p' hp hp' hpp g => by
      have h := hTMloc (e x) (e '' Y) ((hpoly Y).1 hY)
      rw [hYe] at h
      rw [hTM', hTM']
      refine h (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) (fun x => p'.1 (e.symm x), fun x => p'.2 (e.symm x)) ((domc _ _ p.1 p.2).1 hp)
        ((domc _ _ p'.1 p'.2).1 hp') ?_ (fun z => g (e.symm z))
      rintro _ ⟨z, hz, rfl⟩
      simpa only [Equiv.symm_apply_apply] using hpp z hz)
    -- hTMsrc
    (fun x Y p g g' hgg => by
      rw [hTM', hTM']
      exact hTMsrc (e x) (e '' Y) (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) (fun z => g (e.symm z))
        (fun z => g' (e.symm z)) (by
          rintro _ ⟨z, hz, rfl⟩
          simpa only [Equiv.symm_apply_apply] using hgg z hz))
    hBM
    -- hTMbd
    (fun x Y hY hx p g hp hg => by
      have h := hTMbd (e x) (e '' Y) ((hpoly Y).1 hY) ((hmem x Y).2 hx)
      rw [hYe] at h
      have h' := h (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) (fun z => g (e.symm z)) ((domc _ _ p.1 p.2).1 hp) (by
        rw [l1_castEquiv]
        exact hg)
      rw [← hsz Y] at h'
      rw [hTM']
      exact h')
    -- hTMrot
    (fun x Y hY Q hQ p g hp hg => by
      have h := hTMrot (e x) (e '' Y) ((hpoly Y).1 hY) Q hQ
      rw [hYe] at h
      rw [hTM', hTM']
      exact h (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) (fun z => g (e.symm z)) ((domc _ _ p.1 p.2).1 hp) (by
        rw [l1_castEquiv]
        exact hg))
    AM' hAM'
    -- hM
    (fun x Y Ψ h g => by
      rw [hTM, hM]
      exact AM_castEquiv hc he hcpl hS hTM' hAM hAM' x Y ((Ψ, h), g))
    DM'
    -- hDM
    (fun x q g hq => by
      have h := hDM (e x) (fun z => q.1 (e.symm z), fun z => q.2 (e.symm z))
        (fun z => g (e.symm z)) ((domL _ q.1 q.2).1 hq)
      refine (finsum_mem_congr rfl fun Y _ => hTM' x Y (q, g)).trans ?_
      rw [hDM']
      exact (finsum_polysAt_castEquiv hc hm₀' he (k + 1) x
        (fun Y => TM (e x) Y ((fun z => q.1 (e.symm z), fun z => q.2 (e.symm z)),
          fun z => g (e.symm z)))).symm.trans h)
    -- hDMfull
    (fun r hr x q g hq hq' => by
      rw [hDM', hDM']
      have hr' : e.permCongrHom r ∈
          fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) := by
        rw [← castEquiv_fullJSymGroup hc he (k + 1)]
        exact Subgroup.mem_map_of_mem _ hr
      have h := hDMfull (e.permCongrHom r) hr' (e x)
        (fun z => q.1 (e.symm z), fun z => q.2 (e.symm z)) (fun z => g (e.symm z))
        ((domL _ q.1 q.2).1 hq) (by
          rw [actField_castEquiv, actField_castEquiv]
          exact (domL _ _ _).1 hq')
      rw [permCongrHom_apply', actField_castEquiv, actField_castEquiv, actField_castEquiv] at h
      exact h)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ := key
  have hpre : ∀ X : Set (CTorus d L N₁ m₁ (k + 1)),
      {x' : CTorus d L N₁' m₁' (k + 1) |
        (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ X} = e ⁻¹' X := fun X => by
    ext x'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, torusCast_eq_equiv hc he]
  have himg : ∀ X : Set (CTorus d L N₁ m₁ (k + 1)), e '' (e ⁻¹' X) = X := fun X =>
    Set.image_preimage_eq X e.surjective
  have hgsX : ∀ X : Set (CTorus d L N₁ m₁ (k + 1)),
      Tm.gs (k + 1) X = castG hc (Tm'.gs (k + 1) (e ⁻¹' X)) := fun X => by
    rw [hgs, hYp, hpre, hTgs]
  have hpoly2 : ∀ X : Set (CTorus d L N₁ m₁ (k + 1)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) X →
        IsPolyDom (L := L) (N₁ := N₁') (m₁ := m₁') (k := k + 1) m₀' (k + 1) (e ⁻¹' X) :=
    fun X hX => (hpoly _).2 (by rw [himg]; exact hX)
  have hsz2 : ∀ X : Set (CTorus d L N₁ m₁ (k + 1)),
      sizeJ (L := L) (N₁ := N₁') (m₁ := m₁') (k := k + 1) m₀' (k + 1) (e ⁻¹' X) =
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) P.m₀ (k + 1) X := fun X =>
    (hsz _).trans (by rw [himg])
  have domT : ∀ (ε : ℕ → ℝ) (X : Set (CTorus d L N₁ m₁ (k + 1)))
      (Ψ h : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν ε : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) (Tm.gs (k + 1) X) Ψ h ↔
        (xiFieldDom a ν ε : FieldDom d L N₁' m₁' (k + 1) N ϱ).dom (k + 1)
          (Tm'.gs (k + 1) (e ⁻¹' X)) (fun x => Ψ (e x)) (fun x => h (e x)) := fun ε X Ψ h => by
    rw [hgsX X]
    exact xiFieldDom_dom_castG_iff hc he _ a ν ε (k + 1) Ψ h
  have domLT : ∀ (ε : ℕ → ℝ) (Ψ h : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν ε : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) Ψ h ↔
        (xiFieldDom a ν ε : FieldDom d L N₁' m₁' (k + 1) N ϱ).dom (k + 1)
          (levelGS (ϱ := ϱ) (N₁ := N₁') (m₁ := m₁') (k + 1) (le_refl (k + 1)))
          (fun x => Ψ (e x)) (fun x => h (e x)) := fun ε Ψ h => by
    rw [domL ε]
    simp only [Equiv.apply_symm_apply]
  have hE0 : ∀ y X Ψ h, Tm'.E (k + 1) (e.symm y) (e ⁻¹' X) (fun x => Ψ (e x))
      (fun x => h (e x)) = Tm.E (k + 1) y X Ψ h := fun y X Ψ h => by
    rw [hTE]
    simp only [Equiv.apply_symm_apply, himg]
  have hM0 : ∀ y X Ψ h g, Tm'.M (k + 1) (e.symm y) (e ⁻¹' X) (fun x => Ψ (e x))
      (fun x => h (e x)) (fun x => g (e x)) = Tm.M (k + 1) y X Ψ h g := fun y X Ψ h g => by
    rw [hTM]
    simp only [Equiv.apply_symm_apply, himg]
  have hact : ∀ (r' : Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) (Ψ : Fld d L N₁ m₁ (k + 1) N),
      (fun x => (actField r' (fun y => Ψ (e y))) (e.symm x)) =
        actField (e.permCongrHom r') Ψ := by
    intro r' Ψ
    have := actField_castEquiv (e := e) (N := N) r' (fun x => Ψ (e x))
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  have hbb : ∀ (j : ℕ) (r' : Equiv.Perm (CTorus d L N₁' m₁' (k + 1)))
      (y : CTorus d L N₁ m₁ (k + 1)),
      e (blockBase (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L j (r' (e.symm y))) =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L j ((e.permCongrHom r') y) := by
    intro j r' y
    rw [castEquiv_blockBase hc he j]
    congr 1
  have hrx : ∀ (r' : Equiv.Perm (CTorus d L N₁' m₁' (k + 1))) (y : CTorus d L N₁ m₁ (k + 1)),
      e (r' (e.symm y)) = (e.permCongrHom r') y := by
    intro r' y
    have := permCongrHom_apply' (e := e) r' (e.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hpavE : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
      ∃ r' ∈ pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L P'.m₀ (k + 1),
        r = e.permCongrHom r' := fun r hr => by
    rw [← hS] at hr
    obtain ⟨r', hr', hrr⟩ := Subgroup.mem_map.1 hr
    exact ⟨r', hr', hrr.symm⟩
  have hfullE : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∃ r' ∈ fullJSymGroup (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L (k + 1),
        r = e.permCongrHom r' := fun r hr => by
    rw [← castEquiv_fullJSymGroup hc he (k + 1)] at hr
    obtain ⟨r', hr', hrr⟩ := Subgroup.mem_map.1 hr
    exact ⟨r', hr', hrr.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gs_spec
    intro X hX
    rw [hgsX X]
    obtain ⟨h1, h2⟩ := k1 (e ⁻¹' X) (hpoly2 X hX)
    refine ⟨fun x hx => ?_, castG_noAbove hc h2⟩
    rw [Finset.mem_coe, mem_castG_Ω_equiv hc he]
    exact h1 (show e.symm x ∈ e ⁻¹' X by simpa using hx)
  · -- gsStrong
    intro X hX
    rw [hgsX X]
    have H := gsSpecStrong_castG hc he (Nat.succ_pos k) (le_refl (k + 1))
      (k2 (e ⁻¹' X) (hpoly2 X hX))
    rwa [himg] at H
  · -- pavingGS
    intro X hX r hr i
    obtain ⟨r', hr', rfl⟩ := hpavE r hr
    have h3 := k3 (e ⁻¹' X) (hpoly2 X hX) r' hr' i
    rw [hgsX ((e.permCongrHom r') '' X), hgsX X, preimage_image_perm_castEquiv,
      coe_castG_Ω_equiv hc he, coe_castG_Ω_equiv hc he, h3, image_image_perm_castEquiv]
  · -- analyticE
    intro y X hX hy
    have h := k4 (e.symm y) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hy)
    have h2 := analyticOnNhd_pull2 e h
    have hfun : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Tm.E (k + 1) y X p.1 p.2) = fun p => Tm'.E (k + 1) (e.symm y) (e ⁻¹' X)
          (fun x => p.1 (e x)) (fun x => p.2 (e x)) :=
      funext fun p => (hE0 y X p.1 p.2).symm
    rw [hfun]
    exact h2.mono (fun p hp => (domT _ X p.1 p.2).1 hp)
  · -- rotE
    intro y X hX hy R hR Ψ h hd hd'
    have h5 : Tm'.E (k + 1) (e.symm y) (e ⁻¹' X) (fun x => (rotField R Ψ) (e x))
        (fun x => (rotField R h) (e x)) =
        Tm'.E (k + 1) (e.symm y) (e ⁻¹' X) (fun x => Ψ (e x)) (fun x => h (e x)) :=
      k5 (e.symm y) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hy) R hR (fun x => Ψ (e x))
        (fun x => h (e x)) ((domT _ X Ψ h).1 hd)
        ((domT _ X (rotField R Ψ) (rotField R h)).1 hd')
    rwa [hE0, hE0] at h5
  · -- eucE
    intro y X hX hy r hr Ψ h hd hd'
    obtain ⟨r', hr', rfl⟩ := hpavE r hr
    have hd'' := (domT _ ((e.permCongrHom r') '' X) (actField (e.permCongrHom r') Ψ)
      (actField (e.permCongrHom r') h)).1 hd'
    rw [preimage_image_perm_castEquiv, actField_castEquiv', actField_castEquiv'] at hd''
    have h6 := k6 (e.symm y) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hy) r' hr'
      (fun x => Ψ (e x)) (fun x => h (e x)) ((domT _ X Ψ h).1 hd) hd''
    rw [hTE, hTE] at h6
    rw [hbb, ← image_image_perm_castEquiv, himg, hact, hact] at h6
    simpa only [Equiv.apply_symm_apply, himg] using h6
  · -- localE
    intro y X Ψ Ψ' h h' hΨ
    have h7 := k7 (e.symm y) (e ⁻¹' X) (fun x => Ψ (e x)) (fun x => Ψ' (e x))
      (fun x => h (e x)) (fun x => h' (e x)) (fun x hx => hΨ (e x) hx)
    rwa [hE0, hE0] at h7
  · -- boundE
    intro y X hX hy Ψ h hd
    have h8 := k8 (e.symm y) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hy) (fun x => Ψ (e x))
      (fun x => h (e x)) ((domT _ X Ψ h).1 hd)
    rw [hE0, hsz2 X] at h8
    exact h8
  · -- eucEloc
    intro hjk y r hr Ψ h hd hd'
    obtain ⟨r', hr', rfl⟩ := hfullE r hr
    have hd'' := (domLT _ (actField (e.permCongrHom r') Ψ) (actField (e.permCongrHom r') h)).1 hd'
    rw [actField_castEquiv', actField_castEquiv'] at hd''
    have h9 := k9 hjk (e.symm y) r' hr' (fun x => Ψ (e x)) (fun x => h (e x))
      ((domLT _ Ψ h).1 hd) hd''
    have e1 := Eloc_castEquiv hc hm₀' he hTE (k + 1)
      (blockBase (N₁ := N₁') (m₁ := m₁') (k := k + 1) (d := d) L (k + 1) (r' (e.symm y)))
      (actField r' (fun x => Ψ (e x))) (actField r' (fun x => h (e x)))
    have e2 := Eloc_castEquiv hc hm₀' he hTE (k + 1) (e.symm y) (fun x => Ψ (e x))
      (fun x => h (e x))
    have h9' := e1.symm.trans (h9.trans e2)
    rw [hbb, hact, hact] at h9'
    simpa only [Equiv.apply_symm_apply] using h9'
  · -- density
    intro p hp
    have h10 := k10 (fun x => p.1 (e x), fun x => p.2 (e x)) ((domLT _ p.1 p.2).1 hp)
    have e1 := Edens_castEquiv hc hm₀' he hTE (k + 1) (fun x => p.1 (e x)) (fun x => p.2 (e x))
    simp only [Equiv.apply_symm_apply] at e1
    refine e1.symm.trans (h10.trans ?_)
    refine Finset.sum_equiv e (fun z => ?_) (fun z _ => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (castEquiv_aligned_iff hc he _ z).symm
    · rw [hDz']
      simp only [Equiv.apply_symm_apply]
  · -- analyticM
    intro x X hX hx
    have h := k11 (e.symm x) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hx)
    have h2 := analyticOnNhd_pull3 e h
    have hfun : (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
        Fld d L N₁ m₁ (k + 1) N => Tm.M (k + 1) x X p.1 p.2.1 p.2.2) = fun p =>
          Tm'.M (k + 1) (e.symm x) (e ⁻¹' X) (fun z => p.1 (e z)) (fun z => p.2.1 (e z))
            (fun z => p.2.2 (e z)) :=
      funext fun p => (hM0 x X p.1 p.2.1 p.2.2).symm
    rw [hfun]
    refine h2.mono (fun p hp => ⟨(domT _ X p.1 p.2.1).1 hp.1, ?_⟩)
    show Def6.l1 (fun z => p.2.2 (e z)) < 1
    rw [l1_castEquiv']
    exact hp.2
  · -- rotM
    intro x X hX hx R hR hRr Ψ h g hg hd hd'
    have h12 : Tm'.M (k + 1) (e.symm x) (e ⁻¹' X) (fun z => (rotField R Ψ) (e z))
        (fun z => (rotField R h) (e z)) (fun z => (rotField R g) (e z)) =
        R *ᵥ Tm'.M (k + 1) (e.symm x) (e ⁻¹' X) (fun z => Ψ (e z)) (fun z => h (e z))
          (fun z => g (e z)) :=
      k12 (e.symm x) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hx) R hR hRr (fun z => Ψ (e z))
        (fun z => h (e z)) (fun z => g (e z)) (by
          show Def6.l1 (fun z => g (e z)) < 1
          rw [l1_castEquiv']
          exact hg) ((domT _ X Ψ h).1 hd) ((domT _ X (rotField R Ψ) (rotField R h)).1 hd')
    rwa [hM0, hM0] at h12
  · -- eucM
    intro x X hX hx r hr Ψ h g hd hd'
    obtain ⟨r', hr', rfl⟩ := hpavE r hr
    have hd'' := (domT _ ((e.permCongrHom r') '' X) (actField (e.permCongrHom r') Ψ)
      (actField (e.permCongrHom r') h)).1 hd'
    rw [preimage_image_perm_castEquiv, actField_castEquiv', actField_castEquiv'] at hd''
    have h13 := k13 (e.symm x) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hx) r' hr'
      (fun z => Ψ (e z)) (fun z => h (e z)) (fun z => g (e z)) ((domT _ X Ψ h).1 hd) hd''
    rw [hTM, hTM] at h13
    rw [hrx, ← image_image_perm_castEquiv, himg, hact, hact, hact] at h13
    simpa only [Equiv.apply_symm_apply, himg] using h13
  · -- localM
    intro x X Ψ Ψ' h h' g g' hΨ
    have h14 := k14 (e.symm x) (e ⁻¹' X) (fun z => Ψ (e z)) (fun z => Ψ' (e z))
      (fun z => h (e z)) (fun z => h' (e z)) (fun z => g (e z)) (fun z => g' (e z))
      (fun z hz => hΨ (e z) hz)
    rwa [hM0, hM0] at h14
  · -- boundM
    intro x X hX hx Ψ h g hd hg
    have h15 := k15 (e.symm x) (e ⁻¹' X) (hpoly2 X hX) (by simpa using hx) (fun z => Ψ (e z))
      (fun z => h (e z)) (fun z => g (e z)) ((domT _ X Ψ h).1 hd) (by
        show Def6.l1 (fun z => g (e z)) < 1
        rw [l1_castEquiv']
        exact hg)
    rw [hM0, hsz2 X] at h15
    exact h15
  · -- eucMloc
    intro hjk x r hr Ψ h g hd hd'
    obtain ⟨r', hr', rfl⟩ := hfullE r hr
    have hd'' := (domLT _ (actField (e.permCongrHom r') Ψ) (actField (e.permCongrHom r') h)).1 hd'
    rw [actField_castEquiv', actField_castEquiv'] at hd''
    have h16 := k16 hjk (e.symm x) r' hr' (fun z => Ψ (e z)) (fun z => h (e z))
      (fun z => g (e z)) ((domLT _ Ψ h).1 hd) hd''
    have e1 := Mloc_castEquiv hc hm₀' he hTM (k + 1) (r' (e.symm x))
      (actField r' (fun z => Ψ (e z))) (actField r' (fun z => h (e z)))
      (actField r' (fun z => g (e z)))
    have e2 := Mloc_castEquiv hc hm₀' he hTM (k + 1) (e.symm x) (fun z => Ψ (e z))
      (fun z => h (e z)) (fun z => g (e z))
    have h16' := e1.symm.trans (h16.trans e2)
    rw [hrx, hact, hact, hact] at h16'
    simpa only [Equiv.apply_symm_apply] using h16'
  · -- the per-site identity
    intro x p g hp
    have h17 := k17 (e.symm x) (fun z => p.1 (e z), fun z => p.2 (e z)) (fun z => g (e z))
      ((domLT _ p.1 p.2).1 hp)
    have e1 := Mloc_castEquiv hc hm₀' he hTM (k + 1) (e.symm x) (fun z => p.1 (e z))
      (fun z => p.2 (e z)) (fun z => g (e z))
    refine (Eq.trans ?_ (e1.symm.trans h17)).trans ?_
    · simp only [Equiv.apply_symm_apply]
    · rw [hDM']
      simp only [Equiv.apply_symm_apply]

end NewLevelCast

end Balaban.Localization
