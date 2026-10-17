/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassCentre
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The per-centre identity of the new level with the completion in the larger local chart

The centre-labelled energy terms of `LocalClassCentre.lean` (decisions D1(a), D5(a)), completed in
the **larger** local chart `Ξ^c_{k+1}(𝔹_{k+1}(Y⁺); 1, εL_{k+1})`, `ε_{k+1} ≤ εL_{k+1}`
(`localClass_termClausesE_centre_chart`, `LocalClassCentre.lean`; the inclusion `hchart` of the
whole-level domain in the class chart of a polymer at the same radius is not derivable, with the
loss `K_loc` it holds for the larger chart, `levelGS_xiFieldDom_sub_localB`).  The terms need only
be local on the larger chart for the completion not to change their values at the whole-level pairs.

* `localClass_centre_Eloc_eq_chart`: `Eloc_{k+1}(y) = 𝒟(y)` on the whole-level domain at the class
  radius, from `hchart` into the larger charts, the expansion identity `hDz` and the paving
  covariance `hDzcov` (`eloc_eq_of_avg_terms`);
* `localClass_eucEloc_centre_chart`: `eucEloc` at `j = k + 1` for `fullJSymGroup L (k + 1)`
  (`eucEloc_of_eloc_eq`);
* `localClass_centre_Edens_eq_chart`: `Edens_{k+1} = Σ_{z ∈ Λ_{k+1}} 𝒟(z)` (P4 (4.22);
  `edens_eq_of_eloc_eq`).

The source terms (`localClass_termClausesM_chart`, `localClass_site_Mloc_eq_chart`,
`localClass_eucMloc_site_chart`) are in `LocalClassAssembleM.lean` and `LocalClassCentre.lean`; at
`εL = ε` the landed theorems there are their applications.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation
  Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

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
    Eloc P.m₀ Tm (k + 1) y p.1 p.2 = Dz y p :=
  eloc_eq_of_avg_terms hN Tm (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2) (fun _ hr _ hq => xiFieldDom_levelGS_act hr hq) cpl TE
    (fun z Y hY q hq => by
      have h2 := hchart Y hY q hq
      obtain ⟨-, c2⟩ := fieldDom_completion_spec _ (k + 1) _ Y (cpl Y) (hcpl Y)
        (fun q hq => xiDom_mem_layerSub hq)
      exact hTEloc z Y hY _ _ (c2 q h2).1 h2 (c2 q h2).2)
    AE hAE hE Dz hDz hDzcov y hp

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
        Eloc P.m₀ Tm (k + 1) y Ψ h :=
  eucEloc_of_eloc_eq Tm (xiFieldDom a ν εseq) Dz
    (fun y _ hq => localClass_centre_Eloc_eq_chart hN Yp Tm cpl hcpl TE hTEloc AE hAE hE hchart Dz
      hDz (fun r hr => hDzfull r (pavingSymGroup_le_fullJSymGroup P.m₀ hr)) y hq)
    hDzblock hDzfull

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
        Dz z p :=
  edens_eq_of_eloc_eq Tm Dz fun z => localClass_centre_Eloc_eq_chart hN Yp Tm cpl hcpl TE hTEloc
    AE hAE hE hchart Dz hDz hDzcov z hp

end Balaban.Localization
