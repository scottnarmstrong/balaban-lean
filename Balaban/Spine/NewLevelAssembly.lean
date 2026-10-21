/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.SFStep
public import Balaban.Inhabited.ClassHatWitness
public import Balaban.Inhabited.StepTowerLocalChart
public import Balaban.Inhabited.NewLevelLocalFamilyBirth
public import Balaban.Inhabited.NewLevelHatLayer

/-!
# The assembly of A4-1b (`SFNewLevelInput`, blocker 6)

`SFNewLevelInput` asks, for the image `Φ sf` of every member `sf` of the class `ℛ_k` under the
small-field step `Φ` (a parameter of the sub-spine), the four clauses of `SFNewLevelQ` on every read
torus: the term clauses of the new level on the class domain (`SFTermClauses (sfDom …)` of
`newLevelTerms`), the strong specification and the hat specification (ruling R13) of the new
generating sets, and the torus independence of the new level.

* `NewLevelClausesAt P a ν Tm Dz DM`: the level-`(k + 1)` clauses in the form of the conclusion of
  `localClass_newLevel_of_expansion_cast` (the generating sets, the term clauses of `ℰ_{k+1}`,
  `ℳ_{k+1}` on `xiFieldDom a ν`, the densities `Dz`, `DM`).
* `newLevelClausesAt_of_localFamilies`: these clauses at one torus from local families with
  (A1)–(A5) of the step chain's coefficient family (`newLabels_castInputs_of_localFamily` composed
  with `localClass_newLevel_of_expansion_cast`); the families are those of
  `NewLevelTies.newLevel_localFamilies_composed_gap`.
* `NewLevelOpenAt`, **`sfNewLevelInput_of_open`**: `SFNewLevelInput` from the open inputs at every
  member of the class, each a named field: the generating sets of the new level of `Φ` (`gs_hat`),
  the clauses with their reading on the class domain (`clauses`), the torus independence
  (`torusIndep`); the strong specification is `gsSpecStrong_hatGSOf`.  The list of what remains open, with its
  sources and builders, is in `notes/phase1/SPINE.md` (L5 note (7)).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField Balaban.Inhabited Matrix

section Clauses

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The clauses of the new level at one torus**, in the form of the conclusion of
`localClass_newLevel_of_expansion_cast`: the generating sets of the level `k + 1`, the term clauses
of `ℰ_{k+1}`, `ℳ_{k+1}` on the field domain `xiFieldDom a ν`, the energy density `Dz` (P4 (4.22))
and the per-site identity of the source terms `DM`. -/
def NewLevelClausesAt (P : Consts) (a : ℕ → ℝ) (ν : ℝ) (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
        : Prop :=
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
      Mloc P.m₀ Tm (k + 1) x p.1 p.2 g = DM x (p, g))

end Clauses

open Classical in
/-- **Bridge (i): the clauses of the new level read as the term clauses of `newLevelTerms`** on a
class field domain `Dom` contained, at the level `k + 1`, in the domain `xiFieldDom a ν` of the
clauses (`hdom`; for `Dom = sfDom` of the image, the birth domain at the new mass and weight, this is
the mass response of the domain).  The levels `j ≤ k` of `newLevelTerms` are zero with the
whole-level sets; the level `k + 1` is `NewLevelClausesAt` read through `hdom`.  The rotation clause
of the source terms is asked for the complex rotations (`hrotM`; the expansion gives the real
ones), the levels above `k + 1` vanish (`htop`), and the constants have `E₀ ≥ 0`, `c₉ > 0`. -/
theorem sfTermClauses_newLevelTerms_of_clauses {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]
    {ϱ : ℝ} {P : Consts} {a : ℕ → ℝ} {ν : ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    {Dz : CTorus d L N₁ m₁ (k + 1) → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ}
    {DM : CTorus d L N₁ m₁ (k + 1) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ}
    (Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ) (hE₀ : 0 ≤ P.E₀) (hc₉ : 0 < P.c₉)
    (hdom : ∀ (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) Ψ h, Dom.dom (k + 1) G Ψ h →
      (xiFieldDom a ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) G Ψ h)
    (htop : ∀ j, k + 1 < j → Tm.E j = 0 ∧ Tm.M j = 0)
    (hrotM : ∀ x X, IsPolyDom P.m₀ (k + 1) X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
      IsRot R → ∀ Ψ h g, Def6.l1 g < 1 → Def6.l1 (rotField R g) < 1 →
      Dom.dom (k + 1) (Tm.gs (k + 1) X) Ψ h →
      Dom.dom (k + 1) (Tm.gs (k + 1) X) (rotField R Ψ) (rotField R h) →
      Tm.M (k + 1) x X (rotField R Ψ) (rotField R h) (rotField R g) =
        R.mulVec (Tm.M (k + 1) x X Ψ h g))
    (H : NewLevelClausesAt P a ν Tm Dz DM) :
    SFTermClauses P Dom (newLevelTerms Tm) := by
  obtain ⟨hgs, -, hpav, hanE, hrotE, heucE, hlocE, hbdE, heucEloc, -, hanM, -, heucM, hlocM, hbdM,
    heucMloc, -⟩ := H
  have hlt : ∀ {j : ℕ}, j ≤ k + 1 → ¬ j ≤ k → j = k + 1 := fun h1 h2 => by omega
  have hEj : ∀ j, ¬ j ≤ k + 1 → (newLevelTerms Tm).E j = 0 := fun j hj => by
    rw [newLevelTerms_E Tm (by omega)]; exact (htop j (by omega)).1
  have hMj : ∀ j, ¬ j ≤ k + 1 → (newLevelTerms Tm).M j = 0 := fun j hj => by
    rw [newLevelTerms_M Tm (by omega)]; exact (htop j (by omega)).2
  have hElocz : ∀ j, j ≤ k → ∀ y Ψ h, Eloc P.m₀ (newLevelTerms Tm) j y Ψ h = 0 :=
    fun j hj y Ψ h => by simp [Eloc, newLevelTerms_E_le Tm hj]
  have hMlocz : ∀ j, j ≤ k → ∀ x Ψ h g, Mloc P.m₀ (newLevelTerms Tm) j x Ψ h g = 0 :=
    fun j hj x Ψ h g => by simp [Mloc, newLevelTerms_M_le Tm hj]
  refine
    { gs_spec := ?_, analyticE := ?_, analyticM := ?_, rotE := ?_, pavingGS := ?_, eucE := ?_,
      eucEloc := ?_, rotM := ?_, eucM := ?_, eucMloc := ?_, localE := ?_, localM := ?_,
      boundE := ?_, boundM := ?_ }
  · intro j hj1 hjk X hX
    by_cases hk : j ≤ k
    · rw [newLevelTerms_gs_le Tm hk X]
      exact ⟨(levelGS_strong hj1 _ X).subset, (levelGS_strong hj1 _ X).noAbove⟩
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk]
      exact hgs X hX
  · intro j hj1 hjk y X hX hy
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_E_le Tm hk, Pi.zero_apply]
      exact analyticOnNhd_const
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_E Tm hk, newLevelTerms_gs Tm hk]
      exact (hanE y X hX hy).mono fun p hp => hdom _ _ _ hp
  · intro j hj1 hjk x X hX hx
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_M_le Tm hk, Pi.zero_apply]
      exact analyticOnNhd_const
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_M Tm hk, newLevelTerms_gs Tm hk]
      exact (hanM x X hX hx).mono fun p hp => ⟨hdom _ _ _ hp.1, hp.2⟩
  · intro j hj1 hjk y X hX hy R hR Ψ h h1 h2
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_E_le Tm hk, Pi.zero_apply]
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk] at h1 h2
      rw [newLevelTerms_E Tm hk]
      exact hrotE y X hX hy R hR Ψ h (hdom _ _ _ h1) (hdom _ _ _ h2)
  · intro j hj1 hjk X hX r hr i
    by_cases hk : j ≤ k
    · rw [newLevelTerms_gs_le Tm hk, newLevelTerms_gs_le Tm hk]
      by_cases hi : i ≤ j
      · simp only [levelGS, hi, ↓reduceIte, Finset.coe_univ, Set.image_univ]
        exact (Equiv.range_eq_univ _).symm
      · simp [levelGS, hi]
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk]
      exact hpav X hX r hr i
  · intro j hj1 hjk y X hX hy r hr Ψ h h1 h2
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_E_le Tm hk, Pi.zero_apply]
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk] at h1 h2
      rw [newLevelTerms_E Tm hk]
      exact heucE y X hX hy r hr Ψ h (hdom _ _ _ h1) (hdom _ _ _ h2)
  · intro j hj1 hjk y r hr Ψ h h1 h2
    by_cases hk : j ≤ k
    · rw [hElocz j hk, hElocz j hk]
    · obtain rfl := hlt hjk hk
      have e : ∀ y' Ψ' h', Eloc P.m₀ (newLevelTerms Tm) (k + 1) y' Ψ' h' =
          Eloc P.m₀ Tm (k + 1) y' Ψ' h' := fun _ _ _ => by simp [Eloc, newLevelTerms_E Tm hk]
      rw [e, e]
      exact heucEloc hjk y r hr Ψ h (hdom _ _ _ h1) (hdom _ _ _ h2)
  · intro j hj1 hjk x X hX hx R hR Ψ h g hg hg' h1 h2
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_M_le Tm hk, Pi.zero_apply, Matrix.mulVec_zero]
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk] at h1 h2
      rw [newLevelTerms_M Tm hk]
      exact hrotM x X hX hx R hR Ψ h g hg hg' h1 h2
  · intro j hj1 hjk x X hX hx r hr Ψ h g h1 h2
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_M_le Tm hk, Pi.zero_apply]
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk] at h1 h2
      rw [newLevelTerms_M Tm hk]
      exact heucM x X hX hx r hr Ψ h g (hdom _ _ _ h1) (hdom _ _ _ h2)
  · intro j hj1 hjk x r hr Ψ h g h1 h2
    by_cases hk : j ≤ k
    · rw [hMlocz j hk, hMlocz j hk]
    · obtain rfl := hlt hjk hk
      have e : ∀ x' Ψ' h' g', Mloc P.m₀ (newLevelTerms Tm) (k + 1) x' Ψ' h' g' =
          Mloc P.m₀ Tm (k + 1) x' Ψ' h' g' := fun _ _ _ _ => by simp [Mloc, newLevelTerms_M Tm hk]
      rw [e, e]
      exact heucMloc hjk x r hr Ψ h g (hdom _ _ _ h1) (hdom _ _ _ h2)
  · intro j y X Ψ Ψ' h h' hag
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_E_le Tm hk, Pi.zero_apply]
    · by_cases hk1 : j ≤ k + 1
      · obtain rfl := hlt hk1 hk
        rw [newLevelTerms_E Tm hk]
        exact hlocE y X Ψ Ψ' h h' hag
      · simp only [hEj j hk1, Pi.zero_apply]
  · intro j x X Ψ Ψ' h h' g g' hag
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_M_le Tm hk, Pi.zero_apply]
    · by_cases hk1 : j ≤ k + 1
      · obtain rfl := hlt hk1 hk
        rw [newLevelTerms_M Tm hk]
        exact hlocM x X Ψ Ψ' h h' g g' hag
      · simp only [hMj j hk1, Pi.zero_apply]
  · intro j hj1 hjk y X hX hy Ψ h h1
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_E_le Tm hk, Pi.zero_apply, norm_zero]
      positivity
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk] at h1
      rw [newLevelTerms_E Tm hk]
      exact hbdE y X hX hy Ψ h (hdom _ _ _ h1)
  · intro j hj1 hjk x X hX hx Ψ h g h1 hg
    by_cases hk : j ≤ k
    · simp only [newLevelTerms_M_le Tm hk, Pi.zero_apply]
      have h0 : vn (0 : Fin N → ℂ) = 0 := by simp [vn]
      rw [h0]
      have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    · obtain rfl := hlt hjk hk
      rw [newLevelTerms_gs Tm hk] at h1
      rw [newLevelTerms_M Tm hk]
      exact hbdM x X hX hx Ψ h g (hdom _ _ _ h1) hg

open Classical in
/-- **The clauses of the new level at one torus from local families with (A1)–(A5)** (route R-LOC):
the label inputs `hTlblock`, `hTlan`, `hTlloc`, `hTlbd`, `hTlrot`, `hDz` of
`localClass_newLevel_of_expansion_cast` from the families `f z` of the step chain's coefficient
family `e z` (`newLabels_castInputs_of_localFamily`, with `𝒯E` all label sets, the step's weights
and mass and the density `densE0 C`); the other inputs of `localClass_newLevel_of_expansion_cast`
  are
the hypotheses: the generating sets and the terms of the new level (`hgs`, `hE`,
  `hM`: the definition
of the new level of the step map), the bound sum `hsum` (`newLabels_hsum_of_chain_bound_thick`), the
covariance of the density (`hDzblock`, `hDzfull`), the source terms and their density (`TM`,
  `DM`). -/
theorem newLevelClausesAt_of_localFamilies {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]
    {ϱ eps pp : ℝ} {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
    (C : StepClass d L N₁ m₁ k N ϱ)
    {N₁' m₁' : ℕ}
    [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {P : Consts}
    (hm : m₁' ≤ P.m₀ + m₁)
    (hN : L ^ P.m₀ ∣ N₁)
    (hL : 3 ≤ L)
    (h3 : 3 ≤ L ^ (P.m₀ + m₁))
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    (hε : P.eps d L (k + 1) ≤ eps)
    [Fintype (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1))]
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hα₀ : 0 ≤ P.α₀)
    (hα : 0 ≤ P.alpha d)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * (3 * P.α₀)) ≤ 1)
    (hc0 : xiC1 d * (3 * P.α₀) ≤ bgC0 d L N)
    (hc1 : xiC1 d * (3 * P.α₀) ≤ bgC1 d L N)
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
    -- the coefficient family of the step chain and its local families (A1)–(A5)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    (b : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ)
    (f : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hfam : ∀ z, NewLevelLocalFamily S P hc hsep Yp π (e z) (f z) (b z))
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
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
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
    -- the labels of the new level (the local families) and their bounds
    (Tl : (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
      → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y p, Tl T y Y p =
      if sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y then f (blockIndex y) T p else 0)
    (EbE : (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
      → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) = Y then b (blockIndex y) T else 0)
    (hsum : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∑ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), EbE τ z Y ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1)
        Y))
    (AE : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hAE : ∀ z Y p, AE z Y p =
      ((Fintype.card (pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1)) :
        ℂ))⁻¹ • ∑ s : pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L P.m₀ (k + 1),
        ∑ τ ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) 1 (k + 1) Set.univ))), Tl τ (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ :
              Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))⁻¹ p.2)))
    (hE : ∀ y Y Ψ h, Tm.E (k + 1) y Y Ψ h = if y ∈ Y then AE y Y (Ψ, h) else 0)
    (hDzblock : ∀ y y' q, blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' →
        Jr.densE0 C y q = Jr.densE0 C y' q)
    (hDzfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Jr.densE0 C (r y) (actField r q.1, actField r q.2) = Jr.densE0 C y q)
    -- the source terms
    (TM : CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    (hTMan : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → AnalyticOnNhd ℂ (TM x Y)
      ({p | (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2} ×ˢ
        {g | Def6.l1 g < 1}))
    (hTMloc : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y →
      ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → ∀ g, TM x Y (p, g) = TM x Y (p', g))
    (hTMsrc : ∀ x Y (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ z ∈ Y, g z = g' z) → TM x Y (p, g) = TM x Y (p, g'))
    {BM : ℝ}
    (hBM : BM < P.c₉ * ((L : ℝ) ^ (k + 1))⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (hTMbd : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (castG hc (localB (k + 1) (le_refl (k + 1)) (Yp Y) hsep)) p.1 p.2 →
      Def6.l1 g < 1 → vn (TM x Y (p, g)) ≤ BM * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    (hTMrot : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) :
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
      (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      ∑ᶠ Y ∈ polysAt P.m₀ (k + 1) x, TM x Y (q, g) = DM x (q, g))
    (hDMfull : ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        q.1 q.2 →
      (xiFieldDom S.a S.ν (P.eps d L) :
        FieldDom d L N₁ m₁ (k + 1) N (ϱ)).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      DM (r x) ((actField r q.1, actField r q.2), actField r g) = DM x (q, g)) :
    NewLevelClausesAt P S.a S.ν Tm (Jr.densE0 C) DM := by
  obtain ⟨hTlblock, hTlan, hTlloc, hTlbd, hTlrot, hDz⟩ :=
    newLabels_castInputs_of_localFamily Jr C hN hL h3 hG hε hc hsep Yp π hπ e hsupp hval b f
      (fun z => (hfam z).1) (fun z => (hfam z).2.1) (fun z => (hfam z).2.2.1)
      (fun z => (hfam z).2.2.2.1) (fun z => (hfam z).2.2.2.2) Tl hTl EbE hEbE
  exact localClass_newLevel_of_expansion_cast hc hsep hm hN HB hα₀ hα hsmall hc0 hc1 Yp' hYp' Yp
    hYp Tm hgs cpl' hcpl' cpl hcpl _ Tl hTlblock hTlan hTlloc EbE hTlbd hsum hTlrot AE hAE hE _ hDz
    hDzblock hDzfull TM hTMan hTMloc hTMsrc hBM hTMbd hTMrot AM hAM hM DM hDM hDMfull

/-- **The open inputs of A4-1b at a member of the class** (blocker 6), for the image `sf'` of a
member at the scale `k` with the regime index `k₀`:
* `gs_hat` — the generating sets of the new level of the step map are the cast local sets
  `𝔹_{k+1}(X̂)` of ruling R13 (`hatGSOf`; the definition of `Φ`);
* `clauses` — the clauses of the new level at the step's weights and mass
  (`NewLevelClausesAt`, from `newLevelClausesAt_of_localFamilies` at the families of the chain), the
  inclusion of the class domain `sfDom` of the image at the level `k + 1` in their domain (the mass
  response from the step mass to the new birth mass) and the complex rotations of the source terms,
  which bridge (i) (`sfTermClauses_newLevelTerms_of_clauses`) turns into the term clauses of
  `newLevelTerms` on `sfDom`;
* `top` — the levels above `k + 1` vanish;
* `torusIndep` — the torus independence of the new level. -/
structure NewLevelOpenAt (d N L : ℕ) [NeZero L] (P6 : Def6.Consts) (m₁ : ℕ) (ϱ : ℝ) (k₀ k : ℕ)
    (sf' : SFData d L m₁ (k + 1) N ϱ) : Prop where
  gs_hat : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
    ∀ X : Set (CTorus d L N₂ m₁ (k + 1)), IsPolyDom P6.m₀ (k + 1) X →
      (sf'.Tm N₂).gs (k + 1) X = hatGSOf (ϱ := ϱ) P6.m₀ (k + 1) le_rfl X
  clauses : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
    ∃ (a : ℕ → ℝ) (ν : ℝ)
      (Dz : CTorus d L N₂ m₁ (k + 1) → Fld d L N₂ m₁ (k + 1) N × Fld d L N₂ m₁ (k + 1) N → ℂ)
      (DM : CTorus d L N₂ m₁ (k + 1) →
        (Fld d L N₂ m₁ (k + 1) N × Fld d L N₂ m₁ (k + 1) N) × Fld d L N₂ m₁ (k + 1) N → Fin N → ℂ),
      NewLevelClausesAt P6 a ν (sf'.Tm N₂) Dz DM ∧
      (∀ (G : GeneratingSet d L (N₂ * L ^ m₁) (k + 1) ϱ) Ψ h,
        (sfDom P6 k₀ sf' N₂).dom (k + 1) G Ψ h →
          (xiFieldDom a ν (P6.eps d L) : FieldDom d L N₂ m₁ (k + 1) N ϱ).dom (k + 1) G Ψ h) ∧
      (∀ x X, IsPolyDom P6.m₀ (k + 1) X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
        IsRot R → ∀ Ψ h g, Def6.l1 g < 1 → Def6.l1 (rotField R g) < 1 →
        (sfDom P6 k₀ sf' N₂).dom (k + 1) ((sf'.Tm N₂).gs (k + 1) X) Ψ h →
        (sfDom P6 k₀ sf' N₂).dom (k + 1) ((sf'.Tm N₂).gs (k + 1) X) (rotField R Ψ) (rotField R h) →
        (sf'.Tm N₂).M (k + 1) x X (rotField R Ψ) (rotField R h) (rotField R g) =
          R.mulVec ((sf'.Tm N₂).M (k + 1) x X Ψ h g))
  top : ∀ (N₂ : ℕ) [NeZero N₂], ∀ j, k + 1 < j → (sf'.Tm N₂).E j = 0 ∧ (sf'.Tm N₂).M j = 0
  torusIndep : TorusIndep P6.m₀ (fun N₂ _ => newLevelTerms (sf'.Tm N₂))

section Input

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (cs₀ : ℝ → ℝ → OpConsts) (ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **A4-1b from its open inputs** (blocker 6): if at every member `sf` of the class `ℛ_k`
(`SFClassAt`), `1 ≤ k < k₀`, for `β ≥ β₀(κ, c₉)` and `0 < ν ≤ 7/8 L⁻²`, the image `Φ sf` has the
open inputs `NewLevelOpenAt` (the generating sets `𝔹_{k+1}(X̂)`, the clauses of the new level read on
the class domain, the torus independence), then `SFNewLevelInput` holds: the hat and the strong
specification are `hatSpec_hatGSOf`, `gsSpecStrong_hatGSOf` (`L ≥ 3`, cube exponent below `m₀`: the
ties), the other clauses are the inputs. -/
theorem sfNewLevelInput_of_open
    (hL3 : ∀ κ c₉, 3 ≤ (T κ c₉).L)
    (hhat : ∀ κ c₉, hatScale (T κ c₉).L (C7 κ c₉).m₁ (ϱ κ c₉) < (P6 κ c₉).m₀)
    (hE₀ : ∀ κ c₉, 0 ≤ (P6 κ c₉).E₀) (hc₉' : ∀ κ c₉, 0 < (P6 κ c₉).c₉)
    (hopen : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 → ∀ [NeZero (T κ c₉).L],
      ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
      ∀ sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉),
        SFClassAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉) (cs₀ κ c₉).aKer β ν k sf →
        NewLevelOpenAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉)
          (kZero d (T κ c₉).L β ν) k (Φ κ c₉ β ν k sf)) :
    SFNewLevelInput d N T P6 C7 cs₀ ϱ Φ := by
  unfold SFNewLevelInput SFImageInput SFImageInputGen
  intro κ hκ c₉ hc₉
  obtain ⟨β₀, H⟩ := hopen κ hκ c₉ hc₉
  refine ⟨β₀, ?_⟩
  intro β hβ ν hν0 hν _ k hk1 hk sf hsf
  have O := H β hβ ν hν0 hν k hk1 hk sf hsf
  dsimp only [SFNewLevelQ]
  refine ⟨?_, ?_, ?_, O.torusIndep⟩
  · intro N₂ _ hN₂
    obtain ⟨_, _, _, _, hcl, hdom, hrotM⟩ := O.clauses N₂ hN₂
    exact sfTermClauses_newLevelTerms_of_clauses _ (hE₀ κ c₉) (hc₉' κ c₉) hdom (O.top N₂) hrotM
      hcl
  · intro N₂ _ hN₂ X hX
    rw [O.gs_hat N₂ hN₂ X hX]
    exact gsSpecStrong_hatGSOf (hL3 κ c₉) (hhat κ c₉) X
  · intro N₂ _ hN₂ X hX
    rw [O.gs_hat N₂ hN₂ X hX]
    exact hatSpec_hatGSOf _ _ _ X

end Input

end Balaban.RootFSpine
