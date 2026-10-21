/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.SFStepClauses
public import Balaban.Spine.FrozenSFClauses

/-!
# The small-field part of the first step as the general step at `k = 0` (A3-1 (a), (g))

At `k = 0` the general small-field step has no inherited levels: the data of scale `0` is the bare
density (`bareSF`), whose terms vanish, and every clause of the scale `1` is the new level's.

* `bareSF`: the small-field data of scale `0`: `β_0 = β`, `ν_0 = ν`, no terms (LFR §II.7.1, D-IV.4:
  the scale-`0` density is the bare Gibbs factor);
* `sfTermClauses_zero_of_newLevel`: the term clauses of the terms of scale `1` follow from those of
  `newLevelTerms` when the level-`0` terms vanish;
* `sfBase_core`, `sfBase_clauses`, `sfFlatBase_clauses`: the `k = 0` analogues of `sfSucc_core`,
  `sfSucc_clauses`, `sfFlatSucc_clauses`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale

namespace Balaban.RootFSpine

section Bare

variable {d L m₁ N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The small-field data of scale `0`** (the bare density, LFR §II.7.1, D-IV.4): `β_0 = β`,
`ν_0 = ν`, no terms (`ℰ = ℳ = 0`, `ℛ = 0`), the other entries are placeholders that no clause reads. -/
noncomputable def bareSF (β ν : ℝ) : SFData d L m₁ 0 N ϱ where
  β := fun _ => β
  ν := fun _ => ν
  z := fun _ => 1
  a := fun _ => 1
  E := fun _ => 0
  Tm := fun _ _ =>
    { E := fun _ _ _ _ _ => 0
      M := fun _ _ _ _ _ _ => 0
      gs := fun _ _ => levelGen 0 }
  Rt := fun _ _ _ _ _ _ => 0
  corr := fun _ _ _ _ _ _ => 0

end Bare

section Zero

variable {d L N₁ m₁ N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The term clauses of the terms of scale `1` from those of the new level**: the terms of the
level `0` vanish, so `newLevelTerms T` and `T` agree except for the generating sets of the level
`0`, which no clause reads. -/
theorem sfTermClauses_zero_of_newLevel {P : Consts} {Dom : FieldDom d L N₁ m₁ (0 + 1) N ϱ}
    {T : Terms d L N₁ m₁ (0 + 1) N ϱ} (h : SFTermClauses P Dom (newLevelTerms T))
    (hE : ∀ y X Ψ h', T.E 0 y X Ψ h' = 0) (hM : ∀ x X Ψ h' g, T.M 0 x X Ψ h' g = 0) :
    SFTermClauses P Dom T := by
  have hEf : (newLevelTerms T).E = T.E := by
    funext j
    by_cases hj : j ≤ 0
    · obtain rfl : j = 0 := by omega
      funext y X Ψ h'
      rw [newLevelTerms_E_le T le_rfl]; exact (hE y X Ψ h').symm
    · exact newLevelTerms_E T hj
  have hMf : (newLevelTerms T).M = T.M := by
    funext j
    by_cases hj : j ≤ 0
    · obtain rfl : j = 0 := by omega
      funext x X Ψ h' g
      rw [newLevelTerms_M_le T le_rfl]; exact (hM x X Ψ h' g).symm
    · exact newLevelTerms_M T hj
  have hg : ∀ j, 1 ≤ j → (newLevelTerms T).gs j = T.gs j := fun j hj =>
    newLevelTerms_gs T (by omega)
  have hEl : ∀ j, Eloc P.m₀ (newLevelTerms T) j = Eloc P.m₀ T j := fun j => by
    funext y Ψ h'; simp only [Eloc, hEf]
  have hMl : ∀ j, Mloc P.m₀ (newLevelTerms T) j = Mloc P.m₀ T j := fun j => by
    funext x Ψ h' g; simp only [Mloc, hMf]
  refine
    { gs_spec := fun j hj1 hjk X hX => ?_
      analyticE := fun j hj1 hjk y X hX hy => ?_
      analyticM := fun j hj1 hjk x X hX hx => ?_
      rotE := fun j hj1 hjk y X hX hy R hR Ψ h' h1 h2 => ?_
      pavingGS := fun j hj1 hjk X hX r hr i => ?_
      eucE := fun j hj1 hjk y X hX hy r hr Ψ h' h1 h2 => ?_
      eucEloc := fun j hj1 hjk y r hr Ψ h' h1 h2 => ?_
      rotM := fun j hj1 hjk x X hX hx R hR Ψ h' g hg1 hg2 h1 h2 => ?_
      eucM := fun j hj1 hjk x X hX hx r hr Ψ h' g h1 h2 => ?_
      eucMloc := fun j hj1 hjk x r hr Ψ h' g h1 h2 => ?_
      localE := fun j y X Ψ Ψ' h1 h2 hag => ?_
      localM := fun j x X Ψ Ψ' h1 h2 g g' hag => ?_
      boundE := fun j hj1 hjk y X hX hy Ψ h' h1 => ?_
      boundM := fun j hj1 hjk x X hX hx Ψ h' g h1 hg1 => ?_ }
  · rw [← hg j hj1]; exact h.gs_spec j hj1 hjk X hX
  · rw [← hg j hj1, ← hEf]; exact h.analyticE j hj1 hjk y X hX hy
  · rw [← hg j hj1, ← hMf]; exact h.analyticM j hj1 hjk x X hX hx
  · rw [← hg j hj1] at h1 h2; rw [← hEf]; exact h.rotE j hj1 hjk y X hX hy R hR Ψ h' h1 h2
  · rw [← hg j hj1]; exact h.pavingGS j hj1 hjk X hX r hr i
  · rw [← hg j hj1] at h1; rw [← hg j hj1] at h2; rw [← hEf]
    exact h.eucE j hj1 hjk y X hX hy r hr Ψ h' h1 h2
  · rw [← hEl]; exact h.eucEloc j hj1 hjk y r hr Ψ h' h1 h2
  · rw [← hg j hj1] at h1 h2; rw [← hMf]
    exact h.rotM j hj1 hjk x X hX hx R hR Ψ h' g hg1 hg2 h1 h2
  · rw [← hg j hj1] at h1 h2; rw [← hMf]
    exact h.eucM j hj1 hjk x X hX hx r hr Ψ h' g h1 h2
  · rw [← hMl]; exact h.eucMloc j hj1 hjk x r hr Ψ h' g h1 h2
  · rw [← hEf]; exact h.localE j y X Ψ Ψ' h1 h2 hag
  · rw [← hMf]; exact h.localM j x X Ψ Ψ' h1 h2 g g' hag
  · rw [← hg j hj1] at h1; rw [← hEf]; exact h.boundE j hj1 hjk y X hX hy Ψ h' h1
  · rw [← hg j hj1] at h1; rw [← hMf]; exact h.boundM j hj1 hjk x X hX hx Ψ h' g h1 hg1

end Zero

section Base

variable {d L m₁ N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The core of the small-field clauses of the first step** (the `k = 0` analogue of `sfSucc_core`):
no inherited levels, so no splice; from the data `sf'` of scale `1` whose terms of the level `0`
are those of the bare density (none), whose new level satisfies the term clauses, the strong
specification of its generating sets and torus independence, whose density exponent is real and
which is torus coherent, the scale `1` has the term clauses `IsSF2` on the read tori, torus
independence, the renormalization conditions and (D8). -/
theorem sfBase_core {P6 : Def6.Consts} {k0 : ℕ} {β ν : ℝ} {sf' : SFData d L m₁ (0 + 1) N ϱ}
    (hTm : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ 0 →
      (sf'.Tm N₂).E j = (liftOldTermsFam (bareSF (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) β ν).Tm N₂).E j ∧
        (sf'.Tm N₂).M j = (liftOldTermsFam (bareSF (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) β ν).Tm N₂).M j ∧
        (sf'.Tm N₂).gs j = (liftOldTermsFam (bareSF (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) β ν).Tm N₂).gs j)
    (hnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (sfDom P6 k0 sf' N₂) (newLevelTerms (sf'.Tm N₂)))
    (hgsnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (X : Set (CTorus d L N₂ m₁ (0 + 1))),
      IsPolyDom P6.m₀ (0 + 1) X → GsSpec.GsSpecStrong (0 + 1) le_rfl X ((sf'.Tm N₂).gs (0 + 1) X))
    (hhatnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (X : Set (CTorus d L N₂ m₁ (0 + 1))),
      IsPolyDom P6.m₀ (0 + 1) X → GsSpec.HatSpec P6.m₀ (0 + 1) X ((sf'.Tm N₂).gs (0 + 1) X))
    (hTInew : TorusIndep P6.m₀ (fun N₂ _ => newLevelTerms (sf'.Tm N₂)))
    (hR' : RenormCondAlong P6.m₀ (0 + 1) (sf'.ν (0 + 1)) sf'.Tm (0 + 1) (torusSeq L P6.m₀)
      (fun n => torusSeq_ne_zero P6.m₀ n))
    (hreal : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (Ψ₀ : CTorus d L N₂ m₁ (0 + 1) → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (g : CTorus d L N₂ m₁ (0 + 1) → Fin N → ℝ) (D : BgData (topGS d L N₂ m₁ (0 + 1) ϱ) N),
      Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
      Xi (topGS d L N₂ m₁ (0 + 1) ϱ) (aIdeal L (0 + 1) (sf'.a (0 + 1)))
        ((⟨k0, sf'.ν⟩ : Regime L).sfBgMass (0 + 1)) (0 + 1) 1
        (P6.p (sf'.β (0 + 1)) / Real.sqrt (sf'.β (0 + 1))) Ψ₀ h₀ →
      (Complex.exp (expo2 P6 ⟨k0, sf'.ν⟩ sf'.β sf'.a (sf'.Tm N₂) (sf'.E N₂) D
        (fun x i => (g x i : ℂ)))).im = 0)
    (hD8new : D8SF P6.m₀ { sf' with Tm := fun N₂ _ => newLevelTerms (sf'.Tm N₂) }) :
    (∃ ρ' : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ (0 + 1) → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ (0 + 1) → Fin N → ℝ) → ℝ,
      ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
        IsSF2 P6 (⟨k0, sf'.ν⟩ : Regime L) sf'.β sf'.a (sfDom P6 k0 sf' N₂) (sf'.Tm N₂) (ρ' N₂)
          (sf'.E N₂)) ∧
      TorusIndep P6.m₀ sf'.Tm ∧
      (∀ j, 1 ≤ j → j ≤ 0 + 1 →
        RenormCondAlong (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ) P6.m₀ (0 + 1)
          ((⟨k0, sf'.ν⟩ : Regime L).ν (0 + 1)) sf'.Tm j (torusSeq L P6.m₀)
          (fun n => torusSeq_ne_zero P6.m₀ n)) ∧ D8SF P6.m₀ sf' := by
  have hE0 : ∀ (N₂ : ℕ) [NeZero N₂] y X Ψ h', (sf'.Tm N₂).E 0 y X Ψ h' = 0 := by
    intro N₂ _ y X Ψ h'
    rw [(hTm N₂ 0 le_rfl).1]
    simp [liftOldTermsFam_apply, liftOldTerms_E, bareSF]
  have hM0 : ∀ (N₂ : ℕ) [NeZero N₂] x X Ψ h' g, (sf'.Tm N₂).M 0 x X Ψ h' g = 0 := by
    intro N₂ _ x X Ψ h' g
    rw [(hTm N₂ 0 le_rfl).2.1]
    simp [liftOldTermsFam_apply, liftOldTerms_M, bareSF]
  have hterms : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (sfDom P6 k0 sf' N₂) (sf'.Tm N₂) := fun N₂ _ hN =>
    sfTermClauses_zero_of_newLevel (hnew N₂ hN) (hE0 N₂) (hM0 N₂)
  have hgs : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ j, 1 ≤ j → ∀ hjk : j ≤ 0 + 1, ∀ X,
      IsPolyDom P6.m₀ j X → GsSpec.GsSpecStrong j hjk X ((sf'.Tm N₂).gs j X) := by
    intro N₂ _ hN j hj1 hjk X hX
    obtain rfl : j = 0 + 1 := by omega
    exact hgsnew N₂ hN X hX
  have hhat : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ j, 1 ≤ j → j ≤ 0 + 1 → ∀ X,
      IsPolyDom P6.m₀ j X → GsSpec.HatSpec P6.m₀ j X ((sf'.Tm N₂).gs j X) := by
    intro N₂ _ hN j hj1 hjk X hX
    obtain rfl : j = 0 + 1 := by omega
    exact hhatnew N₂ hN X hX
  have htor : ∀ (N₂ : ℕ) [NeZero N₂], ∃ ρ, ReadTorus L P6.m₀ N₂ →
      IsSF2 P6 ⟨k0, sf'.ν⟩ sf'.β sf'.a (sfDom P6 k0 sf' N₂) (sf'.Tm N₂) ρ (sf'.E N₂) := by
    intro N₂ _
    by_cases hN : ReadTorus L P6.m₀ N₂
    · obtain ⟨ρ, hρ⟩ := exists_isSF2_of_real (hterms N₂ hN) (hgs N₂ hN) (hhat N₂ hN)
        fun Ψ₀ h₀ g D _ hR hg hX => hreal N₂ hN Ψ₀ h₀ g D hR hg hX
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨fun _ _ _ => 0, fun h => absurd h hN⟩
  have hTI : TorusIndep P6.m₀ sf'.Tm :=
    ⟨fun j hj1 hjk y X' hy ψ h' N₂ N₃ _ _ hnw₂ hnw₃ hp₂ hp₃ => by
      have := hTInew.E_eq j hj1 hjk y X' hy ψ h' N₂ N₃ hnw₂ hnw₃ hp₂ hp₃
      simpa only [newLevelTerms_E _ (show ¬ j ≤ 0 by omega)] using this⟩
  refine ⟨?_, hTI, fun j hj1 hj => ?_, ⟨fun j hj1 hjk x X' ψ h' g N₂ N₃ _ _ hnw₂ hnw₃ hp₂ hp₃ => ?_,
    hD8new.R_eq⟩⟩
  · choose ρ' hρ' using htor
    exact ⟨ρ', hρ'⟩
  · obtain rfl : j = 0 + 1 := by omega
    exact hR'
  · have h1 := hD8new.M_eq j hj1 hjk x X' ψ h' g N₂ N₃ hnw₂ hnw₃ hp₂ hp₃
    simpa only [newLevelTerms_M _ (show ¬ j ≤ 0 by omega)] using h1

end Base

end Balaban.RootFSpine
