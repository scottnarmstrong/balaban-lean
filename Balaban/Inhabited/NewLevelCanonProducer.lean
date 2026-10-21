/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonPinsOfIrrel
public import Balaban.Inhabited.StepTowerBeta0OldFields

/-!
# The canonically indexed system of inherited levels

`canonOldTermSystem`: the system of inherited levels whose index type is the set `AdmPairs` of
admissible irrelevant pairs of the class, with the old terms `irrelTorus`, the covering data given by
a canonical cover `F`, and the decoupled fields with their pins given per pair.  It satisfies
`OldTermsCanonPinsAt` (surjectivity onto `AdmPairs` and the cover pins hold by construction) and
`OldTermsAreIrrel`.  The decoupled fields `F₁L`, `SolL`, `FkL` and their pins are inputs: the chain
produces them for each admissible pair (`StepTowerBeta0Families`, where `OldTermSystem.mk` is
applied to data quantified over the index type), they are not available as standalone lemmas.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The set of admissible pairs is finite. -/
theorem admPairs_finite (m₀ kk : ℕ) :
    (AdmPairs L N₁ m₁ k d m₀ kk).Finite := by
  classical
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Iic kk)
    (Set.finite_univ.prod Set.finite_univ)) ?_
  intro p hp
  exact ⟨Set.mem_Iic.2 hp.2.1, Set.mem_univ _, Set.mem_univ _⟩

/-- **The canonically indexed system of inherited levels.** -/
noncomputable def canonOldTermSystem (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (t : ℝ) {ϱ₁ : ℝ} (F : CanonCover d L N₁ m₁ k ϱ ϱ₁)
    (i₀ i₁ : Fin N) (κ BG BG₂ δ₁ : ℝ)
    (F₁L : AdmPairs L N₁ m₁ k d C.m₀ k → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (SolL : AdmPairs L N₁ m₁ k d C.m₀ k → Dec2.DecParams (coverOf S.G') ×
      Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (FkL : ∀ p : AdmPairs L N₁ m₁ k d C.m₀ k, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((F.GkC p.1.1 p.1.2.1 p.1.2.2).Ω 1 × Fin N → ℂ) × ((F.GkC p.1.1 p.1.2.1 p.1.2.2).Ω 1 → ℂ))
    (hF₁L : ∀ p, DecFieldPin S κ BG (F₁L p))
    (hSolL : ∀ p, DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * t))) δ₁ (SolL p))
    (hFkL : ∀ p, FkPin S (F.GkC p.1.1 p.1.2.1 p.1.2.2) (FkL p)) : OldTermSystem S t :=
  haveI : Fintype (AdmPairs L N₁ m₁ k d C.m₀ k) := (admPairs_finite C.m₀ k).fintype
  { ι := AdmPairs L N₁ m₁ k d C.m₀ k
    fin := inferInstance
    m₀ := C.m₀
    jL := fun p => p.1.1
    X₁f := fun p => F.X₁fC p.1.1 p.1.2.1 p.1.2.2
    𝒦X := fun p => F.𝒦XC p.1.1 p.1.2.1 p.1.2.2
    XL := fun p => p.1.2.2 ∪ box (cbase (cellSide L C.m₀ m₁ p.1.1) p.1.2.1 -
      natT fun _ => L / 2 * cellSide L C.m₀ m₁ p.1.1) (L * cellSide L C.m₀ m₁ p.1.1)
    ϱ₁ := ϱ₁
    Gk := fun p => F.GkC p.1.1 p.1.2.1 p.1.2.2
    Gj := fun p => F.GjC p.1.1 p.1.2.1 p.1.2.2
    Eτ := fun p r => irrelTorus C.m₀ C.Tm i₀ i₁ p.1.1 p.1.2.1 p.1.2.2 r.1 r.2
    F₁L := F₁L
    SolL := SolL
    FkL := FkL
    ρ := F.ρC
    κ := κ
    BG := BG
    BG₂ := BG₂
    δ₁ := δ₁
    hF₁L := hF₁L
    hSolL := hSolL
    hFkL := hFkL }

/-- **The canonically indexed system has the canonical pins.** -/
theorem canonOldTermSystem_pins (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (t : ℝ) {ϱ₁ : ℝ} (F : CanonCover d L N₁ m₁ k ϱ ϱ₁)
    (i₀ i₁ : Fin N) (κ BG BG₂ δ₁ : ℝ) F₁L SolL FkL hF₁L hSolL hFkL :
    OldTermsCanonPinsAt S C (canonOldTermSystem S C t F i₀ i₁ κ BG BG₂ δ₁ F₁L SolL FkL hF₁L hSolL
      hFkL) (by exact F) i₀ i₁ := by
  refine ⟨rfl, fun p => p.1.2.1, fun p => p.1.2.2, fun _ _ => rfl, ⟨fun p _ => p.2, fun a _ b _ h => ?_,
    fun p hp => ⟨⟨p, hp⟩, Set.mem_univ _, rfl⟩⟩, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  exact Subtype.ext h

/-- **The canonically indexed system with the pinned fields chosen** (`exists_decFieldPin`,
`exists_decSolPin`, `exists_fkPin`): the inputs are the core hypotheses `FlCore` of the step and the
background hypothesis `BgHyp` of the generating sets `Gk` of the canonical cover. -/
noncomputable def canonOldTermSystemOf (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (t : ℝ) {ϱ₁ : ℝ} (F : CanonCover d L N₁ m₁ k ϱ ϱ₁)
    (i₀ i₁ : Fin N) {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ t Kc Cx c₂ BG₂ δ₁)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L S.a₁) S.ν) : OldTermSystem S t :=
  canonOldTermSystem S C t F i₀ i₁ κ BG BG₂ δ₁ (fun _ => (exists_decFieldPin S hC).choose)
    (fun _ => (exists_decSolPin S hC).choose)
    (fun p => (exists_fkPin (N := N) S (F.GkC p.1.1 p.1.2.1 p.1.2.2) HBk).choose)
    (fun _ => (exists_decFieldPin S hC).choose_spec) (fun _ => (exists_decSolPin S hC).choose_spec)
    (fun p => (exists_fkPin (N := N) S (F.GkC p.1.1 p.1.2.1 p.1.2.2) HBk).choose_spec)

/-- The canonical pins of `canonOldTermSystemOf`. -/
theorem canonOldTermSystemOf_pins (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (t : ℝ) {ϱ₁ : ℝ} (F : CanonCover d L N₁ m₁ k ϱ ϱ₁)
    (i₀ i₁ : Fin N) {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ t Kc Cx c₂ BG₂ δ₁) HBk :
    OldTermsCanonPinsAt S C (canonOldTermSystemOf S C t F i₀ i₁ hC HBk) F i₀ i₁ :=
  canonOldTermSystem_pins S C t F i₀ i₁ κ BG BG₂ δ₁ _ _ _ _ _ _

end Balaban.Inhabited
