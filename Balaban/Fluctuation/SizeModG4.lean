/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModUnion
public import Balaban.Fluctuation.SizeModG1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (G4): the support (FLUCTUATION.md Lemma 1.2)

For `Y ∈ 𝒟_j` meeting `Ω` in `S`: `Y ⊆ Ŷ(S)` (`G4_subset`), `Ŷ(S)` is connected
(`G4_siteConnected`), and `d_Ω(S) ≤ d^cov_j(Y)` (`G4_dOmega_le`); if moreover
`Y ∈ 𝒟_j(mod Ω^c)` then `d_Ω(S) ≤ d^cov_j(Y mod Ω^c)` (`G4_dOmega_le_mod`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
theorem Yhat_inter_subset (Ω S : Set (CTorus d L N₁ m₁ K)) : Yhat Ω S ∩ Ω ⊆ S := by
  rintro y ⟨h | ⟨z, hz, -, hy⟩, hΩ⟩
  · exact h
  · exact absurd hΩ hy.1

omit [NeZero N₁] [NeZero L] in
/-- **(G4), inclusion.** -/
theorem G4_subset {Ω Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ j Y) (hne : (Y ∩ Ω).Nonempty) :
    Y ⊆ Yhat Ω (Y ∩ Ω) := by
  obtain ⟨s0, hs0Y, hs0Ω⟩ := hne
  have key : ∀ y, Relation.ReflTransGen (fun u v => u ∈ Y ∧ v ∈ Y ∧ Nbr u v) s0 y →
      y ∈ Y ∧ (y ∈ Ω ∨ ∃ z ∈ Ωᶜ, (∃ s ∈ Y ∩ Ω, Nbr s z) ∧ y ∈ OmegaComp Ω z) := by
    intro y h
    induction h with
    | refl => exact ⟨hs0Y, Or.inl hs0Ω⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.2.1, ?_⟩
      by_cases hcΩ : c ∈ Ω
      · exact Or.inl hcΩ
      · refine Or.inr ?_
        rcases ih.2 with hb | ⟨z, hz, hs, hbz⟩
        · exact ⟨c, hcΩ, ⟨b, ⟨ih.1, hb⟩, hbc.2.2⟩, hcΩ, Relation.ReflTransGen.refl⟩
        · exact ⟨z, hz, hs, hcΩ, hbz.2.tail ⟨hbz.1, hcΩ, hbc.2.2⟩⟩
  intro y hy
  obtain ⟨-, h | h⟩ := key y (hY.2.2 s0 hs0Y y hy)
  · exact Or.inl ⟨hy, h⟩
  · exact Or.inr h

omit [NeZero N₁] [NeZero L] in
/-- **(G4), connectedness of `Ŷ(S)`.** -/
theorem G4_siteConnected {Ω Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ j Y)
    (hne : (Y ∩ Ω).Nonempty) : SiteConnected (Yhat Ω (Y ∩ Ω)) := by
  obtain ⟨s0, hs0Y, hs0Ω⟩ := hne
  set Z := Yhat Ω (Y ∩ Ω) with hZ
  have hYZ : Y ⊆ Z := G4_subset hY ⟨s0, hs0Y, hs0Ω⟩
  have hsymm : ∀ a b : CTorus d L N₁ m₁ K,
      (a ∈ Z ∧ b ∈ Z ∧ Nbr a b) → (b ∈ Z ∧ a ∈ Z ∧ Nbr b a) :=
    fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have reachY : ∀ x ∈ Y, Relation.ReflTransGen (fun u v => u ∈ Z ∧ v ∈ Z ∧ Nbr u v) s0 x :=
    fun x hx => Relation.ReflTransGen.mono (fun u v h => ⟨hYZ h.1, hYZ h.2.1, h.2.2⟩) s0 x
      (hY.2.2 s0 hs0Y x hx)
  have reach : ∀ x ∈ Z, Relation.ReflTransGen (fun u v => u ∈ Z ∧ v ∈ Z ∧ Nbr u v) s0 x := by
    rintro x (⟨hxY, -⟩ | ⟨z, hz, ⟨s, hs, hsz⟩, hx⟩)
    · exact reachY x hxY
    · have hcomp : ∀ y, Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) z y →
          y ∈ Z ∧ Relation.ReflTransGen (fun u v => u ∈ Z ∧ v ∈ Z ∧ Nbr u v) z y := by
        intro y h
        induction h with
        | refl => exact ⟨Or.inr ⟨z, hz, ⟨s, hs, hsz⟩, hz, Relation.ReflTransGen.refl⟩,
            Relation.ReflTransGen.refl⟩
        | @tail b c hab hbc ih =>
          have hcZ : c ∈ Z := Or.inr ⟨z, hz, ⟨s, hs, hsz⟩, hbc.2.1, hab.tail hbc⟩
          exact ⟨hcZ, ih.2.tail ⟨ih.1, hcZ, hbc.2.2⟩⟩
      obtain ⟨hxZ, hzx⟩ := hcomp x hx.2
      have hzZ : z ∈ Z := (hcomp z Relation.ReflTransGen.refl).1
      have hsZ : s ∈ Z := hYZ hs.1
      exact ((reachY s hs.1).tail ⟨hsZ, hzZ, hsz⟩).trans hzx
  intro x hx y hy
  exact (rtg_symm hsymm (reach x hx)).trans (reach y hy)

omit [NeZero N₁] [NeZero L] in
/-- Enlarging `X` to `Z` without adding points of `Ω` keeps an admissible pair admissible. -/
theorem modAdmissible_mono {Ω X Z 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω X 𝒦 W E) (hXZ : X ⊆ Z) (hZΩ : Z ∩ Ω ⊆ X) :
    ModAdmissible m₀ j Ω Z 𝒦 W E := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun b hb => ⟨(h1 b hb).1, (h1 b hb).2.trans hXZ⟩,
    fun z hz => h2 ⟨hZΩ hz, hz.2⟩, h3, h4.trans hXZ, h5⟩

omit [NeZero N₁] [NeZero L] in
/-- A chosen family and structure of `Y` are admissible for every `Ω`. -/
theorem modAdmissible_of_chosen {Ω Y 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h1 : ChosenOne m₀ j Y 𝒦) (h2 : ConnStruct W E) (h3 : (↑W ⊆ Y)) (h4 : MeetsOne m₀ j 𝒦 W) :
    ModAdmissible m₀ j Ω Y 𝒦 W E := by
  refine ⟨h1.1, fun z hz => ?_, h2, h3, h4⟩
  obtain ⟨b, hb, hzb⟩ := h1.2 z hz.1
  exact Set.mem_iUnion₂.2 ⟨b, hb, hzb⟩

/-- **(G4), `d_Ω(S) ≤ d^cov_j(Y)`.** -/
theorem G4_dOmega_le {Ω Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ j Y)
    (hne : (Y ∩ Ω).Nonempty) :
    dOmega m₀ j Ω (Y ∩ Ω) ≤ ENNReal.ofReal (treeLenCovOne m₀ j Y) := by
  classical
  unfold dOmega
  simp only [G4_siteConnected hY hne, ↓reduceIte]
  obtain ⟨𝒦, W, E, hE⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hY
  obtain ⟨h1, h2, h3, h4⟩ := (modAdmissible_iff_chosen (Set.subset_univ Y)).1 hE
  obtain ⟨𝒦', W', E', h1', h2', h3', h4', hc'⟩ := treeLenCovOne_attained m₀ j Y ⟨𝒦, W, E, h1, h2, h3, h4⟩
  have hA := modAdmissible_mono (modAdmissible_of_chosen (Ω := Ω) h1' h2' h3' h4')
    (G4_subset hY hne) ((Yhat_inter_subset Ω _).trans Set.inter_subset_left)
  rw [← hc']
  exact dcovModE_le_of_admissible hA

/-- **(G4), `d_Ω(S) ≤ d^cov_j(Y mod Ω^c)`** for `Y ∈ 𝒟_j(mod Ω^c)`. -/
theorem G4_dOmega_le_mod {Ω Y : Set (CTorus d L N₁ m₁ K)} (hY : DjMod m₀ j Ω Y)
    (hne : (Y ∩ Ω).Nonempty) :
    dOmega m₀ j Ω (Y ∩ Ω) ≤ ENNReal.ofReal (dcovMod m₀ j Ω Y) := by
  classical
  unfold dOmega
  simp only [G4_siteConnected hY.1 hne, ↓reduceIte]
  obtain ⟨𝒦, W, E, hE, hc⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) hY.1)
  have hA := modAdmissible_mono hE (G4_subset hY.1 hne)
    ((Yhat_inter_subset Ω _).trans Set.inter_subset_left)
  rw [← hc]
  exact dcovModE_le_of_admissible hA

end Balaban.Fluctuation
