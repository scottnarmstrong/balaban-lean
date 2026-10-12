/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeMod
public import Balaban.Localization.TreeLengthCov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 4: the multiscale size dominates the modular size (FLUCTUATION.md §4.2)

Step 4 of the proof of Theorem 4.2 compares the multiscale covering size `d̃^cov_{k+1}(Y)`
(`treeLenCov`) of a polymer domain `Y` meeting `Ω = Ω_{k+1}` with the modular size
`d_Ω(Y ∩ Ω)` of Definition 1.1 "directly: the layer-`(k+1)` cubes of a chosen multiscale family form
an admissible family of Definition 1.1 and `ℓ_n⁻¹ ≥ 1`".

* `layerIndex_le`: the layer index is `≤ K`;
* `bondCost_scaleW_le_bondW`: the top-scale bond weight is at most the multiscale bond weight;
* `G4_subset_of_conn`, `G4_siteConnected_of_conn`: (G4) for a nonempty site-connected `Y`
  (the proofs of `G4_subset`, `G4_siteConnected` use only connectedness of `Y`);
* `dOmega_le_treeLenCov`: `d_Ω(Y ∩ Ω) ≤ d̃^cov(Y)` for a site-connected `Y` with `Ω ⊆ Λ_K`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem layerIndex_le (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (x : CTorus d L N₁ m₁ K) :
    G.layerIndex x ≤ K := by
  classical
  unfold GeneratingSet.layerIndex
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · exact Nat.zero_le _

theorem bondCost_scaleW_le_bondW (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) :
    bondCost (scaleW L m₀ m₁ K) E ≤ bondCost (bondW G m₀) E := by
  refine Finset.sum_le_sum fun p _ => ?_
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold scaleW bondW
  rw [pow_add, mul_inv, pow_add, mul_inv]
  have hm : min (G.layerIndex p.1) (G.layerIndex p.2) ≤ K :=
    (min_le_left _ _).trans (layerIndex_le G _)
  have : ((L : ℝ) ^ K)⁻¹ ≤ ((L : ℝ) ^ min (G.layerIndex p.1) (G.layerIndex p.2))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hL hm)
  have h0 : 0 ≤ ((L : ℝ) ^ m₀)⁻¹ * ((L : ℝ) ^ m₁)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left this h0

omit [NeZero N₁] [NeZero L] in
/-- **(G4), inclusion**, for a nonempty site-connected `Y`. -/
theorem G4_subset_of_conn {Ω Y : Set (CTorus d L N₁ m₁ K)} (hY : SiteConnected Y)
    (hne : (Y ∩ Ω).Nonempty) : Y ⊆ Yhat Ω (Y ∩ Ω) := by
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
  obtain ⟨-, h | h⟩ := key y (hY s0 hs0Y y hy)
  · exact Or.inl ⟨hy, h⟩
  · exact Or.inr h

omit [NeZero N₁] [NeZero L] in
/-- **(G4), connectedness of `Ŷ(S)`**, for a nonempty site-connected `Y`. -/
theorem G4_siteConnected_of_conn {Ω Y : Set (CTorus d L N₁ m₁ K)} (hY : SiteConnected Y)
    (hne : (Y ∩ Ω).Nonempty) : SiteConnected (Yhat Ω (Y ∩ Ω)) := by
  obtain ⟨s0, hs0Y, hs0Ω⟩ := hne
  set Z := Yhat Ω (Y ∩ Ω) with hZ
  have hYZ : Y ⊆ Z := G4_subset_of_conn hY ⟨s0, hs0Y, hs0Ω⟩
  have hsymm : ∀ a b : CTorus d L N₁ m₁ K,
      (a ∈ Z ∧ b ∈ Z ∧ Nbr a b) → (b ∈ Z ∧ a ∈ Z ∧ Nbr b a) :=
    fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have reachY : ∀ x ∈ Y, Relation.ReflTransGen (fun u v => u ∈ Z ∧ v ∈ Z ∧ Nbr u v) s0 x :=
    fun x hx => Relation.ReflTransGen.mono (fun u v h => ⟨hYZ h.1, hYZ h.2.1, h.2.2⟩) s0 x
      (hY s0 hs0Y x hx)
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

/-- **Step 4 of Theorem 4.2: `d_Ω(Y ∩ Ω) ≤ d̃^cov_K(Y)`.**  For a site-connected `Y` meeting `Ω`,
with `Ω ⊆ Λ_K`, and a chosen family of `Y` with a connected structure meeting it (so that
`d̃^cov(Y)` is an infimum over a nonempty set), the layer-`K` cubes of the family and the
structure are admissible for Definition 1.1 on `Ŷ(Y ∩ Ω)`, and `ℓ_n⁻¹ ≥ ℓ_K⁻¹`. -/
theorem dOmega_le_treeLenCov (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) (hK : 1 ≤ K)
    {Ω Y : Set (CTorus d L N₁ m₁ K)} (hΩ : Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    (hY : SiteConnected Y) (hne : (Y ∩ Ω).Nonempty)
    (hex : ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧ MeetsFam m₀ 𝒦 W) :
    dOmega m₀ K Ω (Y ∩ Ω) ≤ ENNReal.ofReal (treeLenCov G m₀ Y) := by
  classical
  have hYZ : Y ⊆ Yhat Ω (Y ∩ Ω) := G4_subset_of_conn hY hne
  have hadm : ∀ x ∈ {x | ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧
      MeetsFam m₀ 𝒦 W ∧ x = bondCost (bondW G m₀) E},
      dOmega m₀ K Ω (Y ∩ Ω) ≤ ENNReal.ofReal x := by
    rintro x ⟨𝒦, W, E, h1, h2, h3, h4, rfl⟩
    have hA : ModAdmissible m₀ K Ω (Yhat Ω (Y ∩ Ω)) (𝒦 K) W E := by
      obtain ⟨hc1, hc2⟩ := h1 K hK le_rfl
      refine ⟨fun b hb => ⟨(hc1 b hb).1, (hc1 b hb).2.1.trans hYZ⟩, fun z hz => ?_, h2,
        h3.trans hYZ, fun b hb => h4 K hK le_rfl b hb⟩
      have hzS : z ∈ Y ∩ Ω := Yhat_inter_subset Ω _ hz
      obtain ⟨b, hb, hzb⟩ := hc2 z hzS.1 (hΩ hzS.2)
      exact Set.mem_iUnion₂.2 ⟨b, hb, hzb⟩
    unfold dOmega
    simp only [G4_siteConnected_of_conn hY hne, ↓reduceIte]
    refine (dcovModE_le_of_admissible hA).trans ?_
    exact ENNReal.ofReal_le_ofReal (bondCost_scaleW_le_bondW G m₀ E)
  obtain ⟨𝒦, W, E, h1, h2, h3, h4⟩ := hex
  have hne' : {x | ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧
      MeetsFam m₀ 𝒦 W ∧ x = bondCost (bondW G m₀) E}.Nonempty := ⟨_, 𝒦, W, E, h1, h2, h3, h4, rfl⟩
  have hfin : dOmega m₀ K Ω (Y ∩ Ω) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hne'
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hadm x hx)
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal (le_csInf hne' fun x hx => ?_)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hadm x hx)
  rwa [ENNReal.toReal_ofReal (by
    obtain ⟨𝒦, W, E, -, -, -, -, rfl⟩ := hx
    exact Finset.sum_nonneg fun p _ => bondW_nonneg G m₀ _ _)] at this

end Balaban.Fluctuation
