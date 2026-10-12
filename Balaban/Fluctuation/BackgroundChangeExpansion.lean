/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.BackgroundChangeCompare
public import Balaban.Localization.I5Expansion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 4: the expansion of one cube term and the empty-intersection split

For one action cube `□` (the set `X` of `CovSetup`, a chosen family `𝒦X`), a function `F u s` of the
data `u` and of the decoupling parameters `s : ι → ℂ`, analytic and bounded by `Eb e^{-(κ-1)Δ}` on the
polydisc and local in the sense of (AE2) (Step 3 of the proof of Theorem 4.2),
`cube_expansion` gives

* `F u 1 = ∑_{Y ∩ Ω = ∅} 𝓔(Y) + ∑_{Y ∩ Ω ≠ ∅} 𝓔(Y)` over the polymer domains `Y = Y[𝒞]`
  (the split of Step 4 / FL-A05: the first sum is the contribution to `b_k`);
* `|𝓔(Y)| ≤ Eb e^{-κ₀ Δ - 2κ d̃^cov(Y)}` (AE, GM3, GM4);
* for a site-connected `Y` meeting `Ω ⊆ Λ_K`: `|𝓔(Y)| ≤ Eb e^{-κ₀ Δ - 2κ d_Ω(Y ∩ Ω)}`, by (G4)
  in the form `dOmega_le_treeLenCov`.

The remaining steps of (4.3) -- summing over the cubes `□ ⊂ Y` (G1), pre-summing the domains `Y` with
the same trace `S = Y ∩ Ω` (G2), and the Step 3 bound on `F_□` -- are not in this file.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Analysis Finset

section Expansion

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
variable {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

open Classical in
/-- **The expansion of one cube term, with the split of Step 4.**  Hypotheses are those of
`localization_expansion` (LOC I-5 resummation) plus the hole `Ω`. -/
theorem cube_expansion (Ω : Set (CTorus d L N₁ m₁ K))
    (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κ κ₀ κ₁ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {S : Set U} {F : U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ C u u', AgY (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) u u' → Ag C u u')
    (hana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F p.1 p.2)
      (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ₁) S (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) Ag F) :
    (∀ u ∈ S, F u 1 =
      ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j 𝒦X)).filter (fun Y => Y ∩ Ω = ∅),
        evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u +
      ∑ Y ∈ (polymerDomains c G m₀ (X1 G m₀ j 𝒦X)).filter (fun Y => (Y ∩ Ω).Nonempty),
        evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u) ∧
    (∀ Y, ∀ u ∈ S, ∀ u' ∈ S, AgY Y u u' →
      evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u = evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u') ∧
    (∀ Y, ∀ u ∈ S, ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖ ≤
      Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κ * treeLenCov G m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y) S) ∧
    (Ω ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)) →
      ∀ Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X), SiteConnected Y → (Y ∩ Ω).Nonempty →
        (dOmega m₀ K Ω (Y ∩ Ω)) ≠ ⊤ ∧ ∀ u ∈ S,
        ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
            - 2 * κ * (dOmega m₀ K Ω (Y ∩ Ω)).toReal)) := by
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := localization_expansion (c := c) hS hd hL hc hcinj hdisj
    hopt hκ₀ hκ hκ₁ h1 hlog hEb (AgY := AgY) hrefl hlink hana hbd hloc
  refine ⟨fun u hu => ?_, hlocY, hbound, hanY, fun hΩ Y hY hYc hYne => ?_⟩
  · rw [hsum u hu, ← Finset.sum_filter_add_sum_filter_not
      (polymerDomains c G m₀ (X1 G m₀ j 𝒦X)) (fun Y => Y ∩ Ω = ∅)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext Y
    simp only [Finset.mem_filter, Set.nonempty_iff_ne_empty]
  · have hK : 1 ≤ K := by have := hS.hjK; omega
    have hex : ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧ MeetsFam m₀ 𝒦 W := by
      obtain ⟨C, hCmem, rfl⟩ := Finset.mem_image.1 hY
      have hconn := (Finset.mem_filter.1 hCmem).2
      obtain ⟨W₀, E₀, hW1, hW2, hW3, hW4⟩ := hopt
      obtain ⟨W, E, hW1', hW2', hW3', -⟩ := gm2_tree hS hd hc C hconn hW1 hW2 hW3
      exact ⟨_, W, E, chosen_KY hc, hW1', hW2', hW3'⟩
    have hle := dOmega_le_treeLenCov G m₀ hK hΩ hYc hYne hex
    have hfin : dOmega m₀ K Ω (Y ∩ Ω) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    refine ⟨hfin, fun u hu => ?_⟩
    refine (hbound Y u hu).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hEb
    have hT := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (treeLenCov_nonneg G m₀ Y)] at hT
    have hκ0 : 0 ≤ κ := by linarith
    nlinarith

end Expansion

end Balaban.Fluctuation
