/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Expansion
public import Balaban.LargeField.R.RGasRepR4Decor

/-!
# A fixed localization recipe for the new R boundary term

`astra-aligned/ALIGNED.md` Round 4, equations (39)–(43), fixes the plan-B
choice for the new boundary terms of P7 (3.22)–(3.25), printed pp. 526–527.
For a specified decoupled extension `F S` of the combined old/new exponent
difference, `r4Fresh` is the P3 mixed-derivative coefficient `coef`, summed
over connected cut families with final localization domain `Y`.

The physical extension is **not** supplied by this definition.  The theorems
below expose the exact P3 analytic/locality premises needed for the aggregate
identity and the cut-locality premise needed to discard removed members not
meeting `Y`.  They do not assert those premises for `Rep.B` or the physical
P7 action.  The source for `evTerm` and its estimates is P3, §4, printed
pp. 67–82, formalized by `Localization.localization_expansion`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Analysis Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
  {ι : Type*} [DecidableEq ι] [Fintype ι] {Zt U : Type*}

/-- The chosen new boundary coefficient at final domain `Y` and removed
decoration `S`: P3's connected-family coefficient of the specified decoupled
extension of the P7 (3.22)–(3.25) exponent residual. -/
noncomputable def r4Fresh (c : ι → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Set (CTorus d L N₁ m₁ K))
    (F : Finset Zt → U → (ι → ℂ) → ℂ)
    (S : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U) : ℂ :=
  evTerm c G m₀ X₁ (F S) Y u

/-- Unfold the fixed P3 localization/resummation algorithm. -/
theorem r4Fresh_apply (c : ι → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Set (CTorus d L N₁ m₁ K))
    (F : Finset Zt → U → (ι → ℂ) → ℂ)
    (S : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U) :
    r4Fresh (G := G) (m₀ := m₀) c X₁ F S Y u =
      ∑ C ∈ connFams c G m₀ X₁ Y, coef (F S u) C := rfl

/-- Cut-locality of the new coefficient: if two removed decorations give
the same decoupled functional on the cuts of each connected family ending
at `Y`, their `Y` coefficients agree.  The physical application takes the
second decoration to be the members of the first meeting `Y`. -/
theorem r4Fresh_congr_cut (c : ι → ℕ × CTorus d L N₁ m₁ K)
    (X₁ : Set (CTorus d L N₁ m₁ K))
    (F : Finset Zt → U → (ι → ℂ) → ℂ)
    (S S' : Finset Zt) (Y : Set (CTorus d L N₁ m₁ K)) (u : U)
    (hcut : ∀ C ∈ connFams c G m₀ X₁ Y,
      ∀ w ∈ supportedOn C, F S u w = F S' u w) :
    r4Fresh (G := G) (m₀ := m₀) c X₁ F S Y u =
      r4Fresh (G := G) (m₀ := m₀) c X₁ F S' Y u := by
  simp only [r4Fresh_apply]
  exact Finset.sum_congr rfl (fun C hC => coef_congr (hcut C hC))

section Aggregate

variable [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- The aggregate identity of P7 (3.22)–(3.25) for the specified P3
extension: the sum of the chosen coefficients equals the extension at all
cuts open.  In the physical application `F S u 1` must be identified with
the difference of the old and new exponent in P7 (3.23)–(3.25). -/
theorem r4Fresh_aggregate
    (c : ι → ℕ × CTorus d L N₁ m₁ K)
    {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
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
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {Su : Set U}
    (F : Finset Zt → U → (ι → ℂ) → ℂ) (S : Finset Zt)
    {Ag : Finset ι → U → U → Prop}
    {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ Su → Ag C u u)
    (hlink : ∀ C u u', AgY (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) u u' → Ag C u u')
    (hana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F S p.1 p.2)
      (Su ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ Su, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F S u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ₁) Su
      (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) Ag (F S)) :
    (∀ u ∈ Su, F S u 1 = ∑ Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X),
      r4Fresh (G := G) (m₀ := m₀) c (X1 G m₀ j 𝒦X) F S Y u) ∧
    (∀ Y, ∀ u ∈ Su, ∀ u' ∈ Su,
      AgY Y u u' →
      r4Fresh (G := G) (m₀ := m₀) c (X1 G m₀ j 𝒦X) F S Y u =
        r4Fresh (G := G) (m₀ := m₀) c (X1 G m₀ j 𝒦X) F S Y u') ∧
    (∀ Y, ∀ u ∈ Su,
      ‖r4Fresh (G := G) (m₀ := m₀) c (X1 G m₀ j 𝒦X) F S Y u‖ ≤
        Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κ * treeLenCov G m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ
      (r4Fresh (G := G) (m₀ := m₀) c (X1 G m₀ j 𝒦X) F S Y) Su) := by
  exact localization_expansion c hS hd hL hc hcinj hdisj hopt hκ₀ hκ hκ₁
    h1 hlog hEb hrefl hlink hana hbd hloc

end Aggregate

end Balaban.LargeField
