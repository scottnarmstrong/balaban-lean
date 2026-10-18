/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelFibreSum

/-!
# The closure of the constant `E₀` of the new level (`StepTowerNewLevelE0Close`)

`newLabels_hsum_of_chain_bound'` needs
`E₀ ≥ (A₁ + A₂) Γ`, `Γ = γ (K₀ + 1) (1 + 1/ε) e^{ρ - a_ent - 1}`,
where `A₂` is the constant `B` of the class chain, which depends on the constant `E₀` of the inherited
labels through `B_τ ≤ C_I E₀ …`.  If `A₂ ≤ B₀ + b₁ E₀` with `b₁ Γ ≤ 1/2`, the requirement closes with
the same `E₀`, namely for every `E₀ ≥ 2 Γ (A₁ + B₀)`:
* `closure_requirement`: `(A₁ + A₂) Γ ≤ E₀`;
* `newLabels_hsum_closure`: `hsum` of the new level with this `E₀`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

/-- **The arithmetic of the closure.**  If `A₂ ≤ B₀ + b₁ E₀`, `b₁ Γ ≤ 1/2` and
`2 Γ (A₁ + B₀) ≤ E₀`, then `(A₁ + A₂) Γ ≤ E₀`. -/
theorem closure_requirement {A₁ A₂ B₀ b₁ Γ E₀ : ℝ} (hΓ : 0 ≤ Γ) (hA₂ : A₂ ≤ B₀ + b₁ * E₀)
    (hb : b₁ * Γ ≤ 1 / 2) (hE₀ : 2 * Γ * (A₁ + B₀) ≤ E₀) (hE₀0 : 0 ≤ E₀) :
    (A₁ + A₂) * Γ ≤ E₀ := by
  have h1 : (A₁ + A₂) * Γ ≤ (A₁ + B₀) * Γ + b₁ * E₀ * Γ := by
    have := mul_le_mul_of_nonneg_right (add_le_add_left hA₂ A₁) hΓ
    linarith
  have h2 : b₁ * E₀ * Γ ≤ E₀ / 2 := by
    have := mul_le_mul_of_nonneg_left hb hE₀0
    linarith
  linarith

open Classical in
/-- **`hsum` of the new level with the closed constant.**  The statement of
`newLabels_hsum_of_chain_bound'` with `A₂` bounded affinely by `E₀`: `A₂ ≤ B₀ + b₁ E₀`, `b₁ Γ ≤ 1/2`,
`2 Γ (A₁ + B₀) ≤ E₀`, `Γ = γ (K₀ + 1) (1 + 1/ε) e^{ρ - a_ent - 1}`. -/
theorem newLabels_hsum_closure {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (b : RootIdx d L N₁ m₁ K → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) 1 K Set.univ) → ℝ)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) →
      CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0)
    {A₁ A₂ B₀ b₁ ρ₁ ρ₂ ρ κ E₀ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hρ : aEnt d L + 1 ≤ ρ)
    (hρ₁ : ρ ≤ ρ₁) (hρ₂ : ρ ≤ ρ₂)
    (hb : ∀ z T, b z T ≤ A₁ * Real.exp (-ρ₁ * dExt T) + A₂ * Real.exp (-ρ₂ * dExt T))
    (hκ : κ < (ρ - (aEnt d L + 1)) /
      (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)))
    (hA₂le : A₂ ≤ B₀ + b₁ * E₀) (hE₀0 : 0 ≤ E₀)
    (hsmall : b₁ * ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
      (K0 d L (aEnt d L + 1) + 1) *
      (1 + 1 / ((ρ - (aEnt d L + 1)) /
        (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - κ)) *
      Real.exp (ρ - (aEnt d L + 1))) ≤ 1 / 2)
    (hE₀ : 2 * (((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
      (K0 d L (aEnt d L + 1) + 1) *
      (1 + 1 / ((ρ - (aEnt d L + 1)) /
        (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - κ)) *
      Real.exp (ρ - (aEnt d L + 1)))) * (A₁ + B₀) ≤ E₀) :
    ∀ y (Y : Set (CTorus d L N₁ m₁ K)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y → y ∈ Y →
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y ≤
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  have hc1 := one_le_c1 d L
  have hε0 : 0 < (ρ - (aEnt d L + 1)) /
      (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - κ := by linarith
  have hΓ : 0 ≤ (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L * (K0 d L (aEnt d L + 1) + 1) *
      (1 + 1 / ((ρ - (aEnt d L + 1)) /
        (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - κ)) *
      Real.exp (ρ - (aEnt d L + 1)) := by
    have := K0_pos d L (aEnt d L + 1)
    positivity
  refine newLabels_hsum_of_chain_bound' hN hM b EbE hEbE hA₁ hA₂ hρ hρ₁ hρ₂ hb hκ ?_
  have := closure_requirement hΓ hA₂le hsmall hE₀ hE₀0
  convert this using 1
  ring

end Balaban.Inhabited
