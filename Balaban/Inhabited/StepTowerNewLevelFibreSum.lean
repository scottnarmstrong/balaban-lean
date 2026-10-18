/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelFibreCount

/-!
# `hsum` for the new labels from the entropy-weighted fibre count (`StepTowerNewLevelFibreSum`)

The repair of `newLabels_hsum_of_chain_bound` (`StepTowerNewLevelSum.lean`), whose rate condition
`κ + γ log 2 ≤ ρ/α` cannot hold for the tower.  With `weighted_fibre_le` in place of the crude
count `card_fibre_le` the condition on the rate is
`κ < (ρ - a_ent - 1)/α`, `α = 1 + L^{2d} c₁ · 4 d L`, and the constant is
`E₀ ≥ (A₁ + A₂) γ (K₀ + 1) (1 + 1/ε) e^{ρ - a_ent - 1}`, `ε = (ρ - a_ent - 1)/α - κ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Sum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **`hsum` of the new-level theorem, from a one-term bound, by the entropy count.**  Let
`b(z, T′) ≤ B e^{-ρ d_Ext T′}` with `0 ≤ B` and `a_ent + 1 ≤ ρ`, and let `κ < (ρ - a_ent - 1)/α`,
`α = 1 + L^{2d} c₁ · 4 d L`.  If
`B γ (K₀ + 1) (1 + 1/ε) e^{ρ - a_ent - 1} ≤ E₀` with `γ = (L^{m₀-1})^d c₁` and
`ε = (ρ - a_ent - 1)/α - κ`, then for every polymer `Y` of index `m₀` and every centre
`∑_{T′} EbE T′ y Y ≤ E₀ e^{-κ d_{m₀}(Y)}`. -/
theorem newLabels_hsum_of_entropy (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (b : RootIdx d L N₁ m₁ K → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) 1 K Set.univ) → ℝ)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) →
      CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0)
    {B ρ κ E₀ : ℝ} (hB : 0 ≤ B) (hρ : aEnt d L + 1 ≤ ρ)
    (hb : ∀ z T, b z T ≤ B * Real.exp (-ρ * dExt T))
    (hκ : κ < (ρ - (aEnt d L + 1)) /
      (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)))
    (hE₀ : B * ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) * (K0 d L (aEnt d L + 1) + 1) *
      (1 + 1 / ((ρ - (aEnt d L + 1)) /
        (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - κ)) *
      Real.exp (ρ - (aEnt d L + 1)) ≤ E₀) :
    ∀ y (Y : Set (CTorus d L N₁ m₁ K)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y → y ∈ Y →
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y ≤
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  intro y Y hY hy
  have hc1 := one_le_c1 d L
  set α : ℝ := 1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L) with hα
  have hα1 : 1 ≤ α := by
    have : (0 : ℝ) ≤ ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L) := by positivity
    linarith
  have hαpos : 0 < α := by linarith
  set r : ℝ := aEnt d L + 1 with hr
  set γ : ℝ := (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L with hγ
  set s := sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y with hs
  have hs0 : 0 ≤ s := treeLenCovOne_nonneg m₀ K Y
  set ε : ℝ := (ρ - r) / α - κ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hK0 := K0_pos d L r
  have hγ0 : 0 ≤ γ := by positivity
  have hU : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ),
      EbE T y Y ≤ B * (if sitesOf (piHull m₀ (sitesOf T)) = Y then
        Real.exp (-ρ * dExt T) else 0) := by
    intro T
    rw [hEbE]
    split_ifs
    · exact hb _ T
    · simp
  have hw := weighted_fibre_le (m₁ := m₁) hN hM hY hy hρ
  have h1 : 1 + s ≤ (1 + 1 / ε) * Real.exp (ε * s) := by
    have e1 := Real.add_one_le_exp (ε * s)
    have : 1 + s ≤ (1 + 1 / ε) * (ε * s + 1) := by
      have : (1 + 1 / ε) * (ε * s + 1) = 1 + s + ε * s + 1 / ε := by
        field_simp
        ring
      rw [this]
      have : 0 ≤ ε * s := by positivity
      have : 0 ≤ 1 / ε := by positivity
      linarith
    refine this.trans (mul_le_mul_of_nonneg_left e1 (by positivity))
  calc ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y
      ≤ ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), B * (if sitesOf (piHull m₀ (sitesOf T)) = Y then
          Real.exp (-ρ * dExt T) else 0) := Finset.sum_le_sum fun T _ => hU T
    _ = B * ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (K := K) 1 K Set.univ))), (if sitesOf (piHull m₀ (sitesOf T)) = Y then
          Real.exp (-ρ * dExt T) else 0) := by rw [Finset.mul_sum]
    _ ≤ B * (γ * (1 + s) * (K0 d L r + 1) * Real.exp (-(ρ - r) * (s / α - 1))) :=
        mul_le_mul_of_nonneg_left hw hB
    _ ≤ B * (γ * ((1 + 1 / ε) * Real.exp (ε * s)) * (K0 d L r + 1) *
          Real.exp (-(ρ - r) * (s / α - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hB
        gcongr
    _ = (B * γ * (K0 d L r + 1) * (1 + 1 / ε) * Real.exp (ρ - r)) * Real.exp (-κ * s) := by
        have : Real.exp (ε * s) * Real.exp (-(ρ - r) * (s / α - 1)) =
            Real.exp (ρ - r) * Real.exp (-κ * s) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hε]
          field_simp
          ring
        calc _ = B * γ * (K0 d L r + 1) * (1 + 1 / ε) *
              (Real.exp (ε * s) * Real.exp (-(ρ - r) * (s / α - 1))) := by ring
          _ = _ := by rw [this]; ring
    _ ≤ E₀ * Real.exp (-κ * s) := mul_le_mul_of_nonneg_right hE₀ (Real.exp_pos _).le

open Classical in
/-- **`hsum` for the two-term bound of the class chain, by the entropy count.**  The
repair of `newLabels_hsum_of_chain_bound`: with `0 ≤ ρ ≤ min (ρ₁, ρ₂)`, `a_ent + 1 ≤ ρ`, the rate
condition is `κ < (ρ - a_ent - 1)/α` and the constant `(A₁ + A₂) γ (K₀ + 1) (1 + 1/ε)
e^{ρ - a_ent - 1} ≤ E₀`, `ε = (ρ - a_ent - 1)/α - κ`. -/
theorem newLabels_hsum_of_chain_bound' (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (b : RootIdx d L N₁ m₁ K → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) 1 K Set.univ) → ℝ)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) →
      CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0)
    {A₁ A₂ ρ₁ ρ₂ ρ κ E₀ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hρ : aEnt d L + 1 ≤ ρ)
    (hρ₁ : ρ ≤ ρ₁) (hρ₂ : ρ ≤ ρ₂)
    (hb : ∀ z T, b z T ≤ A₁ * Real.exp (-ρ₁ * dExt T) + A₂ * Real.exp (-ρ₂ * dExt T))
    (hκ : κ < (ρ - (aEnt d L + 1)) /
      (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)))
    (hE₀ : (A₁ + A₂) * ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) *
      (K0 d L (aEnt d L + 1) + 1) *
      (1 + 1 / ((ρ - (aEnt d L + 1)) /
        (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - κ)) *
      Real.exp (ρ - (aEnt d L + 1)) ≤ E₀) :
    ∀ y (Y : Set (CTorus d L N₁ m₁ K)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y → y ∈ Y →
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y ≤
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  have hρ0 : 0 ≤ ρ := (add_nonneg (aEnt_nonneg d L) zero_le_one).trans hρ
  refine newLabels_hsum_of_entropy hN hM b EbE hEbE (B := A₁ + A₂) (add_nonneg hA₁ hA₂) hρ
    (fun z T => ?_) hκ hE₀
  have hd := dExt_nonneg T
  have e1 : Real.exp (-ρ₁ * dExt T) ≤ Real.exp (-ρ * dExt T) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-ρ₂ * dExt T) ≤ Real.exp (-ρ * dExt T) :=
    Real.exp_le_exp.2 (by nlinarith)
  refine (hb z T).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left e1 hA₁, mul_le_mul_of_nonneg_left e2 hA₂]

end Sum

end Balaban.Inhabited
