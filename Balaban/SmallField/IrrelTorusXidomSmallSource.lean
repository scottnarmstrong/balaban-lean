/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSmall
import Mathlib.Tactic.Linarith

/-!
# The small-polymer comparison at the scaled source datum
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ νs : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The source chart's real and complex field estimates discharge all local-coordinate
hypotheses of the `CRotE` comparison in the real-centre frame. -/
theorem trickFnA_shiftTerm_eq_of_scaled_source_small
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hcr : CRotE P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    (hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    {p : CTorus d L N₁ m₁ k → Fin N → ℝ} {h : Fin N → ℝ}
    {z h' : CTorus d L N₁ m₁ k → Fin N → ℂ} {τ ζ σ ε K₂ : ℝ}
    (H : ScaledPsiC G νs τ ζ j p h z h')
    (hyG : y ∈ G.Ω 1) (hyGj : G.layerIndex y = j)
    (hν : 0 < νs * ((L : ℝ) ^ j) ^ 2)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ νs * ((L : ℝ) ^ j) ^ 2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : νs * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.transpose * Q = 1)
    (hQp : Q.mulVec (p y) = rn (p y) • (Pi.single i₀ 1 : Fin N → ℝ))
    (hQnorm : Q.mulVec (fun i => p y i / rn (p y)) =
      (Pi.single i₀ 1 : Fin N → ℝ))
    {ψ : Site d → Spin N} {b : Spin N}
    (hψ0 : ψ 0 = (cmat Q).mulVec (fun i => (p y i : ℂ) + z y i))
    (hb : b = (cmat Q).mulVec
      ((((νs * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' y i)))
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom (νs * ((L : ℝ) ^ j) ^ 2) σ ε K₂ ψ b)
    (hσε : 0 ≤ σ * ε)
    (hsmall : τ ^ 2 * ζ + 2 * N * ζ +
      diamA d L P.m₀ m₁ * (1 + sizeJ P.m₀ j X) * (σ * ε) ≤ r)
    (hfield : 13 * N * τ ^ 2 * ζ ≤ r)
    (hlong : 2 * τ ^ 2 * ζ ^ 2 ≤ r ^ 2)
    (hc : pack S ψ b ∈ TubeAniso i₀ (νs * ((L : ℝ) ^ j) ^ 2) r S) :
    trickFnA i₀ (νs * ((L : ℝ) ^ j) ^ 2) r (fun c' : Cfg d N S =>
      Tm.E j y X
        (fun w => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (w - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
          (νs * ((L : ℝ) ^ j) ^ 2) S c')) (pack S ψ b) =
      Tm.E j y X
        (fun w => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
          (pack S ψ b) (w - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
          (νs * ((L : ℝ) ^ j) ^ 2) S (pack S ψ b)) := by
  have hQe := realOrth_transpose_frame hQ hQnorm
  obtain ⟨hcentre, hcoords, hlongsrc⟩ :=
    Balaban.SmallField.ScaledPsiC.real_frame_bounds H hyG hyGj
      hν hτ hτ1 hντ hζ hζ1 hQ hQp hQe
  apply trickFnA_shiftTerm_eq_of_dataHyp_small hcl hcr hBg hν hμν hj1 hjk
    hy hX hyX hS hS' hne hrad dat hσε
  · intro i
    rw [hψ0]
    exact hcentre i
  · exact hsmall
  · intro i
    rw [hb]
    exact (hcoords i).trans hfield
  · rw [hb]
    exact hlongsrc.trans_le hlong
  · exact hc

end Balaban.SmallField.Def6v2
