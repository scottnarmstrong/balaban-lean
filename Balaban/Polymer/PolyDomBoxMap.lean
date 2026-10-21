/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDomainFamilies
public import Balaban.Fluctuation.Prop33Parts

/-!
# The polymer domains of an old term on two tori

`polyDom_boxMap_iff`: for the label cubes `X₁f` of an old term on the first torus and
`X₁f' = X₁f.image bm` on the second, in the box, a set `Y` in the box is a polymer domain of the first
exactly when `bm '' Y` is one of the second (`polyDom`, the domains of the connected families of the
cut cubes of the cover).  It is `mem_polymerDomains_boxMap_iff` for the cover sets `X1`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale

open scoped Classical

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ jt : ℕ}

theorem polymerDomains_congr_set {N : ℕ} [NeZero N] {K : ℕ} {G : GeneratingSet d L (N * L ^ m₁) K ϱ}
    {S S' : Set (CTorus d L N m₁ K)} (h : S = S') (X : Set (CTorus d L N m₁ K)) :
    polymerDomains (fun i : ParIdx G S => i.1.1) G m₀ X =
      polymerDomains (fun i : ParIdx G S' => i.1.1) G m₀ X := by
  subst h; rfl

/-- **The polymer domains of an old term on two tori.** -/
theorem polyDom_boxMap_iff {ρ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * ρ + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hj1 : 1 ≤ k + 1)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : Finset (CTorus d L N₁' m₁ (k + 1))}
    {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
        m₀ jt 𝒦X)
    (hX₁' : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) =
      X1 (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
        m₀ jt 𝒦X')
    (hX : X₁f' = X₁f.image (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hbox : ∀ x ∈ X₁f, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' Y ∈
        polyDom (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1)
          le_rfl) X₁f' m₀ jt 𝒦X' ↔
      Y ∈ polyDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1)
          le_rfl) X₁f m₀ jt 𝒦X := by
  have hcoe : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) =
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' ↑X₁f := by
    rw [hX, Finset.coe_image]
  unfold polyDom
  rw [← hX₁, ← hX₁', polymerDomains_congr_set hcoe, hcoe]
  exact mem_polymerDomains_boxMap_iff hN hN' le_rfl hn hn' hj1
    (fun x hx => hbox x (Finset.mem_coe.1 hx)) hY

end Balaban.Polymer.TwoTorusStep
