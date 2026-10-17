/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepDetFamily
public import Balaban.Polymer.TwoTorusGapDataThr

/-!
# The determinant new terms at the gap scale with the threshold `(K - 36) / 25` (blocker 7)

`hdt_of_detSum_thr36`: `hdt_of_detSum` for the supports of the quarter box of cell spread
`Dc ℓ ≤ (K ℓ - 36) / 25` (the non-wide supports of `resum_gapScale_torus_wide36`); the slack
hypothesis `hslack` is then a consequence (`compact36_slack`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

section DetFamily

variable {ι G : Type*} {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {N₁ : ι → ℕ} [∀ ℓ, NeZero (N₁ ℓ)]
  {K : ι → ℕ} [∀ ℓ, NeZero (K ℓ)] {m₀ : ℕ}

set_option hygiene false in
local notation "bm[" ℓ "," ℓ' "]" =>
  boxMap ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) ((N₁ ℓ' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc[" ℓ "," ℓ' "]" =>
  boxMap (d := d) (N₁ ℓ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (N₁ ℓ' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "GA[" ℓ "]" => levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
  (ϱ := ϱ) (k + 1) le_rfl
set_option hygiene false in
local notation "HA[" ℓ "]" => levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
  (ϱ := ϱ) k (Nat.le_succ k)
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L m₀ m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}

/-- **The exact torus clause of the determinant new terms at the gap scale** (item 24, `hdt` of
`resum_gapScale_torus_threeTerms`). -/
theorem hdt_of_detSum_thr36 (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : ∀ ℓ, L ^ m₀ ∣ N₁ ℓ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : ∀ ℓ, FlCore N (GA[ℓ]) (HA[ℓ]) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : ∀ ℓ, HatConn (GA[ℓ]))
    {Dset : Set G} {Dat : ∀ ℓ, G → BgData (GA[ℓ]) N}
    (hD : ∀ ℓ, ∀ g ∈ Dset, XiCData (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps (Dat ℓ g))
    (hK36 : ∀ ℓ, 36 ≤ K ℓ)
    {Dc : ι → ℕ} (hDc : ∀ ℓ, Dc ℓ ≤ (K ℓ - 36) / 25)
    (hside : ∀ ℓ, (N₁ ℓ * L ^ m₁) * L ^ (k + 1) = cellSide L m₀ m₁ (k + 1) * K ℓ)
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (Zr : ∀ ℓ, Finset (Torus d (N₁ ℓ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
    (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hYs : ∀ ℓ X, X ∈ P ℓ → sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
    (hZr : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Zr (can X) = (Zr ℓ).image bc[ℓ, can X])
    (Td : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hTd : ∀ ℓ g X, X ∈ P ℓ → g ∈ Dset →
      Td ℓ g X = ∑ zc ∈ Zr ℓ, ∑ y ∈ (Finset.univ.filter fun u : unitPts (GA[ℓ]) =>
          unitBlock1 (u : UnitTorus d L (N₁ ℓ) m₁ k) = zc),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) (Dat ℓ g) y (Ycub ℓ X))
    (hsp : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
      ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK),
      ∀ y ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ ((aK * (Dc ℓ + 1) - 1 : ℕ) : ℤ))
    (hq : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
      ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
    (hraw : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤
          (((aK * (Dc ℓ + 1) - 1) + ((aK * (Dc ℓ + 1) - 1) + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d ((aK * (Dc ℓ + 1) - 1) +
          ((aK * (Dc ℓ + 1) - 1) + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
          ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))))
          (rawOf (Dat ℓ g)))
        (symRaw (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))))
          (rawOf (Dat (can X) g))))
    :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset, Td ℓ g X = Td (can X) g X := by
  have hK26 : ∀ ℓ, 26 ≤ K ℓ := fun ℓ => by have := hK36 ℓ; omega
  refine hdt_of_detSum_gen (Dc := Dc) hN2 hk νS β p₁ δ hd hL hm₀ hm₁ hN hC hδc hcap hsm hmar hαK
    hconn hD hK26 (fun ℓ => by have := hDc ℓ; omega) hside P Q can Wd hP hQ hcanK Zr Ycub hYs hZr
    Td hTd hsp hq ?_ hraw
  intro ℓ X hX hQX _
  have hKK : K ℓ ≤ K (can X) := hcanK ℓ X hX hQX
  have hapos : 0 < aK := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hDs1 : (aK * (Dc ℓ + 1) - 1) + 1 ≤ aK * (Dc ℓ + 1) := by
    have : 1 ≤ aK * (Dc ℓ + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have h4 : 4 * L ^ (k + 1) ≤ aK := by
    have : aK = L ^ (k + 1) * L ^ (m₀ + m₁) := by
      rw [cellSide, ← pow_add]; congr 1; ring
    rw [this]
    have h2 : 4 ≤ L ^ (m₀ + m₁) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ L ^ 2 := Nat.pow_le_pow_left hL 2
        _ ≤ L ^ (m₀ + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith [Nat.zero_le (L ^ (k + 1))]
  have hsl := compact36_slack (K := K ℓ) (K' := K (can X)) (Lk := L ^ (k + 1))
    (Dc := Dc ℓ) (Ds := aK * (Dc ℓ + 1) - 1) hKK h4 (pow_pos (by omega) _) (hK36 ℓ) (hDc ℓ) hDs1
  rw [← hside ℓ, ← hside (can X)] at hsl
  exact hsl

end DetFamily

end Balaban.Polymer.TwoTorusStep
