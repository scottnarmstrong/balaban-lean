/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepDetPair

/-!
# The determinant new terms at the gap scale: the exact torus clause (item 24, blocker 7)

`hdt_of_detSum`: the analogue of `hnew_of_blockEnergy` for the determinant terms.  The determinant
new terms `Td ℓ g X` on the torus `ℓ` are the sums over the roots `zc ∈ Zr ℓ` and the unit points of
the block of `zc` of the determinant activities at the cubes `Ycub ℓ X` of the cells of the polymer
`X` (`hTd`); the roots and the cubes of the torus `can X` are the box-map images (`hZr`, `hYs`).
For a support `X` of the quarter box that is not wide the terms on `ℓ` and on `can X` are equal, from
the pair theorem `sum_blockU_detActivityBg_cellSites` for each root.
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

/-- **The determinant torus clause with the cell spread `Dc ℓ ≤ (K ℓ - 26) / 25` as a parameter**:
the core of `hdt_of_detSum`; the slack `hslack` is a hypothesis. -/
theorem hdt_of_detSum_gen (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
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
    (hK26 : ∀ ℓ, 26 ≤ K ℓ)
    {Dc : ι → ℕ} (hDc : ∀ ℓ, Dc ℓ ≤ (K ℓ - 26) / 25)
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
    (hslack : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X →
      20 * ((aK * (Dc ℓ + 1) - 1) + ((aK * (Dc ℓ + 1) - 1) + 1) / 4 +
        2 * L ^ (k + 1)) + 20 < (N₁ ℓ * L ^ m₁) * L ^ (k + 1) ∧
      20 * ((aK * (Dc ℓ + 1) - 1) + ((aK * (Dc ℓ + 1) - 1) + 1) / 4 +
        2 * L ^ (k + 1)) + 20 < (N₁ (can X) * L ^ m₁) * L ^ (k + 1))
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
  intro ℓ X hX hQX hW g hg
  have hXc : X ∈ P (can X) :=
    mem_P_can (P := P) (Q := Q) (can := can) (hK26 := hK26) (hP := hP) (hQ := hQ)
      (hcanK := hcanK) ℓ X hX hQX
  have hKK : K ℓ ≤ K (can X) := hcanK ℓ X hX hQX
  have : NeZero aK := ⟨(cellSide_pos (L := L) m₀ m₁ (k + 1)).ne'⟩
  have hapos : 0 < aK := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hXq : ∀ c ∈ (↑X : Set (Fin d → ℤ)), ∀ μ, (c μ).natAbs ≤ K ℓ / 4 := fun c hc μ =>
    (hQ ℓ X).1 hQX c hc μ
  have hDs1 : (aK * (Dc ℓ + 1) - 1) + 1 ≤ aK * (Dc ℓ + 1) := by
    have : 1 ≤ aK * (Dc ℓ + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hmargin := compact_site_margins (K := K ℓ) (K' := K (can X)) (cs := aK)
    (Dc := Dc ℓ) (Ds := aK * (Dc ℓ + 1) - 1) (q := aK * (K ℓ / 4 + 1))
    (hK26 ℓ) hKK hapos (hDc ℓ) hDs1 (Nat.le_add_right _ _)
  have hqn := hmargin.2.2
  rw [← hside ℓ] at hqn
  have hnc : N₁ ℓ * L ^ m₁ ≤ N₁ (can X) * L ^ m₁ := by
    have h1 : (N₁ ℓ * L ^ m₁) * L ^ (k + 1) ≤ (N₁ (can X) * L ^ m₁) * L ^ (k + 1) := by
      rw [hside ℓ, hside (can X)]; exact Nat.mul_le_mul_left _ hKK
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos (by omega) _)
  have hinj : Function.Injective bc[ℓ, can X] := by
    have h0 : ∀ ℓ' : ι, NeZero (N₁ ℓ' * L ^ m₁ * L ^ (k + 1 - (k + 1))) := fun ℓ' =>
      ⟨by have := NeZero.pos (N₁ ℓ'); have := NeZero.pos L; positivity⟩
    have := h0 ℓ
    have := h0 (can X)
    refine boxMap_injective_of_le (d := d) ?_
    rw [Nat.sub_self, pow_zero, mul_one, mul_one]
    exact hnc
  rw [hTd ℓ g X hX hg, hTd (can X) g X hXc hg, hZr ℓ X hX hQX, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun zc hzc => ?_
  exact (sum_blockU_detActivityBg_cellSites_gen hN2 hk νS β p₁ δ hd hL hm₀ hm₁ (hN ℓ) (hN (can X))
    (hC ℓ) (hC (can X)) hδc hcap hsm hmar hαK (hconn ℓ) (hconn (can X)) (hD ℓ g hg)
    (hD (can X) g hg) (Kn := K ℓ) (Kn' := K (can X)) (Ds := aK * (Dc ℓ + 1) - 1)
    (q := aK * (K ℓ / 4 + 1)) (hK26 ℓ) hKK (hside ℓ) (hside (can X)) (hDc ℓ) rfl hXq (Ycub ℓ X)
    (Ycub (can X) X) (hYs ℓ X hX) (hYs (can X) X hXc) zc (hsp ℓ X g hX hQX hW hg zc hzc)
    (hq ℓ X g hX hQX hW hg zc hzc) hqn (hslack ℓ X hX hQX hW).1 (hslack ℓ X hX hQX hW).2
    (hraw ℓ X g hX hQX hW hg zc hzc)).symm


/-- **The exact torus clause of the determinant new terms at the gap scale** (item 24, `hdt` of
`resum_gapScale_torus_threeTerms`). -/
theorem hdt_of_detSum (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
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
    (hK26 : ∀ ℓ, 26 ≤ K ℓ)
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
      |(x μ - y μ).valMinAbs| ≤ ((aK * ((K ℓ - 26) / 25 + 1) - 1 : ℕ) : ℤ))
    (hq : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
      ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
    (hslack : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X →
      20 * ((aK * ((K ℓ - 26) / 25 + 1) - 1) + ((aK * ((K ℓ - 26) / 25 + 1) - 1) + 1) / 4 +
        2 * L ^ (k + 1)) + 20 < (N₁ ℓ * L ^ m₁) * L ^ (k + 1) ∧
      20 * ((aK * ((K ℓ - 26) / 25 + 1) - 1) + ((aK * ((K ℓ - 26) / 25 + 1) - 1) + 1) / 4 +
        2 * L ^ (k + 1)) + 20 < (N₁ (can X) * L ^ m₁) * L ^ (k + 1))
    (hraw : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤
          (((aK * ((K ℓ - 26) / 25 + 1) - 1) + ((aK * ((K ℓ - 26) / 25 + 1) - 1) + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d ((aK * ((K ℓ - 26) / 25 + 1) - 1) +
          ((aK * ((K ℓ - 26) / 25 + 1) - 1) + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
          ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))))
          (rawOf (Dat ℓ g)))
        (symRaw (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))))
          (rawOf (Dat (can X) g))))
    :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset, Td ℓ g X = Td (can X) g X := by
  exact hdt_of_detSum_gen (Dc := fun ℓ => (K ℓ - 26) / 25) hN2 hk νS β p₁ δ hd hL hm₀ hm₁ hN hC
    hδc hcap hsm hmar hαK hconn hD hK26 (fun _ => le_rfl) hside P Q can Wd hP hQ hcanK Zr Ycub hYs
    hZr Td hTd hsp hq hslack hraw

end DetFamily

end Balaban.Polymer.TwoTorusStep
