/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapIdentFamily
public import Balaban.Polymer.TwoTorusGapStepDetFamily
public import Balaban.Polymer.TwoTorusGapDataThrFull
public import Balaban.Polymer.TwoTorusGapDataThrDet

/-!
# The energy and determinant clauses at the gap scale, threshold `(K - 36) / 25` (blocker 7)

`resum_gapScale_torus_energyDet_thr36`: `resum_gapScale_torus_energyDet` with the wide supports of
`resum_gapScale_torus_wide36` and the determinant clause `hdt_of_detSum_thr36`, which has no slack
hypothesis.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

section Full3

variable {ι G : Type*} {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {N₁ : ι → ℕ} [∀ ℓ, NeZero (N₁ ℓ)]
  {K : ι → ℕ} [∀ ℓ, NeZero (K ℓ)] {m₀ j : ℕ}

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

/-- **The gap-scale torus clause with the energy and determinant terms proved, with the wide
supports of threshold `(K - 36) / 25`.**  The compact supports have cell spread `Dc ℓ ≤ (K ℓ - 36) / 25`
(`hsp`, `hrawD`), and the slack of the determinant block sum follows (`hdt_of_detSum_thr36`). -/
theorem resum_gapScale_torus_energyDet_thr36 (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : ∀ ℓ, FlCore N (GA[ℓ]) (HA[ℓ]) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG : ∀ ℓ, IsLevel (GA[ℓ]) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hδc : 0 ≤ δc) (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : ∀ ℓ, DecParams (GA[ℓ]) × RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N →
      ((GA[ℓ]).Ω 1 × Fin N → ℂ) × ((GA[ℓ]).Ω 1 → ℂ)}
    {Sol : ∀ ℓ, Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N →
      ((HA[ℓ]).Ω 1 × Fin N → ℂ) × ((HA[ℓ]).Ω 1 → ℂ)}
    (hF₁ : ∀ ℓ, ∀ (s : DecParams (GA[ℓ])) (D : BgData (GA[ℓ]) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA[ℓ]) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA[ℓ]).Ω 1 × Fin N → ℂ)
        (α : (GA[ℓ]).Ω 1 → ℂ), IsDecBg (GA[ℓ]) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ ℓ (s, rawOf D) = (φ, α))
    (hSol : ∀ ℓ, ∀ p : Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA[ℓ]) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol ℓ p).1 = dphi (HA[ℓ]) (Dec2.decG (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1)
          p.2.2.1 p.2.1 (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol ℓ p).2 ∧
        Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol ℓ p).2 ∧
        Small (HA[ℓ]) (Sol ℓ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA[ℓ]) (Sol ℓ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA[ℓ]) (Sol ℓ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA[ℓ]).Ω 1 → ℂ,
          Small (HA[ℓ]) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol ℓ p).2))
    (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : ∀ ℓ, L ^ m₀ ∣ N₁ ℓ)
    {Xc 𝒦X : ∀ ℓ, Set (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    {X₁f : ∀ ℓ, Finset (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    (hcov : ∀ ℓ, CovSetup (GA[ℓ]) m₀ j (Xc ℓ) (𝒦X ℓ))
    (hX₁ : ∀ ℓ, (↑(X₁f ℓ) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) = X1 (GA[ℓ]) m₀ j (𝒦X ℓ))
    (h𝒦 : ∀ ℓ, (𝒦X ℓ).Nonempty)
    {Dset : Set G} {Dat : ∀ ℓ, G → BgData (GA[ℓ]) N}
    (hD : ∀ ℓ, ∀ g ∈ Dset, XiCData (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps (Dat ℓ g))
    {ψh : ∀ ℓ, G → unitPts (GA[ℓ]) × Fin N → ℂ}
    (hψh : ∀ ℓ, ∀ g ∈ Dset, ∀ p, ‖ψh ℓ g p‖ ≤ cψ)
    {Zm : ∀ ℓ, Finset (unitPts (GA[ℓ]))} {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k 1 κ cψ cc < δ₁)
    {Bl : ∀ ℓ, Finset (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    (hZ : ∀ ℓ, ∀ x₀ ∈ Bl ℓ,
      readSites (HA[ℓ]) k (jBlock d L (N₁ ℓ * L ^ m₁) (k + 1) (k + 1) x₀) ⊆ ↑(X₁f ℓ))
    (hBM : ∀ ℓ, ∀ x₀ ∈ Bl ℓ, BlockMargin (GA[ℓ]) (X₁f ℓ)
      (↑(blockSites d L (N₁ ℓ) m₁ (k + 1) k
        (jBlock d L (N₁ ℓ * L ^ m₁) (k + 1) (k + 1) x₀)) :
        Set (CTorus d L (N₁ ℓ) m₁ (k + 1))))
    (hconn : ∀ ℓ, HatConn (GA[ℓ]))
    (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hK61 : ∀ ℓ, 61 ≤ K ℓ)
    {Dc : ι → ℕ} (hDc : ∀ ℓ, Dc ℓ ≤ (K ℓ - 36) / 25)
    (hside : ∀ ℓ, (N₁ ℓ * L ^ m₁) * L ^ (k + 1) = cellSide L m₀ m₁ (k + 1) * K ℓ)
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hcompact : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ c ∈ X, ∀ c' ∈ X, ∀ μ,
      |c μ - c' μ| ≤ (((K ℓ - 26) / 25 : ℕ) : ℤ))
    (hcoverX : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X₁f (can X) = (X₁f ℓ).image bm[ℓ, can X])
    (hBl : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Bl (can X) = (Bl ℓ).image bm[ℓ, can X])
    (hfamD : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
      ∀ Ds : ℕ, Ds = cellSide L m₀ m₁ (k + 1) * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ (↑(X₁f ℓ) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) ∪ cellsOf[ℓ, X], ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1))
          ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))))) (rawOf (Dat ℓ g)))
        (symRaw (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))))
          (rawOf (Dat (can X) g))) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) →
        ∀ i, ψh (can X) g (unitPt (hG (can X)) (bm[ℓ, can X]
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))), i) =
          ψh ℓ g (unitPt (hG ℓ) y, i)) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) →
        (unitPt (hG (can X)) (bm[ℓ, can X]
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))) ∈ Zm (can X) ↔
          unitPt (hG ℓ) y ∈ Zm ℓ)))
    (Te : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hTe : ∀ ℓ g X, X ∈ P ℓ → g ∈ Dset →
      Te ℓ g X = ∑ x₀ ∈ Bl ℓ, evDec (X₁f ℓ) m₀ j (𝒦X ℓ) 1 νS (hG ℓ) cc (F₁ ℓ) (Sol ℓ)
        (blockEnergyFun (GA[ℓ]) (HA[ℓ]) (compWeight L 1) νS k
          (jBlock d L (N₁ ℓ * L ^ m₁) (k + 1) (k + 1) x₀)) (Zm ℓ) um tm
        cellsOf[ℓ, X] (rawOf (Dat ℓ g), ψh ℓ g))
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
    (hrawD : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
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
    (sz : Finset (Fin d → ℤ) → ℕ) (τ : ι → Finset (Fin d → ℤ) → ℕ) (W : Submodule ℂ (G → ℂ))
    (R : Finset (Fin d → ℤ) → Prop) (Ag : Finset (Fin d → ℤ) → G → G → Prop)
    (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    {B a κr κ₂ κ' lam : ℝ} {t₀ : ℕ}
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hWd : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Wd ℓ X → K ℓ ≤ 25 * X.card + 10)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κr)
    (hκ₂ : κr + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (To Tinh : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hsplit : ∀ ℓ g X, T ℓ g X = Te ℓ g X + Td ℓ g X + To ℓ g X + Tinh ℓ g X)
    (hob : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ Dset,
      To ℓ g X = To (can X) g X)
    (hinh : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ Dset,
      ‖Tinh ℓ g X - Tinh (can X) g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tn ℓ g X‖ ≤
        (B + (a + 2 * B) * Real.exp κ₂ + 2 * B * Real.exp (κ₂ * (t₀ : ℝ))) *
          Real.exp (-κr * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  have hK26 : ∀ ℓ, 26 ≤ K ℓ := fun ℓ => by have := hK61 ℓ; omega
  exact resum_gapScale_torus_threeTerms_thr36 K hd hK61 P Q sz τ can Dset W R Ag
    T Wd hP hQ hsz hτ hR hAg hcanK hWd hB ha hκ hκ₂ hlam hκ' hsupp hloc han hbd Te Td To Tinh hsplit
    (fun ℓ X hX hQX hW _ g hg => hnew_of_blockEnergy hC hk hG cc hcψ hMX hmar hαK hsm hF₁ hSol hd
      hL hm₀ hm₁ hN hcov hX₁ h𝒦 hD hψh hum hZ hBM hK26 hside P Q can Wd hP hQ hcanK hcompact
      hcoverX hBl hfamD Te hTe ℓ X hX hQX hW g hg)
    (fun ℓ X hX hQX hW _ g hg => hdt_of_detSum_thr36 hN2 hk νS β p₁ δ hd hL hm₀ hm₁ hN hC hδc hcap hsm
      hmar hαK hconn hD (fun ℓ => by have := hK61 ℓ; omega) hDc hside P Q can Wd hP hQ hcanK Zr Ycub hYs hZr Td hTd hsp hq
      hrawD ℓ X hX hQX hW g hg)
    hob hinh

end Full3

end Balaban.Polymer.TwoTorusStep
