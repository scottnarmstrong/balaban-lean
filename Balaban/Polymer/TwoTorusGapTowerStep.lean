/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepFinal
public import Balaban.Polymer.TwoTorusGapCloseResum
public import Balaban.Polymer.TwoTorusGapStepObsFamily

/-!
# The gap-scale step with inherited terms from the previous scale (item 24, blocker 7)

`resum_gapScale_torus_step`: the step `resum_gapScale_torus_full` for the terms `T = Te + Td + To +
Tinh`, with the hypotheses on `T` derived from the new terms `Te + Td + To` and the inherited terms
`Tinh`, and the closeness `hinh` of the inherited terms (with constant `0`) from their equality on
the common quarter box (`hIH`, `hinh_of_quarterBox`), which is the fourth conclusion of the step at
the previous scale.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv MeasureTheory Metric

section Final

open Balaban.Inhabited Balaban.Inhabited.LevelStep

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

set_option hygiene false in
local notation "SA[" ℓ "]" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁ ℓ) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "XA[" ℓ "]" => (↑(LocalCover.nbhdF m₀ (xs ℓ)) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1)))
set_option hygiene false in
local notation "𝒴A[" ℓ "]" => polyDom (GA[ℓ]) (LocalCover.nbhdF m₀ (xs ℓ)) m₀ k
  (LocalCover.fam m₀ (xs ℓ))
/-- **The four `T`-hypotheses of the gap-scale step from the new and the inherited terms.** -/
theorem gapStep_T_facts {ι G : Type*} {d : ℕ} (P : ι → Finset (Finset (Fin d → ℤ))) (Dset : Set G)
    (sz : Finset (Fin d → ℤ) → ℕ) (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop)
    (T Te Td To Tinh : ι → G → Finset (Fin d → ℤ) → ℂ) {Bn Bi κ' : ℝ}
    (hsplit : ∀ ℓ g X, T ℓ g X = Te ℓ g X + Td ℓ g X + To ℓ g X + Tinh ℓ g X)
    (hsuppN : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Te ℓ g X + Td ℓ g X + To ℓ g X = 0)
    (hsuppI : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tinh ℓ g X = 0)
    (hlocN : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' →
      Te ℓ g X + Td ℓ g X + To ℓ g X = Te ℓ g' X + Td ℓ g' X + To ℓ g' X)
    (hlocI : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tinh ℓ g X = Tinh ℓ g' X)
    (hanN : ∀ ℓ X, X ∈ P ℓ → (fun g => Te ℓ g X + Td ℓ g X + To ℓ g X) ∈ W)
    (hanI : ∀ ℓ X, X ∈ P ℓ → (fun g => Tinh ℓ g X) ∈ W)
    (hbdN : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset,
      ‖Te ℓ g X + Td ℓ g X + To ℓ g X‖ ≤ Bn * Real.exp (-κ' * (sz X : ℝ)))
    (hbdI : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tinh ℓ g X‖ ≤ Bi * Real.exp (-κ' * (sz X : ℝ))) :
    (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0) ∧
    (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X) ∧
    (∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W) ∧
    (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖T ℓ g X‖ ≤ (Bn + Bi) * Real.exp (-κ' * (sz X : ℝ))) := by
  classical
  have hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0 := fun ℓ X hX hR' g => by
    have h1 := hsuppN ℓ X hX hR' g
    have h2 := hsuppI ℓ X hX hR' g
    rw [hsplit, h1, h2, add_zero]
  have hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X := fun ℓ X hX g g' h => by
    rw [hsplit, hsplit, hlocN ℓ X hX g g' h, hlocI ℓ X hX g g' h]
  have han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W := fun ℓ X hX => by
    have : (fun g => T ℓ g X) =
        (fun g => Te ℓ g X + Td ℓ g X + To ℓ g X) + (fun g => Tinh ℓ g X) := by
      funext g; simp only [Pi.add_apply]; rw [hsplit]
    rw [this]; exact W.add_mem (hanN ℓ X hX) (hanI ℓ X hX)
  have hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖T ℓ g X‖ ≤
      (Bn + Bi) * Real.exp (-κ' * (sz X : ℝ)) := fun ℓ X hX g hg => by
    rw [hsplit]
    calc _ ≤ ‖Te ℓ g X + Td ℓ g X + To ℓ g X‖ + ‖Tinh ℓ g X‖ := norm_add_le _ _
      _ ≤ Bn * Real.exp (-κ' * (sz X : ℝ)) + Bi * Real.exp (-κ' * (sz X : ℝ)) :=
        add_le_add (hbdN ℓ X hX g hg) (hbdI ℓ X hX g hg)
      _ = _ := by ring
  exact ⟨hsupp, hloc, han, hbd⟩

/-- **The gap-scale step with the inherited terms of the previous scale.** -/
theorem resum_gapScale_torus_step (hN2 : 2 ≤ N)
    (hk : 1 ≤ k)
    (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : ∀ ℓ, FlCore N (GA[ℓ]) (HA[ℓ]) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG : ∀ ℓ, IsLevel (GA[ℓ]) (k + 1))
    (cc : ℂ)
    {cψ : ℝ}
    (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hδc : 0 ≤ δc)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
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
    (hd : 0 < d)
    (hL : 2 ≤ L)
    (hm₀ : 1 ≤ m₀)
    (hm₁ : 1 ≤ m₁)
    (hN : ∀ ℓ, L ^ m₀ ∣ N₁ ℓ)
    {Xc 𝒦X : ∀ ℓ, Set (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    {X₁f : ∀ ℓ, Finset (CTorus d L (N₁ ℓ) m₁ (k + 1))}
    (hcov : ∀ ℓ, CovSetup (GA[ℓ]) m₀ j (Xc ℓ) (𝒦X ℓ))
    (hX₁ : ∀ ℓ, (↑(X₁f ℓ) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) = X1 (GA[ℓ]) m₀ j (𝒦X ℓ))
    (h𝒦 : ∀ ℓ, (𝒦X ℓ).Nonempty)
    {Dset : Set G}
    {Dat : ∀ ℓ, G → BgData (GA[ℓ]) N}
    (hD : ∀ ℓ, ∀ g ∈ Dset, XiCData (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps (Dat ℓ g))
    {ψh : ∀ ℓ, G → unitPts (GA[ℓ]) × Fin N → ℂ}
    (hψh : ∀ ℓ, ∀ g ∈ Dset, ∀ p, ‖ψh ℓ g p‖ ≤ cψ)
    {Zm : ∀ ℓ, Finset (unitPts (GA[ℓ]))}
    {um tm : ℂ}
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
    (hK26 : ∀ ℓ, 26 ≤ K ℓ)
    (hside : ∀ ℓ, (N₁ ℓ * L ^ m₁) * L ^ (k + 1) = cellSide L m₀ m₁ (k + 1) * K ℓ)
    (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop)
    (can : Finset (Fin d → ℤ) → ι)
    (Wd : ι → Finset (Fin d → ℤ) → Prop)
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
      |(x μ - y μ).valMinAbs| ≤ ((aK * ((K ℓ - 26) / 25 + 1) - 1 : ℕ) : ℤ))
    (hq : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
      ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
    (hslack : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X →
      20 * ((aK * ((K ℓ - 26) / 25 + 1) - 1) + ((aK * ((K ℓ - 26) / 25 + 1) - 1) + 1) / 4 +
        2 * L ^ (k + 1)) + 20 < (N₁ ℓ * L ^ m₁) * L ^ (k + 1) ∧
      20 * ((aK * ((K ℓ - 26) / 25 + 1) - 1) + ((aK * ((K ℓ - 26) / 25 + 1) - 1) + 1) / 4 +
        2 * L ^ (k + 1)) + 20 < (N₁ (can X) * L ^ m₁) * L ^ (k + 1))
    (hrawD : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ zc ∈ Zr ℓ,
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
    (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ)
    (W : Submodule ℂ (G → ℂ))
    (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop)
    (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    {Bn Bi κr κ₂ κ' lam : ℝ}
    {t₀ : ℕ}
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hWd : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Wd ℓ X → K ℓ ≤ 25 * X.card)
    (hBn : 0 ≤ Bn) (hBi : 0 ≤ Bi)
    (hκ : 0 ≤ κr)
    (hκ₂ : κr + Real.log 2 ≤ κ₂)
    (hlam : κ₂ ≤ lam)
    (hκ' : 7 * lam + κ₂ ≤ κ')
    (To Tinh : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hsuppN : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Te ℓ g X + Td ℓ g X + To ℓ g X = 0)
    (hsuppI : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tinh ℓ g X = 0)
    (hlocN : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' →
      Te ℓ g X + Td ℓ g X + To ℓ g X = Te ℓ g' X + Td ℓ g' X + To ℓ g' X)
    (hlocI : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tinh ℓ g X = Tinh ℓ g' X)
    (hanN : ∀ ℓ X, X ∈ P ℓ → (fun g => Te ℓ g X + Td ℓ g X + To ℓ g X) ∈ W)
    (hanI : ∀ ℓ X, X ∈ P ℓ → (fun g => Tinh ℓ g X) ∈ W)
    (hbdN : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset,
      ‖Te ℓ g X + Td ℓ g X + To ℓ g X‖ ≤ Bn * Real.exp (-κ' * (sz X : ℝ)))
    (hbdI : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tinh ℓ g X‖ ≤ Bi * Real.exp (-κ' * (sz X : ℝ)))
    (hKL : ∀ ℓ, L ≤ (K ℓ - 26) / 25 + 1)
    (xs : ∀ ℓ, CTorus d L (N₁ ℓ) m₁ (k + 1))
    (iy : Fin N)
    (hxsb : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → xs (can X) = bm[ℓ, can X] (xs ℓ))
    (hspO : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ x ∈ LocalCover.nbhd m₀ (xs ℓ), ∀ y ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ Ds)
    (hqS : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X →
      ∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
    (hq₁ : p₁ / cψ ≤ 1 / 4)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {Ev : ∀ ℓ, Set (CTorus d L (N₁ ℓ) m₁ (k + 1)) →
      RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N × ((SA[ℓ]).U × Fin N → ℂ) → ℂ}
    (hEv : ∀ ℓ, (Ev ℓ) = evTerm (fun i : ParIdx (GA[ℓ]) (XA[ℓ]) => i.1.1) (GA[ℓ]) m₀
        (X1 (GA[ℓ]) m₀ k (LocalCover.fam m₀ (xs ℓ)))
        (fun u s => siteFun (GA[ℓ]) (HA[ℓ]) (xs ℓ) iy ((F₁ ℓ) (extParams (GA[ℓ]) (XA[ℓ]) s, u.1))
          ((Sol ℓ) (extParams (GA[ℓ]) (XA[ℓ]) s,
            flEdat (GA[ℓ]) (HA[ℓ]) ((F₁ ℓ) (extParams (GA[ℓ]) (XA[ℓ]) s, u.1))
              u.1.1 (hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₁ ℓ)
                (extParams (GA[ℓ]) (XA[ℓ]) s) u.1 u.2))).1
          (u.1, hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₁ ℓ)
            (extParams (GA[ℓ]) (XA[ℓ]) s) u.1 u.2)))
    (hdEv : ∀ ℓ, ∀ Y ∈ 𝒴A[ℓ], ∀ u ∈ XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA[ℓ]).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA[ℓ]).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir (SA[ℓ]).hG' Y u u' → (Ev ℓ) Y u = (Ev ℓ) Y u')
    (hdj : ∀ ℓ, ∀ Y ∈ 𝒴A[ℓ], IsDj m₀ (k + 1) Y)
    (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
    (hθ : ∀ ℓ, ∀ g ∈ Dset, ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps)
    (hp : ∀ ℓ, 0 < (SA[ℓ]).p₁)
    {Lb : ι → Type}
    [∀ ℓ, Fintype (Lb ℓ)]
    (Lab : ∀ ℓ, CubeLabels (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ (Lb ℓ))
    {𝒴v : ∀ ℓ, Finset (Set (CTorus d L (N₁ ℓ) m₁ (k + 1)))}
    (ys : ∀ ℓ, (Lb ℓ) ≃ {Y // Y ∈ (𝒴v ℓ)})
    (hys : ∀ ℓ, ∀ l, (Lab ℓ).ysite l = ((ys ℓ) l).1)
    {εH κH κ0 Kco Kobs : ι → ℝ}
    (A : ∀ ℓ, physParam N (SA[ℓ]) → ℂ → LabelAct (Lab ℓ) ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb (εH ℓ) (κH ℓ) (κ0 ℓ) (Kco ℓ))
    (hκ0 : ∀ ℓ, aEnt d L + 1 ≤ (κ0 ℓ))
    (hεH : ∀ ℓ, 0 ≤ (εH ℓ))
    (hK : ∀ ℓ, (Kco ℓ) + (Kco ℓ) + K0 d L (κ0 ℓ) + K0 d L (κ0 ℓ) ≤ (Kobs ℓ))
    (Rg : ℝ)
    (hRg : 0 ≤ Rg)
    (𝒰 : Set ℂ)
    (hTo : ∀ ℓ g X, X ∈ P ℓ → g ∈ Dset →
      To ℓ g X =
      obsCoeffParam ((SA[ℓ]).blockSplit m₀ (hp ℓ)).μ
        (fun θ t σ => tiltActObs (A ℓ) (hN ℓ) (hκ0 ℓ) (hεH ℓ) (hdj ℓ) (hK ℓ) Rg hRg 𝒰 θ t σ)
        (fun m => obsY1 m₀ (SA[ℓ]) ((Lb ℓ) ⊕ (Lb ℓ)) (𝒴A[ℓ]) m)
        (fun m => blockMarkC (SA[ℓ]) m₀ (hp ℓ) m.1 m.2)
        (fun θ m T'' => obsHker (𝒴A[ℓ]) (fun Y => hatCoeff ((Ev ℓ) Y)
          (θ.1 : RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N) (obsUnitVec (SA[ℓ]) m)) m₀ T'')
        (obsRemLab (𝒴A[ℓ]) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ ((Lb ℓ) ⊕ (Lb ℓ)) (𝒴A[ℓ]) (rootCube (m₀ := m₀) (blockIndex (xs ℓ)))))
        (fun θ => obsGrFam (SA[ℓ]) m₀ (hp ℓ) (Ev ℓ) (𝒴A[ℓ])
          (XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps) θ) (θ ℓ g) (Ycub ℓ X))
    (hrawO : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1)) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) ((θ ℓ g).1 : RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) ((θ (can X) g).1 : RawData d L ((N₁ (can X)) * L ^ m₁) (k + 1) N)))
    (hmemV : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ Z : Set (CTorus d L (N₁ ℓ) m₁ (k + 1)),
      (∀ x ∈ Z, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)))))) → ((fun x => bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) '' Z ∈ (𝒴v (can X)) ↔ Z ∈ (𝒴v ℓ)))
    (hAeq0 : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : (Lb ℓ)) (l' : (Lb (can X))),
      (∀ x ∈ (Lab ℓ).ysite l, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)))))) →
      (Lab (can X)).ysite l' = (fun x => bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) '' (Lab ℓ).ysite l →
      ∀ (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b) (Φ' : ∀ b, ((SA[can X]).blockSplit m₀ (hp (can X))).Ωb b),
      (∀ x, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) →
        Φ' ((SA[can X]).cellOf m₀ (unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1)))))))
          ⟨unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))), rfl⟩ =
          Φ ((SA[ℓ]).cellOf m₀ (unitPt (SA[ℓ]).hG' x)) ⟨unitPt (SA[ℓ]).hG' x, rfl⟩) →
      ((A (can X)) (((θ (can X) g).1, 0) : physParam N (SA[can X])) σ).H l' Φ' = ((A ℓ) (((θ ℓ g).1, 0) : physParam N (SA[ℓ])) σ).H l Φ)
    (hAeqθ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : (Lb ℓ)) (l' : (Lb (can X))),
      (∀ x ∈ (Lab ℓ).ysite l, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)))))) →
      (Lab (can X)).ysite l' = (fun x => bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) '' (Lab ℓ).ysite l →
      ∀ (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b) (Φ' : ∀ b, ((SA[can X]).blockSplit m₀ (hp (can X))).Ωb b),
      (∀ x, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) →
        Φ' ((SA[can X]).cellOf m₀ (unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1)))))))
          ⟨unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))), rfl⟩ =
          Φ ((SA[ℓ]).cellOf m₀ (unitPt (SA[ℓ]).hG' x)) ⟨unitPt (SA[ℓ]).hG' x, rfl⟩) →
      ((A (can X)) (θ (can X) g) σ).H l' Φ' = ((A ℓ) (θ ℓ g) σ).H l Φ)
    (hsplit : ∀ ℓ g X, T ℓ g X = Te ℓ g X + Td ℓ g X + To ℓ g X + Tinh ℓ g X)
    (hIH : ∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tinh ℓ g X = Tinh ℓ' g X) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tn ℓ g X‖ ≤
        ((Bn + Bi) + (0 + 2 * (Bn + Bi)) * Real.exp κ₂ + 2 * (Bn + Bi) * Real.exp (κ₂ * (t₀ : ℝ))) *
          Real.exp (-κr * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  classical
  obtain ⟨hsupp, hloc, han, hbd⟩ := gapStep_T_facts P Dset sz W R Ag T Te Td To Tinh hsplit hsuppN
    hsuppI hlocN hlocI hanN hanI hbdN hbdI
  exact resum_gapScale_torus_full hN2 hk νS β p₁ δ hC hG cc hcψ hMX hδc hmar hαK hsm hF₁ hSol hd hL hm₀ hm₁ hN hcov hX₁ h𝒦 hD hψh hum hZ hBM hconn hcap hK26 hside P Q can Wd hP hQ hcanK hcompact hcoverX hBl hfamD Te hTe Zr Ycub hYs hZr Td hTd hsp hq hslack hrawD sz τ W R Ag T hsz hτ hR hAg hWd (add_nonneg hBn hBi) le_rfl hκ hκ₂ hlam hκ' hsupp hloc han hbd To Tinh hKL xs iy hxsb hspO hqS hq₁ hrad hEv hdEv hdj θ hθ hp Lab ys hys A hκ0 hεH hK Rg hRg 𝒰 hTo hrawO hmemV hAeq0 hAeqθ hsplit (hinh_of_quarterBox K P Q sz τ can Dset Tinh Wd hQ hcanK hIH)

end Final

end Balaban.Polymer.TwoTorusStep
