/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDecSol

/-!
# The decoupled covariance on two tori, and the fluctuation from the raw data

* `decSol_value_twoTorus_of_decBg` (D0): the values of the decoupled fluctuation solution on two
  tori correspond on a component when its data are `flEdat` of the values of the decoupled
  background pair (the maps `F₁`, `F₁'` with the defining property of Theorem I-4b at level
  `j + 1`): the only hypotheses on the data are the agreement of the raw data on `RowsDep (S_Y)`
  and of the fluctuations `ψ, ψ'` on `S_Y^F` (the source `f₁` of `flEdat` is `0`).  The chain is
  `decBg_value_twoTorus`'s proof (`i4b_exists_unique`, `hF₁`) → `decSol_data_of_decBg` →
  `decSol_value_twoTorus`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### D0: the fluctuation values from the raw data -/

section FromRaw

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱp : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K) (hjp : j + 1 ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "PA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱp)
  (j + 1) hjp
local notation "PB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱp)
  (j + 1) hjp
local notation "CA" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "CB" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- **D0: the decoupled fluctuation on two tori, from the raw data.**  Let `F₁`, `F₁'` be maps
with the defining property of the decoupled background pair of Theorem I-4b for the generating set
`levelGS (j + 1)` of each torus (as in `decBg_value_twoTorus`), and `Sol`, `Sol'` maps with the
defining property of the analytic solution of Theorem I-4a for the pair
`(coverOf (levelGS (j + 1)), levelGS j)` (as in `decSol_value_twoTorus`).  Let the data of the
fluctuation problem be `flEdat` of the background values: `e = (barField D.Ψ φ, flAlpha α, ψ, 0)`
with `(φ, α) = F₁ (s, rawOf D)` (and likewise on the second torus).  Under the geometric
hypotheses of the two comparisons on a common component `Y`, if the raw data agree on
`RowsDep (S_Y)` and the fluctuations agree on `S_Y^F`, then the fluctuation multipliers agree on
`S_Y^F` and the fluctuation fields on `Y`.  The base potential and the base field of the
fluctuation data are compared by `decSol_data_of_decBg`; the source `f₁ = 0` needs no
hypothesis. -/
theorem decSol_value_twoTorus_of_decBg {c BG : ℝ} (hS : DecSpecs d L c BG) {a : ℕ → ℝ} {ν : ℝ}
    (SPA : DGSetting PA a ν) (SPB : DGSetting PB a ν) (hconn : HatConn PA)
    (hconn' : HatConn PB) (HBg : BgHyp d L K ϱp a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : DecParams PA × RawData d L (N₁ * L ^ m₁) K N → ((PA).Ω 1 × Fin N → ℂ) × ((PA).Ω 1 → ℂ)}
    {F₁' : DecParams PB × RawData d L (N₁' * L ^ m₁) K N →
      ((PB).Ω 1 × Fin N → ℂ) × ((PB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams PA) (D : BgData PA N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC PA (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (PA).Ω 1 × Fin N → ℂ)
        (α : (PA).Ω 1 → ℂ), IsDecBg PA a ν (rho4 d L N BG κ) s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams PB) (D : BgData PB N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC PB (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (PB).Ω 1 × Fin N → ℂ)
        (α : (PB).Ω 1 → ℂ), IsDecBg PB a ν (rho4 d L N BG κ) s D φ α → F₁' (s, rawOf D) = (φ, α))
    {s : DecParams PA} {s' : DecParams PB} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData PA N} {D' : BgData PB N}
    (hDd : InUnionDomainC PA (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC PB (bgC0 d L N) (c7 d L N BG κ) ν D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (PA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (PB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes PA X₁, P ∉ 𝒞 → extS PA s P = 0)
    (hs0' : ∀ P ∈ parCubes PB X₁', P ∉ 𝒞' → extS PB s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY PA X₁ 𝒞 Y).image bm = SY PB X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres PA (SY PA X₁ 𝒞 Y),
      sProd PB (extS PB s') (Prod.map id bm q) = sProd PA (extS PA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hD : RawBoxAgree {z | RowsDep PA a ν (SY PA X₁ 𝒞 Y) z} (rawOf D) (rawOf D'))
    {Kc Cx cstar BG₂ : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG₂)
    (SA : Dec2.CoverBase CA HA a ν Kc Cx) (SB : Dec2.CoverBase CB HB a ν Kc Cx) {κ₂ : ℝ}
    (hκ₂ : 0 ≤ κ₂) (hM₂ : cstar * Real.exp (N0 d L * κ₂) ≤ (L : ℝ) ^ m₁) (ιU : Bool)
    {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8))
    {Sol : Dec2.DecParams CA × Edat HA N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams CB × Edat HB N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams CA × Edat HA N, (∀ P, ‖p.1 P‖ < Real.exp κ₂) →
      StrictDataM HA N ιU δ₀ δ₁ p.2 →
        (Sol p).1 = dphi HA (Dec2.decG CA HA a ν p.1) p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed CA HA a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small HA (Sol p).2 (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) ∧
        Small HA (Sol p).2 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        SupBounds HA (Sol p).1 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small HA δα' (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) →
          Dec2.DecFixed CA HA a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HA a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams CB × Edat HB N, (∀ P, ‖p.1 P‖ < Real.exp κ₂) →
      StrictDataM HB N ιU δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi HB (Dec2.decG CB HB a ν p.1) p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed CB HB a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small HB (Sol' p).2 (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) ∧
        Small HB (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        SupBounds HB (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ₂) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small HB δα' (c6' d L N (famConst d L BG₂ κ₂) (gamma1 d / 8)) →
          Dec2.DecFixed CB HB a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HB a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {σ : Dec2.DecParams CA} {σ' : Dec2.DecParams CB} (hσ : ∀ P, ‖σ P‖ < Real.exp κ₂)
    (hσ' : ∀ P, ‖σ' P‖ < Real.exp κ₂)
    {ψ : CTorus d L N₁ m₁ K → Fin N → ℂ} {ψ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    (he : StrictDataM HA N ιU δ₀ δ₁ (flEdat PA HA (F₁ (s, rawOf D)) D.Ψ ψ))
    (he' : StrictDataM HB N ιU δ₀ δ₁ (flEdat PB HB (F₁' (s', rawOf D')) D'.Ψ ψ'))
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hYF : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYFc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    (hσ0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → Dec2.extS CA σ P = 0)
    (hσ0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → Dec2.extS CB σ' P = 0)
    (hBF' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagreeF : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd (Dec2.extS CB σ') (Prod.map id bm q) = (CA).sProd (Dec2.extS CA σ) q)
    (hΨB : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, ψ x = ψ' (bm x)) :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      (Sol' (σ', flEdat PB HB (F₁' (s', rawOf D')) D'.Ψ ψ')).2 (ιb x) =
        (Sol (σ, flEdat PA HA (F₁ (s, rawOf D)) D.Ψ ψ)).2 x) ∧
    (∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      (Sol' (σ', flEdat PB HB (F₁' (s', rawOf D')) D'.Ψ ψ')).1 (ιb y, i) =
        (Sol (σ, flEdat PA HA (F₁ (s, rawOf D)) D.Ψ ψ)).1 (y, i)) := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDC⟩ := id hDd
  obtain ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hDC'⟩ := id hDd'
  obtain ⟨φ, α, hsol, -⟩ := i4b_exists_unique hS SPA HBg hκ hM (fun P => (hs P).le) hδ0 hδε hε
    hδ hνε hDC
  obtain ⟨φ', α', hsol', -⟩ := i4b_exists_unique hS SPB HBg hκ hM (fun P => (hs' P).le) hδ0' hδε'
    hε' hδ' hνε' hDC'
  have e1 := hF₁ s D hs hDd φ α hsol
  have e2 := hF₁' s' D' hs' hDd' φ' α' hsol'
  rw [e1] at he ⊢
  rw [e2] at he' ⊢
  obtain ⟨hαB, hφR⟩ := decSol_data_of_decBg hj1 hj hjp hS SPA SPB hconn hconn' HBg hκ hM
    (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hDC hDC'
    hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hD hsol hsol'
  exact decSol_value_twoTorus hj1 hj hjp hF SA SB hκ₂ hM₂ ιU h0 h1 hδ₀ hδ₁ hSol hSol' hσ hσ' he
    he' hYF hYFc hσ0 hσ0' hY' hBF' hagreeF hYR hn hn' hαB hφR hΨB (fun _ _ _ => rfl)

end FromRaw

end Balaban.Polymer.TwoTorusStep
