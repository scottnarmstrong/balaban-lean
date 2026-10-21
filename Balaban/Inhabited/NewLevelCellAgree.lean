/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelClassCells
public import Balaban.Polymer.IrrelTorusBCell

/-!
# The cell case of the two-torus comparison of the new level (ruling R15)

Under ruling R15 the irrelevant term `irrelTorus` files at the distinguished cell `□(y₀)` the relevant
parts of the polymers in the box of half-side `r_K = ⌊L^{m₀+m₁+K}/8⌋` around `y₀` only, so its value
at the cell is the same on two tori (`irrelTorus_cell_boxAgree`):

* `cellTermsAgree_of_class`: **`CellTermsAgree` holds** for classes whose terms are the members
  `Tm N₁`, `Tm N₁'` of a family with `TorusIndep`, the locality of the terms of the second torus,
  `L^{m₀} ∣ N₁, N₁'`, the margin `8 (R + r_K) + 3 L^K + L · cellSide < n` on both tori, and a set `Z`
  in the box of radius `R` containing the polymer and the stencil `y₀ + L^j e_μ`;
* `newLevel_coeff_twoTorus_of_class_cells_R15`: `newLevel_coeff_twoTorus_of_class_cells` with its
  premise `hcell` discharged (the margins at the cell side of level `k + 1` added): the coefficient of
  the new level is the same on two tori, the remaining premises being those of
  `newLevel_coeff_twoTorus_of_class_cells` other than `hcell`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep
  Balaban.SmallField.Def6v2


section Cell

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))

/-- **The agreement of the irrelevant term at the distinguished cell** (ruling R15; the named
hypothesis `hcellcase` of `oldTerm_E_agree`): for classes `C`, `C'` whose terms are the members
`Tm N₁`, `Tm N₁'` of a family with `TorusIndep`, with the locality of the terms on the second torus,
`L^{m₀} ∣ N₁, N₁'`, `8 ≤ L^{m₀+m₁}`, the margin `8 (R + r_K) + 3 L^{k+1} + L · cellSide < n` on both
tori, an aligned `y₀` and a set `Z` in the centred box of radius `R` containing `X₀` and the stencil
`y₀ + L^j e_μ`, `CellTermsAgree C C' i₀ i₁ j y₀ X₀ Z`. -/
theorem cellTermsAgree_of_class {C : StepClass d L N₁ m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ (k + 1) N ϱ}
    (hCm : C'.m₀ = C.m₀) (hCT : C.Tm = Tm N₁) (hCT' : C'.Tm = Tm N₁')
    (hTI : TorusIndep C.m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₁').E j y X Ψ h = (Tm N₁').E j y X Ψ' h')
    (hN₁ : L ^ C.m₀ ∣ N₁) (hN₁' : L ^ C.m₀ ∣ N₁') (hM8 : 8 ≤ L ^ (C.m₀ + m₁))
    (i₀ i₁ : Fin N) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) {R : ℕ}
    (hmar : 8 * (R + L ^ (C.m₀ + m₁ + (k + 1)) / 8) + 3 * L ^ (k + 1) +
      L * cellSide L C.m₀ m₁ j < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmar' : 8 * (R + L ^ (C.m₀ + m₁ + (k + 1)) / 8) + 3 * L ^ (k + 1) +
      L * cellSide L C.m₀ m₁ j < (N₁' * L ^ m₁) * L ^ (k + 1))
    {y₀ : CTorus d L N₁ m₁ (k + 1)} (hy₀ : Aligned (L ^ j) y₀)
    {X₀ Z : Set (CTorus d L N₁ m₁ (k + 1))}
    (hZbox : ∀ z ∈ Z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z) (hXZ : X₀ ⊆ Z)
    (hstZ : ∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈ Z) :
    CellTermsAgree C C' i₀ i₁ j y₀ X₀ Z := by
  intro hX₀ r r' hr
  rw [hCm, hCT, hCT']
  subst hX₀
  exact irrelTorus_cell_boxAgree (Tm := Tm) (m₀ := C.m₀) hj1 hjk hTI hlocB hN₁ hN₁' hM8 hmar hmar'
    hy₀ (fun μ => hZbox _ (hstZ μ)) (fun z hz => hZbox z (hXZ hz)) i₀ i₁ r.1 r.2 r'.1 r'.2
    (fun x hx => (hr x (hXZ hx)).1.symm) (fun μ => (hr _ (hstZ μ)).1.symm)
    (fun x hx => (hr x (hXZ hx)).2.symm)

end Cell

section Final


variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl


attribute [local irreducible] NewLevelSystem.Dom

/-- **The coefficient of the new level on two tori, with the cell case discharged** (blocker 7, the
step clause; ruling R15): `newLevel_coeff_twoTorus_of_class_cells` with its premise `hcell`
proved by `cellTermsAgree_of_class` on the margins `canonZ` of the canonical covers (which lie in the
regions `X₁` by the cover requirement `hX1`), under the margins `hmarC`, `hmarC'` at the cell side of
level `k + 1` on both tori.  All other premises are those of `newLevel_coeff_twoTorus_of_class_cells`. -/
theorem newLevel_coeff_twoTorus_of_class_cells_R15
    (hN2 : 2 ≤ N)
    (hk : 1 ≤ k)
    (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)}
    {t pp : ℝ}
    {Jr : (SA).JointRep t pp}
    {C' : StepClass d L N₁' m₁ k N ϱ}
    {pp' : ℝ}
    {Jr' : (SB).JointRep t pp'}
    (NS : NewLevelSystem (SA) C z Jr)
    (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hC' : FlCore N (GB) (HB) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hκ : NS'.κ = NS.κ)
    (hBG : NS'.BG = NS.BG)
    (hBG₂ : NS'.BG₂ = NS.BG₂)
    (hp₁ : NS'.p₁ = NS.p₁)
    (hεU : NS.Z.εU = NS'.Z.εU)
    (hκH : NS.Z.κH = NS'.Z.κH)
    (hκ0 : NS.Z.κ0 = NS'.Z.κ0)
    (hGA : IsLevel (GA) (k + 1))
    (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (θ : physParam N (SA))
    (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t)
    (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z} (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hρc : 2 * NS.p₁ ≤ cψ)
    (hrad : markedRad d L N k 1 NS.κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hI𝒴 : NS.Z.I.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hI𝒴' : NS'.Z.I.𝒴 = (Finset.univ.biUnion fun z : TB =>
        polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁' m₁ (k + 1) × Fin N =>
        polyDom (GB) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (humB : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k 1 NS.κ NS.p₁ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hδc : 0 ≤ δc)
    (hconn : HatConn (SA).G')
    (hconn' : HatConn (SB).G')
    (hD : XiCData (SA).G' (compWeight L 1) (SA).ν (k + 1) 1 t (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2))
    (hD' : XiCData (SB).G' (compWeight L 1) (SA).ν (k + 1) 1 t (bgOfRaw (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) θ'.1.2))
    (i₀ i₁ : Fin N)
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁}
    {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    (hP : OldTermsCanonPinsAt (SA) C NS.O F i₀ i₁)
    (hP' : OldTermsCanonPinsAt (SB) C' NS'.O F' i₀ i₁)
    (hCm : C'.m₀ = C.m₀)
    {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ (k + 1) N ϱ}
    (hCT : C.Tm = Tm N₁)
    (hCT' : C'.Tm = Tm N₁')
    (hTI : TorusIndep C.m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₁').E j y X Ψ h = (Tm N₁').E j y X Ψ' h')
    (hM8 : 8 ≤ L ^ (C.m₀ + m₁))
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k → insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    (hcX' : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k → insert y₀ X₀ ⊆ ↑(F'.X₁fC j y₀ X₀))
    {R₂ : ℕ}
    (hRR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (hGA2 : (SA).G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hGB2 : (SB).G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hnE : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (LC : CanonCoverLocal F F')
    (SpG : DGSetting (SA).G' (compWeight L (SA).a₁) (SA).ν) (hm₀1 : 1 ≤ C.m₀)
    (hbig : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁ * L ^ m₁ * L ^ (k + 1))
    (hbig' : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁' * L ^ m₁ * L ^ (k + 1))
    (hX1 : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      ∀ x ∈ nearSet (zRad L m₁ k) (canonPts LC j y₀ X₀),
        LocalCover.nbhd C.m₀ x ⊆ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hPK : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      LC.PK' j (bm y₀) (bm '' X₀) = bm '' LC.PK j y₀ X₀)
    (hPJ : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      LC.PJ' j (bm y₀) (bm '' X₀) = bm '' LC.PJ j y₀ X₀)
    (hmarC : 8 * (R + L ^ (C.m₀ + m₁ + (k + 1)) / 8) + 3 * L ^ (k + 1) +
      L * cellSide L C.m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmarC' : 8 * (R + L ^ (C.m₀ + m₁ + (k + 1)) / 8) + 3 * L ^ (k + 1) +
      L * cellSide L C.m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {K : NewLevelConsts}
    (hK : NS.HasConsts K)
    (hK' : NS'.HasConsts K)
    {oδc : ℝ}
    (oMX : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (omar : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < oδc)
    (oαK : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (osm : oδc ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    (hρ : 0 < NS.O.ρ)
    (hΦan : ∀ τ, AnalyticOnNhd ℂ (fun t' => (eTermFun (SA).G' (NS.O.Gk τ) (NS.O.Gj τ)
      (stepG d L N₁ m₁ k ϱ) (compWeight L (SA).a₁) (NS.O.FkL τ)
      (fun r => ((SA).β : ℂ)⁻¹ * NS.O.Eτ τ r)) t'.1 t'.2.1 t'.2.2)
      (FlReal (SA).G' (stepG d L N₁ m₁ k ϱ) (SA).a₁ (SA).ν NS.O.BG NS.O.κ t (NS.O.X₁f τ)
        NS.O.BG₂ NS.O.δ₁))
    (hn19 : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn19' : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hmE₁ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmE₂ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1)):
    NS'.coeff θ' (T.image (σc)) = NS.coeff θ T := by
  have hN₁ : L ^ C.m₀ ∣ N₁ := by
    have := NS.OS.hN
    rwa [hP.1] at this
  have hN₁' : L ^ C.m₀ ∣ N₁' := by
    have := NS'.OS.hN
    rwa [hP'.1, hCm] at this
  refine newLevel_coeff_twoTorus_of_class_cells (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (T := T) (hT := hT) (hC := hC) (hC' := hC') (hκ := hκ) (hBG := hBG) (hBG₂ := hBG₂) (hp₁ := hp₁) (hεU := hεU) (hκH := hκH) (hκ0 := hκ0) (hGA := hGA) (hGB := hGB) (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (θ := θ) (θ' := θ') (hθ := hθ) (hθ' := hθ') (hraw := hraw) (hcψ := hcψ) (hρc := hρc) (hrad := hrad) (hI𝒴 := hI𝒴) (hI𝒴' := hI𝒴') (hum := hum) (humB := humB) (hδc := hδc) (hconn := hconn) (hconn' := hconn') (hD := hD) (hD' := hD') (i₀ := i₀) (i₁ := i₁) (hP := hP) (hP' := hP') (hCm := hCm) (hCT := hCT) (hCT' := hCT') (hTI := hTI) (hlocB := hlocB) (hM8 := hM8) (hcX := hcX) (hcX' := hcX') (hRR := hRR) (hcloc := hcloc) (hcov := hcov) (hGA2 := hGA2) (hGB2 := hGB2) (hnE := hnE) (hnE' := hnE') (LC := LC) (SpG := SpG) (hm₀1 := hm₀1) (hbig := hbig) (hbig' := hbig') (hX1 := hX1) (hPK := hPK) (hPJ := hPJ) (hK := hK) (hK' := hK') (oMX := oMX) (omar := omar) (oαK := oαK) (osm := osm) (hρ := hρ) (hΦan := hΦan) (hn19 := hn19) (hn19' := hn19') (hmE₁ := hmE₁) (hmE₂ := hmE₂) (hcell := ?_)
  intro j y₀ X₀ hadm hbox
  have hjk : j ≤ k := hadm.2.1
  have hcs : cellSide L C.m₀ m₁ j ≤ cellSide L C.m₀ m₁ (k + 1) := by
    unfold cellSide
    exact Nat.pow_le_pow_right (NeZero.pos L) (by omega)
  have hLcs : L * cellSide L C.m₀ m₁ j ≤ L * cellSide L C.m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_left _ hcs
  have hsub : ∀ w ∈ canonPts LC j y₀ X₀, w ∈ canonZ LC C.m₀ j y₀ X₀ := fun w hw =>
    subset_cellUnion _ _ ⟨w, hw, by simp [Balaban.LargeField.supDist_self]⟩
  have hZX : canonZ LC C.m₀ j y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀) := cellUnion_subset _ (hX1 j y₀ X₀ hadm)
  exact cellTermsAgree_of_class (j := j) (R := R) hCm hCT hCT' hTI hlocB hN₁ hN₁' hM8 i₀ i₁ hadm.1 (by omega)
    (by omega) (by omega) hadm.2.2.1 (fun z hz => hbox z (hZX hz))
    (fun x hx => hsub x (Or.inl (Or.inl (Or.inl (Set.mem_insert_of_mem _ hx)))))
    (fun μ => hsub _ (Or.inl (Or.inl (Or.inr ⟨μ, rfl⟩))))

end Final

end Balaban.Inhabited
