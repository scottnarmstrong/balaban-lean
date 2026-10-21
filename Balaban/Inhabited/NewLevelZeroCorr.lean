/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffTwoTorus
public import Balaban.Polymer.TwoTorusDirectTerms
public import Balaban.Inhabited.E0CoeffFamilyTorusIT
import Mathlib.Tactic.Linarith

/-!
# The zero-source labels and activities of two systems of the new level on two tori

* `zeroSourceTermFormula_evDec`: the formula of the zero-source terms of a `ZeroSourceSystem` in the
  form `evDec` (`ZeroSourceTermFormula` rewritten by `FFmarked_one_zero`);
* `zeroSource_labelCorr`: for two systems of the new level on the tori `N₁`, `N₁'` (steps `hatStepKG`)
  whose zero-source direct terms have the explicit form (`hI𝒴`: the labels are the domains of the
  local covers), the labels of the zero-source family with blocks in a set `T` of the box correspond
  to those with blocks in `cubeMap '' T` and their zero-source activities agree at corresponding
  block variables (`directTerms_labelCorr_twoTorus`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

section ZF

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem physVq_one_of_mem (S : StepSetting d L N₁ m₁ k N ϱ) (t : ℝ) (θ : physParam N S)
    (hθ : θ ∈ physV S S.a₁ S.ν t) : ((θ.1, 0) : physParam N S) ∈ physVq S S.a₁ S.ν t 1 :=
  ⟨⟨hθ.1, by simp [l1Ball, physInclBg_apply]⟩, by simp⟩

theorem DecFieldPin.congr {S : StepSetting d L N₁ m₁ k N ϱ} {κ κ' BG BG' : ℝ} (hκ : κ = κ')
    (hBG : BG = BG')
    {F : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)} (h : DecFieldPin S κ BG F) :
    DecFieldPin S κ' BG' F := by
  subst hκ hBG; exact h

theorem DecSolPin.congr {S : StepSetting d L N₁ m₁ k N ϱ} {κ κ' BG₂ BG₂' δ₀ δ₀' δ₁ δ₁' : ℝ}
    (hκ : κ = κ') (hBG₂ : BG₂ = BG₂') (hδ₀ : δ₀ = δ₀') (hδ₁ : δ₁ = δ₁')
    {Sol : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    (h : DecSolPin S κ BG₂ δ₀ δ₁ Sol) : DecSolPin S κ' BG₂' δ₀' δ₁' Sol := by
  subst hκ hBG₂ hδ₀ hδ₁; exact h

/-- **The zero-source terms in the form `evDec`.** -/
theorem zeroSourceTermFormula_evDec (S : StepSetting d L N₁ m₁ k N ϱ)
    {F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    {Tf : Set (CTorus d L N₁ m₁ (k + 1)) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hT : ZeroSourceTermFormula S F₂ Sol₂ Tf) :
    ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
      (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      Tf Y x w σ (Θ, 0) = -(S.β : ℂ) *
        ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
            (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
            (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y)
            w.1) taylorWeight x.1 σ Θ
        else 0 := by
  intro Y x w σ Θ
  rw [hT Y x w σ Θ]
  refine congrArg (fun t => -((S.β : ℝ) : ℂ) * t) (Finset.sum_congr rfl fun z _ => ?_)
  by_cases hY : Y ∈ polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k z))
  · rw [ite_eq_left hY, ite_eq_left hY]
    exact congrArg (fun FF => rayTerm (dl3 (evTerm
      (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) :
        Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' 1
      (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z))) FF Y) w.1)
        taylorWeight x.1 σ Θ)
      (FFmarked_one_zero (a₁ := S.a₁) (ν := S.ν)
        (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
        (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k z) ∅).symm
  · rw [ite_eq_right hY, ite_eq_right hY]

end ZF

section Z

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "FA" => ((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ)
set_option hygiene false in
local notation "FB" => ((SB).U × Fin N → ℂ) × ((SB).U × Fin N → ℂ)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

theorem zeroSource_labelCorr
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : (SA).JointRep t pp}
    {C' : StepClass d L N₁' m₁ k N ϱ} {z' : RootIdx d L N₁' m₁ (k + 1)} {pp' : ℝ}
    {Jr' : (SB).JointRep t pp'}
    (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' z' Jr')
    (hκ : NS'.κ = NS.κ) (hBG : NS'.BG = NS.BG) (hBG₂ : NS'.BG₂ = NS.BG₂)
    (hp₁ : NS.p₁ = NS'.p₁) (hεU : NS.Z.εU = NS'.Z.εU) (hκH : NS.Z.κH = NS'.Z.κH)
    (hκ0 : NS.Z.κ0 = NS'.Z.κ0)
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      k (Nat.le_succ k)) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hC' : FlCore N (GB) (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      k (Nat.le_succ k)) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (hm₁ : 1 ≤ m₁) {R : ℕ}
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρc : 2 * NS.p₁ ≤ cψ)
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
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    ∃ ψ₀ : (∀ y : {Y // Y ∈ NS.Z.I.𝒴}, blocksOf 1 (k + 1) Set.univ y.1 ⊆ T →
        {Y // Y ∈ NS'.Z.I.𝒴}),
      (∀ y hy, blocksOf 1 (k + 1) Set.univ (ψ₀ y hy).1 =
        (blocksOf 1 (k + 1) Set.univ y.1).image (σc)) ∧
      (∀ y₁ hy₁ y₂ hy₂, ψ₀ y₁ hy₁ = ψ₀ y₂ hy₂ → y₁ = y₂) ∧
      (∀ y' : {Y // Y ∈ NS'.Z.I.𝒴}, blocksOf 1 (k + 1) Set.univ y'.1 ⊆ T.image (σc) →
        ∃ y hy, ψ₀ y hy = y') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hy,
        ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
            Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
          (NS'.Z.A₀ θ' (s : ℂ)).H (ψ₀ y hy) Φ' = (NS.Z.A₀ θ (s : ℂ)).H y Φ) := by
  have hVθ : ((θ.1, 0) : physParam N (SA)) ∈ physVq (SA) (SA).a₁ (SA).ν t 1 := physVq_one_of_mem (SA) t θ hθ
  have hVθ' : ((θ'.1, 0) : physParam N (SB)) ∈ physVq (SB) (SB).a₁ (SB).ν t 1 := physVq_one_of_mem (SB) t θ' hθ'
  have hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N NS.BG NS.κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N NS.BG NS.κ) s D φ α →
        NS.Z.F₂ b (s, rawOf D) = (φ, α) :=
    fun b => NS.Z.hF₂ b

  have hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N NS.BG NS.κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N NS.BG NS.κ) s D φ α →
        NS'.Z.F₂ b (s, rawOf D) = (φ, α) :=
    fun b => (NS'.Z.hF₂ b).congr hκ hBG

  have hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t))) t p.2 →
        (NS.Z.Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS.Z.Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS.Z.Sol₂ b p).2 ∧
        Small (HA) (NS.Z.Sol₂ b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small (HA) (NS.Z.Sol₂ b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds (HA) (NS.Z.Sol₂ b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (NS.Z.Sol₂ b p).2) :=
    fun b => NS.Z.hSol₂ b

  have hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t))) t p.2 →
        (NS'.Z.Sol₂ b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS'.Z.Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (NS'.Z.Sol₂ b p).2 ∧
        Small (HB) (NS'.Z.Sol₂ b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small (HB) (NS'.Z.Sol₂ b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds (HB) (NS'.Z.Sol₂ b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (NS'.Z.Sol₂ b p).2) :=
    fun b => (NS'.Z.hSol₂ b).congr hκ hBG₂ (by rw [hκ, hBG]) rfl

  have hIT : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (x w : FA) (σ : ℂ)
        (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      NS.Z.I.T Y x w σ (Θ, 0) = -(((SA).β : ℝ) : ℂ) * ∑ z : TA,
        if Y ∈ polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 νS hGA (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.Z.F₂ z) (NS.Z.Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) νS k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0 :=
    zeroSourceTermFormula_evDec (SA) NS.Z.hT

  have hIT' : ∀ (Y : Set (CTorus d L N₁' m₁ (k + 1))) (x w : FB) (σ : ℂ)
        (Θ : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      NS'.Z.I.T Y x w σ (Θ, 0) = -(((SB).β : ℝ) : ℂ) * ∑ z : TB,
        if Y ∈ polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 νS hGB (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.Z.F₂ z) (NS'.Z.Sol₂ z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) νS k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0 :=
    zeroSourceTermFormula_evDec (SB) NS'.Z.hT
  obtain ⟨ψ₀, h1, h2, h3, h4⟩ := directTerms_labelCorr_twoTorus (hN2 := hN2) (hk := hk)
    (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (hC := hC) (hC' := hC') (hGA := hGA) (hGB := hGB)
    (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (hN := hN) (hN' := hN') (hm₁ := hm₁)
    (hn := hn) (hn' := hn') (θ := θ) (θ' := θ') (hθ := hθ.1) (hθ' := hθ'.1) (hraw := hraw)
    (hp := NS.hp) (hp' := NS'.hp) (I := NS.Z.I) (I' := NS'.Z.I) (hF := NS.Z.hF)
    (hF' := NS'.Z.hF) (hρI := NS.Z.hp₁) (hRσ := one_lt_two) (hεU := NS.Z.hεU)
    (hκ0 := NS.hκ02)
    (KcL := 2 * (K0 d L NS.Z.κ0 + 1)) (hKc := by have := K0_pos d L NS.Z.κ0; linarith) (hρI' := NS'.Z.hp₁) (hRσ' := one_lt_two)
    (hεU' := NS'.Z.hεU) (hκ0' := NS'.hκ02)
    (KcL' := 2 * (K0 d L NS'.Z.κ0 + 1)) (hKc' := by have := K0_pos d L NS'.Z.κ0; linarith) (hρe := hp₁) (hRσe := rfl)
    (hεUe := hεU) (hae := hκH) (hκ0e := hκ0) (hKce := by rw [hκ0]) (hV := hVθ)
    (hV' := hVθ') (cc := (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (hcψ := hcψ)
    (hρc := hρc) (hrad := hrad)
    (hF₂ := hF₂) (hF₂' := hF₂') (hSol₂ := hSol₂) (hSol₂' := hSol₂')
    (hI𝒴 := hI𝒴) (hI𝒴' := hI𝒴') (hIT := hIT) (hIT' := hIT') (T := T) (hT := hT)
  exact ⟨ψ₀, h1, h2, h3, h4⟩

end Z
end Balaban.Inhabited
