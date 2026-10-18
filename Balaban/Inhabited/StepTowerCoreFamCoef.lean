/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyGCore
public import Balaban.Inhabited.E0CoeffFamilyRotHeq
public import Balaban.Inhabited.StepTowerCoreFamRay
public import Balaban.Inhabited.StepTowerCoreFamMark
public import Balaban.Polymer.TwoTorusE1Coef
import Mathlib.Tactic.Linarith

/-!
# The interpolation coefficient of the core in canonical form, and its uniqueness

`core_c_eq_canonical` rewrites the coefficient `c θ C = gsumCoeff … (A₀ θ) … C` of the core, whose
labels and activity are given up to `HEq`, with the labels `thickLabels I0.𝒴 I0.dom` and the
activity `commonAct (zeroSourceAct (labelActFamilyOn … I0 …))` of the direct terms `I0`.
`gsumCoeff_relabel` says that a bijection of the labels preserving the sites and the activities
does not change `gsumCoeff`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory
  Balaban.Polymer.TwoTorusStep

section Canon

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => (((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ))

/-- **The interpolation coefficient of the core in canonical form.** -/
theorem core_c_eq_canonical
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁]
    (hN : L ^ 1 ∣ N₁) (ν β p₁ : ℝ)
    (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < (SA).p₁)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol : TA → Dec2.DecParams (coverOf (GA)) ×
      Edat (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
        (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)) N →
      ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
        (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)).Ω 1 × Fin N → ℂ) ×
      ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
        (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)).Ω 1 → ℂ)}
    (z : TA)
    {Lb : Type} [Fintype Lb]
    {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb} {εH : ℝ}
    {A₀ : physParam N (SA) → ℂ →
      LabelAct (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        ((SA).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {c : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hc : ∀ θ C, c θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
      (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)) (A₀ θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
        commonAnchor Lb (fun _ => Set.univ) (e1DomG (SA)) z i)
      (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) C)
    (hGdep : ∀ θ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u))
    {val : FA → FA → ℂ → ΛA → ℂ}
    (I0 : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
      (2 * T.κdec - 1) (rawOf (SA).D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SA) (SA).a₁ (SA).ν T.t (1 / (SA).β))
      (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
      (physAgΘ (SA)) (AgFDirPair (SA)))
    (hFd : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0
      (physVq (SA) (SA).a₁ (SA).ν T.t 1))
    (hεU : 0 ≤ (SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
    (hLbI : Lb = {Y // Y ∈ I0.𝒴})
    (hεHI : εH = 2 ^ 2 * (2 * ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))))
    (hLabI : HEq Lab₀ (thickLabels I0.𝒴 I0.dom))
    (hAI : HEq A₀ (commonAct (zeroSourceAct
      (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0 hFd hN hp
        (by norm_num) hεU T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two)) :
    ∀ θ C, c θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
        (commonLabels (thickLabels I0.𝒴 I0.dom) hN (by have := T.hL; omega)
          (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        (commonAct (zeroSourceAct
          (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0 hFd hN hp
            (by norm_num) hεU T.κ0_ent T.marks_K0_le) 2 (by norm_num))
          hN (by have := T.hL; omega)
          (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
          (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two θ)
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
          commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
        (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) C := by
  intro θ C
  rw [hc θ C]
  subst hLbI hεHI
  obtain rfl := eq_of_heq hLabI
  obtain rfl : ‹Fintype {Y // Y ∈ I0.𝒴}› = Finset.fintypeCoeSort I0.𝒴 := Subsingleton.elim _ _
  have hAH := labelAct_H_of_heq (f := A₀) (hε := rfl) (hκ := rfl) (hκ0 := rfl) (hKc := rfl)
    (h := hAI)
  exact gsumCoeff_congr _ _ _ _ _ _ _ (fun i u => hGdep θ i u)
    (fun s _ y _ => funext (hAH θ (s : ℂ) y)) (fun _ _ _ _ => rfl)



end Canon

section Relabel

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {𝔅 : Type*}

/-- **A bijection of the labels that preserves the sites and the activities does not change
`gsumCoeff`.** -/
theorem gsumCoeff_relabel {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb'] (Lab : CubeLabels m₀ j Ω Lb)
    (Lab' : CubeLabels m₀ j Ω Lb') {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (A' : ℂ → LabelAct Lab' Ωb εH' κH' κ0' Kc')
    {ι : Type*} [Fintype ι] (y0 : ι → Lb) (y0' : ι → Lb')
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (e : Lb ≃ Lb')
    (hys : ∀ y, Lab'.ysite (e y) = Lab.ysite y)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, (A' (s : ℂ)).H (e y) Φ = (A (s : ℂ)).H y Φ)
    (hy0 : ∀ i, y0' i = e (y0 i))
    (hGdep : ∀ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i u))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    gsumCoeff μ Lab' A' y0' G T = gsumCoeff μ Lab A y0 G T := by
  have h := gsumCoeff_transport μ μ Lab Lab' A A' y0 y0' G G hGdep id T
    (fun _ _ _ _ h => h) (fun Φ Φ' => Φ = Φ')
    (fun Z _ F F' _ hFF => by
      have : F' = F := funext fun Φ => hFF Φ Φ rfl
      rw [this])
    (fun _ => True) (fun _ => True) (fun _ _ y hy => absurd trivial hy)
    (fun _ _ y hy => absurd trivial hy) (fun y _ _ => e y) (fun _ _ _ => trivial)
    (fun y _ _ => by rw [hys, Finset.image_id])
    (fun y₁ _ _ y₂ _ _ h => e.injective h)
    (fun y' _ hy' => ⟨e.symm y', trivial, by
      have e1 : Lab.ysite (e.symm y') = Lab'.ysite y' := by
        rw [← hys, Equiv.apply_symm_apply]
      rw [e1]
      simpa only [Finset.image_id] using hy', by simp⟩)
    (fun s hs y _ _ Φ Φ' h => by rw [← h]; exact hA s hs y Φ)
    (fun i _ => i)
    (fun i _ => by rw [hy0, hys, Finset.image_id])
    (fun _ _ _ _ h => h)
    (fun i' hi' => ⟨i', by
      have e1 : Lab.ysite (y0 i') = Lab'.ysite (y0' i') := by rw [hy0, hys]
      rw [e1]
      simpa only [Finset.image_id] using hi', rfl⟩)
    (fun s hs i _ Φ Φ' h => by rw [← h])
  rwa [Finset.image_id] at h

end Relabel

section Unique

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => (((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ))

/-- **The interpolation coefficient of the core is unique.**  Two systems of the core objects on the
same step (pinned `F₁`, `Sol`, direct terms `I0` with pinned `F₂`, `Sol₂`, labels and activity
`Lab₀`, `A₀` up to `HEq`) give the same coefficient `c θ C = gsumCoeff … (A₀ θ) … C` at every
parameter `θ` of `physV` and every set `C` of cubes. -/
theorem coreCoeff_unique
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁]
    (hN : L ^ 1 ∣ N₁) (ν β p₁ : ℝ)
    (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < (SA).p₁)
    (z : TA) (θ : physParam N (SA)) (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν T.t)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Lb : Type} [Fintype Lb]
    {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb} {εH : ℝ}
    {A₀ : physParam N (SA) → ℂ →
      LabelAct (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        ((SA).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {c : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hc : ∀ θ C, c θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
      (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)) (A₀ θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
        commonAnchor Lb (fun _ => Set.univ) (e1DomG (SA)) z i)
      (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) C)
    {val : FA → FA → ℂ → ΛA → ℂ}
    (I0 : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
      (2 * T.κdec - 1) (rawOf (SA).D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SA) (SA).a₁ (SA).ν T.t (1 / (SA).β))
      (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
      (physAgΘ (SA)) (AgFDirPair (SA)))
    (hFd : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0
      (physVq (SA) (SA).a₁ (SA).ν T.t 1))
    (hεU : 0 ≤ (SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
    (hLbI : Lb = {Y // Y ∈ I0.𝒴})
    (hεHI : εH = 2 ^ 2 * (2 * ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))))
    (hLabI : HEq Lab₀ (thickLabels I0.𝒴 I0.dom))
    (hAI : HEq A₀ (commonAct (zeroSourceAct
      (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0 hFd hN hp
        (by norm_num) hεU T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two)) 
    (hI𝒴 : I0.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hSol : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol b))
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hSol₂ : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol₂ b))
    (hT : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : FA) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                I0.T Y x w σ (Θ, 0) = -((SA).β : ℂ) *
                  ∑ z : TA, if Y ∈ polyDom (SA).G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      (SA).G' 1 (X1 (SA).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν k z
                        (F₂ z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂ z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂ z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                              (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                          (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0)
    (hGdep : ∀ θ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u))
    {Lb' : Type} [Fintype Lb']
    {Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb'} {εH' : ℝ}
    {A₀' : physParam N (SA) → ℂ →
      LabelAct (commonLabels Lab₀' hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        ((SA).blockSplit 1 hp).Ωb εH' (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {c' : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hc' : ∀ θ C, c' θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
      (commonLabels Lab₀' hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)) (A₀' θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
        commonAnchor Lb' (fun _ => Set.univ) (e1DomG (SA)) z i)
      (fun i u Φ => e1MarkGParamG (SA) F₁' Sol' p₁ hp z T.t θ i u Φ) C)
    {val' : FA → FA → ℂ → ΛA → ℂ}
    (I0' : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
      (2 * T.κdec - 1) (rawOf (SA).D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SA) (SA).a₁ (SA).ν T.t (1 / (SA).β))
      (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
      (physAgΘ (SA)) (AgFDirPair (SA)))
    (hFd' : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0'
      (physVq (SA) (SA).a₁ (SA).ν T.t 1))
    (hεU' : 0 ≤ (SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
    (hLbI' : Lb' = {Y // Y ∈ I0'.𝒴})
    (hεHI' : εH' = 2 ^ 2 * (2 * ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))))
    (hLabI' : HEq Lab₀' (thickLabels I0'.𝒴 I0'.dom))
    (hAI' : HEq A₀' (commonAct (zeroSourceAct
      (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0' hFd' hN hp
        (by norm_num) hεU' T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU')) T.κ0_two)) 
    (hI𝒴' : I0'.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hF₁' : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    (hSol' : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol' b))
    {F₂' : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₂' : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    (hF₂' : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    (hSol₂' : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol₂' b))
    (hT' : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : FA) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                I0'.T Y x w σ (Θ, 0) = -((SA).β : ℂ) *
                  ∑ z : TA, if Y ∈ polyDom (SA).G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      (SA).G' 1 (X1 (SA).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν k z
                        (F₂' z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂' z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂' z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                              (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                          (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0)
    (hGdep' : ∀ θ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁' Sol' p₁ hp z T.t θ i u))
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    c' θ C = c θ C := by
  classical
  have hθ1 := hθ.1
  have hcan := core_c_eq_canonical T hm₀ hk hN ν β p₁ D hp z hc hGdep I0 hFd hεU hLbI hεHI hLabI
    hAI θ C
  have hcan' := core_c_eq_canonical T hm₀ hk hN ν β p₁ D hp z hc' hGdep' I0' hFd' hεU' hLbI'
    hεHI' hLabI' hAI' θ C
  rw [hcan, hcan']
  have h𝒴 : I0.𝒴 = I0'.𝒴 := hI𝒴.trans hI𝒴'.symm
  let e : ({Y // Y ∈ I0.𝒴} ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1DomG (SA))) ≃
      ({Y // Y ∈ I0'.𝒴} ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1DomG (SA))) :=
    Equiv.sumCongr (Equiv.subtypeEquivRight (fun Y => by rw [h𝒴])) (Equiv.refl _)
  obtain ⟨D₀, hD₀, hD₀θ⟩ := hθ1
  have hV : ((θ.1, 0) : physParam N (SA)) ∈ physVq (SA) (SA).a₁ (SA).ν T.t 1 :=
    ⟨⟨hθ.1, by simp [l1Ball, physIncl_apply]⟩, by simp⟩
  refine Eq.trans (gsumCoeff_congr _ _ _ _
    (fun i u Φ => e1MarkGParamG (SA) F₁' Sol' p₁ hp z T.t θ i u Φ)
    (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) _ (fun i u => hGdep' θ i u)
    (fun _ _ _ _ => rfl) (fun s _ i _ => ?_)) ?_
  · funext Φ
    exact (e1MarkGParamG_unique_tower T hk D _ rfl hp F₁ F₁' hF₁ hF₁' Sol Sol' hSol hSol' z θ
      hθ.1 i (s : ℂ) Φ).symm
  · refine gsumCoeff_relabel _ _ _ _ _ _ _ _ e ?_ ?_ ?_ (fun i u => hGdep θ i u) C
    · intro y
      rcases y with y | y <;> rfl
    · intro s hs y Φ
      rcases y with ⟨Y, hY⟩ | r
      · have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
        have hsR : ‖(s : ℂ)‖ < 2 := lt_of_le_of_lt hs1 one_lt_two
        have he1 : e (Sum.inl ⟨Y, hY⟩) = Sum.inl ⟨Y, h𝒴 ▸ hY⟩ := rfl
        rw [he1, commonAct_H_inl, commonAct_H_inl, zeroSourceAct_H, zeroSourceAct_H,
          labelActFamilyOn_H (SA) 1 _ hFd' hN hp (by norm_num) hεU' T.κ0_ent T.marks_K0_le hV hsR,
          labelActFamilyOn_H (SA) 1 _ hFd hN hp (by norm_num) hεU T.κ0_ent T.marks_K0_le hV hsR]
        have hD₀θ' : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D₀ := hD₀θ
        have hJ : physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ) ((θ.1, 0) : physParam N (SA)) =
            ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), 0) := by
          rw [physInclScaled_apply]
          refine Prod.ext rfl ?_
          funext x i
          simp
        rw [hJ, hD₀θ']
        congr 1
        exact (directTerm_unique_tower T hk D hp (SA) rfl F₂ F₂' Sol₂ Sol₂' (fun z => hF₂ z)
          (fun z => hF₂' z) hSol₂ hSol₂' I0.T I0'.T hT hT' Y hD₀
          (ψ := (SA).hatOf 1 p₁ hp Φ) ((SA).hatOf_mem 1 hp hp Φ) (by simpa using hsR)).symm
      · rfl
    · intro i
      rfl

end Unique

end Balaban.Inhabited
