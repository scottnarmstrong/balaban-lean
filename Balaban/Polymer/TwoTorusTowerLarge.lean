/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusE0Coef
public import Balaban.Inhabited.E1CoeffFamilyG
public import Balaban.Inhabited.MarkCorrBudgetG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The two-torus coefficient theorems at the tower, for large `β`

The landed two-torus coefficient theorems `gsumCoeff_e1_twoTorus_fromTowerG` and
`e0Coeff_twoTorus_fromTowerG` carry, besides the data of the tower, the hypotheses `hum`, `hGdep`,
`hdom`, `hdom'`, `hcψ`, `hrad` and `2 ρ_I ≤ c_ψ`.  Here these are discharged.

* `hdom`, `hdom'`: the label domains `e1DomG` consist of domains of the level `k + 1`
  (`e1DomG_isDj_of_eq`).
* `hrad`, `hcψ`, `2 ρ_I ≤ c_ψ`: take `c_ψ = lvCpsiG …` (the hat radius of the scale); the radius
  `hrad` is the field `fl_radius` of the scale datum (the norm of `(β L^(k(d-2)))^(-1/2)` is that of
  the `β_U` power), and `ρ_I ≤ p₁` gives `2 ρ_I ≤ 2 p₁ < c_ψ` by the field `ray_margin`.
* `hum`, with `ρ = p₁`: `‖u‖ ≤ 1` and `p₁ ≤ c_ψ`, `markedRad` monotone in `c_ψ`, and `fl_radius`.
* `hGdep`: the dependence of the marks on the blocks of their label holds for the pair
  `(F₁, Sol)` produced by `markCorrFamily_fromTowerG`, not for an arbitrary pair with the defining
  properties; the corollaries therefore return the pair, with its defining properties.  The
  threshold `β₀` is that of `exists_beta0_corrRG` (`2 · 17/16 ≤ corrRG`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale Balaban.Inhabited
  Balaban.Inhabited.LevelStep Balaban.Inhabited.MarkBudgetAudit MeasureTheory

section Radius

/-- **The radius hypotheses of the two-torus theorems, from the scale datum.**  With
`c_ψ = lvCpsiG …` (the hat radius of the scale): `0 ≤ c_ψ`; the marked radius of `c_ψ` at
`cc = (β L^(k(d-2)))^(-1/2)` is below `t` (`hrad`); for every `ρ_I ≤ p₁`, `2 ρ_I ≤ c_ψ`; and for
`ρ = p₁` the radius condition `hum`. -/
theorem tower_radius_fromScaleData {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    0 ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ∧
    markedRad d L N k 1 T.κ (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t ∧
    (∀ ρI : ℝ, ρI ≤ p₁ → 2 * ρI ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ∧
    (∀ u : ℂ, ‖u‖ ≤ 1 →
      ‖u‖ * markedRad d L N k 1 T.κ p₁
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t) := by
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
  have hcψ := D.cψ_pos
  have hr0 := D.r_pos
  have hlt2 : 2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h := mul_le_mul_of_nonneg_right
      (show (2 : ℝ) ≤ 2 * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ by linarith)
      hp.le
    linarith [D.ray_margin]
  have hfl := D.fl_radius
  rw [hbU] at hfl
  have hmem := compWeightG_mem T hk
  have hCs : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by have := T.hd; omega) T.hL (by linarith [hmem.1]) T.κ
  refine ⟨hcψ.le, hfl, fun ρI h => by linarith, fun u hu => ?_⟩
  rw [hbU]
  have hmr : 0 ≤ markedRad d L N k 1 T.κ p₁ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    unfold markedRad
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg hCs hp.le))
  have hmono : markedRad d L N k 1 T.κ p₁ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≤
      markedRad d L N k 1 T.κ (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
        (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    unfold markedRad
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) hCs) (norm_nonneg _)) (Real.sqrt_nonneg _)
  calc ‖u‖ * markedRad d L N k 1 T.κ p₁ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      ≤ 1 * markedRad d L N k 1 T.κ p₁ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
        mul_le_mul_of_nonneg_right hu hmr
    _ < T.t := by rw [one_mul]; exact lt_of_le_of_lt hmono hfl

end Radius

section Pairs

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "SB" => StepTowerG.step T k hk N₁' ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := T.m₁)
  (K := k + 1) (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "ΛB" => RawData d L (N₁' * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => (((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ))
set_option hygiene false in
local notation "FB" => (((SB).U × Fin N → ℂ) × ((SB).U × Fin N → ℂ))

/-- **The pair of the tower with its defining properties and the block dependence of its marks.**
For the step `SA` of the tower at a scale with `0 < β` and `2 · 17/16 ≤ corrRG`, there is a pair
`(F₁, Sol)` (indexed by roots and blocks) such that, for every root `z`, the maps `b ↦ F₁ (z, b)`,
`b ↦ Sol (z, b)` satisfy the defining properties `hF₁`, `hSol` of the landed two-torus theorems, and
for every parameter `θ`, bridge label `i` and `u`, the marks `e1MarkGParamG` with `ρ = p₁` depend
only on the blocks of `i` (`hGdep`). -/
theorem tower_pairs_dep_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
    (hN : L ^ 1 ∣ N₁) (h5 : 5 < N₁) {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β) (hp : 0 < p₁)
    (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) :
    ∃ (F₁ : TA × TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ))
      (Sol : TA × TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
        ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)),
      ∀ z : TA,
      (∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
        (∀ P, ‖s P‖ < Real.exp T.κ) →
        InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
          (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
          F₁ (z, b) (s, rawOf D) = (φ, α)) ∧
      (∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
        (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
        StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
          (Sol (z, b) p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1
            p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol (z, b) p).2 ∧
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol (z, b) p).2 ∧
          Small (HA) (Sol (z, b) p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
          Small (HA) (Sol (z, b) p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          SupBounds (HA) (Sol (z, b) p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
              (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol (z, b) p).2)) ∧
      ∀ (θ : physParam N (SA))
        (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
        DepOn (blocksOf 1 (k + 1) Set.univ i.1)
          (e1MarkGParamG (SA) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t θ i u) := by
  classical
  have hA : (SA).p₁ = p₁ := rfl
  have hp' : 0 < (SA).p₁ := hp
  have h3N : L ^ T.m₀ ∣ N₁ := by rw [hm₀]; exact hN
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  obtain ⟨F₁, Sol, hF⟩ := markCorrFamily_fromTowerG T hm₀ D h5 hν0 hν hβ hp hRU rfl
    (S := T.step k hk N₁ ν β p₁) rfl hp'
  refine ⟨F₁, Sol, fun z => ?_⟩
  obtain ⟨hP, hJ2, hJ4, hcnt, hblk⟩ := hF z
  have hout := markedOutDecCorr_fields (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).hG'
    T.hd hN (fun b => (hV b).1) (fun b => (hV b).2.2.1) z
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) hP hJ2 hJ4 (ρ := p₁) hp le_rfl hp' T.t_pos
    (((T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)
  obtain ⟨-, hdep, -⟩ := hout
  refine ⟨fun b => (hblk b).2.2.2.2.2.1, fun b => (hblk b).2.2.2.2.2.2, ?_⟩
  intro θ i u
  by_cases hc : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight L (T.step k hk N₁ ν β p₁).a₁)
        (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < (17 / 16 : ℝ)
  · have e : e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp' z T.t θ i u = _ :=
      funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp' z T.t θ i u Φ hc.1 hc.2
    rw [e]
    exact hdep i.1 i.2 _ hc.1 u (e1_rad_ltG T hk hβ hp hRU hc.2.le)
  · intro Φ Φ' _
    rw [e1MarkGParamG_of_not _ _ _ _ hp' z T.t θ i u Φ hc,
      e1MarkGParamG_of_not _ _ _ _ hp' z T.t θ i u Φ' hc]

/-- **The energy coefficient on two tori at the tower, for large `β`.**  There is a threshold
`β₀` such that, beyond it, at every scale datum of the tower, the hypotheses `hum`, `hGdep`, `hdom`,
`hdom'`, `hL2`, `hcψ`, `hrad` and `2 ρ_I ≤ c_ψ` of `gsumCoeff_e1_twoTorus_fromTowerG` hold with
`ρ = p₁`, `c_ψ = lvCpsiG …` and `ρ_I ≤ p₁`; the pairs `(F₁, Sol)`, `(F₁', Sol')` of the two tori are
the ones of `markCorrFamily_fromTowerG` (returned with their defining properties).  The threshold
is that of `exists_beta0_corrRG` (`2 · 17/16 ≤ corrRG`); the radius hypotheses need no threshold. -/
theorem gsumCoeff_e1_twoTorus_fromTowerG_large {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ {k : ℕ}
    (hk : 1 ≤ k)
    {N₁ N₁' : ℕ}
    [NeZero N₁]
    [NeZero N₁']
    (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁')
    (_h5 : 5 < N₁)
    (_h5' : 5 < N₁')
    (ν : ℝ)
    (_hνpos : 0 < ν)
    (_hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (β ρs : ℝ)
    (_hρs : 0 < ρs)
    (_hβρ : max 1 ρs ≤ β)
    (_hβle : β₀ ≤ β)
    (p₁ q : ℝ)
    (_hq0 : 0 < q)
    (_hq : q ≤ ρs)
    (D : StepScaleDataG T k hk N₁ ν β p₁)
    (D' : StepScaleDataG T k hk N₁' ν β p₁)
    (hp : 0 < p₁)
    (_hp₁ : p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))))
    (z : TA)
    {rc R : ℕ}
    (_hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
    (_hrc : L ^ (k + 1) * rc ≤ R)
    (_hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (_hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (_hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (θ : physParam N (SA))
    (θ' : physParam N (SB))
    (_hθ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) ν (k + 1) 1 T.t)
    (_hθ' : (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) ν (k + 1) 1 T.t)
    (_hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (_hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x),
    ∃ (F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) (F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) (Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)) (Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)),
      (∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α)) ∧
      (∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α)) ∧
      (∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2)) ∧
      (∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2)) ∧
    (∃ (val : FA → FA → ℂ → ΛA → ℂ) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → ℂ → ΛA → ℂ)
        (val' : FB → FB → ℂ → ΛB → ℂ) (𝒴' : Finset (Set (CTorus d L N₁' T.m₁ (k + 1))))
        (Tt' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → ℂ → ΛB → ℂ),
        (∀ Θ ∈ physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β),
          ∃ I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SA).β))
              (2 * T.κdec - 1) Θ (physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β))
              (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
              (physAgΘ (SA)) (AgFDirPair (SA)),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (∀ Θ ∈ physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β),
          ∃ I' : DirectTerms (SB) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              ((SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SB).β))
              (2 * T.κdec - 1) Θ (physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β))
              (physXW (SB) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
              (physAgΘ (SB)) (AgFDirPair (SB)),
            I'.𝒴 = 𝒴' ∧ I'.T = Tt') ∧
        ∀ {ρI Rσ εU a κ0 KcL : ℝ} {Θ₀ : ΛA} {Θ₀' : ΛB} {SΛ : Set ΛA} {SΛ' : Set ΛB}
          {XW : Set (FA × FA)} {XW' : Set (FB × FB)} {valI : FA → FA → ℂ → ΛA → ℂ}
          {valI' : FB → FB → ℂ → ΛB → ℂ} {AgΘ : Set (CTorus d L N₁ T.m₁ (k + 1)) → ΛA → ΛA → Prop}
          {AgΘ' : Set (CTorus d L N₁' T.m₁ (k + 1)) → ΛB → ΛB → Prop}
          {AgF : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → Prop}
          {AgF' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → Prop}
          (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀ SΛ XW valI AgΘ AgF)
          (I' : DirectTerms (SB) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀' SΛ' XW' valI' AgΘ' AgF'),
          I.𝒴 = 𝒴 → I.T = Tt → I'.𝒴 = 𝒴' → I'.T = Tt' →
          ∀ {cJ cJ' : ℂ} {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
            (hF : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I V)
            (hF' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' V')
            (hρI : 0 < ρI) (hRσ : 1 < Rσ) (hεU : 0 ≤ εU) (hκ0 : aEnt d L + 2 ≤ κ0)
            (hKc : K0 d L κ0 ≤ KcL),
            ((θ.1, 0) : physParam N (SA)) ∈ V → ((θ'.1, 0) : physParam N (SB)) ∈ V' →
            ρI ≤ p₁ →
          gsumCoeff ((SB).blockSplit 1 hp).μ
              (commonLabels (thickLabels I'.𝒴 I'.dom) hN' (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl))
              (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
                  hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
                hN' (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl)
                (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
              (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB)) (bc z) i')
              (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' p₁ hp (bc z) T.t θ' i' u Φ') (Tb.image (σc)) =
            gsumCoeff ((SA).blockSplit 1 hp).μ
              (commonLabels (thickLabels I.𝒴 I.dom) hN (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
              (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
                  hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
                hN (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
                (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
              (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
              (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) Tb) := by
  obtain ⟨β₀, hβ₀⟩ := exists_beta0_corrRG T hA p
  refine ⟨β₀, ?_⟩
  intro k hk N₁ N₁' _ _ hN hN' h5 h5' ν hνpos hν β ρs hρs hβρ hβle p₁ q hq0 hq D D' hp hp₁ z rc R hz hrc hroot hn hn' θ θ' hθ hθ' hraw Tb hTb
  have hβpos : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβρ)
  have hRU := hβ₀ k hk β hβle p₁ hp hp₁
  obtain ⟨F₁r, Solr, hpA⟩ :=
    tower_pairs_dep_fromTowerG T hm₀ hN h5 D hνpos.le hν hβpos hp hRU
  obtain ⟨F₁r', Solr', hpB⟩ :=
    tower_pairs_dep_fromTowerG T hm₀ hN' h5' D' hνpos.le hν hβpos hp hRU
  obtain ⟨hcψ, hrad, hρc, hum⟩ := tower_radius_fromScaleData T D hp
  obtain ⟨hF₁, hSol, hGd⟩ := hpA z
  obtain ⟨hF₁', hSol', -⟩ := hpB (bc z)
  refine ⟨fun b => F₁r (z, b), fun b => F₁r' (bc z, b), fun b => Solr (z, b),
    fun b => Solr' (bc z, b), hF₁, hF₁', hSol, hSol', ?_⟩
  obtain ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', hE⟩ :=
    gsumCoeff_e1_twoTorus_fromTowerG T hm₀ hk hN hN' h5 h5' ν hνpos hν β ρs hρs hβρ p₁ q hq0 hq D D' hF₁ hF₁' hSol hSol' z hz hrc hroot hn hn' θ θ' hθ hθ' hraw (ρ := p₁) hp hp hp hum (fun i u => hGd θ i u) (by have := T.hL; omega) (e1DomG_isDj_of_eq T hm₀ D rfl rfl) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl) hcψ hrad Tb hTb
  refine ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', ?_⟩
  intro ρI Rσ εU a κ0 KcL Θ₀ Θ₀' SΛ SΛ' XW XW' valI valI' AgΘ AgΘ' AgF AgF' I I' h1 h2 h1' h2'
    cJ cJ' V V' hF hF' hρI hRσ hεU hκ0 hKc hV hV' hρIp
  exact hE I I' h1 h2 h1' h2' hF hF' hρI hRσ hεU hκ0 hKc hV hV' (by linarith [hρc ρI hρIp])

/-- **The energy `E0` on two tori at the tower, for large `β`.**  The corollary of
`e0Coeff_twoTorus_fromTowerG` obtained as `gsumCoeff_e1_twoTorus_fromTowerG_large` from
`gsumCoeff_e1_twoTorus_fromTowerG`: same threshold, same choices, same hypotheses discharged. -/
theorem e0Coeff_twoTorus_fromTowerG_large {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, ∀ {k : ℕ}
    (hk : 1 ≤ k)
    {N₁ N₁' : ℕ}
    [NeZero N₁]
    [NeZero N₁']
    (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁')
    (_h5 : 5 < N₁)
    (_h5' : 5 < N₁')
    (ν : ℝ)
    (_hνpos : 0 < ν)
    (_hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (β ρs : ℝ)
    (_hρs : 0 < ρs)
    (_hβρ : max 1 ρs ≤ β)
    (_hβle : β₀ ≤ β)
    (p₁ q : ℝ)
    (_hq0 : 0 < q)
    (_hq : q ≤ ρs)
    (D : StepScaleDataG T k hk N₁ ν β p₁)
    (D' : StepScaleDataG T k hk N₁' ν β p₁)
    (hp : 0 < p₁)
    (_hp₁ : p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))))
    (z : TA)
    {rc R : ℕ}
    (_hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
    (_hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (_hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (_hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (_hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (θ : physParam N (SA))
    (θ' : physParam N (SB))
    {D₀ : BgData (GA) N}
    {D₀' : BgData (GB) N}
    (_hD₀ : XiCData (GA) (compWeight L 1) ν (k + 1) 1 T.t D₀)
    (_hD₀' : XiCData (GB) (compWeight L 1) ν (k + 1) 1 T.t D₀')
    (_hθD : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D₀)
    (_hθD' : (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) = rawOf D₀')
    (_hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (_hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x),
    ∃ (F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) (F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) (Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)) (Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)),
      (∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α)) ∧
      (∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α)) ∧
      (∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2)) ∧
      (∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2)) ∧
    (∃ (val : FA → FA → ℂ → ΛA → ℂ) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → ℂ → ΛA → ℂ)
        (val' : FB → FB → ℂ → ΛB → ℂ) (𝒴' : Finset (Set (CTorus d L N₁' T.m₁ (k + 1))))
        (Tt' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → ℂ → ΛB → ℂ),
        (∀ Θ ∈ physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β),
          ∃ I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SA).β))
              (2 * T.κdec - 1) Θ (physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β))
              (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
              (physAgΘ (SA)) (AgFDirPair (SA)),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (∀ Θ ∈ physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β),
          ∃ I' : DirectTerms (SB) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              ((SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SB).β))
              (2 * T.κdec - 1) Θ (physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β))
              (physXW (SB) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
              (physAgΘ (SB)) (AgFDirPair (SB)),
            I'.𝒴 = 𝒴' ∧ I'.T = Tt') ∧
        ∀ {ρI Rσ εU a κ0 KcL : ℝ} {Θ₀ : ΛA} {Θ₀' : ΛB} {SΛ : Set ΛA} {SΛ' : Set ΛB}
          {XW : Set (FA × FA)} {XW' : Set (FB × FB)} {valI : FA → FA → ℂ → ΛA → ℂ}
          {valI' : FB → FB → ℂ → ΛB → ℂ} {AgΘ : Set (CTorus d L N₁ T.m₁ (k + 1)) → ΛA → ΛA → Prop}
          {AgΘ' : Set (CTorus d L N₁' T.m₁ (k + 1)) → ΛB → ΛB → Prop}
          {AgF : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → Prop}
          {AgF' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → Prop}
          (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀ SΛ XW valI AgΘ AgF)
          (I' : DirectTerms (SB) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀' SΛ' XW' valI' AgΘ' AgF'),
          I.𝒴 = 𝒴 → I.T = Tt → I'.𝒴 = 𝒴' → I'.T = Tt' →
          ∀ {cJ cJ' : ℂ} {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
            (hF : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I V)
            (hF' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' V')
            (hρI : 0 < ρI) (hRσ : 1 < Rσ) (hεU : 0 ≤ εU) (hκ0 : aEnt d L + 2 ≤ κ0)
            (hKc : K0 d L κ0 ≤ KcL),
            ((θ.1, 0) : physParam N (SA)) ∈ V → ((θ'.1, 0) : physParam N (SB)) ∈ V' →
            ρI ≤ p₁ →
          ∑ y ∈ (SB).blockU (bc z),
              detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D₀' y (Tb.image (σc)) +
            gsumCoeff ((SB).blockSplit 1 hp).μ
              (commonLabels (thickLabels I'.𝒴 I'.dom) hN' (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl))
              (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
                  hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
                hN' (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl)
                (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
              (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB)) (bc z) i')
              (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' p₁ hp (bc z) T.t θ' i' u Φ') (Tb.image (σc)) =
            ∑ y ∈ (SA).blockU z,
              detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D₀ y Tb +
            gsumCoeff ((SA).blockSplit 1 hp).μ
              (commonLabels (thickLabels I.𝒴 I.dom) hN (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
              (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
                  hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
                hN (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
                (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
              (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
              (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) Tb) := by
  obtain ⟨β₀, hβ₀⟩ := exists_beta0_corrRG T hA p
  refine ⟨β₀, ?_⟩
  intro k hk N₁ N₁' _ _ hN hN' h5 h5' ν hνpos hν β ρs hρs hβρ hβle p₁ q hq0 hq D D' hp hp₁ z rc R hz hrc hroot hn hn' θ θ' D₀ D₀' hD₀ hD₀' hθD hθD' hraw Tb hTb
  have hβpos : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβρ)
  have hRU := hβ₀ k hk β hβle p₁ hp hp₁
  obtain ⟨F₁r, Solr, hpA⟩ :=
    tower_pairs_dep_fromTowerG T hm₀ hN h5 D hνpos.le hν hβpos hp hRU
  obtain ⟨F₁r', Solr', hpB⟩ :=
    tower_pairs_dep_fromTowerG T hm₀ hN' h5' D' hνpos.le hν hβpos hp hRU
  obtain ⟨hcψ, hrad, hρc, hum⟩ := tower_radius_fromScaleData T D hp
  obtain ⟨hF₁, hSol, hGd⟩ := hpA z
  obtain ⟨hF₁', hSol', -⟩ := hpB (bc z)
  refine ⟨fun b => F₁r (z, b), fun b => F₁r' (bc z, b), fun b => Solr (z, b),
    fun b => Solr' (bc z, b), hF₁, hF₁', hSol, hSol', ?_⟩
  obtain ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', hE⟩ :=
    e0Coeff_twoTorus_fromTowerG T hm₀ hk hN hN' h5 h5' ν hνpos hν β ρs hρs hβρ p₁ q hq0 hq D D' hF₁ hF₁' hSol hSol' z hz hrc hroot hn hn' θ θ' hD₀ hD₀' hθD hθD' hraw (ρ := p₁) hp hp hp hum (fun i u => hGd θ i u) (by have := T.hL; omega) (e1DomG_isDj_of_eq T hm₀ D rfl rfl) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl) hcψ hrad Tb hTb
  refine ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', ?_⟩
  intro ρI Rσ εU a κ0 KcL Θ₀ Θ₀' SΛ SΛ' XW XW' valI valI' AgΘ AgΘ' AgF AgF' I I' h1 h2 h1' h2'
    cJ cJ' V V' hF hF' hρI hRσ hεU hκ0 hKc hV hV' hρIp
  exact hE I I' h1 h2 h1' h2' hF hF' hρI hRσ hεU hκ0 hKc hV hV' (by linarith [hρc ρI hρIp])

end Pairs


end Balaban.Polymer.TwoTorusStep
