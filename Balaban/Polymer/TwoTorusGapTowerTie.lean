/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyG

/-!
# The energy new terms of the tower step and the determinant clause of the gap scales (blocker 7)

The gap-scale two-torus clause (`resum_gapScale_torus_step_thr36`) is stated for abstract terms
`T = Te + Td + To + Tinh` with the specifications `hTe` (the localized block-energy terms `evDec` at
fixed marks and a fixed hat field), `hTd` (the determinant activities `detActivityBg` of the unit
blocks of the roots of `Zr`, at the cube set `Ycub X`) and `hTo` (the observable coefficient
`obsCoeffParam`).  The tower produces the energy new terms of one zero-class step as the family
`e0 z θ C = dz z θ C + c z θ C` of `e0CoeffFamily_value_fromTowerG` (root `z`, parameter
`θ = (raw datum, source)`, set `C` of cubes of `π_{k+1}`), with `ℰ₀(z) = ∑_C e0 z (rawOf D′, 0) C`.

* `sum_blockU_eq_rootFilter`: the sum over the unit blocks of the block `B(z)` is the sum of the
  specification `hTd` with `Zr = {z}`.
* `towerEnergy_split_fromTowerG`: at every datum `D′` of the chart and every source `g`, the energy
  term of the root `z` at `C` is the determinant term of the specification `hTd` (with `Zr = {z}`,
  block scale `1`, mass `ν`, radius `rho4 d L N T.BG T.κ`, datum `D′`, cube set `C`) plus the mark
  coefficient `c z θ C = gsumCoeff …` (the interpolation coefficient of the label activity `A₀` with
  the corrected marks `e1MarkGParamG`).

So the determinant part of the tower's energy new terms is the specification `hTd`; the mark part is
the coefficient `gsumCoeff …`, not the localized term `evDec` of the specification `hTe` (which
enters the marks `e1MarkGParamG` through `decMarkCorr`).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited Balaban.Inhabited.LevelStep

open Classical in
/-- **The block `B(z)` as the root filter of the determinant clause.**  The sum over the unit
blocks of `B(z)` is the sum, over the roots of `{z}`, of the sums over the unit blocks whose
level-one block is the root: the form of the specification `hTd` with `Zr = {z}`. -/
theorem sum_blockU_eq_rootFilter {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (f : S.U → ℂ) :
    ∑ y ∈ S.blockU z, f y = ∑ zc ∈ ({z} : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))),
      ∑ y ∈ (Finset.univ.filter fun u : unitPts S.G' =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = zc), f y := by
  rw [Finset.sum_singleton]
  rfl

open Classical in
/-- **The energy new terms of the tower step: determinant term of `hTd` plus mark coefficient.**
For the general tower with block scale `1`, beyond the threshold of
`e0CoeffFamily_value_fromTowerG`, at every scale datum: there are decoupling pairs `F₁, Sol`, labels
`Lab₀` and the label activity `A₀` of the energy family such that for every root `z` the energy
family `e0` of the root and its mark coefficient `c` satisfy
* `c θ C = gsumCoeff (S.blockSplit 1 hp).μ (commonLabels Lab₀ …) (A₀ θ) (commonAnchor …)
  (e1MarkGParamG S (F₁ (z, ·)) (Sol (z, ·)) p₁ hp z T.t θ) C` for all `θ, C`;
* at every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)`, every source `g` and every cube set `C`:
  `e0 z (rawOf D′, g) C = ∑_{zc ∈ {z}} ∑_{y : unitBlock1 y = zc} detActivityBg 1 (compWeight L 1)
  1 ν (rho4 d L N T.BG T.κ) D′ y C + c z (rawOf D′, g) C`, the first sum being the right side of
  the specification `hTd` with `Zr = {z}` and the datum `D′`;
* `ℰ₀(z) = ∑_C e0 z (rawOf D′, 0) C` for the step with the datum `D′` of the chart with constant
  field `h₀`. -/
theorem towerEnergy_split_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁)
            (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS))
            (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
            (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)),
      ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∃ c e0 : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
            (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff (S.blockSplit 1 hp).μ
            (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
            (fun i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          (∀ D' : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
            ∀ (g : Fld d L N₁ T.m₁ (k + 1) N) C,
              e0 (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C =
                (∑ zc ∈ ({z} : Finset (RootIdx d L N₁ T.m₁ (k + 1))),
                  ∑ y ∈ (Finset.univ.filter fun u : unitPts S.G' =>
                    unitBlock1 (u : UnitTorus d L N₁ T.m₁ k) = zc),
                    detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D' y C) +
                c (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C) ∧
          (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
            (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
              ∑ C, e0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) := by
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, -, hz⟩ :=
    H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, fun z => ?_⟩
  obtain ⟨-, -, c, hc, -, -, dz, -, -, e0, he, -, hsum, E, hE, hdz, -⟩ := hz z
  refine ⟨c, e0, hc, fun D' hD' g C => ?_, hsum⟩
  rw [he, hdz D' hD' g C, hE D' C]
  congr 1
  subst hϱ
  subst hS
  exact sum_blockU_eq_rootFilter _ z _

end Balaban.Polymer.TwoTorusStep
