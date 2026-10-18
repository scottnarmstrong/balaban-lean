/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerRootFSuppCore
public import Balaban.Polymer.TwoTorusGapTowerTieObs
public import Balaban.Polymer.TwoTorusGapDataThrDet
public import Balaban.Polymer.TwoTorusGapTowerTie

/-!
# The new terms of the tower step on two tori: one set of witnesses (blocker 7)

`towerGapTerms_twoTorus_fromTowerG_core`: at a scale of the general tower with block scale `1`, the
witnesses of `stepIdentity_zeroClass_fibre_fromTowerG_explicitCore` are chosen once for every torus
(as functions of the side `n` and of the scale data), and for these witnesses:
* on every torus: the step identity of the zero class on the fibre `h ≡ h₀`, `e0 = dz + c`, the
  determinant term in the form `hTd` (`Zr = {z}`), and the bounds
  `‖c‖, ‖dz‖ ≤ B e^{-(3/2) κ_dec dExt C}` on `physV`, `‖mObs‖ ≤ B e^{-(3/2) κ_dec dExt C}` on
  `physVq`, with one constant `B` for all tori (the entropy bound `sum_exp_obsRemLab_le` makes the
  constant of the observable coefficient independent of the torus); analyticity, locality and
  support of the three terms;
* on every family of tori: `hob` (the observable coefficient of a site at a support of the quarter box
  that is not wide is the same on `ℓ` and on `can X`), `hdt` (the determinant term of a root) and
  `hen` (the mark coefficient of a root), under the data of the gap scale.

`towerNewTerms_twoTorus_fromTowerG` and `towerEnergyCoef_twoTorus_fromTowerG` are projections of
this theorem.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section Core

set_option hygiene false in
local notation "ST[" n "]" => StepTowerG.step T k hk n ν β p₁
set_option hygiene false in
local notation "SA[" ℓ "]" => StepTowerG.step T k hk (N₁ ℓ) ν β p₁
set_option hygiene false in
local notation "bm[" ℓ "," ℓ' "]" =>
  boxMap ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) ((N₁ ℓ' * L ^ T.m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc[" ℓ "," ℓ' "]" =>
  boxMap (d := d) (N₁ ℓ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) (N₁ ℓ' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "aK" => cellSide L 1 T.m₁ (k + 1)
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) T.m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L 1 T.m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}

open Classical in
/-- **The new terms of the tower step on two tori, on one set of witnesses.**  Beyond the threshold
of `stepIdentity_zeroClass_fibre_fromTowerG_explicitCore` and of the marks (`exists_beta0_e1G`), at
every scale there are the energy families `e0 = dz + c` and the observable coefficients `mObs` of the
tower on every torus of side `n` with scale data (the witnesses of the explicit core), and a constant
`B ≥ 0`, such that
* on every torus: the step identity of the zero class on the fibre `h ≡ h₀`; `e0 = dz + c`; the
  determinant term at a chart datum `D′` is the specification `hTd` with `Zr = {z}`; the bounds
  `‖c z θ C‖, ‖dz z θ C‖ ≤ B e^{-(3/2) κ_dec dExt C}` for `θ ∈ physV` and
  `‖mObs y i θ C‖ ≤ B e^{-(3/2) κ_dec dExt C}` for `θ ∈ physVq`; the analyticity of `c`, `dz` on
  `physV` and of `mObs` on `physVq`; their locality (`c`, `dz`: the restriction to the thickened
  hull of `sitesOf C`; `mObs`: the restriction to `sitesOf C`); their support (the root cube in `C`);
* on every family of tori `ℓ` with scale data: the clauses `hob` (as in
  `towerNewTerms_twoTorus_fromTowerG`), `hdt` (as there) and `hen` (as in
  `towerEnergyCoef_twoTorus_fromTowerG`) for the witnesses of the tori `ℓ`. -/
theorem towerGapTerms_twoTorus_fromTowerG_core {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (ν : ℝ) (_ : 0 < ν) (_ : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ)
        (_ : β₀ ≤ β) (p₁ : ℝ) (_ : 0 < p₁) (_ : p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))))
        (q : ℝ) (_ : 0 < q) (_ : q ≤ 1),
      ∃ (e0 dz c : ∀ (n : ℕ) [NeZero n], L ^ T.m₀ ∣ n → 5 < n → StepScaleDataG T k hk n ν β p₁ →
            RootIdx d L n T.m₁ (k + 1) → physParam N (ST[n]) →
            Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ)
        (mObs : ∀ (n : ℕ) [NeZero n], L ^ T.m₀ ∣ n → 5 < n → StepScaleDataG T k hk n ν β p₁ →
            CTorus d L n T.m₁ (k + 1) → Fin N → physParam N (ST[n]) →
            Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ) (B : ℝ),
        0 ≤ B ∧
        (∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n) (Dn : StepScaleDataG T k hk n ν β p₁),
          (∀ (D' : BgData (ST[n]).G' N) (hDh : ∀ y i, D'.h y i = ((ST[n]).h₀ i : ℂ)),
            XiCData (ST[n]).G' (ST[n]).a (ST[n]).ν (k + 1) 1 T.t D' →
            ∀ g : Fld d L n T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
              ((ST[n]).withDatum D' hDh).TstepC (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)) g =
                Complex.exp (-((ST[n]).β : ℂ) * ((ST[n]).withDatum D' hDh).AnewC -
                  (((ST[n]).withDatum D' hDh).Eppp
                      (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)) : ℂ) *
                    (((ST[n]).withDatum D' hDh).nU : ℂ) +
                  FcompAtC (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)).m₀
                    (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)).Tm (ST[n]).a (ST[n]).ν
                    (Nat.le_succ k) ((ST[n]).withDatum D' hDh).psiKdC g +
                  ∑ z : RootIdx d L n T.m₁ (k + 1), ∑ C,
                    e0 n h3 h5' Dn z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (ST[n]).G'),
                      (0 : CTorus d L n T.m₁ (k + 1) → Fin N → ℂ)) C +
                  ∑ y : CTorus d L n T.m₁ (k + 1), ∑ i : Fin N, g y i *
                    ∑ T', mObs n h3 h5' Dn y i
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (ST[n]).G'), g) T')) ∧
          (∀ z θ C, e0 n h3 h5' Dn z θ C = dz n h3 h5' Dn z θ C + c n h3 h5' Dn z θ C) ∧
          (∀ z (D' : BgData (ST[n]).G' N),
            XiCData (ST[n]).G' (ST[n]).a (ST[n]).ν (k + 1) 1 T.t D' →
            ∀ (g : Fld d L n T.m₁ (k + 1) N) C,
              dz n h3 h5' Dn z (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C =
                ∑ zc ∈ ({z} : Finset (RootIdx d L n T.m₁ (k + 1))),
                  ∑ y ∈ (Finset.univ.filter fun u : unitPts (ST[n]).G' =>
                    unitBlock1 (u : UnitTorus d L n T.m₁ k) = zc),
                    detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D' y C) ∧
          ∀ C : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            (∀ z, (∀ θ ∈ physV (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t,
                ‖c n h3 h5' Dn z θ C‖ ≤ B * Real.exp (-(3 / 2 * T.κdec) * dExt C) ∧
                ‖dz n h3 h5' Dn z θ C‖ ≤ B * Real.exp (-(3 / 2 * T.κdec) * dExt C)) ∧
              AnalyticOnNhd ℂ (fun θ => c n h3 h5' Dn z θ C)
                (physV (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t) ∧
              AnalyticOnNhd ℂ (fun θ => dz n h3 h5' Dn z θ C)
                (physV (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t) ∧
              (∀ θ ∈ physV (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t,
                ∀ θ' ∈ physV (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t,
                physRestrict (N := N) (thickSet (ST[n]).G' (Yhat Set.univ (sitesOf C)))
                    (physIncl N (ST[n]) θ) =
                  physRestrict (thickSet (ST[n]).G' (Yhat Set.univ (sitesOf C)))
                    (physIncl N (ST[n]) θ') →
                c n h3 h5' Dn z θ C = c n h3 h5' Dn z θ' C ∧
                  dz n h3 h5' Dn z θ C = dz n h3 h5' Dn z θ' C) ∧
              (∀ θ, c n h3 h5' Dn z θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C) ∧
              (∀ θ, dz n h3 h5' Dn z θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C)) ∧
            ∀ y i, (∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
                ‖mObs n h3 h5' Dn y i θ C‖ ≤ B * Real.exp (-(3 / 2 * T.κdec) * dExt C)) ∧
              AnalyticOnNhd ℂ (fun θ => mObs n h3 h5' Dn y i θ C)
                (physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q) ∧
              (∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
                ∀ θ' ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
                physRestrict (N := N) (sitesOf C) (physIncl N (ST[n]) θ) =
                  physRestrict (sitesOf C) (physIncl N (ST[n]) θ') →
                mObs n h3 h5' Dn y i θ C = mObs n h3 h5' Dn y i θ' C) ∧
              (∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q, mObs n h3 h5' Dn y i θ C ≠ 0 →
                rootCube (m₀ := 1) (blockIndex y) ∈ C)) ∧
        ∀ {ι : Type*} (N₁ : ι → ℕ) [∀ ℓ, NeZero (N₁ ℓ)] (h3N : ∀ ℓ, L ^ T.m₀ ∣ N₁ ℓ)
          (h5 : ∀ ℓ, 5 < N₁ ℓ) (D : ∀ ℓ, StepScaleDataG T k hk (N₁ ℓ) ν β p₁),
        (∀ {G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
          (_ : ∀ ℓ, 26 ≤ K ℓ)
          (_ : ∀ ℓ, (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) = aK * K ℓ)
          (_ : ∀ ℓ, L ≤ (K ℓ - 26) / 25 + 1)
          (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
          (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
          (_ : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
            X = Y.image (fun b μ => (b μ).valMinAbs))
          (_ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
          (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ))
          (_ : ∀ ℓ X, X ∈ P ℓ → sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
          (xs : ∀ ℓ, CTorus d L (N₁ ℓ) T.m₁ (k + 1)) (iy : Fin N)
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → xs (can X) = bm[ℓ, can X] (xs ℓ))
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
            ∀ x ∈ LocalCover.nbhd 1 (xs ℓ), ∀ y ∈ LocalCover.nbhd 1 (xs ℓ) ∪ sitesOf (Ycub ℓ X),
            ∀ μ, |(x μ - y μ).valMinAbs| ≤ Ds)
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X →
            ∀ x ∈ LocalCover.nbhd 1 (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
            |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
          {Dset : Set G} (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
          (_ : ∀ ℓ, ∀ g ∈ Dset, θ ℓ g ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q)
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ LocalCover.nbhd 1 (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
            RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1))
                ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) w}
              (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))))
                ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N))
              (symRaw (Equiv.addRight
                (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1)))))
                ((θ (can X) g).1 : RawData d L (N₁ (can X) * L ^ T.m₁) (k + 1) N)))
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ LocalCover.nbhd 1 (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
            ∀ x, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1))
              (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))) →
            ∀ i, (θ (can X) g).2 (bm[ℓ, can X] (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) *
              L ^ (k + 1)))) - fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1))))
              i = (θ ℓ g).2 x i),
          ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset,
            mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (θ ℓ g) (Ycub ℓ X) =
              mObs (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (xs (can X)) iy
                (θ (can X) g) (Ycub (can X) X)) ∧
        (∀ {G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
          (_ : ∀ ℓ, 36 ≤ K ℓ) {Dc : ι → ℕ} (_ : ∀ ℓ, Dc ℓ ≤ (K ℓ - 36) / 25)
          (_ : ∀ ℓ, (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) = aK * K ℓ)
          (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
          (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
          (_ : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
            X = Y.image (fun b μ => (b μ).valMinAbs))
          (_ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
          (zr : ∀ ℓ, RootIdx d L (N₁ ℓ) T.m₁ (k + 1))
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → zr (can X) = bc[ℓ, can X] (zr ℓ))
          (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ))
          (_ : ∀ ℓ X, X ∈ P ℓ → sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
          {Dset : Set G} (Dat : ∀ ℓ, G → BgData (SA[ℓ]).G' N)
          (_ : ∀ ℓ, ∀ g ∈ Dset, XiCData (SA[ℓ]).G' (compWeight L 1) ν (k + 1) 1 T.t (Dat ℓ g))
          (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
          (_ : ∀ ℓ, ∀ g ∈ Dset,
            ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N) = rawOf (Dat ℓ g))
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK),
            ∀ y ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
            |(x μ - y μ).valMinAbs| ≤ ((aK * (Dc ℓ + 1) - 1 : ℕ) : ℤ))
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
            |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤
                (((aK * (Dc ℓ + 1) - 1) + ((aK * (Dc ℓ + 1) - 1) + 1) / 4 : ℕ) : ℤ)) →
            RawBoxAgree {w | InBox d ((aK * (Dc ℓ + 1) - 1) +
                ((aK * (Dc ℓ + 1) - 1) + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
                ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) w}
              (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))))
                (rawOf (Dat ℓ g)))
              (symRaw (Equiv.addRight
                (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1)))))
                (rawOf (Dat (can X) g)))),
          ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset,
            dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) =
              dz (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (zr (can X)) (θ (can X) g)
                (Ycub (can X) X)) ∧
        ∀ {G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
          (_ : ∀ ℓ, 36 ≤ K ℓ) {Dc : ι → ℕ} (_ : ∀ ℓ, Dc ℓ ≤ (K ℓ - 36) / 25)
          (_ : ∀ ℓ, (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) = aK * K ℓ)
          (_ : ∀ ℓ, L ≤ (K ℓ - 26) / 25 + 1)
          (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
          (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
          (_ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
          (zr : ∀ ℓ, RootIdx d L (N₁ ℓ) T.m₁ (k + 1))
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → zr (can X) = bc[ℓ, can X] (zr ℓ))
          (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ))
          (_ : ∀ ℓ X, sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
          {Dset : Set G} (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
          (_ : ∀ ℓ, ∀ g ∈ Dset, θ ℓ g ∈ physV (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t)
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK),
            ∀ y ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
            |(x μ - y μ).valMinAbs| ≤ ((aK * (Dc ℓ + 1) - 1 : ℕ) : ℤ))
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
            |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
          (_ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤
                (((aK * (Dc ℓ + 1) - 1) + ((aK * (Dc ℓ + 1) - 1) + 1) / 4 : ℕ) : ℤ)) →
            RawBoxAgree {w | InBox d ((aK * (Dc ℓ + 1) - 1) +
                ((aK * (Dc ℓ + 1) - 1) + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
                ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) w}
              (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))))
                ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N))
              (symRaw (Equiv.addRight
                (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1)))))
                ((θ (can X) g).1 : RawData d L (N₁ (can X) * L ^ T.m₁) (k + 1) N))),
          ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset,
            c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) =
              c (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (zr (can X)) (θ (can X) g)
                (Ycub (can X) X) := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    towerGapTerms_twoTorus_fromTowerG_core_supp T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨e0, dz, c, mObs, B, hB, hT, -, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  exact ⟨e0, dz, c, mObs, B, hB, hT, hF⟩

end Core

end Balaban.Polymer.TwoTorusStep
