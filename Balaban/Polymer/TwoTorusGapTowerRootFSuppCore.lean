/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerCloseAux
public import Balaban.Polymer.TwoTorusGapTowerTieObs
public import Balaban.Polymer.TwoTorusGapDataThrDet
public import Balaban.Polymer.TwoTorusGapTowerTie

/-!
# The new terms of the tower step on two tori, with the polymer support of the observable (blocker 7)

`towerGapTerms_twoTorus_fromTowerG_core_supp`: `towerGapTerms_twoTorus_fromTowerG_core` with the
further clause for the same witnesses `mObs`: at `θ ∈ physVq`, `mObs y i θ T' ≠ 0` implies that the
sites of the cube set `T'` form a domain `𝒟_{k+1}` (`IsPolyDom 1 (k + 1) (sitesOf T')`: a nonempty,
connected union of `π'`-cubes), as in the explicit core
`stepIdentity_zeroClass_fibre_fromTowerG_explicitCore`.  The theorem
`towerGapTerms_twoTorus_fromTowerG_core` (in `TwoTorusGapTowerCloseCore.lean`) is its projection.
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
/-- **The new terms of the tower step on two tori, on one set of witnesses, with the support of the
observable coefficients.**  The statement of `towerGapTerms_twoTorus_fromTowerG_core`
with the clause `hsupp`, and the separate bound of the observable coefficients
`‖mObs y i θ C‖ ≤ Co e^{-(3/2) κ_dec dExt C}` with the explicit constant `Co` (the left side of
`obsRate_le_birthScale`), next to the lumped `B`.  Original description:
  Beyond the threshold
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
theorem towerGapTerms_twoTorus_fromTowerG_core_supp_obs {d L N : ℕ} [NeZero L] {κmin : ℝ}
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
              Set.univ) → ℂ) (B Co : ℝ),
        0 ≤ B ∧
        Co = (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t /
            lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * p₁ / obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
          ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 *
              (K0 d L T.κ0 + 1)) ∧
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
        (∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n) (Dn : StepScaleDataG T k hk n ν β p₁)
            (y : CTorus d L n T.m₁ (k + 1)) (i : Fin N),
          ∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
            ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
              mObs n h3 h5' Dn y i θ T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T')) ∧
        (∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n) (Dn : StepScaleDataG T k hk n ν β p₁)
            (y : CTorus d L n T.m₁ (k + 1)) (i : Fin N)
            (C : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ)),
          ∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
            ‖mObs n h3 h5' Dn y i θ C‖ ≤ Co * Real.exp (-(3 / 2 * T.κdec) * dExt C)) ∧
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
    stepIdentity_zeroClass_fibre_fromTowerG_explicitCore T hm₀ hhull hA p hCR hs0 hs
  obtain ⟨β₁, hβ₁, hRm, -⟩ := exists_beta0_e1G T hm₀ hA p β₀
  refine ⟨β₁, CE, CF, (le_max_left _ _).trans hβ₁, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  have hβ0 : β₀ ≤ β := ((le_max_right _ _).trans hβ₁).trans hβ
  have HH := fun (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n)
      (Dn : StepScaleDataG T k hk n ν β p₁) =>
    H k hk n h3 h5' ν hν0 hν β hβ0 p₁ hp₁ q hq0 hq1 Dn (ϱ := rhoSepG d L T.m₁) rfl
      (T.step k hk n ν β p₁) rfl hp0
  choose F₁ Sol Lb hLb Lab₀ εH A₀ e0 Lbo hLbo Labo εHo hεHo Ao mObs hα hroot hamp hlab hsrcF
    hsite hid using HH
  choose hP hsp hdp hF c hc1 hc2 hcv dz hd1 hd2 he0 he2 hev hEdet using hroot
  have hdzAll : ∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n)
      (Dn : StepScaleDataG T k hk n ν β p₁) z (D' : BgData (ST[n]).G' N),
      XiCData (ST[n]).G' (ST[n]).a (ST[n]).ν (k + 1) 1 T.t D' →
      ∀ (g : Fld d L n T.m₁ (k + 1) N) C,
        dz n h3 h5' Dn z (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C =
          ∑ zc ∈ ({z} : Finset (RootIdx d L n T.m₁ (k + 1))),
            ∑ y ∈ (Finset.univ.filter fun u : unitPts (ST[n]).G' =>
              unitBlock1 (u : UnitTorus d L n T.m₁ k) = zc),
              detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D' y C := by
    intro n _ h3 h5' Dn z D' hD' g C
    obtain ⟨E, hEt, hEd, -⟩ := hEdet n h3 h5' Dn z
    rw [hEd D' hD' g C, hEt D' C]
    exact sum_blockU_eq_rootFilter _ z _
  -- the constants of the bounds
  obtain ⟨Cdz, hCdz⟩ : ∃ x : ℝ, x = (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) := ⟨_, rfl⟩
  obtain ⟨Co, hCo⟩ : ∃ x : ℝ, x =
      (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t
          (β * (L : ℝ) ^ (k * (d - 2)))) *
        (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * p₁ /
          (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
        (((N * L ^ (d * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
        ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
        Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
      CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
          (2 * T.κdec - 1) T.κ0 T.κ' *
        (8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 *
          (K0 d L T.κ0 + 1)) := ⟨_, rfl⟩
  have hκ'ge : 3 / 2 * T.κdec ≤ T.κ' := by
    have := T.κ'_eq; have := T.κ0_nonneg; linarith
  have hB0 : 0 ≤ |K0 d L T.κ0| + |Cdz| + |Co| := by positivity
  have hobs : ∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n)
      (Dn : StepScaleDataG T k hk n ν β p₁) (y : CTorus d L n T.m₁ (k + 1)) (i : Fin N)
      (C : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ)),
      ∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
        ‖mObs n h3 h5' Dn y i θ C‖ ≤ Co * Real.exp (-(3 / 2 * T.κdec) * dExt C) := by
    intro n _ h3 h5' Dn y i C θ hθ
    have hN1 : L ^ 1 ∣ n := by rwa [hm₀] at h3
    have hcov1 : LevelCoversG d L N n T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
        (lvTopG d L n T.m₁ k (rhoSepG d L T.m₁)) (lvLowG d L n T.m₁ k (rhoSepG d L T.m₁)) 1 := by
      have h := Dn.covers
      rw [hm₀] at h
      exact h
    have hdj : ∀ Y ∈ obsDomains (ST[n]) (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
        IsDj 1 (k + 1) Y :=
      obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ T.hd (hcov1.2 (y, i)).1
        (hcov1.2 (y, i)).2.2.1
    obtain ⟨-, -, -, -, -, -, -, -, -, hfam⟩ := hsite n h3 h5' Dn y i hdj
    have h1 := (hfam C).2.1 θ hθ
    rw [T.obsFamilyRate_eq] at h1
    have hbx := rootCube_mem_obsRowLabel_obsDomains (ST[n]) T.hd hN1 y (hcov1.2 (y, i)).1
      (hcov1.2 (y, i)).2.1 (hcov1.2 (y, i)).2.2.1 (hcov1.2 (y, i)).2.2.2.2
    have ha8 : 0 ≤ 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
        (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (cK2'_pos_general T.fam_nonneg).le T.t_pos.le)) (sq_nonneg _)
    have hsum := sum_exp_obsRemLab_le hN1 ((Labo n h3 h5' Dn).sum (Labo n h3 h5' Dn)) _ hdj _ hbx
      T.κ0_ent ha8
    have hCP := CPE_nonneg' (d := d) (L := L)
      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ'
    have hp1 : (ST[n]).p₁ = p₁ := rfl
    rw [hp1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    have h2 := mul_le_mul_of_nonneg_left hsum hCP
    rw [hCo]
    exact add_le_add (le_refl _) h2
  have hCoB : Co ≤ |K0 d L T.κ0| + |Cdz| + |Co| := by
    linarith only [le_abs_self Co, abs_nonneg Cdz, abs_nonneg (K0 d L T.κ0)]
  have hCoeq : Co = (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t /
            lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * p₁ / obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
          ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 *
              (K0 d L T.κ0 + 1)) := by
    rw [hCo, hm₀]
  refine ⟨e0, dz, c, mObs, |K0 d L T.κ0| + |Cdz| + |Co|, Co, hB0, hCoeq, ?_, ?_, hobs, ?_⟩
  · intro n _ h3 h5' Dn
    have hN1 : L ^ 1 ∣ n := by rwa [hm₀] at h3
    have hcov1 : LevelCoversG d L N n T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
        (lvTopG d L n T.m₁ k (rhoSepG d L T.m₁)) (lvLowG d L n T.m₁ k (rhoSepG d L T.m₁)) 1 := by
      have h := Dn.covers
      rw [hm₀] at h
      exact h
    refine ⟨hid n h3 h5' Dn, he0 n h3 h5' Dn, hdzAll n h3 h5' Dn,
      fun C => ⟨fun z => ⟨fun θ hθ => ⟨?_, ?_⟩, (hc2 n h3 h5' Dn z C).1, (hd2 n h3 h5' Dn z C).1,
        fun θ hθ θ' hθ' hr => ⟨(hc2 n h3 h5' Dn z C).2.1 θ hθ θ' hθ' hr,
          (hd2 n h3 h5' Dn z C).2.1 θ hθ θ' hθ' hr⟩,
        fun θ hne => ((hc2 n h3 h5' Dn z C).2.2.2.2 θ hne).1,
        fun θ hne => ((hd2 n h3 h5' Dn z C).2.2.2 θ hne).1⟩, fun y i => ?_⟩⟩
    · have hx : Real.exp (-T.κ' * dExt C) ≤ Real.exp (-(3 / 2 * T.κdec) * dExt C) :=
        Real.exp_le_exp.2 (by
          have h0 := mul_le_mul_of_nonneg_right hκ'ge (dExt_nonneg C)
          linarith only [h0])
      refine ((hc2 n h3 h5' Dn z C).2.2.2.1 θ hθ).trans ?_
      exact mul_le_mul (by linarith only [le_abs_self (K0 d L T.κ0), abs_nonneg Cdz, abs_nonneg Co]) hx
        (Real.exp_pos _).le hB0
    · have hx : Real.exp (-T.κ' * dExt C) ≤ Real.exp (-(3 / 2 * T.κdec) * dExt C) :=
        Real.exp_le_exp.2 (by
          have h0 := mul_le_mul_of_nonneg_right hκ'ge (dExt_nonneg C)
          linarith only [h0])
      have h1 := (hd2 n h3 h5' Dn z C).2.2.1 θ hθ
      rw [← hCdz] at h1
      refine h1.trans ?_
      exact mul_le_mul (by linarith only [le_abs_self Cdz, abs_nonneg (K0 d L T.κ0), abs_nonneg Co]) hx
        (Real.exp_pos _).le hB0
    · have hdj : ∀ Y ∈ obsDomains (ST[n]) (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
          IsDj 1 (k + 1) Y :=
        obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ T.hd (hcov1.2 (y, i)).1
          (hcov1.2 (y, i)).2.2.1
      obtain ⟨-, -, -, -, -, -, -, -, -, hfam⟩ := hsite n h3 h5' Dn y i hdj
      refine ⟨fun θ hθ => ?_, (hfam C).1, (hfam C).2.2.2.2,
        fun θ hθ hne => ((hfam C).2.2.1 θ hθ hne).1⟩
      have h1 := (hfam C).2.1 θ hθ
      rw [T.obsFamilyRate_eq] at h1
      have hbx := rootCube_mem_obsRowLabel_obsDomains (ST[n]) T.hd hN1 y (hcov1.2 (y, i)).1
        (hcov1.2 (y, i)).2.1 (hcov1.2 (y, i)).2.2.1 (hcov1.2 (y, i)).2.2.2.2
      have ha8 : 0 ≤ 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg (cK2'_pos_general T.fam_nonneg).le T.t_pos.le)) (sq_nonneg _)
      have hsum := sum_exp_obsRemLab_le hN1 ((Labo n h3 h5' Dn).sum (Labo n h3 h5' Dn)) _ hdj _ hbx
        T.κ0_ent ha8
      have hCP := CPE_nonneg' (d := d) (L := L)
        ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ'
      have hp1 : (ST[n]).p₁ = p₁ := rfl
      rw [hp1] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      have h2 := mul_le_mul_of_nonneg_left hsum hCP
      have h3' : Co ≤ |K0 d L T.κ0| + |Cdz| + |Co| := by
        linarith only [le_abs_self Co, abs_nonneg Cdz, abs_nonneg (K0 d L T.κ0)]
      refine le_trans ?_ h3'
      rw [hCo]
      exact add_le_add (le_refl _) h2
  · intro n _ h3 h5' Dn y i θ hθ T' hne
    have hcov1 : LevelCoversG d L N n T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
        (lvTopG d L n T.m₁ k (rhoSepG d L T.m₁)) (lvLowG d L n T.m₁ k (rhoSepG d L T.m₁)) 1 := by
      have h := Dn.covers
      rw [hm₀] at h
      exact h
    have hdj : ∀ Y ∈ obsDomains (ST[n]) (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
        IsDj 1 (k + 1) Y :=
      obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ T.hd (hcov1.2 (y, i)).1
        (hcov1.2 (y, i)).2.2.1
    obtain ⟨-, -, -, -, -, -, -, -, -, hfam⟩ := hsite n h3 h5' Dn y i hdj
    exact ((hfam T').2.2.1 θ hθ hne).2
  · clear hCo hCdz
    intro ι N₁ _ h3N h5 D
    have hN : ∀ ℓ, L ^ 1 ∣ N₁ ℓ := fun ℓ => by have := h3N ℓ; rwa [hm₀] at this
    have hcov1 : ∀ ℓ, LevelCoversG d L N (N₁ ℓ) T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
        (lvTopG d L (N₁ ℓ) T.m₁ k (rhoSepG d L T.m₁))
        (lvLowG d L (N₁ ℓ) T.m₁ k (rhoSepG d L T.m₁)) 1 := fun ℓ => by
      have h := (D ℓ).covers
      rw [hm₀] at h
      exact h
    have hbU : ∀ ℓ, (SA[ℓ]).betaU = β * (L : ℝ) ^ (k * (d - 2)) := fun ℓ =>
      hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
    refine ⟨?_, ?_, ?_⟩
    · -- `hob`: the observable coefficient of a site
      intro G K _ hK26 hside hKL P Q can Wd hP hQ hcanK Ycub hYs xs iy hxsb hsp hqS Dset θ hθV
        hraw hsrc ℓ₀ X hX hQX hW g hg
      choose 𝒴v ys hys h𝒴v F₂ Sol₂ hF₂ hSol₂ hAx using
        fun ℓ => hlab (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)
      choose F₃ Sol₃ Ev₃ hF₃ hSol₃ hEv₃ hanEv₃ hAs using
        fun ℓ => hsrcF (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)
      have hdj : ∀ ℓ, ∀ Y ∈ obsDomains (SA[ℓ]) (LocalCover.nbhdF 1 (xs ℓ)) 1 k
          (LocalCover.fam 1 (xs ℓ)), IsDj 1 (k + 1) Y := fun ℓ =>
        obsDomains_isDj (X₁f := LocalCover.nbhdF 1 (xs ℓ)) _ T.hd ((hcov1 ℓ).2 (xs ℓ, iy)).1
          ((hcov1 ℓ).2 (xs ℓ, iy)).2.2.1
      choose hR hR1 hRθ Ev hEvx ha hd hb hmk hfam using
        fun ℓ => hsite (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (hdj ℓ)
      choose Fy Soly hFy hSoly hEvF using hEvx
      simp only [hbU] at hAx hEv₃ hEvF
      have hrad := (D ℓ₀).fl_radius
      rw [hbU ℓ₀] at hrad
      have hcψ0 := (D ℓ₀).cψ_pos
      have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
        rw [div_le_iff₀ hcψ0]
        have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ :=
          mul_pos (D ℓ₀).r_pos hp0
        nlinarith [(D ℓ₀).ray_margin]
      exact hob_of_obsLabelFormulas (K := K) T.hN hk ν β p₁ T.δ (fun ℓ => (D ℓ).core)
        T.large_block T.dom_margin T.coer_margin T.δc_small (by have := T.hd; omega)
        (by have := T.hL; omega) le_rfl (by have := T.m₁_four; omega) hN hK26 hside hKL P Q can Wd
        hP hQ hcanK Ycub hYs xs iy hxsb hsp hqS _ hcψ0 hq hrad hFy hSoly hEvF
        (fun ℓ Y _ => hd ℓ Y) hdj θ (fun ℓ g hg => (hθV ℓ g hg).1.1) (fun _ => hp0)
        (fun ℓ => Labo (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)) ys hys
        (fun ℓ => Ao (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)) (fun _ => T.κ0_ent)
        (fun ℓ => (hεHo (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).le) (fun _ => le_refl _) _ (hR ℓ₀)
        (ball (0 : ℂ) (3 / 2))
        (fun ℓ g X => mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (θ ℓ g) (Ycub ℓ X))
        (fun ℓ g X _ _ => hmk ℓ (θ ℓ g) (Ycub ℓ X)) hraw (Nat.lt_of_lt_of_le two_pos T.hN) h𝒴v
        hF₂ hSol₂ hθV hAx hF₃ hSol₃ hEv₃ hanEv₃ hAs hsrc ℓ₀ X hX hQX hW g hg
    · -- `hdt`: the determinant term of a root
      intro G K _ hK36 Dc hDc hside P Q can Wd hP hQ hcanK zr hzr Ycub hYs Dset Dat hDat θ hθD hsp
        hq hraw
      refine hdt_of_detSum_thr36 (K := K) (Dc := Dc) T.hN hk ν β p₁ T.δ (by have := T.hd; omega)
        (by have := T.hL; omega) le_rfl (by have := T.m₁_four; omega) hN (fun ℓ => (D ℓ).core)
        (δc_nonneg_of_flCore T.hd T.t_pos (Classical.choice T.core) T.dom_margin) T.large_block
        T.δc_small T.dom_margin T.coer_margin (fun _ => hatConn_lvTopG T.hL) hDat hK36 hDc hside
        P Q can Wd hP hQ hcanK (fun ℓ => {zr ℓ}) Ycub hYs (fun ℓ X hX hQX => ?_)
        (fun ℓ g X => dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X)) (fun ℓ g X _ hg => ?_)
        (fun ℓ X g hX hQX hW hg zc hzc => by
          obtain rfl := Finset.mem_singleton.1 hzc; exact hsp ℓ X g hX hQX hW hg)
        (fun ℓ X g hX hQX hW hg zc hzc => by
          obtain rfl := Finset.mem_singleton.1 hzc; exact hq ℓ X g hX hQX hW hg)
        (fun ℓ X g hX hQX hW hg zc hzc => by
          obtain rfl := Finset.mem_singleton.1 hzc; exact hraw ℓ X g hX hQX hW hg)
      · rw [Finset.image_singleton, hzr ℓ X hX hQX]
      · have hθe : θ ℓ g = (⟨rawOf (Dat ℓ g), rawOf_mem_rawSub _⟩, (θ ℓ g).2) :=
          Prod.ext (Subtype.ext (hθD ℓ g hg)) rfl
        rw [hθe]
        exact hdzAll (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (Dat ℓ g) (hDat ℓ g hg) _ _
    · -- `hen`: the mark coefficient of a root
      intro G K _ hK36 Dc hDc hside hKL P Q can Wd hQ hcanK zr hzr Ycub hYs Dset θ hθV hspX hqX
        hraw ℓ X hX hQX hW g hg
      have hm1 : 1 ≤ T.m₁ := by have := T.m₁_four; omega
      have hd : 0 < d := by have := T.hd; omega
      have hrad := (D ℓ).fl_radius
      rw [hbU ℓ] at hrad
      have hcψ0 := (D ℓ).cψ_pos
      have hq4 : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
        rw [div_le_iff₀ hcψ0]
        have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ :=
          mul_pos (D ℓ).r_pos hp0
        nlinarith [(D ℓ).ray_margin]
      have hρc : 2 * p₁ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
        rw [div_le_iff₀ hcψ0] at hq4
        linarith
      have hRU := hRm k hk β hβ p₁ hp0 hp₁
      have hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k 1 T.κ p₁
          ((((SA[ℓ]).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
        intro u hu
        have h := e1_rad_ltG (N₁ := N₁ ℓ) (ϱ := rhoSepG d L T.m₁) (ν := ν) T hk
          (by linarith [(le_max_left _ _).trans hβ₁]) hp0 hRU (u := u) (by linarith)
        rw [norm_zero, add_zero] at h
        exact h
      have hzr' := hzr ℓ X hX hQX
      rw [hzr']
      obtain ⟨E0, -, -, val, I0, hFd, hεU, hrest⟩ := hEdet (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ)
      obtain ⟨hLbeq, hεeq, hLab, hrest⟩ := hrest
      have hAeq := hrest.1
      obtain ⟨h𝒴, F₂, Sol₂, hF₂, hSol₂, hTt⟩ := hrest.2
      obtain ⟨E0', -, -, val', I0', hFd', hεU', hrest'⟩ :=
        hEdet (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (bc[ℓ, can X] (zr ℓ))
      obtain ⟨hLbeq', hεeq', hLab', hrest'⟩ := hrest'
      have hAeq' := hrest'.1
      obtain ⟨h𝒴', F₂', Sol₂', hF₂', hSol₂', hTt'⟩ := hrest'.2
      rw [hc1 (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ),
        hc1 (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) _,
        gsumCoeff_commonLabels_congr _ hLbeq hLab _ _ _ _ _ hεeq hAeq,
        gsumCoeff_commonLabels_congr _ hLbeq' hLab' _ _ _ _ _ hεeq' hAeq']
      symm
      have hapos : 0 < aK := cellSide_pos (L := L) 1 T.m₁ (k + 1)
      have hcanK' := hcanK ℓ X hX hQX
      have h4 : 4 * L ^ (k + 1) ≤ aK := by
        have hL2 := T.hL
        have h4' : 4 ≤ L ^ (1 + T.m₁) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ L ^ 2 := Nat.pow_le_pow_left (by omega) 2
            _ ≤ L ^ (1 + T.m₁) := Nat.pow_le_pow_right (by omega) (by omega)
        have : aK = L ^ (k + 1) * L ^ (1 + T.m₁) := by
          unfold cellSide; rw [← pow_add]; congr 1; omega
        rw [this]
        exact Nat.mul_le_mul_left _ h4' |>.trans_eq' (by ring)
      have hDs1 : (aK * (Dc ℓ + 1) - 1) + 1 ≤ aK * (Dc ℓ + 1) := by
        have : 1 ≤ aK * (Dc ℓ + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
      obtain ⟨hsl, hsl'⟩ := compact36_slack (K := K ℓ) (K' := K (can X)) (Lk := L ^ (k + 1))
        (Dc := Dc ℓ) (Ds := aK * (Dc ℓ + 1) - 1) hcanK' h4 (pow_pos (by have := T.hL; omega) _)
        (hK36 ℓ) (hDc ℓ) hDs1
      obtain ⟨-, -, hqn⟩ := compact_site_margins (K := K ℓ) (K' := K (can X)) (cs := aK)
        (Dc := Dc ℓ) (Ds := aK * (Dc ℓ + 1) - 1) (q := aK * (K ℓ / 4 + 1))
        (by have := hK36 ℓ; omega) hcanK' hapos (by have := hDc ℓ; omega) hDs1 (Nat.le_add_right _ _)
      have hlab := towerLab_margin (hK36 ℓ) (hDc ℓ) (hKL ℓ) hapos h4 rfl
      have hlab' := towerLab_margin (K := K (can X)) (Dc := Dc ℓ) (hK36 (can X))
        (by have := hDc ℓ; omega) (hKL (can X)) hapos h4 rfl
      rw [← hside ℓ] at hsl hqn hlab
      rw [← hside (can X)] at hsl' hlab'
      simp only [hbU ℓ] at hTt
      simp only [hbU (can X)] at hTt'
      exact gsumCoeff_e1_cellSites T.hN hk ν β p₁ T.δ (D ℓ).core (D (can X)).core (SA[ℓ]).hG'
        (SA[can X]).hG' T.large_block T.dom_margin T.coer_margin T.δc_small
        (fun b => (hsp (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) b).1)
        (fun b => (hsp (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) _ b).1)
        (fun b => (hsp (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) b).2)
        (fun b => (hsp (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) _ b).2) hd (hN ℓ)
        (hN (can X)) hm1 (by have := hK36 ℓ; omega) hcanK' (hside ℓ) (hside (can X)) (Dc := Dc ℓ)
        (by have := hDc ℓ; omega) rfl (X := (↑X : Set (Fin d → ℤ)))
        (fun c hc μ => (hQ ℓ X).1 hQX c hc μ) (Ycub ℓ X) (Ycub (can X) X)
        (hYs ℓ X) (hYs (can X) X) (zr ℓ) (hspX ℓ X g hX hQX hW hg) (hqX ℓ X g hX hQX hW hg) hqn hsl
        hsl' hlab hlab' (θ ℓ g) (θ (can X) g) (hθV ℓ g hg).1 (hθV (can X) g hg).1
        (hraw ℓ X g hX hQX hW hg) hp0 hp0 hp0 hum (hdp (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g))
        (by have := T.hL; omega)
        (e1DomG_isDj_of_eq T hm₀ (D ℓ) rfl rfl) (e1DomG_isDj_of_eq T hm₀ (D (can X)) rfl rfl) I0 I0'
        hFd hFd' hp0 le_rfl hεU T.κ0_two T.marks_K0_le
        (fst_zero_mem_physVq (SA[ℓ]) (hθV ℓ g hg) one_pos)
        (fst_zero_mem_physVq (SA[can X]) (hθV (can X) g hg) one_pos) _ hcψ0.le hρc hrad hF₂ hF₂'
        hSol₂ hSol₂' h𝒴 h𝒴'
        (fun Y x w σ Θ => (hTt Y x w σ Θ).trans (congrArg (fun t => -(((SA[ℓ]).β : ℝ) : ℂ) * t)
          (rayTerm_evTerm_eq_evDec (SA[ℓ]).hG' _ F₂ Sol₂ Y w.1 x.1 σ Θ)))
        (fun Y x w σ Θ => (hTt' Y x w σ Θ).trans
          (congrArg (fun t => -(((SA[can X]).β : ℝ) : ℂ) * t)
            (rayTerm_evTerm_eq_evDec (SA[can X]).hG' _ F₂' Sol₂' Y w.1 x.1 σ Θ)))

/-- `towerGapTerms_twoTorus_fromTowerG_core_supp`: the projection of
`towerGapTerms_twoTorus_fromTowerG_core_supp_obs` forgetting the separate observable constant. -/
theorem towerGapTerms_twoTorus_fromTowerG_core_supp {d L N : ℕ} [NeZero L] {κmin : ℝ}
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
        (∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n) (Dn : StepScaleDataG T k hk n ν β p₁)
            (y : CTorus d L n T.m₁ (k + 1)) (i : Fin N),
          ∀ θ ∈ physVq (ST[n]) (ST[n]).a₁ (ST[n]).ν T.t q,
            ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
              mObs n h3 h5' Dn y i θ T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T')) ∧
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
  obtain ⟨β₀, CE, CF, h0, hCE, hCF, H⟩ :=
    towerGapTerms_twoTorus_fromTowerG_core_supp_obs T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h0, hCE, hCF, fun k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1 => ?_⟩
  obtain ⟨e0, dz, c, mObs, B, -, hB, -, hA', hS, -, hι⟩ :=
    H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  exact ⟨e0, dz, c, mObs, B, hB, hA', hS, hι⟩

end Core

end Balaban.Polymer.TwoTorusStep
