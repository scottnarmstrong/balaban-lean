/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerTieObs
public import Balaban.Polymer.TwoTorusGapDataThrDet
public import Balaban.Polymer.TwoTorusGapTowerTie
public import Balaban.Inhabited.StepIdentityFibreFamiliesCore
public import Balaban.Polymer.TwoTorusGapTowerCloseCore

/-!
# The new terms of the tower step on two tori (blocker 7)

`towerNewTerms_twoTorus_fromTowerG`: at a scale of the general tower with block scale `1`, for a
family of tori `ℓ` with their scale data, the witnesses of
`stepIdentity_zeroClass_fibre_fromTowerG_core` are chosen on every torus.  For them:
* the step identity holds on every torus with the energy family `e0 ℓ` and the observable
  coefficient `mObs ℓ`, and `e0 ℓ z = dz ℓ z + c ℓ z` (determinant term and mark coefficient);
* the determinant term at a chart datum `D′` is the sum of the specification `hTd` with `Zr = {z}`:
  `dz ℓ z (rawOf D′, g) C = ∑_{zc ∈ {z}} ∑_{y : unitBlock1 y = zc} detActivityBg … D′ y C`;
* (`hob`) the observable coefficient of the site `(xs ℓ, iy)` at a support `X` of the quarter box
  that is not wide is the same on the torus `ℓ` and on `can X`:
  `mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X) = mObs (can X) (xs (can X)) iy (θ (can X) g) (Ycub (can X) X)`
  (`hob_of_obsLabelFormulas`, with `hEv`, `hmemV`, `hAeq0`, `hAeqθ` discharged by the formulas of
  the core);
* (`hdt`) the determinant term of the root `zr ℓ` at such a support is the same on `ℓ` and on
  `can X` (`hdt_of_detSum_thr36`, threshold `(K - 36) / 25`).

The theorem is a projection of `towerGapTerms_twoTorus_fromTowerG_core` (the witnesses of the
explicit core, chosen once per torus).
So `hTo` (`To ℓ g X = mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X)`) and `hTd` are theorems about the tower's
new terms.  The remaining hypotheses are data of the tori and of the parameters: the geometry of
the gap scale, the parameters `θ ℓ g` (in the chart with sources of the `q`-ball for `hob`; raw data
`rawOf (Dat ℓ g)` of chart data for `hdt`), and the agreement of raw data and sources on the
recentred box.  The mark coefficient `c` is not compared here.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section ObsTower

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
/-- **The new terms of the tower step on two tori.**  Beyond the threshold of
`stepIdentity_zeroClass_fibre_fromTowerG_core`, for a family of tori `ℓ` (`L ∣ N₁ ℓ`, `5 < N₁ ℓ`)
with scale data: there are the energy families `e0 ℓ = dz ℓ + c ℓ` and the observable coefficients
`mObs ℓ` of the tower (the witnesses of the core on each torus) such that
* on every torus the step identity of the zero class holds on the fibre `h ≡ h₀`:
  `TstepC(g) = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ∑_U e0 ℓ z (rawOf D′, 0) U
  + ∑_{y,i} g(y,i) ∑_V mObs ℓ y i (rawOf D′, g) V]`;
* the determinant term at a chart datum `D′` is `∑_{zc ∈ {z}} ∑_{y : unitBlock1 y = zc}
  detActivityBg 1 (compWeight L 1) 1 ν (rho4 …) D′ y C` (the specification `hTd`, `Zr = {z}`);
* for the geometry of a gap scale and parameters `θ ℓ g` of the chart with sources in the `q`-ball
  whose raw data and sources agree on the recentred box, the observable coefficient of the site
  `(xs ℓ, iy)` at a support `X` of the quarter box that is not wide is the same on `ℓ` and on
  `can X`;
* for the geometry of a gap scale with threshold `(K - 36) / 25`, roots `zr ℓ` corresponding under
  the box maps and parameters with raw data `rawOf (Dat ℓ g)` of chart data agreeing on the
  recentred box, the determinant term of the root `zr ℓ` at such a support is the same on `ℓ` and
  on `can X`. -/
theorem towerNewTerms_twoTorus_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) {ι : Type*} (N₁ : ι → ℕ) [∀ ℓ, NeZero (N₁ ℓ)]
        (_ : ∀ ℓ, L ^ T.m₀ ∣ N₁ ℓ) (_ : ∀ ℓ, 5 < N₁ ℓ)
        (ν : ℝ) (_ : 0 < ν) (_ : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (_ : β₀ ≤ β)
        (p₁ : ℝ) (_ : 0 < p₁) (_ : p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))))
        (q : ℝ) (_ : 0 < q) (_ : q ≤ 1) (_ : ∀ ℓ, StepScaleDataG T k hk (N₁ ℓ) ν β p₁),
      ∃ (e0 dz c : ∀ ℓ, RootIdx d L (N₁ ℓ) T.m₁ (k + 1) → physParam N (SA[ℓ]) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ)
        (mObs : ∀ ℓ, CTorus d L (N₁ ℓ) T.m₁ (k + 1) → Fin N → physParam N (SA[ℓ]) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ),
        (∀ ℓ (D' : BgData (SA[ℓ]).G' N) (hDh : ∀ y i, D'.h y i = ((SA[ℓ]).h₀ i : ℂ)),
          XiCData (SA[ℓ]).G' (SA[ℓ]).a (SA[ℓ]).ν (k + 1) 1 T.t D' →
          ∀ g : Fld d L (N₁ ℓ) T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
            ((SA[ℓ]).withDatum D' hDh).TstepC (zeroClass d L (N₁ ℓ) T.m₁ k N (rhoSepG d L T.m₁)) g =
              Complex.exp (-((SA[ℓ]).β : ℂ) * ((SA[ℓ]).withDatum D' hDh).AnewC -
                (((SA[ℓ]).withDatum D' hDh).Eppp
                    (zeroClass d L (N₁ ℓ) T.m₁ k N (rhoSepG d L T.m₁)) : ℂ) *
                  (((SA[ℓ]).withDatum D' hDh).nU : ℂ) +
                FcompAtC (zeroClass d L (N₁ ℓ) T.m₁ k N (rhoSepG d L T.m₁)).m₀
                  (zeroClass d L (N₁ ℓ) T.m₁ k N (rhoSepG d L T.m₁)).Tm (SA[ℓ]).a (SA[ℓ]).ν
                  (Nat.le_succ k) ((SA[ℓ]).withDatum D' hDh).psiKdC g +
                ∑ z : RootIdx d L (N₁ ℓ) T.m₁ (k + 1), ∑ C,
                  e0 ℓ z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (SA[ℓ]).G'),
                    (0 : CTorus d L (N₁ ℓ) T.m₁ (k + 1) → Fin N → ℂ)) C +
                ∑ y : CTorus d L (N₁ ℓ) T.m₁ (k + 1), ∑ i : Fin N, g y i *
                  ∑ T', mObs ℓ y i ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (SA[ℓ]).G'), g)
                    T')) ∧
        (∀ ℓ z θ C, e0 ℓ z θ C = dz ℓ z θ C + c ℓ z θ C) ∧
        (∀ ℓ z (D' : BgData (SA[ℓ]).G' N),
          XiCData (SA[ℓ]).G' (SA[ℓ]).a (SA[ℓ]).ν (k + 1) 1 T.t D' →
          ∀ (g : Fld d L (N₁ ℓ) T.m₁ (k + 1) N) C,
            dz ℓ z (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C =
              ∑ zc ∈ ({z} : Finset (RootIdx d L (N₁ ℓ) T.m₁ (k + 1))),
                ∑ y ∈ (Finset.univ.filter fun u : unitPts (SA[ℓ]).G' =>
                  unitBlock1 (u : UnitTorus d L (N₁ ℓ) T.m₁ k) = zc),
                  detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D' y C) ∧
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
            mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X) =
              mObs (can X) (xs (can X)) iy (θ (can X) g) (Ycub (can X) X)) ∧
        ∀ {G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
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
            dz ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) = dz (can X) (zr (can X)) (θ (can X) g) (Ycub (can X) X) := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    towerGapTerms_twoTorus_fromTowerG_core.{_, _, _, 0} T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ι N₁ _ h3N h5 ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1 D
  obtain ⟨e0, dz, c, mObs, _, -, hT, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨hob, hdt, -⟩ := hF N₁ h3N h5 D
  exact ⟨fun ℓ => e0 (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ), fun ℓ => dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ),
    fun ℓ => c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ), fun ℓ => mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ),
    fun ℓ => (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).1, fun ℓ => (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).2.1,
    fun ℓ => (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).2.2.1, hob, hdt⟩

end ObsTower

end Balaban.Polymer.TwoTorusStep
