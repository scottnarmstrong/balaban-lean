/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyCells
public import Balaban.Inhabited.StepIdentityFibreExplicitCore
public import Balaban.Polymer.TwoTorusGapTowerTieNew
public import Balaban.Polymer.TwoTorusGapTowerCloseCore

/-!
# The energy coefficient of the tower step on two tori (blocker 7)

* `gsumCoeff_commonLabels_congr` and `towerLab_margin` are in `TwoTorusGapTowerCloseAux.lean`.
* `towerEnergyCoef_twoTorus_fromTowerG`: for the witnesses of
  `stepIdentity_zeroClass_fibre_fromTowerG_explicitCore` on a family of tori, the step identity,
  `e0 = dz + c`, and the clause `hen` of the gap scale for the mark coefficient `c` of a root:
  `c ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) = c (can X) (zr (can X)) (θ (can X) g) (Ycub (can X) X)` for supports
  of the quarter box that are not wide, from the explicit direct terms of the core and
  `gsumCoeff_e1_cellSites`.  It is a projection of `towerGapTerms_twoTorus_fromTowerG_core`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section EnergyTower

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
/-- **The energy coefficient of the tower step on two tori.**  Beyond the threshold of
`stepIdentity_zeroClass_fibre_fromTowerG_explicitCore` and of the marks (`exists_beta0_e1G`), for a
family of tori `ℓ` with scale data: there are the energy families `e0 ℓ = dz ℓ + c ℓ` and the
observable coefficients `mObs ℓ` of the tower (the witnesses of the core on each torus) such that
* on every torus the step identity of the zero class holds on the fibre `h ≡ h₀`;
* `e0 ℓ z = dz ℓ z + c ℓ z` (determinant term and mark coefficient);
* (`hen`) for the geometry of a gap scale with threshold `(K - 36) / 25` and `L ≤ (K - 26) / 25 + 1`,
  roots `zr ℓ` corresponding under the coarse box maps, parameters `θ ℓ g` of the charts whose raw
  data agree on the recentred boxes, the mark coefficient of the root `zr ℓ` at the cubes of the cells
  of a support `X` of the quarter box that is not wide is the same on `ℓ` and on `can X`:
  `c ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) = c (can X) (zr (can X)) (θ (can X) g) (Ycub (can X) X)`.
The coefficient is written on the direct-terms record of the core (`gsumCoeff_commonLabels_congr`)
and compared by `gsumCoeff_e1_cellSites`. -/
theorem towerEnergyCoef_twoTorus_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
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
            c ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) = c (can X) (zr (can X)) (θ (can X) g) (Ycub (can X) X) := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    towerGapTerms_twoTorus_fromTowerG_core.{_, 0, 0, _} T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ι N₁ _ h3N h5 ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1 D
  obtain ⟨e0, dz, c, mObs, _, -, hT, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  exact ⟨fun ℓ => e0 (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ), fun ℓ => dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ),
    fun ℓ => c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ), fun ℓ => mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ),
    fun ℓ => (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).1, fun ℓ => (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).2.1,
    (hF N₁ h3N h5 D).2.2⟩

end EnergyTower

end Balaban.Polymer.TwoTorusStep
