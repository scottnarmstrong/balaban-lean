/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerRootFSuppTower
public import Balaban.Polymer.TwoTorusGapTowerCloseCore
public import Balaban.Polymer.TwoTorusGapTowerCloseResum
public import Balaban.Polymer.TwoTorusGapDataThr
public import Balaban.Polymer.TwoTorusGapTowerCloseCells

/-!
# The gap-scale clause at the tower (blocker 7)

`towerGapScale_resum_fromTowerG`: at every scale of the general tower with block scale `1`, the new
terms of the step of a root `zr ℓ` and of an observable site `(xs ℓ, iy)` at a support `X` of the
torus `ℓ`,
`T ℓ g X = c ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) + dz ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) + mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X)`
(the witnesses of `towerGapTerms_twoTorus_fromTowerG_core`, no inherited terms: `Tinh = 0`), are
resummed on any family of tori with `2 ≤ K ℓ` cells per side into terms `Tn` with the same sum, equal
on the common quarter boxes of all tori, bounded by `B' e^{-κ |X|}`, local and analytic.

* `hbd` (in the proof): `‖T ℓ g X‖ ≤ 3 B e^{(3/2) κ_dec} e^{-((3/2) κ_dec / c₁) |X|}`, from the
  bounds of the core in `e^{-(3/2) κ_dec dExt}`, `|X| ≤ |Ycub ℓ X|`
  (`card_le_card_of_sitesOf_cells`) and (G1) (`exp_neg_dExt_le_card`).
* wide supports: spread above `S = (K - 36) / 25 - L` cells; they have `S + 2` cells
  (`card_ge_of_not_spread`), which pays the chain above `Kthr = 300 L + 100`.
* compact supports above `Kthr` at margin `τ ≥ L`: if the cell `r0` of the root lies in `X`, the
  geometry of the root box holds (`rootBox_geom`) and `hen`, `hdt` of the core apply on the subfamily
  `{ℓ // Kthr ≤ K ℓ}`; otherwise `c` and `dz` vanish on both tori (support: the root cube lies in
  `Ycub X`).  Likewise for the site with its cell `x0` (`cellNbhd_geom`, `hob`).
* below `Kthr`, or at margin `τ < L`: the closeness comes from `hbd` (`resum_gapScale_torus_mixed`,
  `a = 2 B' e^{(Kthr/4) lam}`, `t₀ = L`).

The remaining hypotheses are data: the definitions of `P`, `Q`, `τ`, the canonical torus `can`, the
cubes `Ycub` of the cells, the root `zr ℓ` (root cube in the cell `r0`) and the site `xs ℓ` (in the
cell `x0`) corresponding under the box maps, the parameters `θ ℓ g` (in `physVq`, raw data of chart
data `Dat ℓ g`), the agreement of raw data and sources on the recentred boxes at compact supports
containing `r0` (resp. `x0`), the relation `Ag` with its meaning on each torus, and a space `W`
containing the pull-backs of analytic functions.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section Tower

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
/-- **The gap-scale clause at the tower.**  Beyond the threshold of
`towerGapTerms_twoTorus_fromTowerG_core`, at every scale there are the witnesses `e0 = dz + c`,
`mObs` of the tower on every torus (with the step identity) and a constant `B ≥ 0` such that, on any
family of tori `ℓ` with scale data and `2 ≤ K ℓ` cells per side, under the data of the gap scale
(listed in the module header), the terms `T ℓ g X = c + dz + mObs` of the root `zr ℓ` (root cube in
the cell `r0`) and of the site `(xs ℓ, iy)` (in the cell `x0`) at the cubes `Ycub ℓ X` of the cells of
`X` have resummed terms `Tn`: the explicit formula of `resum_gapScale_torus_of_wideMargin`, the same
sum over the polymers of each torus, equal on the common quarter boxes, bounded by
`(B' + (2 B' e^{((300 L + 100)/4) lam} + 2 B') e^{κ₂} + 2 B' e^{κ₂ L}) e^{-κ |X|}`,
`B' = 3 B e^{(3/2) κ_dec}`, for the rates `κ + log 2 ≤ κ₂ ≤ lam`, `7 lam + κ₂ ≤ (3/2) κ_dec / c₁`,
local for `Ag` and in `W`. -/
theorem towerGapScale_resum_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
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
          ∀ z θ C, e0 n h3 h5' Dn z θ C = dz n h3 h5' Dn z θ C + c n h3 h5' Dn z θ C) ∧
        ∀ {ι G : Type*} (N₁ : ι → ℕ) [∀ ℓ, NeZero (N₁ ℓ)] (h3N : ∀ ℓ, L ^ T.m₀ ∣ N₁ ℓ)
          (h5 : ∀ ℓ, 5 < N₁ ℓ) (D : ∀ ℓ, StepScaleDataG T k hk (N₁ ℓ) ν β p₁)
          (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (_ : ∀ ℓ, 2 ≤ K ℓ)
          (_ : ∀ ℓ, (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) = aK * K ℓ)
          (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
          (can : Finset (Fin d → ℤ) → ι) (τ : ι → Finset (Fin d → ℤ) → ℕ)
          (_ : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
            X = Y.image (fun b μ => (b μ).valMinAbs))
          (_ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
          (_ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
          (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ))
          (_ : ∀ ℓ X, sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
          (zr : ∀ ℓ, RootIdx d L (N₁ ℓ) T.m₁ (k + 1)) (r0 : Fin d → ℤ)
          (_ : ∀ ℓ, (fun μ => (((((rootCube (m₀ := 1) (zr ℓ)).1 μ).val / aK : ℕ) :
            ZMod (K ℓ))).valMinAbs) = r0)
          (_ : ∀ ℓ X, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X → zr (can X) = bc[ℓ, can X] (zr ℓ))
          (xs : ∀ ℓ, CTorus d L (N₁ ℓ) T.m₁ (k + 1)) (iy : Fin N) (x0 : Fin d → ℤ)
          (_ : ∀ ℓ, (fun μ => (((((xs ℓ μ).val / aK : ℕ)) : ZMod (K ℓ))).valMinAbs) = x0)
          (_ : ∀ ℓ X, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X → xs (can X) = bm[ℓ, can X] (xs ℓ))
          {Dset : Set G} (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
          (_ : ∀ ℓ, ∀ g ∈ Dset, θ ℓ g ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q)
          (Dat : ∀ ℓ, G → BgData (SA[ℓ]).G' N)
          (_ : ∀ ℓ, ∀ g ∈ Dset, XiCData (SA[ℓ]).G' (compWeight L 1) ν (k + 1) 1 T.t (Dat ℓ g))
          (_ : ∀ ℓ, ∀ g ∈ Dset,
            ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N) = rawOf (Dat ℓ g))
          (_ : ∀ ℓ X g, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
            (∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
            L ≤ τ ℓ X → x0 ∈ X → g ∈ Dset →
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
          (_ : ∀ ℓ X g, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
            (∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
            L ≤ τ ℓ X → x0 ∈ X → g ∈ Dset →
            ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ LocalCover.nbhd 1 (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
            ∀ x, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1))
              (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))) →
            ∀ i, (θ (can X) g).2 (bm[ℓ, can X] (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) *
              L ^ (k + 1)))) - fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1))))
              i = (θ ℓ g).2 x i)
          (_ : ∀ ℓ X g, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
            (∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
            L ≤ τ ℓ X → r0 ∈ X → g ∈ Dset →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ box (rootCube (m₀ := 1) (zr ℓ)).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤
                (((aK * ((K ℓ - 36) / 25 + 1) - 1) + ((aK * ((K ℓ - 36) / 25 + 1) - 1) + 1) / 4 :
                  ℕ) : ℤ)) →
            RawBoxAgree {w | InBox d ((aK * ((K ℓ - 36) / 25 + 1) - 1) +
                ((aK * ((K ℓ - 36) / 25 + 1) - 1) + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
                ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) w}
              (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))))
                (rawOf (Dat ℓ g)))
              (symRaw (Equiv.addRight
                (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1)))))
                (rawOf (Dat (can X) g))))
          (Ag : Finset (Fin d → ℤ) → G → G → Prop)
          (_ : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
          (_ : ∀ ℓ X g g', X ∈ P ℓ → Ag X g g' → θ ℓ g = θ ℓ g' ∨
            (θ ℓ g ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q ∧
              θ ℓ g' ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q ∧
              physRestrict (N := N) (thickSet (SA[ℓ]).G' (Yhat Set.univ (sitesOf (Ycub ℓ X))))
                  (physIncl N (SA[ℓ]) (θ ℓ g)) =
                physRestrict (thickSet (SA[ℓ]).G' (Yhat Set.univ (sitesOf (Ycub ℓ X))))
                  (physIncl N (SA[ℓ]) (θ ℓ g'))))
          (W : Submodule ℂ (G → ℂ))
          (_ : ∀ ℓ (f : physParam N (SA[ℓ]) → ℂ),
            AnalyticOnNhd ℂ f (physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q) →
              (fun g => f (θ ℓ g)) ∈ W)
          {κ κ₂ lam : ℝ} (_ : 0 ≤ κ) (_ : κ + Real.log 2 ≤ κ₂) (_ : κ₂ ≤ lam)
          (_ : 7 * lam + κ₂ ≤ 3 / 2 * T.κdec / c1 d L),
        ∃ Tt : ι → G → Finset (Fin d → ℤ) → ℂ,
          (∀ ℓ g X, Tt ℓ g X = c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) +
            dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) +
            mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (θ ℓ g) (Ycub ℓ X)) ∧
        ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
        ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
          (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
          (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then Tt (can X) g X else
            Tt ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
              (Tt ℓ g X₀ - Tt (can X₀) g X₀)) ∧
          (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, Tt ℓ g X) ∧
          (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
          (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tn ℓ g X‖ ≤
            (3 * B * Real.exp (3 / 2 * T.κdec) +
              (2 * (3 * B * Real.exp (3 / 2 * T.κdec)) *
                  Real.exp ((((300 * L + 100) / 4 : ℕ) : ℝ) * lam) +
                2 * (3 * B * Real.exp (3 / 2 * T.κdec))) * Real.exp κ₂ +
              2 * (3 * B * Real.exp (3 / 2 * T.κdec)) * Real.exp (κ₂ * (L : ℝ))) *
              Real.exp (-κ * (X.card : ℝ))) ∧
          (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
          (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    towerGapScale_resum_fromTowerG_supp T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨e0, dz, c, mObs, B, hB, hT, -, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  exact ⟨e0, dz, c, mObs, B, hB, hT, hF⟩

end Tower

end Balaban.Polymer.TwoTorusStep
