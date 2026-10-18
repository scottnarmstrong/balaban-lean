/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

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
    towerGapTerms_twoTorus_fromTowerG_core T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨e0, dz, c, mObs, B, hB, hT, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  refine ⟨e0, dz, c, mObs, B, hB,
    fun n _ h3 h5' Dn => ⟨(hT n h3 h5' Dn).1, (hT n h3 h5' Dn).2.1⟩, ?_⟩
  intro ι G N₁ _ h3N h5 D K _ hK2 hside P Q can τ hP hQ hτ hcanK Ycub hYs zr r0 hr0 hzr xs iy x0
    hx0 hxsb Dset θ hθV Dat hDat hθD hrawO hsrcO hrawR Ag hAg hAgθ W hWan κ κ₂ lam hκ hκ₂ hlam
    hrate
  obtain ⟨Tt, hTt⟩ : ∃ Tt : ι → G → Finset (Fin d → ℤ) → ℂ, ∀ ℓ g X,
      Tt ℓ g X = c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) +
        dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) +
        mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (θ ℓ g) (Ycub ℓ X) :=
    ⟨_, fun _ _ _ => rfl⟩
  refine ⟨Tt, hTt, ?_⟩
  have hL3 := T.hL
  have hκd : 0 ≤ 3 / 2 * T.κdec := by
    have := T.κdec_lower; have := T.κ0_nonneg; linarith
  -- `hbd`: the bound in `e^{-κ' |X|}`
  have hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tt ℓ g X‖ ≤
      3 * B * Real.exp (3 / 2 * T.κdec) *
        Real.exp (-(3 / 2 * T.κdec / c1 d L) * ((Finset.card X : ℕ) : ℝ)) := by
    intro ℓ X hX g hg
    obtain ⟨Y, -, rfl⟩ := (hP ℓ X).1 hX
    have hcard := card_le_card_of_sitesOf_cells (hside ℓ) (Ycub ℓ _) Y (hYs ℓ _)
    have hN1 : L ^ 1 ∣ N₁ ℓ := by have := h3N ℓ; rwa [hm₀] at this
    have hE := exp_neg_dExt_le_card hN1 le_rfl (Ycub ℓ (Y.image fun b μ => (b μ).valMinAbs))
      hκd hcard
    obtain ⟨hcz, hoz⟩ := (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).2.2.2
      (Ycub ℓ (Y.image fun b μ => (b μ).valMinAbs))
    obtain ⟨h1, h2⟩ := (hcz (zr ℓ)).1 (θ ℓ g) (hθV ℓ g hg).1
    have h3' := (hoz (xs ℓ) iy).1 (θ ℓ g) (hθV ℓ g hg)
    rw [hTt]
    have hn : ‖c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g)
          (Ycub ℓ (Y.image fun b μ => (b μ).valMinAbs)) +
        dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g)
          (Ycub ℓ (Y.image fun b μ => (b μ).valMinAbs)) +
        mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (θ ℓ g)
          (Ycub ℓ (Y.image fun b μ => (b μ).valMinAbs))‖ ≤
        3 * (B * Real.exp (-(3 / 2 * T.κdec) *
          dExt (Ycub ℓ (Y.image fun b μ => (b μ).valMinAbs)))) := by
      refine (norm_add₃_le).trans ?_
      linarith
    refine hn.trans ?_
    have hm := mul_le_mul_of_nonneg_left hE hB
    nlinarith [Real.exp_pos (3 / 2 * T.κdec)]
  -- `hloc`: locality for `Ag`
  have hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tt ℓ g X = Tt ℓ g' X := by
    intro ℓ X hX g g' hag
    rw [hTt, hTt]
    rcases hAgθ ℓ X g g' hX hag with h | ⟨hg1, hg2, hr⟩
    · rw [h]
    · obtain ⟨hcz, hoz⟩ := (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).2.2.2 (Ycub ℓ X)
      obtain ⟨-, -, -, hlc, -, -⟩ := hcz (zr ℓ)
      obtain ⟨e1, e2⟩ := hlc _ hg1.1 _ hg2.1 hr
      obtain ⟨-, -, hlo, -⟩ := hoz (xs ℓ) iy
      have hr' := physRestrict_eq_of_subset
        (fun x hx => Or.inl (subset_Yhat Set.univ (sitesOf (Ycub ℓ X)) hx)) hr
      rw [e1, e2, hlo _ hg1 _ hg2 hr']
  -- `han`: the terms are in `W`
  have han : ∀ ℓ X, X ∈ P ℓ → (fun g => Tt ℓ g X) ∈ W := by
    intro ℓ X _
    obtain ⟨hcz, hoz⟩ := (hT (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ)).2.2.2 (Ycub ℓ X)
    obtain ⟨-, ha1, ha2, -⟩ := hcz (zr ℓ)
    obtain ⟨-, ha3, -⟩ := hoz (xs ℓ) iy
    have hsub : physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q ⊆
        physV (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t := fun _ hx => hx.1
    have hfun : (fun g => Tt ℓ g X) = fun g =>
        (fun θ' => c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) θ' (Ycub ℓ X) +
          dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) θ' (Ycub ℓ X) +
          mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy θ' (Ycub ℓ X)) (θ ℓ g) :=
      funext fun g => hTt ℓ g X
    rw [hfun]
    exact hWan ℓ _ (((ha1.mono hsub).add (ha2.mono hsub)).add ha3)

  have hL1 : 1 ≤ L := by omega
  have : NeZero aK := ⟨(cellSide_pos (L := L) 1 T.m₁ (k + 1)).ne'⟩
  have hsupB : ∀ ℓ X, L ≤ τ ℓ X → ∀ c ∈ X, ∀ μ, (c μ).natAbs + L ≤ K ℓ / 4 := by
    intro ℓ X ht c hc μ
    have h1 : (c μ).natAbs ≤ X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs) :=
      (Finset.le_sup (f := fun μ => (c μ).natAbs) (Finset.mem_univ μ)).trans
        (Finset.le_sup (f := fun x => Finset.univ.sup fun μ => (x μ).natAbs) hc)
    rw [hτ] at ht
    omega
  -- `hWm`: a wide support pays the chain
  have hWm : ∀ ℓ X, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
      (¬ ∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
      τ ℓ X ≤ 7 * X.card := by
    intro ℓ X hK hX hQX hw
    obtain ⟨Y, hY, rfl⟩ := (hP ℓ X).1 hX
    have hc := card_ge_of_not_spread hY (fun x hx μ => (hQ ℓ _).1 hQX x hx μ) hw
    have hτ4 : τ ℓ (Y.image fun b μ => (b μ).valMinAbs) ≤ K ℓ / 4 := by rw [hτ]; omega
    omega
  -- cells of the root cube and of the site
  have hcellRS : ∀ ℓ (x : CTorus d L (N₁ ℓ) T.m₁ (k + 1)) μ,
      ((rootCube (m₀ := 1) (blockIndex x)).1 μ).val / aK = (x μ).val / aK := by
    intro ℓ x μ
    have haK : aK = L ^ (k + 1) * L ^ (1 + T.m₁) := by
      unfold cellSide; rw [← pow_add]; congr 1; omega
    show ((cbase aK (rootSite (blockIndex x))) μ).val / aK = _
    rw [rootSite_blockIndex]
    have h1 := cbase_val_div (M := 1) (cellSide_pos (L := L) 1 T.m₁ (k + 1))
      (blockBase L (k + 1) x) μ
    rw [mul_one] at h1
    rw [h1]
    have h2 := cbase_val_div (M := L ^ (1 + T.m₁)) (pow_pos (by omega : 0 < L) (k + 1)) x μ
    rw [← haK] at h2
    exact h2
  have hcorner : ∀ ℓ μ, ((cbase aK (xs ℓ)) μ).val / aK = (xs ℓ μ).val / aK := fun ℓ μ => by
    have h := cbase_val_div (M := 1) (cellSide_pos (L := L) 1 T.m₁ (k + 1)) (xs ℓ) μ
    rwa [mul_one] at h
  have hcellR : ∀ ℓ X, rootCube (m₀ := 1) (zr ℓ) ∈ Ycub ℓ X → r0 ∈ X := by
    intro ℓ X h
    have hs : (rootCube (m₀ := 1) (zr ℓ)).1 ∈ sitesOf (Ycub ℓ X) :=
      mem_sitesOf.2 ⟨_, h, mem_box_self _ (cellSide_pos 1 T.m₁ (k + 1))⟩
    rw [hYs ℓ X] at hs
    rw [← hr0 ℓ]
    exact hs
  have hcellO : ∀ ℓ X, rootCube (m₀ := 1) (blockIndex (xs ℓ)) ∈ Ycub ℓ X → x0 ∈ X := by
    intro ℓ X h
    have hs : (rootCube (m₀ := 1) (blockIndex (xs ℓ))).1 ∈ sitesOf (Ycub ℓ X) :=
      mem_sitesOf.2 ⟨_, h, mem_box_self _ (cellSide_pos 1 T.m₁ (k + 1))⟩
    rw [hYs ℓ X] at hs
    have hs' : (fun μ => (((((rootCube (m₀ := 1) (blockIndex (xs ℓ))).1 μ).val / aK : ℕ) :
        ZMod (K ℓ))).valMinAbs) ∈ X := hs
    simp only [hcellRS ℓ (xs ℓ)] at hs'
    rw [← hx0 ℓ]
    exact hs'
  have hYs' : ∀ ℓ X, ∀ y ∈ sitesOf (Ycub ℓ X),
      (fun μ => (((((y μ).val / aK : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈ (↑X : Set (Fin d → ℤ)) := by
    intro ℓ X y hy
    rw [hYs ℓ X] at hy
    exact hy
  -- `hex`: the exact clause above the threshold at margin `τ ≥ L`
  have hex : ∀ ℓ X, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
      ¬ (¬ ∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
      L ≤ τ ℓ X → ∀ g ∈ Dset, Tt ℓ g X = Tt (can X) g X := by
    intro ℓ X hK hX hQX hW hτL g hg
    have hKc : 300 * L + 100 ≤ K (can X) := le_trans hK (hcanK ℓ X hX hQX)
    obtain ⟨can', hcan'⟩ : ∃ can' : Finset (Fin d → ℤ) → {l : ι // 300 * L + 100 ≤ K l},
        ∀ (l : {l : ι // 300 * L + 100 ≤ K l}) X' (hX' : X' ∈ P l.1) (hQX' : Q l.1 X'),
          can' X' = ⟨can X', le_trans l.2 (hcanK l.1 X' hX' hQX')⟩ :=
      ⟨fun X' => if h : 300 * L + 100 ≤ K (can X') then ⟨can X', h⟩ else ⟨ℓ, hK⟩,
        fun l X' hX' hQX' => dite_eq_left _⟩
    have hcanK' : ∀ (l : {l : ι // 300 * L + 100 ≤ K l}) X', X' ∈ P l.1 → Q l.1 X' →
        K l.1 ≤ K (can' X').1 := fun l X' hX' hQX' => by
      rw [hcan' l X' hX' hQX']; exact hcanK l.1 X' hX' hQX'
    have hnum : ∀ l : {l : ι // 300 * L + 100 ≤ K l}, 36 ≤ K l.1 ∧ 26 ≤ K l.1 ∧
        L ≤ (K l.1 - 26) / 25 + 1 ∧ (K l.1 - 36) / 25 - L + L - 1 ≤ (K l.1 - 36) / 25 ∧
        (K l.1 - 36) / 25 ≤ (K l.1 - 26) / 25 ∧
        (K l.1 - 36) / 25 - L + L - 1 ≤ (K l.1 - 26) / 25 ∧ 2 * (L - 1) ≤ (K l.1 - 26) / 25 :=
      fun l => by have := l.2; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    obtain ⟨hob, hdt, hen⟩ := hF (ι := {l : ι // 300 * L + 100 ≤ K l}) (fun l => N₁ l.1)
      (fun l => h3N l.1) (fun l => h5 l.1) (fun l => D l.1)
    have hcomp := not_not.1 hW
    -- the root part
    have hroot : c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) +
          dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (zr ℓ) (θ ℓ g) (Ycub ℓ X) =
        c (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (zr (can X)) (θ (can X) g)
            (Ycub (can X) X) +
          dz (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (zr (can X)) (θ (can X) g)
            (Ycub (can X) X) := by
      by_cases hr : r0 ∈ X
      · have hgeo := fun (l : {l : ι // 300 * L + 100 ≤ K l}) X'
            (h : ¬ ¬ ((∀ c ∈ X', ∀ c' ∈ X', ∀ μ,
              |c μ - c' μ| ≤ (((K l.1 - 36) / 25 - L : ℕ) : ℤ)) ∧ L ≤ τ l.1 X' ∧ r0 ∈ X')) =>
          rootBox_geom (hside l.1) (hnum l).2.1 hL1 (rootCube (m₀ := 1) (zr l.1)).2.1 (hr0 l.1)
            (↑X' : Set (Fin d → ℤ)) (not_not.1 h).2.2 (hsupB l.1 X' (not_not.1 h).2.1)
            (not_not.1 h).1 (hnum l).2.2.2.1 (hnum l).2.2.2.2.1 (sitesOf (Ycub l.1 X'))
            (hYs' l.1 X')
        have eD := hdt (G := G) (fun l => K l.1) (fun l => (hnum l).1)
          (Dc := fun l => (K l.1 - 36) / 25) (fun l => le_rfl) (fun l => hside l.1)
          (fun l => P l.1) (fun l => Q l.1) can'
          (fun l X' => ¬ ((∀ c ∈ X', ∀ c' ∈ X', ∀ μ,
            |c μ - c' μ| ≤ (((K l.1 - 36) / 25 - L : ℕ) : ℤ)) ∧ L ≤ τ l.1 X' ∧ r0 ∈ X'))
          (fun l X' => hP l.1 X') (fun l X' => hQ l.1 X') hcanK' (fun l => zr l.1)
          (fun l X' hX' hQX' => by
            rw [hcan' l X' hX' hQX']; exact hzr l.1 X' l.2 hX' hQX')
          (fun l => Ycub l.1) (fun l X' _ => hYs l.1 X') (Dset := Dset) (fun l => Dat l.1)
          (fun l => hDat l.1) (fun l => θ l.1) (fun l => hθD l.1)
          (fun l X' _ _ _ hW' _ => (hgeo l X' hW').1)
          (fun l X' _ _ _ hW' _ => (hgeo l X' hW').2)
          (fun l X' g' hX' hQX' hW' hg' => by
            obtain ⟨hc', ht', hr'⟩ := not_not.1 hW'
            rw [hcan' l X' hX' hQX']
            exact hrawR l.1 X' g' l.2 hX' hQX' hc' ht' hr' hg')
          ⟨ℓ, hK⟩ X hX hQX (not_not.2 ⟨hcomp, hτL, hr⟩) g hg
        have eC := hen (G := G) (fun l => K l.1) (fun l => (hnum l).1)
          (Dc := fun l => (K l.1 - 36) / 25) (fun l => le_rfl) (fun l => hside l.1)
          (fun l => (hnum l).2.2.1) (fun l => P l.1) (fun l => Q l.1) can'
          (fun l X' => ¬ ((∀ c ∈ X', ∀ c' ∈ X', ∀ μ,
            |c μ - c' μ| ≤ (((K l.1 - 36) / 25 - L : ℕ) : ℤ)) ∧ L ≤ τ l.1 X' ∧ r0 ∈ X'))
          (fun l X' => hQ l.1 X') hcanK' (fun l => zr l.1)
          (fun l X' hX' hQX' => by
            rw [hcan' l X' hX' hQX']; exact hzr l.1 X' l.2 hX' hQX')
          (fun l => Ycub l.1) (fun l X' => hYs l.1 X') (Dset := Dset) (fun l => θ l.1)
          (fun l g' hg' => (hθV l.1 g' hg').1)
          (fun l X' _ _ _ hW' _ => (hgeo l X' hW').1)
          (fun l X' _ _ _ hW' _ => (hgeo l X' hW').2)
          (fun l X' g' hX' hQX' hW' hg' => by
            obtain ⟨hc', ht', hr'⟩ := not_not.1 hW'
            rw [hcan' l X' hX' hQX']
            dsimp only
            rw [hθD l.1 g' hg', hθD (can X') g' hg']
            exact hrawR l.1 X' g' l.2 hX' hQX' hc' ht' hr' hg')
          ⟨ℓ, hK⟩ X hX hQX (not_not.2 ⟨hcomp, hτL, hr⟩) g hg
        rw [hcan' ⟨ℓ, hK⟩ X hX hQX] at eD eC
        dsimp only at eD eC
        rw [eC, eD]
      · have hz : ∀ ℓ', ∀ θ', c (N₁ ℓ') (h3N ℓ') (h5 ℓ') (D ℓ') (zr ℓ') θ' (Ycub ℓ' X) = 0 ∧
            dz (N₁ ℓ') (h3N ℓ') (h5 ℓ') (D ℓ') (zr ℓ') θ' (Ycub ℓ' X) = 0 := by
          intro ℓ' θ'
          obtain ⟨-, -, -, -, hsc, hsd⟩ :=
            ((hT (N₁ ℓ') (h3N ℓ') (h5 ℓ') (D ℓ')).2.2.2 (Ycub ℓ' X)).1 (zr ℓ')
          exact ⟨by_contra fun h => hr (hcellR ℓ' X (hsc θ' h)),
            by_contra fun h => hr (hcellR ℓ' X (hsd θ' h))⟩
        rw [(hz ℓ _).1, (hz ℓ _).2, (hz (can X) _).1, (hz (can X) _).2]
    -- the site part
    have hsite : mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (xs ℓ) iy (θ ℓ g) (Ycub ℓ X) =
        mObs (N₁ (can X)) (h3N (can X)) (h5 (can X)) (D (can X)) (xs (can X)) iy (θ (can X) g)
          (Ycub (can X) X) := by
      by_cases hx : x0 ∈ X
      · have hx0' : ∀ l : {l : ι // 300 * L + 100 ≤ K l},
            (fun μ => (((((cbase aK (xs l.1) μ).val / aK : ℕ)) : ZMod (K l.1))).valMinAbs) = x0 :=
          fun l => by simp only [hcorner l.1]; exact hx0 l.1
        have hgeo := fun (l : {l : ι // 300 * L + 100 ≤ K l}) X'
            (h : ¬ ¬ ((∀ c ∈ X', ∀ c' ∈ X', ∀ μ,
              |c μ - c' μ| ≤ (((K l.1 - 36) / 25 - L : ℕ) : ℤ)) ∧ L ≤ τ l.1 X' ∧ x0 ∈ X')) =>
          cellNbhd_geom (hside l.1) (hnum l).2.1 hL1 (aligned_cbase (xs l.1)) (hx0' l)
            (↑X' : Set (Fin d → ℤ)) (not_not.1 h).2.2 (hsupB l.1 X' (not_not.1 h).2.1)
            (not_not.1 h).1 (hnum l).2.2.2.2.2.1 (hnum l).2.2.2.2.2.2 le_rfl
            (sitesOf (Ycub l.1 X')) (hYs' l.1 X')
        have eO := hob (G := G) (fun l => K l.1) (fun l => (hnum l).2.1) (fun l => hside l.1)
          (fun l => (hnum l).2.2.1) (fun l => P l.1) (fun l => Q l.1) can'
          (fun l X' => ¬ ((∀ c ∈ X', ∀ c' ∈ X', ∀ μ,
            |c μ - c' μ| ≤ (((K l.1 - 36) / 25 - L : ℕ) : ℤ)) ∧ L ≤ τ l.1 X' ∧ x0 ∈ X'))
          (fun l X' => hP l.1 X') (fun l X' => hQ l.1 X') hcanK' (fun l => Ycub l.1)
          (fun l X' _ => hYs l.1 X') (fun l => xs l.1) iy
          (fun l X' hX' hQX' => by
            rw [hcan' l X' hX' hQX']; exact hxsb l.1 X' l.2 hX' hQX')
          (fun l X' _ _ hW' Ds hDs => by subst hDs; exact (hgeo l X' hW').1)
          (fun l X' _ _ hW' => (hgeo l X' hW').2) (Dset := Dset) (fun l => θ l.1)
          (fun l => hθV l.1)
          (fun l X' g' hX' hQX' hW' hg' => by
            obtain ⟨hc', ht', hx'⟩ := not_not.1 hW'
            rw [hcan' l X' hX' hQX']
            exact hrawO l.1 X' g' l.2 hX' hQX' hc' ht' hx' hg')
          (fun l X' g' hX' hQX' hW' hg' => by
            obtain ⟨hc', ht', hx'⟩ := not_not.1 hW'
            rw [hcan' l X' hX' hQX']
            exact hsrcO l.1 X' g' l.2 hX' hQX' hc' ht' hx' hg')
          ⟨ℓ, hK⟩ X hX hQX (not_not.2 ⟨hcomp, hτL, hx⟩) g hg
        rw [hcan' ⟨ℓ, hK⟩ X hX hQX] at eO
        dsimp only at eO
        exact eO
      · have hz : ∀ ℓ', θ ℓ' g ∈ physVq (SA[ℓ']) (SA[ℓ']).a₁ (SA[ℓ']).ν T.t q →
            mObs (N₁ ℓ') (h3N ℓ') (h5 ℓ') (D ℓ') (xs ℓ') iy (θ ℓ' g) (Ycub ℓ' X) = 0 := by
          intro ℓ' hθ
          obtain ⟨-, -, -, hso⟩ :=
            ((hT (N₁ ℓ') (h3N ℓ') (h5 ℓ') (D ℓ')).2.2.2 (Ycub ℓ' X)).2 (xs ℓ') iy
          exact by_contra fun h => hx (hcellO ℓ' X (hso _ hθ h))
        rw [hz ℓ (hθV ℓ g hg), hz (can X) (hθV (can X) g hg)]
    rw [hTt, hTt, hsite, hroot]
  obtain ⟨Φ, Tn, r1, r2, r3, r4, r5, -, r7, r8⟩ := resum_gapScale_torus_mixed K
    (by have := T.hd; omega) (300 * L + 100) L hK2 P Q Finset.card τ can Dset W (fun _ => True) Ag
    Tt (fun ℓ X => ¬ ∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ))
    (B := 3 * B * Real.exp (3 / 2 * T.κdec)) (κ' := 3 / 2 * T.κdec / c1 d L) hP hQ
    (fun _ => rfl) hτ (fun _ _ _ => trivial) hAg hcanK hWm (by positivity) hκ hκ₂ hlam hrate
    (fun _ _ _ h => absurd trivial h) hloc han hbd hex
  exact ⟨Φ, Tn, r1, r2, r3, r4, r5, r7, r8⟩

end Tower

end Balaban.Polymer.TwoTorusStep
