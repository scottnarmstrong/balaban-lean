/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsFamily
public import Balaban.Polymer.TwoTorusGapDataSrc
public import Balaban.Polymer.TwoTorusGapTowerTieMem

/-!
# The observable new terms at the gap scale from the formulas of the activity (blocker 7)

`hob_of_obsSum` has three correspondence hypotheses on the observable activity: the label domains
(`hmemV`) and the activities of corresponding labels at the zero source (`hAeq0`) and at the
parameter (`hAeqθ`).  `hob_of_obsLabelFormulas` replaces them by the formulas that the tower
exports for its activity (`obsFamily_full_fromTowerG_rho_core`): the labels correspond to the
domains of the local covers of the blocks and of the sites (`h𝒴v`), and the activity is the
potential part of the direct terms at `(e.1, 0)` (`hAx`, decoupled pairs per block) and the
potential part plus the source part at `e` (`hAs`, decoupled pairs per site), on a set `V ℓ`
containing the parameters.  The source of the parameters on the two tori agrees on the recentred
box (`hsrc`), as the raw data do (`hraw`).

* `tieObs_sizes`: the margins `25 Ds + 25 < n`, `n'` and `L a_K ≤ Ds + 1` of a compact support.
* `hmemV` is `mem_obsLabelDomains_recentred_iff`, `hAeq0` is `labelActZero_recentred` (after
  `rayTerm_evTerm_eq_evDec`) and `hAeqθ` is `labelActSource_recentred`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv

/-- **The margins of a compact support.**  For `26 ≤ K ≤ K'`, sides `n = a_K K`, `n' = a_K K'`,
`L ≤ (K - 26) / 25 + 1` and `Ds = a_K ((K - 26) / 25 + 1) - 1`: `25 Ds + 25 < n`, `25 Ds + 25 < n'`
and `L a_K ≤ Ds + 1`. -/
theorem tieObs_sizes {L aK K K' n n' Ds : ℕ} (hK : 26 ≤ K) (hKK : K ≤ K') (hn : n = aK * K)
    (hn' : n' = aK * K') (hKL : L ≤ (K - 26) / 25 + 1) (hDs : Ds = aK * ((K - 26) / 25 + 1) - 1)
    (ha : 0 < aK) :
    25 * Ds + 25 < n ∧ 25 * Ds + 25 < n' ∧ L * aK ≤ Ds + 1 := by
  have h1 : 1 ≤ aK * ((K - 26) / 25 + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h25, h25', -⟩ := compact_site_margins (K := K) (K' := K') (cs := aK)
    (Dc := (K - 26) / 25) (Ds := Ds) (q := 0) hK hKK ha le_rfl (by omega) (Nat.zero_le _)
  refine ⟨hn ▸ h25, hn' ▸ h25', ?_⟩
  calc L * aK = aK * L := Nat.mul_comm _ _
    _ ≤ aK * ((K - 26) / 25 + 1) := Nat.mul_le_mul_left _ hKL
    _ = Ds + 1 := by omega

section ObsTie

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {ι G : Type*} {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {N₁ : ι → ℕ} [∀ ℓ, NeZero (N₁ ℓ)]
  {K : ι → ℕ} [∀ ℓ, NeZero (K ℓ)] {m₀ : ℕ}

set_option hygiene false in
local notation "bm[" ℓ "," ℓ' "]" =>
  boxMap ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)) ((N₁ ℓ' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "GA[" ℓ "]" => levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
  (ϱ := ϱ) (k + 1) le_rfl
set_option hygiene false in
local notation "HA[" ℓ "]" => levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
  (ϱ := ϱ) k (Nat.le_succ k)
set_option hygiene false in
local notation "SA[" ℓ "]" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁ ℓ) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "XA[" ℓ "]" => (↑(LocalCover.nbhdF m₀ (xs ℓ)) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1)))
set_option hygiene false in
local notation "𝒴A[" ℓ "]" => polyDom (GA[ℓ]) (LocalCover.nbhdF m₀ (xs ℓ)) m₀ k
  (LocalCover.fam m₀ (xs ℓ))
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L m₀ m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}
set_option hygiene false in
local notation "TA[" ℓ "]" => Torus d (N₁ ℓ * L ^ m₁ * L ^ (k + 1 - (k + 1)))

/-- **The exact torus clause of the observable new terms from the formulas of the activity.**  The
statement of `hob_of_obsSum` with its hypotheses `hmemV`, `hAeq0`, `hAeqθ` replaced by the formulas of
the labels and of the activity (`h𝒴v`, `hAx`, `hAs` with the decoupled pairs per block and per site
and their defining properties) and by the agreement `hsrc` of the sources on the recentred box. -/
theorem hob_of_obsLabelFormulas (hN2 : 2 ≤ N)
    (hk : 1 ≤ k)
    (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : ∀ ℓ, FlCore N (GA[ℓ]) (HA[ℓ]) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hd : 0 < d)
    (hL : 2 ≤ L)
    (hm₀ : 1 ≤ m₀)
    (hm₁ : 1 ≤ m₁)
    (hN : ∀ ℓ, L ^ m₀ ∣ (N₁ ℓ))
    (hK26 : ∀ ℓ, 26 ≤ K ℓ)
    (hside : ∀ ℓ, (N₁ ℓ * L ^ m₁) * L ^ (k + 1) = cellSide L m₀ m₁ (k + 1) * K ℓ)
    (hKL : ∀ ℓ, L ≤ (K ℓ - 26) / 25 + 1)
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (can : Finset (Fin d → ℤ) → ι) (Wd : ι → Finset (Fin d → ℤ) → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hYs : ∀ ℓ X, X ∈ P ℓ → sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
    (xs : ∀ ℓ, CTorus d L (N₁ ℓ) m₁ (k + 1)) (iy : Fin N)
    (hxsb : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → xs (can X) = bm[ℓ, can X] (xs ℓ))
    (hsp : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ x ∈ LocalCover.nbhd m₀ (xs ℓ), ∀ y ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ Ds)
    (hqS : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X →
      ∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
      |(x μ).valMinAbs| ≤ ((aK * (K ℓ / 4 + 1) : ℕ) : ℤ))
    -- the site and the terms of its expansion
    (cc : ℂ)
    {cψ : ℝ}
    (hcψ : 0 < cψ)
    (hq : p₁ / cψ ≤ 1 / 4)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₁ : ∀ ℓ, DecParams (GA[ℓ]) × RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N →
      ((GA[ℓ]).Ω 1 × Fin N → ℂ) × ((GA[ℓ]).Ω 1 → ℂ)}
    (hF₁ : ∀ ℓ, ∀ (s : DecParams (GA[ℓ])) (D : BgData (GA[ℓ]) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA[ℓ]) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA[ℓ]).Ω 1 × Fin N → ℂ)
        (α : (GA[ℓ]).Ω 1 → ℂ), IsDecBg (GA[ℓ]) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        (F₁ ℓ) (s, rawOf D) = (φ, α))
    {Sol : ∀ ℓ, Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N → ((HA[ℓ]).Ω 1 × Fin N → ℂ) × ((HA[ℓ]).Ω 1 → ℂ)}
    (hSol : ∀ ℓ, ∀ p : Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA[ℓ]) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        ((Sol ℓ) p).1 = dphi (HA[ℓ]) (Dec2.decG (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) ((Sol ℓ) p).2 ∧
        Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) ((Sol ℓ) p).2 ∧
        Small (HA[ℓ]) ((Sol ℓ) p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA[ℓ]) ((Sol ℓ) p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA[ℓ]) ((Sol ℓ) p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA[ℓ]).Ω 1 → ℂ, Small (HA[ℓ]) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol ℓ) p).2))
    {Ev : ∀ ℓ, Set (CTorus d L (N₁ ℓ) m₁ (k + 1)) →
      RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N × ((SA[ℓ]).U × Fin N → ℂ) → ℂ}
    (hEv : ∀ ℓ, (Ev ℓ) = evTerm (fun i : ParIdx (GA[ℓ]) (XA[ℓ]) => i.1.1) (GA[ℓ]) m₀
        (X1 (GA[ℓ]) m₀ k (LocalCover.fam m₀ (xs ℓ)))
        (fun u s => siteFun (GA[ℓ]) (HA[ℓ]) (xs ℓ) iy ((F₁ ℓ) (extParams (GA[ℓ]) (XA[ℓ]) s, u.1))
          ((Sol ℓ) (extParams (GA[ℓ]) (XA[ℓ]) s,
            flEdat (GA[ℓ]) (HA[ℓ]) ((F₁ ℓ) (extParams (GA[ℓ]) (XA[ℓ]) s, u.1))
              u.1.1 (hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₁ ℓ)
                (extParams (GA[ℓ]) (XA[ℓ]) s) u.1 u.2))).1
          (u.1, hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₁ ℓ)
            (extParams (GA[ℓ]) (XA[ℓ]) s) u.1 u.2)))
    (hdEv : ∀ ℓ, ∀ Y ∈ 𝒴A[ℓ], ∀ u ∈ XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA[ℓ]).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA[ℓ]).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir (SA[ℓ]).hG' Y u u' → (Ev ℓ) Y u = (Ev ℓ) Y u')
    (hdj : ∀ ℓ, ∀ Y ∈ 𝒴A[ℓ], IsDj m₀ (k + 1) Y)
    {Dset : Set G}
    (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
    (hθ : ∀ ℓ, ∀ g ∈ Dset, ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps)
    (hp : ∀ ℓ, 0 < (SA[ℓ]).p₁)
    {Lb : ι → Type} [∀ ℓ, Fintype (Lb ℓ)]
    (Lab : ∀ ℓ, CubeLabels (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ (Lb ℓ))
    {𝒴v : ∀ ℓ, Finset (Set (CTorus d L (N₁ ℓ) m₁ (k + 1)))}
    (ys : ∀ ℓ, (Lb ℓ) ≃ {Y // Y ∈ (𝒴v ℓ)})
    (hys : ∀ ℓ, ∀ l, (Lab ℓ).ysite l = ((ys ℓ) l).1)
    {εH κH κ0 Kco Kobs : ι → ℝ}
    (A : ∀ ℓ, physParam N (SA[ℓ]) → ℂ → LabelAct (Lab ℓ) ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb (εH ℓ) (κH ℓ) (κ0 ℓ) (Kco ℓ))
    (hκ0 : ∀ ℓ, aEnt d L + 1 ≤ (κ0 ℓ))
    (hεH : ∀ ℓ, 0 ≤ (εH ℓ))
    (hK : ∀ ℓ, (Kco ℓ) + (Kco ℓ) + K0 d L (κ0 ℓ) + K0 d L (κ0 ℓ) ≤ (Kobs ℓ))
    (Rg : ℝ)
    (hR : 0 ≤ Rg)
    (𝒰 : Set ℂ)
    (To : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hTo : ∀ ℓ g X, X ∈ P ℓ → g ∈ Dset →
      To ℓ g X =
      obsCoeffParam ((SA[ℓ]).blockSplit m₀ (hp ℓ)).μ
        (fun θ t σ => tiltActObs (A ℓ) (hN ℓ) (hκ0 ℓ) (hεH ℓ) (hdj ℓ) (hK ℓ) Rg hR 𝒰 θ t σ)
        (fun m => obsY1 m₀ (SA[ℓ]) ((Lb ℓ) ⊕ (Lb ℓ)) (𝒴A[ℓ]) m)
        (fun m => blockMarkC (SA[ℓ]) m₀ (hp ℓ) m.1 m.2)
        (fun θ m T'' => obsHker (𝒴A[ℓ]) (fun Y => hatCoeff ((Ev ℓ) Y)
          (θ.1 : RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N) (obsUnitVec (SA[ℓ]) m)) m₀ T'')
        (obsRemLab (𝒴A[ℓ]) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ ((Lb ℓ) ⊕ (Lb ℓ)) (𝒴A[ℓ]) (rootCube (m₀ := m₀) (blockIndex (xs ℓ)))))
        (fun θ => obsGrFam (SA[ℓ]) m₀ (hp ℓ) (Ev ℓ) (𝒴A[ℓ])
          (XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps) θ) (θ ℓ g) (Ycub ℓ X))
    (hraw : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1)) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) ((θ ℓ g).1 : RawData d L ((N₁ ℓ) * L ^ m₁) (k + 1) N))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) ((θ (can X) g).1 : RawData d L ((N₁ (can X)) * L ^ m₁) (k + 1) N)))
    (hN0 : 0 < N)
    (h𝒴v : ∀ ℓ, 𝒴v ℓ = (Finset.univ.biUnion fun z : TA[ℓ] =>
        polyDom (GA[ℓ]) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z))) ∪
      (Finset.univ.biUnion fun s : CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N =>
        polyDom (GA[ℓ]) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1)))
    {F₂ : ∀ ℓ, TA[ℓ] → DecParams (GA[ℓ]) × RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N →
      ((GA[ℓ]).Ω 1 × Fin N → ℂ) × ((GA[ℓ]).Ω 1 → ℂ)}
    (hF₂ : ∀ ℓ (b : TA[ℓ]) (s : DecParams (GA[ℓ])) (D : BgData (GA[ℓ]) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA[ℓ]) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA[ℓ]).Ω 1 × Fin N → ℂ)
        (α : (GA[ℓ]).Ω 1 → ℂ), IsDecBg (GA[ℓ]) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂ ℓ b (s, rawOf D) = (φ, α))
    {Sol₂ : ∀ ℓ, TA[ℓ] → Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N →
      ((HA[ℓ]).Ω 1 × Fin N → ℂ) × ((HA[ℓ]).Ω 1 → ℂ)}
    (hSol₂ : ∀ ℓ (b : TA[ℓ]) (p : Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA[ℓ]) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ ℓ b p).1 = dphi (HA[ℓ]) (Dec2.decG (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1)
          p.2.2.1 p.2.1 (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ ℓ b p).2 ∧
        Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ ℓ b p).2 ∧
        Small (HA[ℓ]) (Sol₂ ℓ b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA[ℓ]) (Sol₂ ℓ b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA[ℓ]) (Sol₂ ℓ b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA[ℓ]).Ω 1 → ℂ, Small (HA[ℓ]) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ ℓ b p).2))
    {V : ∀ ℓ, Set (physParam N (SA[ℓ]))}
    (hθV : ∀ ℓ, ∀ g ∈ Dset, θ ℓ g ∈ V ℓ)
    (hAx : ∀ ℓ, ∀ e ∈ V ℓ, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb ℓ)
      (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b),
      (A ℓ ((e.1, 0) : physParam N (SA[ℓ])) σ).H l Φ = -(β : ℂ) *
        ∑ z : TA[ℓ], if (Lab ℓ).ysite l ∈ polyDom (GA[ℓ])
            (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evTerm
            (fun i : ParIdx (GA[ℓ]) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
              Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) => i.1.1)
            (GA[ℓ]) m₀ (X1 (GA[ℓ]) m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)))
            (fun u s => blockEnergyFun (GA[ℓ]) (HA[ℓ]) (compWeight L 1) νS k z
              (F₂ ℓ z (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
                Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) s, u.1))
              (Sol₂ ℓ z (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
                  Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) s,
                flEdat (GA[ℓ]) (HA[ℓ]) (F₂ ℓ z (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀
                  (LocalCover.blockSite k z)) : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) s, u.1))
                  u.1.1 (hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₂ ℓ z)
                    (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
                      Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) s) u.1 u.2))).1
              (u.1, hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₂ ℓ z)
                (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
                  Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) s) u.1 u.2)) ((Lab ℓ).ysite l))
            ((SA[ℓ]).hatOf m₀ p₁ (hp ℓ) Φ)) taylorWeight ((SA[ℓ]).hatOf m₀ p₁ (hp ℓ) Φ) σ
            (e.1 : RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N)
        else 0)
    {F₃ : ∀ ℓ, CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N →
      DecParams (GA[ℓ]) × RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N →
        ((GA[ℓ]).Ω 1 × Fin N → ℂ) × ((GA[ℓ]).Ω 1 → ℂ)}
    {Sol₃ : ∀ ℓ, CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N →
        ((HA[ℓ]).Ω 1 × Fin N → ℂ) × ((HA[ℓ]).Ω 1 → ℂ)}
    {Ev₃ : ∀ ℓ, CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N → Set (CTorus d L (N₁ ℓ) m₁ (k + 1)) →
      RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N × (unitPts (GA[ℓ]) × Fin N → ℂ) → ℂ}
    (hF₃ : ∀ ℓ (a : CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N) (s : DecParams (GA[ℓ]))
      (D : BgData (GA[ℓ]) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA[ℓ]) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA[ℓ]).Ω 1 × Fin N → ℂ)
        (α : (GA[ℓ]).Ω 1 → ℂ), IsDecBg (GA[ℓ]) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃ ℓ a (s, rawOf D) = (φ, α))
    (hSol₃ : ∀ ℓ (a : CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GA[ℓ])) × Edat (HA[ℓ]) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA[ℓ]) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃ ℓ a p).1 = dphi (HA[ℓ]) (Dec2.decG (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1)
          p.2.2.1 p.2.1 (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ ℓ a p).2 ∧
        Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ ℓ a p).2 ∧
        Small (HA[ℓ]) (Sol₃ ℓ a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA[ℓ]) (Sol₃ ℓ a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA[ℓ]) (Sol₃ ℓ a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA[ℓ]).Ω 1 → ℂ, Small (HA[ℓ]) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA[ℓ])) (HA[ℓ]) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA[ℓ]) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ ℓ a p).2))
    (hEv₃ : ∀ ℓ (a : CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N), Ev₃ ℓ a =
      evTerm (fun i : ParIdx (GA[ℓ]) (↑(LocalCover.nbhdF m₀ a.1) :
          Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) => i.1.1)
        (GA[ℓ]) m₀ (X1 (GA[ℓ]) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GA[ℓ]) (HA[ℓ]) a.1 a.2
          (F₃ ℓ a (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ a.1) :
            Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) t, u.1))
          (Sol₃ ℓ a (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ a.1) :
              Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) t,
            flEdat (GA[ℓ]) (HA[ℓ])
              (F₃ ℓ a (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ a.1) :
                Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) t, u.1))
              u.1.1 (hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₃ ℓ a)
                (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ a.1) :
                  Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) t) u.1 u.2))).1
          (u.1, hatPsiF (GA[ℓ]) 1 νS (SA[ℓ]).hG' cc (F₃ ℓ a)
            (extParams (GA[ℓ]) (↑(LocalCover.nbhdF m₀ a.1) :
              Set (CTorus d L (N₁ ℓ) m₁ (k + 1))) t) u.1 u.2)))
    (hanEv₃ : ∀ ℓ (a : CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N)
      (Y : Set (CTorus d L (N₁ ℓ) m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃ ℓ a Y) (XiCRaw (GA[ℓ]) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GA[ℓ]) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hAs : ∀ ℓ, ∀ e ∈ V ℓ, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb ℓ)
      (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b),
      (A ℓ e σ).H l Φ = (A ℓ ((e.1, 0) : physParam N (SA[ℓ])) σ).H l Φ +
        ∑ s : CTorus d L (N₁ ℓ) m₁ (k + 1) × Fin N,
          if (Lab ℓ).ysite l ∈ polyDom (GA[ℓ]) (LocalCover.nbhdF m₀ s.1) m₀ k
              (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃ ℓ s ((Lab ℓ).ysite l)) (fun _ => (1 : ℂ))
              ((SA[ℓ]).hatOf m₀ p₁ (hp ℓ) Φ) ((SA[ℓ]).hatOf m₀ p₁ (hp ℓ) Φ) σ
              (e.1 : RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N)
          else 0)
    (hsrc : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset →
      ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ x, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ m₁) * L ^ (k + 1))
        (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) * L ^ (k + 1)))) →
      ∀ i, (θ (can X) g).2 (bm[ℓ, can X] (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ m₁) *
        L ^ (k + 1)))) - fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ m₁) * L ^ (k + 1)))) i =
        (θ ℓ g).2 x i) :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset, To ℓ g X = To (can X) g X := by
  have hρc : 2 * p₁ ≤ cψ := by
    have h := (div_le_iff₀ hcψ).1 hq
    linarith
  have hLa : 0 < L * aK := Nat.mul_pos (by omega) (cellSide_pos (L := L) m₀ m₁ (k + 1))
  have hef : (L - 1) * aK ≤ L * aK := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hAx' : ∀ ℓ, ∀ e ∈ V ℓ, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb ℓ)
      (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b),
      (A ℓ ((e.1, 0) : physParam N (SA[ℓ])) σ).H l Φ = -(β : ℂ) *
        ∑ z : TA[ℓ], if (Lab ℓ).ysite l ∈ polyDom (GA[ℓ])
            (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SA[ℓ]).hG' cc (F₂ ℓ z) (Sol₂ ℓ z)
            (blockEnergyFun (GA[ℓ]) (HA[ℓ]) (compWeight L 1) νS k z) ∅ 1 0 ((Lab ℓ).ysite l))
            ((SA[ℓ]).hatOf m₀ p₁ (hp ℓ) Φ)) taylorWeight ((SA[ℓ]).hatOf m₀ p₁ (hp ℓ) Φ) σ
            (e.1 : RawData d L (N₁ ℓ * L ^ m₁) (k + 1) N)
        else 0 := fun ℓ e he σ hσ l Φ =>
    (hAx ℓ e he σ hσ l Φ).trans (congrArg (fun x => -(β : ℂ) * x)
      (rayTerm_evTerm_eq_evDec (SA[ℓ]).hG' cc (F₂ ℓ) (Sol₂ ℓ) _ _ _ _ _))
  refine hob_of_obsSum hN2 hk νS β p₁ δ hC hMX hmar hαK hsm hd hL hm₀ hm₁ hN hK26 hside hKL P Q
    can Wd hP hQ hcanK Ycub hYs xs iy hxsb hsp hqS cc hcψ hq hrad hF₁ hSol hEv hdEv hdj θ hθ hp
    Lab ys hys A hκ0 hεH hK Rg hR 𝒰 To hTo hraw ?_ ?_ ?_
  · intro ℓ X g hX hQX hW hg Ds hDs z hz hint Z hZ
    obtain ⟨hn, hn', hDsa⟩ := tieObs_sizes (hK26 ℓ) (hcanK ℓ X hX hQX) (hside ℓ) (hside (can X))
      (hKL ℓ) hDs (cellSide_pos (L := L) m₀ m₁ (k + 1))
    rw [h𝒴v ℓ, h𝒴v (can X)]
    exact mem_obsLabelDomains_recentred_iff hN0 (isLevel_levelGS (by omega) le_rfl)
      (isLevel_levelGS (by omega) le_rfl) (hN ℓ) (hN (can X)) _ _
      (fun μ => dvd_val_intCast (cellSide_dvd (hN ℓ) le_rfl) (hz μ))
      (fun μ => dvd_val_intCast (cellSide_dvd (hN (can X)) le_rfl) (hz μ))
      (by omega) (by omega) Z hZ
  · intro ℓ X g hX hQX hW hg Ds hDs z hz hint σ hσ l l' hlR hl' Φ Φ' hΦ
    obtain ⟨hn, hn', hDsa⟩ := tieObs_sizes (hK26 ℓ) (hcanK ℓ X hX hQX) (hside ℓ) (hside (can X))
      (hKL ℓ) hDs (cellSide_pos (L := L) m₀ m₁ (k + 1))
    exact labelActZero_recentred hN2 hk νS β p₁ δ (hC ℓ) (hC (can X)) hMX hmar hαK hsm hd hL
      hm₀ hm₁ (hN ℓ) (hN (can X)) z hz _ _ rfl rfl (by omega) (by omega) (by omega) (by omega) cc
      hcψ.le hρc hrad (hF₂ ℓ) (hF₂ (can X)) (hSol₂ ℓ) (hSol₂ (can X)) (hp ℓ) (hp (can X)) (Lab ℓ)
      (Lab (can X)) (A ℓ) (A (can X)) (hAx' ℓ) (hAx' (can X)) (θ ℓ g) (θ (can X) g) (hθV ℓ g hg)
      (hθV (can X) g hg) (hθ ℓ g hg) (hθ (can X) g hg) (hraw ℓ X g hX hQX hW hg Ds hDs z hz hint)
      hσ l l' hlR hl' Φ Φ' hΦ
  · intro ℓ X g hX hQX hW hg Ds hDs z hz hint σ hσ l l' hlR hl' Φ Φ' hΦ
    obtain ⟨hn, hn', hDsa⟩ := tieObs_sizes (hK26 ℓ) (hcanK ℓ X hX hQX) (hside ℓ) (hside (can X))
      (hKL ℓ) hDs (cellSide_pos (L := L) m₀ m₁ (k + 1))
    exact labelActSource_recentred hN2 hk νS β p₁ δ (hC ℓ) (hC (can X)) hMX hmar hαK hsm hd hL
      hm₀ hm₁ (hN ℓ) (hN (can X)) z hz _ _ rfl rfl (by omega) (by omega) (by omega) (by omega) cc
      hcψ.le hρc hrad (hF₂ ℓ) (hF₂ (can X)) (hSol₂ ℓ) (hSol₂ (can X)) (hp ℓ) (hp (can X)) (Lab ℓ)
      (Lab (can X)) (A ℓ) (A (can X)) (hAx' ℓ) (hAx' (can X)) (hF₃ ℓ) (hSol₃ ℓ) (hEv₃ ℓ)
      (hanEv₃ ℓ) (hF₃ (can X)) (hSol₃ (can X)) (hEv₃ (can X)) (hanEv₃ (can X)) (hAs ℓ)
      (hAs (can X)) (θ ℓ g) (θ (can X) g) (hθV ℓ g hg) (hθV (can X) g hg) (hθ ℓ g hg)
      (hθ (can X) g hg) (hraw ℓ X g hX hQX hW hg Ds hDs z hz hint)
      (hsrc ℓ X g hX hQX hW hg Ds hDs z hz hint) hσ l l' hlR hl' Φ Φ' hΦ

end ObsTie

end Balaban.Polymer.TwoTorusStep
