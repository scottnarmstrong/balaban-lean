/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsPair
public import Balaban.Polymer.TwoTorusGapIdentFamily
public import Balaban.Polymer.TwoTorusGapObsFull

/-!
# The observable new terms at the gap scale: the exact torus clause (item 24, blocker 7)

`hob_of_obsSum`: the analogue of `hdt_of_detSum` for the observable terms.  The observable terms
`To ℓ g X` on the torus `ℓ` are the coefficients of the observable `obsCoeffParam` at the parameters
`θ ℓ g` and the cubes `Ycub ℓ X` of the cells of the polymer `X` (`hTo`); for a support `X` of the
quarter box that is not wide the terms on `ℓ` and on `can X` are equal, from the pair theorem
`obsCoeffParam_cellSites`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv

section ObsFamily

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

/-- **The exact torus clause of the observable new terms at the gap scale** (item 24, `hob` of
`resum_gapScale_torus_threeTerms`). -/
theorem hob_of_obsSum (hN2 : 2 ≤ N)
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
    (hmemV : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ Z : Set (CTorus d L (N₁ ℓ) m₁ (k + 1)),
      (∀ x ∈ Z, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)))))) → ((fun x => bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) '' Z ∈ (𝒴v (can X)) ↔ Z ∈ (𝒴v ℓ)))
    (hAeq0 : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : (Lb ℓ)) (l' : (Lb (can X))),
      (∀ x ∈ (Lab ℓ).ysite l, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)))))) →
      (Lab (can X)).ysite l' = (fun x => bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) '' (Lab ℓ).ysite l →
      ∀ (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b) (Φ' : ∀ b, ((SA[can X]).blockSplit m₀ (hp (can X))).Ωb b),
      (∀ x, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) →
        Φ' ((SA[can X]).cellOf m₀ (unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1)))))))
          ⟨unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))), rfl⟩ =
          Φ ((SA[ℓ]).cellOf m₀ (unitPt (SA[ℓ]).hG' x)) ⟨unitPt (SA[ℓ]).hG' x, rfl⟩) →
      ((A (can X)) (((θ (can X) g).1, 0) : physParam N (SA[can X])) σ).H l' Φ' = ((A ℓ) (((θ ℓ g).1, 0) : physParam N (SA[ℓ])) σ).H l Φ)
    (hAeqθ : ∀ ℓ X g, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → g ∈ Dset → ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
      ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ (xs ℓ) ∪ sitesOf (Ycub ℓ X), ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : (Lb ℓ)) (l' : (Lb (can X))),
      (∀ x ∈ (Lab ℓ).ysite l, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)))))) →
      (Lab (can X)).ysite l' = (fun x => bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))) '' (Lab ℓ).ysite l →
      ∀ (Φ : ∀ b, ((SA[ℓ]).blockSplit m₀ (hp ℓ)).Ωb b) (Φ' : ∀ b, ((SA[can X]).blockSplit m₀ (hp (can X))).Ωb b),
      (∀ x, InBox d (Ds + (Ds + 1) / 4) (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) →
        Φ' ((SA[can X]).cellOf m₀ (unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1)))))))
          ⟨unitPt (SA[can X]).hG' (bm[ℓ, can X] (x + (fun μ => ((z μ : ℤ) : ZMod (((N₁ ℓ) * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod (((N₁ (can X)) * L ^ m₁) * L ^ (k + 1))))), rfl⟩ =
          Φ ((SA[ℓ]).cellOf m₀ (unitPt (SA[ℓ]).hG' x)) ⟨unitPt (SA[ℓ]).hG' x, rfl⟩) →
      ((A (can X)) (θ (can X) g) σ).H l' Φ' = ((A ℓ) (θ ℓ g) σ).H l Φ)
    :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ Dset, To ℓ g X = To (can X) g X := by
  intro ℓ X hX hQX hW g hg
  have hXc : X ∈ P (can X) :=
    mem_P_can (P := P) (Q := Q) (can := can) (hK26 := hK26) (hP := hP) (hQ := hQ)
      (hcanK := hcanK) ℓ X hX hQX
  have hKK : K ℓ ≤ K (can X) := hcanK ℓ X hX hQX
  have : NeZero aK := ⟨(cellSide_pos (L := L) m₀ m₁ (k + 1)).ne'⟩
  have hapos : 0 < aK := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hXq : ∀ c ∈ (↑X : Set (Fin d → ℤ)), ∀ μ, (c μ).natAbs ≤ K ℓ / 4 := fun c hc μ =>
    (hQ ℓ X).1 hQX c hc μ
  rw [hTo ℓ g X hX hg, hTo (can X) g X hXc hg]
  symm
  obtain ⟨Ds, hDs⟩ : ∃ Ds, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 := ⟨_, rfl⟩
  have hDs1 : Ds + 1 ≤ aK * ((K ℓ - 26) / 25 + 1) := by
    have : 1 ≤ aK * ((K ℓ - 26) / 25 + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  obtain ⟨hn25, hn25', hqn⟩ := compact_site_margins (K := K ℓ) (K' := K (can X)) (cs := aK)
    (Dc := (K ℓ - 26) / 25) (Ds := Ds) (q := aK * (K ℓ / 4 + 1)) (hK26 ℓ) hKK hapos le_rfl hDs1
    (Nat.le_add_right _ _)
  rw [← hside ℓ] at hn25 hqn
  rw [← hside (can X)] at hn25'
  have hDsa : L * aK ≤ Ds + 1 := by
    calc L * aK = aK * L := Nat.mul_comm _ _
      _ ≤ aK * ((K ℓ - 26) / 25 + 1) := Nat.mul_le_mul_left _ (hKL ℓ)
      _ = Ds + 1 := by omega
  have hbm : bm[ℓ, can X] '' sitesOf (Ycub ℓ X) = sitesOf (Ycub (can X) X) := by
    rw [hYs ℓ X hX, hYs (can X) X hXc]
    exact boxMap_image_cellSites (d := d) (n := (N₁ ℓ * L ^ m₁) * L ^ (k + 1))
      (n' := (N₁ (can X) * L ^ m₁) * L ^ (k + 1)) (hside ℓ) (hside (can X)) (hK26 ℓ) hKK
      (↑X : Set (Fin d → ℤ)) hXq
  exact obsCoeffParam_cellSites hN2 hk νS β p₁ δ (hC ℓ) (hC (can X)) hMX hmar hαK hsm hd hL hm₀
    hm₁ (hN ℓ) (hN (can X)) hDsa hn25 hqn (by omega) (by omega) (Ycub ℓ X) (Ycub (can X) X) hbm
    (xs ℓ) (xs (can X)) (hxsb ℓ X hX hQX) iy (hsp ℓ X hX hQX hW Ds hDs) (hqS ℓ X hX hQX hW) cc
    hcψ hq hrad (hF₁ ℓ) (hF₁ (can X)) (hSol ℓ) (hSol (can X)) (hEv ℓ) (hEv (can X)) (hdEv ℓ)
    (hdj ℓ) (hdj (can X)) (θ ℓ g) (θ (can X) g) (hθ ℓ g hg) (hθ (can X) g hg)
    (hraw ℓ X g hX hQX hW hg Ds hDs) (hp ℓ) (hp (can X)) (Lab ℓ) (Lab (can X)) (ys ℓ)
    (ys (can X)) (hys ℓ) (hys (can X)) (hmemV ℓ X g hX hQX hW hg Ds hDs) (A ℓ) (A (can X))
    (hκ0 ℓ) (hκ0 (can X)) (hεH ℓ) (hεH (can X)) (hK ℓ) (hK (can X)) Rg hR 𝒰
    (hAeq0 ℓ X g hX hQX hW hg Ds hDs) (hAeqθ ℓ X g hX hQX hW hg Ds hDs)

end ObsFamily

end Balaban.Polymer.TwoTorusStep
