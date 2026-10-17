/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerTieObs
public import Balaban.Inhabited.StepIdentityFibreFamiliesCore

/-!
# The observable new terms of the tower step on two tori (blocker 7)

`towerObs_hob_fromTowerG`: at a scale of the general tower with block scale `1`, for a family of
tori `ℓ` with their scale data, the witnesses of `stepIdentity_zeroClass_fibre_fromTowerG_core` are
chosen on every torus; the step identity holds on every torus with the energy family `e0 ℓ` and the
observable coefficient `mObs ℓ`, and the observable coefficient of the site `(xs ℓ, iy)` at a
support `X` of the quarter box that is not wide is the same on the torus `ℓ` and on `can X`:
`mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X) = mObs (can X) (xs (can X)) iy (θ (can X) g) (Ycub (can X) X)`.
This is the specification `hTo` of the gap-scale step (`To ℓ g X = mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X)`,
the formula `obsCoeffParam …` being a clause of the core) together with its exact torus clause
`hob`, with `hEv`, `hmemV`, `hAeq0`, `hAeqθ` discharged by the formulas of the core
(`hob_of_obsLabelFormulas`).  The remaining hypotheses are data of the tori and of the parameters:
the geometry of the gap scale (`hK26`, `hside`, `hKL`, `hP`, `hQ`, `hcanK`, `hYs`, `hxsb`, `hsp`,
`hqS`), the parameters `θ ℓ g` in the chart with sources of the `q`-ball (`hθV`), and the agreement of
their raw data (`hraw`) and of their sources (`hsrc`) on the recentred box.
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
local notation "aK" => cellSide L 1 T.m₁ (k + 1)
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) T.m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L 1 T.m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}

open Classical in
/-- **The observable new terms of the tower step on two tori.**  Beyond the threshold of
`stepIdentity_zeroClass_fibre_fromTowerG_core`, for a family of tori `ℓ` (`L ∣ N₁ ℓ`, `5 < N₁ ℓ`)
with scale data `D ℓ`: there are the energy families `e0 ℓ` and the observable coefficients
`mObs ℓ` of the tower (the witnesses of the core on each torus) such that
* on every torus the step identity of the zero class holds on the fibre `h ≡ h₀`:
  `TstepC(g) = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ∑_U e0 ℓ z (rawOf D′, 0) U
  + ∑_{y,i} g(y,i) ∑_V mObs ℓ y i (rawOf D′, g) V]`;
* for the geometry of a gap scale (cell numbers `K ℓ ≥ 26`, polymers `P ℓ` of the cell torus, the
  quarter box `Q`, the canonical torus `can X`, the wide supports `Wd`, the cubes `Ycub ℓ X` of the
  cells of `X`, a site `xs ℓ` corresponding under the box maps) and parameters `θ ℓ g` of the chart
  with sources in the `q`-ball whose raw data and sources agree on the recentred box, the
  observable coefficient of the site `(xs ℓ, iy)` at a support `X` of the quarter box that is not
  wide is the same on `ℓ` and on `can X`. -/
theorem towerObs_hob_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
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
      ∃ (e0 : ∀ ℓ, RootIdx d L (N₁ ℓ) T.m₁ (k + 1) → physParam N (SA[ℓ]) →
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
        ∀ {G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
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
              mObs (can X) (xs (can X)) iy (θ (can X) g) (Ycub (can X) X) := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    stepIdentity_zeroClass_fibre_fromTowerG_core T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ι N₁ _ h3N h5 ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1 D
  have HH := fun ℓ => H k hk (N₁ ℓ) (h3N ℓ) (h5 ℓ) ν hν0 hν β hβ p₁ hp₁ q hq0 hq1 (D ℓ)
    (ϱ := rhoSepG d L T.m₁) rfl (T.step k hk (N₁ ℓ) ν β p₁) rfl hp0
  choose F₁ Sol Lb hLb Lab₀ εH A₀ e0 Lbo hLbo Labo εHo hεHo Ao mObs hα hroot hamp hlab hsrcF
    hsite hid using HH
  refine ⟨e0, mObs, hid, ?_⟩
  intro G K _ hK26 hside hKL P Q can Wd hP hQ hcanK Ycub hYs xs iy hxsb hsp hqS Dset θ hθV hraw
    hsrc ℓ₀ X hX hQX hW g hg
  choose 𝒴v ys hys h𝒴v F₂ Sol₂ hF₂ hSol₂ hAx using hlab
  choose F₃ Sol₃ Ev₃ hF₃ hSol₃ hEv₃ hanEv₃ hAs using hsrcF
  have hN : ∀ ℓ, L ^ 1 ∣ N₁ ℓ := fun ℓ => by have := h3N ℓ; rwa [hm₀] at this
  have hcov1 : ∀ ℓ, LevelCoversG d L N (N₁ ℓ) T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
      (lvTopG d L (N₁ ℓ) T.m₁ k (rhoSepG d L T.m₁))
      (lvLowG d L (N₁ ℓ) T.m₁ k (rhoSepG d L T.m₁)) 1 := fun ℓ => by
    have h := (D ℓ).covers
    rw [hm₀] at h
    exact h
  have hdj : ∀ ℓ, ∀ Y ∈ obsDomains (SA[ℓ]) (LocalCover.nbhdF 1 (xs ℓ)) 1 k
      (LocalCover.fam 1 (xs ℓ)), IsDj 1 (k + 1) Y := fun ℓ =>
    obsDomains_isDj (X₁f := LocalCover.nbhdF 1 (xs ℓ)) _ T.hd ((hcov1 ℓ).2 (xs ℓ, iy)).1
      ((hcov1 ℓ).2 (xs ℓ, iy)).2.2.1
  choose hR hR1 hRθ Ev hEvx ha hd hb hmk hfam using fun ℓ => hsite ℓ (xs ℓ) iy (hdj ℓ)
  choose Fy Soly hFy hSoly hEvF using hEvx
  have hbU : ∀ ℓ, (SA[ℓ]).betaU = β * (L : ℝ) ^ (k * (d - 2)) := fun ℓ =>
    hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
  simp only [hbU] at hAx hEv₃ hEvF
  have hrad := (D ℓ₀).fl_radius
  rw [hbU ℓ₀] at hrad
  have hcψ0 := (D ℓ₀).cψ_pos
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ0]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ :=
      mul_pos (D ℓ₀).r_pos hp0
    nlinarith [(D ℓ₀).ray_margin]
  exact hob_of_obsLabelFormulas (K := K) T.hN hk ν β p₁ T.δ (fun ℓ => (D ℓ).core) T.large_block
    T.dom_margin T.coer_margin T.δc_small (by have := T.hd; omega) (by have := T.hL; omega) le_rfl
    (by have := T.m₁_four; omega) hN hK26 hside hKL P Q can Wd hP hQ hcanK Ycub hYs xs iy hxsb hsp
    hqS _ hcψ0 hq hrad hFy hSoly hEvF (fun ℓ Y _ => hd ℓ Y) hdj θ
    (fun ℓ g hg => (hθV ℓ g hg).1.1) (fun _ => hp0) Labo ys hys Ao (fun _ => T.κ0_ent)
    (fun ℓ => (hεHo ℓ).le) (fun _ => le_refl _) _ (hR ℓ₀) (ball (0 : ℂ) (3 / 2))
    (fun ℓ g X => mObs ℓ (xs ℓ) iy (θ ℓ g) (Ycub ℓ X)) (fun ℓ g X _ _ => hmk ℓ (θ ℓ g) (Ycub ℓ X))
    hraw (Nat.lt_of_lt_of_le two_pos T.hN) h𝒴v hF₂ hSol₂ hθV hAx hF₃ hSol₃ hEv₃ hanEv₃ hAs hsrc
    ℓ₀ X hX hQX hW g hg

end ObsTower

end Balaban.Polymer.TwoTorusStep
