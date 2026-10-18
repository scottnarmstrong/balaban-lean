/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerDataOrigin
public import Balaban.Polymer.TwoTorusGapDataTower

/-!
# The gap-scale clause at the first gap scale: the data are the unit background (blocker 7)

`towerGapScale_resum_fromTowerG_unitBg`: `towerGapScale_resum_fromTowerG_origin` at the scale where
the background datum of the step is the base datum `(T.step …).D'` (the constant unit field and the
constant `h`, i.e. `unitBg`).  The parameters `θ ℓ g` have the raw data of this datum and the
sources of `σ g`, the source `g` on `ℤ^d` transported to each torus by the centred representatives.
Then the three agreement hypotheses `hrawO`, `hrawR` (raw data on the recentred boxes) and `hsrcO`
(sources on the recentred box) are proved:

* `hrawO`, `hrawR`: both raw data are constant (`rawBoxAgree_unitBg_recentred`);
* `hsrcO`: the recentring vector `z` lies in the box of the site `0`, and a coordinate `a - z` of
  the box of radius `r = Ds + (Ds + 1) / 4` has the same centred representative on both tori since
  `4 r + 1 < aK * K ℓ ≤ aK * K (can X)` (`valMinAbs_recentre`, `four_mul_lt_cells`);
* `hDat` is `(D ℓ).xi`.

At a later scale the raw data are not constant: the induction over the scales has to supply, for
the data `Dat ℓ g` of the scale, the agreement of `rawOf (Dat ℓ g)` and of the sources of `θ ℓ g`
on the recentred boxes of the compact supports containing the cell `0` (the hypotheses `hrawO`,
`hsrcO`, `hrawR` of `towerGapScale_resum_fromTowerG_origin`), that is, the agreement of the
backgrounds of the earlier scales on the two tori.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section UnitBg

/-- **The centred representative of a recentred coordinate.**  If `|z| ≤ r` and the coordinate
`x + z` of the torus `ℤ/n` has centred representative of size at most `r`, then the box map to
`ℤ/n'` followed by the translation by `-z` has the same centred representative as `x`, provided
`4 r + 1 < n, n'`. -/
theorem valMinAbs_recentre {n n' : ℕ} [NeZero n] [NeZero n'] {r : ℕ} (hn : 4 * r + 1 < n)
    (hn' : 4 * r + 1 < n') {zv : ℤ} (hz : |zv| ≤ r) {x : ZMod n}
    (hx : |(x + (zv : ZMod n)).valMinAbs| ≤ r) :
    ((((x + (zv : ZMod n)).valMinAbs : ℤ) : ZMod n') - (zv : ZMod n')).valMinAbs =
      x.valMinAbs := by
  set a := (x + (zv : ZMod n)).valMinAbs with ha
  have h2 : |a - zv| ≤ ((2 * r : ℕ) : ℤ) := by
    push_cast
    calc |a - zv| ≤ |a| + |zv| := abs_sub _ _
      _ ≤ 2 * r := by linarith
  have hxa : x = ((a - zv : ℤ) : ZMod n) := by
    have : ((a : ℤ) : ZMod n) = x + zv := ZMod.coe_valMinAbs _
    push_cast
    rw [this]; ring
  have e1 : x.valMinAbs = a - zv := by
    rw [hxa]
    exact valMinAbs_intCast_of_abs_le (by omega) h2
  have e2 : ((a : ZMod n') - (zv : ZMod n')) = ((a - zv : ℤ) : ZMod n') := by push_cast; rfl
  rw [e1]
  simpa using valMinAbs_intCast_of_abs_le (m := n') (r := 2 * r) (by omega) h2

/-- The arithmetic of the recentring box: `4 (Ds + (Ds + 1) / 4) + 1 < A K` for
`Ds = A ((K - 26) / 25 + 1) - 1`, `0 < A`, `61 ≤ K`. -/
theorem four_mul_lt_cells {A K : ℕ} (hA : 0 < A) (hK : 61 ≤ K) :
    4 * ((A * ((K - 26) / 25 + 1) - 1) + (A * ((K - 26) / 25 + 1) - 1 + 1) / 4) + 1 < A * K := by
  have hq : 5 * ((K - 26) / 25 + 1) ≤ K := by omega
  have h1 : A * (5 * ((K - 26) / 25 + 1)) ≤ A * K := Nat.mul_le_mul_left A hq
  have h2 : 0 < A * ((K - 26) / 25 + 1) := Nat.mul_pos hA (by omega)
  have h3 : A * (5 * ((K - 26) / 25 + 1)) = 5 * (A * ((K - 26) / 25 + 1)) := by ring
  omega

set_option hygiene false in
local notation "ST[" n "]" => StepTowerG.step T k hk n ν β p₁
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
/-- **The gap-scale clause at the first gap scale.**
`towerGapScale_resum_fromTowerG_origin` for the data of the step that are the unit background, with
the sources of `θ ℓ g` the transported `σ g`: the hypotheses on the raw data and the sources on the
recentred boxes are proved. -/
theorem towerGapScale_resum_fromTowerG_unitBg {d L N : ℕ} [NeZero L] {κmin : ℝ}
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
          (iy : Fin N)
          {Dset : Set G} (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
          (_ : ∀ ℓ, ∀ g ∈ Dset, θ ℓ g ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q)
          (σ : G → (Fin d → ℤ) → Fin N → ℂ)
          (_ : ∀ ℓ g x i, (θ ℓ g).2 x i = σ g (fun μ => (x μ).valMinAbs) i)
          (_ : ∀ ℓ, ∀ g ∈ Dset,
            ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N) = rawOf (SA[ℓ]).D')
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
          (∀ ℓ g X, Tt ℓ g X = c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (0 : RootIdx d L (N₁ ℓ) T.m₁ (k + 1)) (θ ℓ g) (Ycub ℓ X) +
            dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (0 : RootIdx d L (N₁ ℓ) T.m₁ (k + 1)) (θ ℓ g) (Ycub ℓ X) +
            mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) (0 : CTorus d L (N₁ ℓ) T.m₁ (k + 1)) iy (θ ℓ g) (Ycub ℓ X)) ∧
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
    towerGapScale_resum_fromTowerG_origin T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨e0, dz, c, mObs, B, hB, hT, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  refine ⟨e0, dz, c, mObs, B, hB, hT, ?_⟩
  intro ι G N₁ _ h3N h5 D K _ hK2 hside P Q can τ hP hQ hτ hcanK Ycub hYs iy Dset θ hθV σ hθsrc
    hθD Ag hAg hAgθ W hWan κ κ₂ lam hκ hκ₂ hlam hrate
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) T.hN
  refine hF N₁ h3N h5 D K hK2 hside P Q can τ hP hQ hτ hcanK Ycub hYs iy θ hθV
    (fun ℓ _ => (SA[ℓ]).D') (fun ℓ g _ => (D ℓ).xi) hθD ?_ ?_ ?_ Ag hAg hAgθ W hWan hκ hκ₂ hlam hrate
  · intro ℓ X g _ _ _ _ _ _ hg Ds _ z _ _
    rw [hθD ℓ g hg, hθD (can X) g hg]
    exact rawBoxAgree_unitBg_recentred hN0 _ _ _
  · intro ℓ X g hK hX hQ' _ _ _ hg Ds hDs z _ hint x hx i
    rw [hθsrc, hθsrc]
    have hx0 : ((0 : CTorus d L (N₁ ℓ) T.m₁ (k + 1)) ∈
        LocalCover.nbhd 1 (0 : CTorus d L (N₁ ℓ) T.m₁ (k + 1))) := by
      have := LocalCover.mem_nbhdF_self (d := d) (L := L) 1 (0 : CTorus d L (N₁ ℓ) T.m₁ (k + 1))
      rwa [← Finset.mem_coe, LocalCover.coe_nbhdF] at this
    have hz0 := hint 0 (Or.inl hx0)
    have hn1 := hside ℓ
    have hn2 := hside (can X)
    have hKc : K ℓ ≤ K (can X) := hcanK ℓ X hX hQ'
    have hApos : 0 < aK := cellSide_pos (L := L) 1 T.m₁ (k + 1)
    have hK61 : 61 ≤ K ℓ := by omega
    have hlt := four_mul_lt_cells hApos hK61
    subst hDs
    have hlt1 : 4 * ((aK * ((K ℓ - 26) / 25 + 1) - 1) +
        (aK * ((K ℓ - 26) / 25 + 1) - 1 + 1) / 4) + 1 <
        (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) := by rw [hn1]; exact hlt
    have hlt2 : 4 * ((aK * ((K ℓ - 26) / 25 + 1) - 1) +
        (aK * ((K ℓ - 26) / 25 + 1) - 1 + 1) / 4) + 1 <
        (N₁ (can X) * L ^ T.m₁) * L ^ (k + 1) :=
      lt_of_lt_of_le hlt (by rw [hn2]; exact Nat.mul_le_mul_left _ hKc)
    congr 1
    funext μ
    have := valMinAbs_recentre hlt1 hlt2 (zv := z μ) (x := x μ)
      (by simpa using hz0 μ) (hx μ)
    exact this
  · intro ℓ X g _ _ _ _ _ _ hg z _ _
    exact rawBoxAgree_unitBg_recentred hN0 _ _ _

end UnitBg

end Balaban.Polymer.TwoTorusStep
