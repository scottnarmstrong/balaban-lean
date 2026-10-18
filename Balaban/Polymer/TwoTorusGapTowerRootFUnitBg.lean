/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerRootFClause
public import Balaban.Polymer.TwoTorusGapTowerDataUnitBg

/-!
# Root-F's two-torus clause at the first gap scale (blocker 7)

`towerGapScale_rootFClause_unitBg`: `towerGapScale_rootFClause` for the data of the first gap scale
(`Dat = (T.step …).D'`, the unit background; sources of `θ ℓ g` equal to `σ g` evaluated at the
centred representative, the transport of Root-F).  The agreement of the raw data on the recentred
boxes is `rawBoxAgree_unitBg_recentred`; the agreement of the sources is the centred
representative of a recentred coordinate (`valMinAbs_recentre_gen`), where the translation `z` is
bounded by the box radius plus the position `a aK` of the site in the cell `a`
(`recentre_arith`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section RootFUnit

/-- The centred representative of a recentred coordinate: if `|z| ≤ R` and the coordinate
`x + z` of `ℤ/n` has centred representative of size at most `r`, then the box map to `ℤ/n'`
followed by the translation by `-z` has the same centred representative as `x`, provided
`2 (R + r) + 1 < n, n'`. -/
theorem valMinAbs_recentre_gen {n n' R r : ℕ} [NeZero n] [NeZero n'] (hn : 2 * (R + r) + 1 < n)
    (hn' : 2 * (R + r) + 1 < n') {zv : ℤ} (hz : |zv| ≤ R) {x : ZMod n}
    (hx : |(x + (zv : ZMod n)).valMinAbs| ≤ r) :
    ((((x + (zv : ZMod n)).valMinAbs : ℤ) : ZMod n') - (zv : ZMod n')).valMinAbs =
      x.valMinAbs := by
  set b := (x + (zv : ZMod n)).valMinAbs with hb
  have h2 : |b - zv| ≤ ((R + r : ℕ) : ℤ) := by
    push_cast
    calc |b - zv| ≤ |b| + |zv| := abs_sub _ _
      _ ≤ R + r := by linarith
  have hxa : x = ((b - zv : ℤ) : ZMod n) := by
    have : ((b : ℤ) : ZMod n) = x + zv := ZMod.coe_valMinAbs _
    push_cast
    rw [this]; ring
  have e1 : x.valMinAbs = b - zv := by
    rw [hxa]
    exact valMinAbs_intCast_of_abs_le hn h2
  have e2 : ((b : ZMod n') - (zv : ZMod n')) = ((b - zv : ℤ) : ZMod n') := by push_cast; rfl
  rw [e1, e2]
  exact valMinAbs_intCast_of_abs_le hn' h2

/-- The arithmetic of the recentring box at the site `a aK`: with `Ds = A ((K - 26) / 25 + 1) - 1`,
`61 ≤ K` and `4 b < K`, `2 ((r + b A) + r) + 1 < A K` for `r = Ds + (Ds + 1) / 4`. -/
theorem recentre_arith {A K b Ds : ℕ} (hA : 0 < A) (hK : 61 ≤ K) (hb : 4 * b < K)
    (hDs : Ds = A * ((K - 26) / 25 + 1) - 1) :
    2 * ((Ds + (Ds + 1) / 4 + b * A) + (Ds + (Ds + 1) / 4)) + 1 < A * K := by
  have hq : 25 * ((K - 26) / 25 + 1) + 1 ≤ K := by omega
  have hS : 0 < A * ((K - 26) / 25 + 1) := Nat.mul_pos hA (by omega)
  have h1 : 25 * (A * ((K - 26) / 25 + 1)) + A ≤ A * K := by
    nlinarith [Nat.mul_le_mul_left A hq]
  have h2 : 4 * (b * A) < A * K := by nlinarith
  omega

section Unit

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
local notation "zrA[" ℓ "]" => (fun μ => ((a μ * ((L ^ (1 + T.m₁) : ℕ) : ℤ) : ℤ) :
  ZMod (N₁ ℓ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) : RootIdx d L (N₁ ℓ) T.m₁ (k + 1))
set_option hygiene false in
local notation "xsA[" ℓ "]" => (fun μ => ((a μ * ((cellSide L 1 T.m₁ (k + 1) : ℕ) : ℤ) : ℤ) :
  ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1))) : CTorus d L (N₁ ℓ) T.m₁ (k + 1))
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) T.m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L 1 T.m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}

open Classical in
/-- **Root-F's two-torus clause at the first gap scale.**
`towerGapScale_rootFClause` for the data of the step that are the unit background, with the
sources of `θ ℓ g` the transported `σ g` (`σ g` evaluated at the centred representative): the
hypotheses on the raw data and the sources on the recentred boxes are proved. -/
theorem towerGapScale_rootFClause_unitBg {d L N : ℕ} [NeZero L] {κmin : ℝ}
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
          (a : Fin d → ℤ) (_ : ∀ ℓ μ, 4 * |a μ| < (K ℓ : ℤ))
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
          (∀ ℓ g X, Tt ℓ g X = c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) zrA[ℓ] (θ ℓ g) (Ycub ℓ X) +
            dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) zrA[ℓ] (θ ℓ g) (Ycub ℓ X) +
            mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) xsA[ℓ] iy (θ ℓ g) (Ycub ℓ X)) ∧
        ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
        ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
          (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
          (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then Tt (can X) g X else
            Tt ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
              (Tt ℓ g X₀ - Tt (can X₀) g X₀)) ∧
          (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, Tt ℓ g X) ∧
          (∀ (ℓ ℓ' : ι) g (A : Finset (Fin d → ℤ)), a ∈ A →
            (∀ y ∈ A, ∀ μ, 4 * |y μ| < (K ℓ : ℤ) ∧ 4 * |y μ| < (K ℓ' : ℤ)) →
            Tn ℓ g A = Tn ℓ' g A) ∧
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
    towerGapScale_rootFClause T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨e0, dz, c, mObs, B, hB, hT, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  refine ⟨e0, dz, c, mObs, B, hB, hT, ?_⟩
  intro ι G N₁ _ h3N h5 D K _ hK2 hside a ha P Q can τ hP hQ hτ hcanK Ycub hYs iy Dset θ hθV σ
    hθsrc hθD Ag hAg hAgθ W hWan κ κ₂ lam hκ hκ₂ hlam hrate
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) T.hN
  refine hF N₁ h3N h5 D K hK2 hside a ha P Q can τ hP hQ hτ hcanK Ycub hYs iy θ hθV
    (fun ℓ _ => (SA[ℓ]).D') (fun ℓ g _ => (D ℓ).xi) hθD ?_ ?_ ?_ Ag hAg hAgθ W hWan hκ hκ₂ hlam
    hrate
  · intro ℓ X g _ _ _ _ _ _ hg Ds _ z _ _
    rw [hθD ℓ g hg, hθD (can X) g hg]
    exact rawBoxAgree_unitBg_recentred hN0 _ _ _
  · intro ℓ X g hK hX hQ' _ _ _ hg Ds hDs z _ hint x hx i
    rw [hθsrc, hθsrc]
    have hx0 : xsA[ℓ] ∈ LocalCover.nbhd 1 xsA[ℓ] := by
      have := LocalCover.mem_nbhdF_self (d := d) (L := L) 1 xsA[ℓ]
      rwa [← Finset.mem_coe, LocalCover.coe_nbhdF] at this
    have hz0 := hint xsA[ℓ] (Or.inl hx0)
    have hn1 := hside ℓ
    have hn2 := hside (can X)
    have hKc : K ℓ ≤ K (can X) := hcanK ℓ X hX hQ'
    have hApos : 0 < aK := cellSide_pos (L := L) 1 T.m₁ (k + 1)
    have hK61 : 61 ≤ K ℓ := by omega
    congr 1
    funext μ
    have hb : 4 * (a μ).natAbs < K ℓ := by
      have := ha ℓ μ
      rcases abs_cases (a μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hlt := recentre_arith hApos hK61 hb hDs
    have hvm : ((xsA[ℓ] μ)).valMinAbs = a μ * (aK : ℤ) :=
      valMinAbs_mul_cell hApos (hside ℓ) (hK2 ℓ) (ha ℓ μ)
    have h0 := hz0 μ
    rw [hvm] at h0
    generalize hr : Ds + (Ds + 1) / 4 = r at hlt h0 hx
    have e : |a μ * (aK : ℤ)| = (((a μ).natAbs * aK : ℕ) : ℤ) := by
      rw [abs_mul, Int.abs_eq_natAbs, Nat.abs_cast]; push_cast; rfl
    have hz : |z μ| ≤ (((r + (a μ).natAbs * aK : ℕ)) : ℤ) := by
      have h1 := abs_sub (a μ * (aK : ℤ) + z μ) (a μ * (aK : ℤ))
      have h2 : (a μ * (aK : ℤ) + z μ) - a μ * (aK : ℤ) = z μ := by ring
      rw [h2, e] at h1
      push_cast at h1 ⊢
      linarith
    have hlt1 : 2 * ((r + (a μ).natAbs * aK) + r) + 1 < (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) := by
      rw [hn1]; exact hlt
    have hlt2 : 2 * ((r + (a μ).natAbs * aK) + r) + 1 < (N₁ (can X) * L ^ T.m₁) * L ^ (k + 1) :=
      lt_of_lt_of_le hlt1 (by rw [hn1, hn2]; exact Nat.mul_le_mul_left _ hKc)
    exact valMinAbs_recentre_gen hlt1 hlt2 hz (hx μ)
  · intro ℓ X g _ _ _ _ _ _ hg z _ _
    exact rawBoxAgree_unitBg_recentred hN0 _ _ _

end Unit

end RootFUnit

end Balaban.Polymer.TwoTorusStep
