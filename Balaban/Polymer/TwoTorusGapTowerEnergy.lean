/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyCells
public import Balaban.Inhabited.StepIdentityFibreExplicitCore
public import Balaban.Polymer.TwoTorusGapTowerTieNew

/-!
# The energy coefficient of the tower step on two tori (blocker 7)

* `gsumCoeff_commonLabels_congr`: the interpolation coefficient on the common labels depends only on
  the label system (label type, labels, amplitude and activity up to `HEq`).
* `towerLab_margin`: the label margin of `mem_obsLabelDomains_recentred_iff` at a compact support.
* `towerEnergyCoef_twoTorus_fromTowerG`: for the witnesses of
  `stepIdentity_zeroClass_fibre_fromTowerG_explicitCore` on a family of tori, the step identity,
  `e0 = dz + c`, and the clause `hen` of the gap scale for the mark coefficient `c` of a root:
  `c ℓ (zr ℓ) (θ ℓ g) (Ycub ℓ X) = c (can X) (zr (can X)) (θ (can X) g) (Ycub (can X) X)` for supports
  of the quarter box that are not wide, from the explicit direct terms of the core and
  `gsumCoeff_e1_cellSites`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section Congr

/-- **The interpolation coefficient on the common labels depends only on the label system.**  If the
label types, the label systems, the amplitudes and the activities agree (`HEq`), the coefficients
with the bridge anchors of the root `z` and the marks `G` agree. -/
theorem gsumCoeff_commonLabels_congr {d L N₁ m₁ K m₀ : ℕ} [NeZero N₁] [NeZero L] {β : Type*}
    [Fintype β]
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {E : Type*} {Lb Lb' : Type} [hLb : Fintype Lb] [hLb' : Fintype Lb'] (h : Lb = Lb')
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb}
    {Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb'}
    (hLab : HEq Lab Lab') (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y)
    {εH εH' κH κ0 Kc : ℝ} (hε : εH = εH')
    {A : E → ℂ → LabelAct (commonLabels Lab hN hL reads dom hdom) Ωb εH κH κ0 Kc}
    {A' : E → ℂ → LabelAct (commonLabels Lab' hN hL reads dom hdom) Ωb εH' κH κ0 Kc}
    (hA : HEq A A') (θ : E) (z : RootIdx d L N₁ m₁ K)
    (G : {Y' // Y' ∈ bridgeFamily m₀ reads dom z} → ℂ → (∀ b, Ωb b) → ℂ)
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    gsumCoeff μ (commonLabels Lab hN hL reads dom hdom) (A θ)
        (fun i => commonAnchor Lb reads dom z i) G C =
      gsumCoeff μ (commonLabels Lab' hN hL reads dom hdom) (A' θ)
        (fun i => commonAnchor Lb' reads dom z i) G C := by
  subst h hε
  obtain rfl : hLb = hLb' := Subsingleton.elim _ _
  obtain rfl := eq_of_heq hLab
  obtain rfl := eq_of_heq hA
  rfl

end Congr

section Margin

/-- **The label margin of a compact support.**  For `36 ≤ K`, `Dc ≤ (K - 36) / 25`,
`L ≤ (K - 26) / 25 + 1`, `4 L^(k+1) ≤ a_K` and `Ds = a_K (Dc + 1) - 1`, the label margin of
`mem_obsLabelDomains_recentred_iff` at the radius `Ds + (Ds + 1) / 4 + 2 L^(k+1)` holds below
`a_K K`. -/
theorem towerLab_margin {L aK K Dc Ds Lk : ℕ} (hK : 36 ≤ K) (hD : Dc ≤ (K - 36) / 25)
    (hKL : L ≤ (K - 26) / 25 + 1) (ha : 0 < aK) (h4 : 4 * Lk ≤ aK) (hDs : Ds = aK * (Dc + 1) - 1) :
    2 * ((Ds + (Ds + 1) / 4 + 2 * Lk) + 2 * ((L - 1) * aK + L * aK)) + 5 * (L * aK) < aK * K := by
  have h1 : Ds + 1 ≤ aK * (Dc + 1) := by
    have : 1 ≤ aK * (Dc + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have h2 : (L - 1) * aK ≤ L * aK := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have h3 : L * aK ≤ aK * ((K - 26) / 25 + 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hKL
  have h5 : 4 * (Dc + 1) + 2 + 13 * ((K - 26) / 25 + 1) < K := by omega
  have h6 : aK * (4 * (Dc + 1) + 2 + 13 * ((K - 26) / 25 + 1)) < aK * K :=
    Nat.mul_lt_mul_of_pos_left h5 ha
  have h7 : aK * (4 * (Dc + 1) + 2 + 13 * ((K - 26) / 25 + 1)) =
      4 * (aK * (Dc + 1)) + 2 * aK + 13 * (aK * ((K - 26) / 25 + 1)) := by ring
  omega

end Margin

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
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    stepIdentity_zeroClass_fibre_fromTowerG_explicitCore T hm₀ hhull hA p hCR hs0 hs
  obtain ⟨β₁, hβ₁, hR, -⟩ := exists_beta0_e1G T hm₀ hA p β₀
  refine ⟨β₁, CE, CF, (le_max_left _ _).trans hβ₁, hCE, hCF, ?_⟩
  intro k hk ι N₁ _ h3N h5 ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1 D
  have hβ0 : β₀ ≤ β := ((le_max_right _ _).trans hβ₁).trans hβ
  have HH := fun ℓ => H k hk (N₁ ℓ) (h3N ℓ) (h5 ℓ) ν hν0 hν β hβ0 p₁ hp₁ q hq0 hq1 (D ℓ)
    (ϱ := rhoSepG d L T.m₁) rfl (T.step k hk (N₁ ℓ) ν β p₁) rfl hp0
  choose F₁ Sol Lb hLb Lab₀ εH A₀ e0 Lbo hLbo Labo εHo hεHo Ao mObs hα hroot hamp hlab hsrcF
    hsite hid using HH
  choose hP hsp hdp hF c hc1 hc2 hcv dz hd1 hd2 he0 he2 hev hEdet using hroot
  refine ⟨e0, dz, c, mObs, hid, he0, ?_⟩
  intro G K _ hK36 Dc hDc hside hKL P Q can Wd hQ hcanK zr hzr Ycub hYs Dset θ hθV hspX hqX hraw
    ℓ X hX hQX hW g hg
  have hm1 : 1 ≤ T.m₁ := by have := T.m₁_four; omega
  have hd : 0 < d := by have := T.hd; omega
  have hN : ∀ ℓ, L ^ 1 ∣ N₁ ℓ := fun ℓ => by have := h3N ℓ; rwa [hm₀] at this
  have hbU : ∀ ℓ, (SA[ℓ]).betaU = β * (L : ℝ) ^ (k * (d - 2)) := fun ℓ =>
    hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ
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
  have hRU := hR k hk β hβ p₁ hp0 hp₁
  have hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k 1 T.κ p₁
      ((((SA[ℓ]).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
    intro u hu
    have h := e1_rad_ltG (N₁ := N₁ ℓ) (ϱ := rhoSepG d L T.m₁) (ν := ν) T hk
      (by linarith [(le_max_left _ _).trans hβ₁]) hp0 hRU (u := u) (by linarith)
    rw [norm_zero, add_zero] at h
    exact h
  have hzr' := hzr ℓ X hX hQX
  rw [hzr']
  obtain ⟨E0, -, -, val, I0, hFd, hεU, hrest⟩ := hEdet ℓ (zr ℓ)
  obtain ⟨hLbeq, hεeq, hLab, hrest⟩ := hrest
  have hAeq := hrest.1
  obtain ⟨h𝒴, F₂, Sol₂, hF₂, hSol₂, hTt⟩ := hrest.2
  obtain ⟨E0', -, -, val', I0', hFd', hεU', hrest'⟩ := hEdet (can X) (bc[ℓ, can X] (zr ℓ))
  obtain ⟨hLbeq', hεeq', hLab', hrest'⟩ := hrest'
  have hAeq' := hrest'.1
  obtain ⟨h𝒴', F₂', Sol₂', hF₂', hSol₂', hTt'⟩ := hrest'.2
  rw [hc1 ℓ (zr ℓ), hc1 (can X) _, gsumCoeff_commonLabels_congr _ hLbeq hLab _ _ _ _ _ hεeq hAeq,
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
    (fun b => (hsp ℓ (zr ℓ) b).1) (fun b => (hsp (can X) _ b).1) (fun b => (hsp ℓ (zr ℓ) b).2)
    (fun b => (hsp (can X) _ b).2) hd (hN ℓ) (hN (can X)) hm1 (by have := hK36 ℓ; omega) hcanK'
    (hside ℓ) (hside (can X)) (Dc := Dc ℓ) (by have := hDc ℓ; omega) rfl
    (X := (↑X : Set (Fin d → ℤ))) (fun c hc μ => (hQ ℓ X).1 hQX c hc μ) (Ycub ℓ X) (Ycub (can X) X)
    (hYs ℓ X) (hYs (can X) X) (zr ℓ) (hspX ℓ X g hX hQX hW hg) (hqX ℓ X g hX hQX hW hg) hqn hsl hsl'
    hlab hlab' (θ ℓ g) (θ (can X) g) (hθV ℓ g hg).1 (hθV (can X) g hg).1
    (hraw ℓ X g hX hQX hW hg) hp0 hp0 hp0 hum (hdp ℓ (zr ℓ) (θ ℓ g)) (by have := T.hL; omega)
    (e1DomG_isDj_of_eq T hm₀ (D ℓ) rfl rfl) (e1DomG_isDj_of_eq T hm₀ (D (can X)) rfl rfl) I0 I0' hFd
    hFd' hp0 le_rfl hεU T.κ0_two T.marks_K0_le (fst_zero_mem_physVq (SA[ℓ]) (hθV ℓ g hg) one_pos)
    (fst_zero_mem_physVq (SA[can X]) (hθV (can X) g hg) one_pos) _ hcψ0.le hρc hrad hF₂ hF₂' hSol₂
    hSol₂' h𝒴 h𝒴'
    (fun Y x w σ Θ => (hTt Y x w σ Θ).trans (congrArg (fun t => -(((SA[ℓ]).β : ℝ) : ℂ) * t)
      (rayTerm_evTerm_eq_evDec (SA[ℓ]).hG' _ F₂ Sol₂ Y w.1 x.1 σ Θ)))
    (fun Y x w σ Θ => (hTt' Y x w σ Θ).trans (congrArg (fun t => -(((SA[can X]).β : ℝ) : ℂ) * t)
      (rayTerm_evTerm_eq_evDec (SA[can X]).hG' _ F₂' Sol₂' Y w.1 x.1 σ Θ)))

end EnergyTower

end Balaban.Polymer.TwoTorusStep
