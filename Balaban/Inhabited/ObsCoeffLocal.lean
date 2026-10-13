/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffFamily
public import Balaban.Inhabited.ObsSourceLocal
public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Fluctuation.MarkIntTermAnalytic

/-!
# Locality of the observable coefficient in the datum and the source

The coefficient `obsCoeffParam … θ T` of the observable is the resummed sum of the kernel with the
first-order terms plus the coefficient of the remainder marks.  It reads the parameter
`θ = (raw datum, source)` only through

* the kernel entries `hker θ i T₁` at the sets `T₁ ⊆ T`,
* the activity `Aact θ s 1` at the labels whose sites lie in `Ŷ(sitesOf T)`, `s ∈ [0,1]`,
* the remainder marks `Gr θ i s` at the anchors whose sites lie in `Ŷ(sitesOf T)`.

* `obsCoeffParam_congr_of_local`: the generic congruence from these three premises.
* `Yhat_univ_eq`: on the whole torus `Ŷ(S) = S`.
* `obsHker_hatCoeff_local`: the kernel premise from the locality of the expansion `Ev` in the
  raw datum.
* `tiltActObs_H_local_of_labels`: the activity premise on the observable labels from the
  locality of the activity on the labels of the family.
* `obsGrFam_local`: the remainder-mark premise.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

omit [NeZero N₁] [NeZero L] in
/-- On the whole torus the enlarged region `Ŷ(S)` is `S`. -/
theorem Yhat_univ_eq (S : Set (CTorus d L N₁ m₁ K)) :
    Yhat (Set.univ : Set (CTorus d L N₁ m₁ K)) S = S := by
  ext y
  simp [Yhat]

/-- **Locality of the observable coefficient.**  Let `θ, θ'` be two parameters and `T` a finite
set of cubes.  If the kernel entries at the sets `T₁ ⊆ T`, the activities `Aact · s 1`
(`s ∈ [0,1]`) at the labels with sites in `Ŷ(sitesOf T)`, and the remainder marks `Gr · i s` at
the anchors with sites in `Ŷ(sitesOf T)` agree at `θ` and `θ'`, then `obsCoeffParam … θ T =
obsCoeffParam … θ' T`.  The first-order marks `G1 i` do not depend on the parameter; the
block-dependence of `G1 i` and of `Gr · i s` on the blocks of their labels is the standard one. -/
theorem obsCoeffParam_congr_of_local {E ι ι' Lb : Type*} [Fintype ι] [Fintype ι'] [Fintype Lb]
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
    (Aact : E → ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (y1 : ι → Lb) (G1 : ι → (∀ b, Ωb b) → ℂ) (hker : E → ι → Finset 𝔅 → ℂ)
    (yr : ι' → Lb) (Gr : E → ι' → ℂ → (∀ b, Ωb b) → ℂ)
    (hG1dep : ∀ i, DepOn (blocksOf m₀ j Ω (Lab.ysite (y1 i))) (G1 i))
    (hGrdep : ∀ θ i s, DepOn (blocksOf m₀ j Ω (Lab.ysite (yr i))) (Gr θ i s))
    (T : Finset 𝔅) {θ θ' : E}
    (hk : ∀ i (T₁ : Finset 𝔅), T₁ ⊆ T → hker θ i T₁ = hker θ' i T₁)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab.ysite y ⊆ Yhat Ω (sitesOf T) →
      (Aact θ (s : ℂ) 1).H y = (Aact θ' (s : ℂ) 1).H y)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, Lab.ysite (yr i) ⊆ Yhat Ω (sitesOf T) →
      Gr θ i (s : ℂ) = Gr θ' i (s : ℂ)) :
    obsCoeffParam μ Aact y1 G1 hker yr Gr θ T = obsCoeffParam μ Aact y1 G1 hker yr Gr θ' T := by
  classical
  unfold obsCoeffParam
  refine congrArg₂ (· + ·) ?_ ?_
  · unfold kernelMarkSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T₁ _ =>
      Finset.sum_congr rfl fun S' _ => ?_
    by_cases h : T₁ ∪ S' = T
    · have h1 : T₁ ⊆ T := h ▸ Finset.subset_union_left
      have h2 : S' ⊆ T := h ▸ Finset.subset_union_right
      simp only [h, ite_true]
      rw [hk i T₁ h1]
      refine congrArg₂ (· * ·) rfl ?_
      exact markIntTerm_param_congr_of_local μ Aact (y1 i) (fun _ => G1 i)
        (fun _ => hG1dep i) S' (θ := θ) (θ' := θ')
        (fun s hs y hy => hA s hs y
          (ysite_subset_Yhat hN hj hΩ Lab y (hy.trans h2)))
        (fun _ => rfl)
    · simp [h]
  · exact gsumCoeff_param_congr_of_local μ hN hj hΩ (fun θ t => Aact θ t 1) yr Gr hGrdep T hA hG

end Generic

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

section Restrict

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **Equal restrictions give the two agreements.**  If two parameters have the same restriction
(raw datum and source, `physRestrict`) to `thickSet S.G' Z`, their raw data agree on
`thickSet S.G' Z` and their sources agree on `Z`. -/
theorem agree_of_physRestrict_thickSet (Z : Set (CTorus d L N₁ m₁ (k + 1)))
    {θ θ' : physParam N S}
    (h : physRestrict (N := N) (thickSet S.G' Z) (physIncl N S θ) =
      physRestrict (thickSet S.G' Z) (physIncl N S θ')) :
    agreeOn (thickSet S.G' Z) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∧ ∀ x ∈ Z, θ.2 x = θ'.2 x :=
  physAgΘThick_of_restrict S (Y := Z) subset_rfl h

end Restrict

section Kernel

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ} {cψ : ℝ}
  {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
  {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ}

/-- The unit vectors `Pi.single m 1` have entries of norm at most `1`. -/
theorem norm_obsUnitVec_le (m : ObsMarkIdx S) (p : S.U × Fin N) : ‖obsUnitVec S m p‖ ≤ 1 := by
  unfold obsUnitVec
  by_cases h : p = m
  · subst h; simp
  · simp [h]

/-- **Locality of the kernel in the raw datum.**  Let `Ev Y` be local in the raw datum on the
thickening of `Y` (clause `hd` of `obsEv_fromTower`).  Two raw data `r, r' ∈ A` that agree on
`thickSet Z` give the same kernel entry `obsHker … T₁` for every `T₁` whose sites lie in `Z`:
the domains `Y` with label `T₁` are the sets `sitesOf T₁`. -/
theorem obsHker_hatCoeff_local (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hd : ∀ Y, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    {r r' : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hr : r ∈ A) (hr' : r' ∈ A)
    {Z : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn (thickSet S.G' Z) r r')
    (m : ObsMarkIdx S)
    {T₁ : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT₁ : sitesOf T₁ ⊆ Z) :
    obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T₁ =
      obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r' (obsUnitVec S m)) m₀ T₁ := by
  classical
  unfold obsHker
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [Finset.mem_filter] at hY
  have hYT : Y ⊆ Z := by
    have := sitesOf_obsRowLabel hN (hdj Y hY.1)
    rw [hY.2] at this
    exact this ▸ hT₁
  have hag' : agreeOn (thickSet S.G' Y) r r' := agreeOn_mono (thickSet_mono hYT) hag
  unfold hatCoeff
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(isOpen_ball (x := (0 : ℂ)) (ε := cψ)).mem_nhds
    (show (0 : ℂ) ∈ ball (0 : ℂ) cψ by simpa using hcψ)] with ζ hζ
  have hmem : ∀ p, ‖(ζ • obsUnitVec S m) p‖ ≤ cψ := by
    intro p
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    have h1 : ‖ζ‖ < cψ := by simpa using hζ
    calc ‖ζ‖ * ‖obsUnitVec S m p‖ ≤ ‖ζ‖ * 1 := by
          gcongr; exact norm_obsUnitVec_le m p
      _ ≤ cψ := by linarith
  exact hd Y (r, ζ • obsUnitVec S m) ⟨hr, hmem⟩ (r', ζ • obsUnitVec S m) ⟨hr', hmem⟩
    ⟨hag', fun _ _ _ => rfl⟩

end Kernel

section Activity

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {Lb : Type} [Fintype Lb]
variable {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ Lb} {εH κH κ0 Kc : ℝ}
  {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ → Type}
  [∀ b, MeasurableSpace (Ωb b)] {E₁ E₂ : Type*} [Zero E₂]
  (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
  {hN : L ^ m₀ ∣ N₁} {hκ0 : aEnt d L + 1 ≤ κ0} {hεH : 0 ≤ εH}
  {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y}
  {Kobs : ℝ} {hK : Kc + Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs}

/-- **The activity premise on the observable labels.**  Let `Z` be a set of sites.  If the
activities of the labels of the family `A` whose sites lie in `Z` agree at `e, e'` (both at the
zero-source parameters `(e.1, 0), (e'.1, 0)` and at `e, e'`), then the tilted activity on the
observable labels `obsLab (Lab.sum Lab) hdj` agrees at `e, e'`, for every `t, σ`, on every label
whose sites lie in `Z`.  The labels outside `Lab.sum Lab` have zero activity. -/
theorem tiltActObs_H_local_of_labels {e e' : E₁ × E₂} (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    (Z : Set (CTorus d L N₁ m₁ (k + 1)))
    (hz0 : ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z → (A (e.1, 0) u).H w = (A (e'.1, 0) u).H w)
    (hz1 : ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z → (A e u).H w = (A e' u).H w)
    (t σ : ℂ) (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs)
    (hy : (obsLab (Lab.sum Lab) hdj).ysite y ⊆ Z) :
    (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 e t σ).H y =
      (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 e' t σ).H y := by
  refine tiltActObs_H_local A Rg hR 𝒰 t σ y ?_
  refine physActObs_H_local A t y fun z hz => ?_
  subst hz
  have hzZ : (Lab.sum Lab).ysite z ⊆ Z := by simpa [obsLab] using hy
  refine physAct_H_local A t z ?_ ?_
  · intro u w hw
    subst hw
    exact hz0 u w (by simpa using hzZ)
  · intro w hw
    subst hw
    exact hz1 t w (by simpa using hzZ)

end Activity

section Remainder

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ} {hp : 0 < S.p₁} {cψ : ℝ}
  {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
  {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ}
  {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}

/-- **Locality of the remainder marks in the raw datum.**  For parameters whose raw data lie in `A`
and agree on `thickSet Z`, the remainder mark of every index whose domain lies in `Z` is the same
(the dummy index has the mark `0`).  The marks do not read the source. -/
theorem obsGrFam_local
    (hd : ∀ Y, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4) {θ θ' : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A)
    {Z : Set (CTorus d L N₁ m₁ (k + 1))}
    (hag : agreeOn (thickSet S.G' Z) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (idx : RemIdx 𝒴) (hidx : ∀ Y, idx = some Y → Y.1 ⊆ Z) (u : ℂ) :
    obsGrFam S m₀ hp Ev 𝒴 A θ idx u = obsGrFam S m₀ hp Ev 𝒴 A θ' idx u := by
  rw [obsGrFam_of_mem hθ, obsGrFam_of_mem hθ']
  cases idx with
  | none => rfl
  | some Y =>
    funext Φ
    exact obsGrRawC_local (fun Y _ => hd Y) hcψ hq hθ hθ' Y
      (agreeOn_mono (thickSet_mono (hidx Y rfl)) hag) u Φ

end Remainder

section Tower

variable {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleData T k hk N₁ ν β p₁)
  (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
  (hp : 0 < S.p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (h3N : 3 ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)

include Dsc hS in
/-- **Locality of the observable coefficient at the tower.**  Let `Ev` be a sharp-hat family local
in the raw datum (clause `hd` of `obsEv_fromTower`) and let the activity `Aact` of the family of
labels be local in the pair (raw datum, source): for `e, e'` of `physVq` that agree on the
thickening of `Z` in the datum and on `Z` in the source, the activities of the labels with sites in
`Z` agree, at the parameters `(e.1, 0), (e'.1, 0)` and at `e, e'`.  Then for `θ, θ'` of `physVq`
whose raw data agree on `thickSet S.G' (sitesOf T')` and whose sources agree on `sitesOf T'`, the
coefficients `obsCoeffParam … T'` agree.  (The region of the datum is the thickening of the sites
of `T'` by `resDep`; the region of the source is the sites of `T'`; the kernel, the first-order
terms and the remainder marks read the datum only, the activity reads both.) -/
theorem obsCoeffParam_local_of_Ev {q : ℝ}
    (hAloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
      agreeOn (thickSet S.G' Z) (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
        (Aact ((e.1, 0) : physParam 2 S) u).H w = (Aact ((e'.1, 0) : physParam 2 S) u).H w ∧
        (Aact e u).H w = (Aact e' u).H w)
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    {θ θ' : physParam 2 S} (hθ : θ ∈ physVq S S.a₁ S.ν T.t q) (hθ' : θ' ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (hr : agreeOn (thickSet S.G' (sitesOf T')) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
      (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))
    (hg : ∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) :
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T' := by
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hcψ := Dsc.cψ_pos
  have hp₁ : S.p₁ = p₁ := by subst hS; rfl
  have hq : S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k) ≤ 1 / 4 := by
    rw [hp₁, div_le_iff₀ hcψ]
    have : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ := mul_pos Dsc.r_pos (hp₁ ▸ hp)
    nlinarith [Dsc.ray_margin]
  have hcell : ∀ m : ObsMarkIdx S,
      obsMarkCube S 1 m ∈ blocksOf (d := 3) (L := 3) (N₁ := N₁)
        (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite
          (obsY1 1 S (Lb ⊕ Lb) (obsDomains S
            (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)) :=
    fun m => obsCubeLab_mem 1 (obsMarkCube S 1 m)
  have ha1 : S.a₁ = 1 := by subst hS; rfl
  have hν1 : S.ν = ν := by subst hS; rfl
  have hr0 : (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
      XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t := by
    have := physV_fst_mem_xiCRaw (S := S) hθ.1
    rwa [ha1, hν1] at this
  have hr0' : (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
      XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t := by
    have := physV_fst_mem_xiCRaw (S := S) hθ'.1
    rwa [ha1, hν1] at this
  refine obsCoeffParam_congr_of_local (S.blockSplit 1 hp).μ hN3 (le_refl (k + 1))
    isPiUnion_univ_K
    (Lab := obsLab (Lab.sum Lab) hdj)
    (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
    (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
    (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
    (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
    (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
    (fun m => depOn_blockMarkC m.1 m.2 (hcell m))
    (fun θ i u => depOn_obsGrFam_all (hp := hp) hN3 hcψ hq hdj (fun Y _ => hd Y) _
      (fun Y => Sum.inl (Sum.inr Y)) _ (fun Y => rfl) θ i u)
    T' (θ := θ) (θ' := θ') ?_ ?_ ?_
  · intro m T₁ hT₁
    exact obsHker_hatCoeff_local hN3 hcψ hdj hd hr0 hr0' hr m (sitesOf_mono hT₁)
  · intro s _ y' hy'
    rw [Yhat_univ_eq] at hy'
    exact tiltActObs_H_local_of_labels Aact Rg hR (ball (0 : ℂ) (3 / 2)) (sitesOf T')
      (fun u w hw => (hAloc θ hθ θ' hθ' _ hr hg u w hw).1)
      (fun u w hw => (hAloc θ hθ θ' hθ' _ hr hg u w hw).2) _ _ y' hy'
  · intro s _ i hi
    rw [Yhat_univ_eq] at hi
    refine obsGrFam_local hd hcψ hq hr0 hr0' hr _ ?_ _
    intro Y hY
    subst hY
    exact hi

end Tower

end Balaban.Inhabited
