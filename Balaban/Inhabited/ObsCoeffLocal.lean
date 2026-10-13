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
  physAgΘ_of_restrict S (Y := Z) subset_rfl h

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

section TowerLocal

open Set

/-- **Locality of the activity family in the datum and the source, with the activity family of
`obsTiltLabels_fromTower`.**  The statement of `obsTiltLabels_fromTower` with one more clause on
the activity `A`: for `e, e'` of `physVq` whose raw data agree on `thickSet S.G' Z` and whose
sources agree on `Z`, the activities of the labels with sites in `Z` agree, at the zero-source
parameters and at `e, e'`, for every `u`. -/
theorem obsTiltLabels_local_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s Θ : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2)
    (hΘ : 0 < Θ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∀ {Kc : ℝ}, K0 3 3 T.κ0 ≤ Kc →
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc),
        (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
          ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
          agreeOn (thickSet S.G' Z) (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
            (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
          ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
            (A ((e.1, 0) : physParam 2 S) u).H w = (A ((e'.1, 0) : physParam 2 S) u).H w ∧
            (A e u).H w = (A e' u).H w) ∧
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
          ∀ {𝒴obs : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))}
            (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y) {Kobs : ℝ}
            (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs),
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (physActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) ∧
          ∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
            (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
          ∑ y, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
            Rg hR (ball (0 : ℂ) (3 / 2))
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ) 1).H y
            ((S.blockSplit 1 hp).restr x)) ∧
        ∀ {𝒴obs : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1)))}
          (hdj : ∀ Y ∈ 𝒴obs, IsDj 1 (k + 1) Y) {Kobs : ℝ}
          (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs),
        (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
            (physActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              r.1 r.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg) y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ × ℂ =>
            (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2.1 r.2.2).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ (ball (0 : ℂ) (3 / 2) ×ˢ ball (0 : ℂ) Rg))) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg → ∀ e ∈ physVq S S.a₁ S.ν T.t q,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le
              hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t 1).H y Φ) (ball (0 : ℂ) (3 / 2))) ∧
          (∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
              hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t σ).H y Φ) (ball (0 : ℂ) Rg)) ∧
          (∀ t y Φ, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
            hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) e t 0).H y Φ = 0)) ∧
        (∀ (Rg : ℝ) (hR : 0 ≤ Rg), 1 < Rg →
          (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
            (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
              Rg hR (ball (0 : ℂ) (3 / 2)) r.1 r.2 1).H y Φ)
            (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) (3 / 2))) ∧
          (∀ y, ∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ u ∈ ball (0 : ℂ) (3 / 2),
            ContinuousOn ((tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
              hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ u 1).H y)
              (physCarrier S 1 hp))) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q →
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤ Θ ∧
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
            (∀ y Φ, DifferentiableOn ℂ
              (fun t => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) t 1).H y Φ)
              (ball (0 : ℂ) (3 / 2))) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ y Φ, DifferentiableOn ℂ
              (fun σ => (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) σ).H y Φ)
              (ball (0 : ℂ) (obsRg CR s (p : ℝ) (β * 3 ^ k)))) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ y Φ,
              (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) 0).H y Φ = 0) ∧
            (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
                S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x =
              ∑ y, (tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent
                hεH.le hdj hK (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (r : ℂ) 1).H y
                ((S.blockSplit 1 hp).restr x))) := by
  classical
  obtain ⟨β₁, CE, CF, hβ₁, hCE, hCF, hfam⟩ := activityFamilyAnalytic_fromTower T hA p
  obtain ⟨b₀, hb₀, hb⟩ := obsTilt_of_physAct.{0} (CR := CR) (CU := CE + CF) (s := s)
    (p := (p : ℝ)) (Θ := Θ) hCR (by positivity) hs0 hs hΘ
  refine ⟨max (max β₁ b₀) 3, CE, CF, le_max_right _ _, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp Kc hKc
  have hβ₁' : β₁ ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hβb₀ : b₀ ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hβ3 : 3 ≤ β := le_trans (le_max_right _ _) hβ
  have hH : BgHyp 3 3 (k + 1) (rhoSep T.m₁) (compWeight 3 S.a₁) S.ν := by
    subst hS
    exact bgHyp_lv (k := k) T.m₁ hνpos.le hν
  have hXi : XiCData S.G' S.a S.ν (k + 1) 1 T.t S.D' := by
    subst hS
    exact D.xi
  obtain ⟨Jr, val, 𝒴, Tt, I, -, -, -, -, -, -, hF, hεU, hεpos, hε4, hrest⟩ :=
    hfam k hk N₁ h3N hN ν hνpos hν β hβ₁' p₁ hp0 hp₁ q hq0 hq D S hS hp
  obtain ⟨A, hAeq, hhol, hcont, -, -, -, -, h7, h8, -, -, -, -⟩ := hrest hKc
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hsub : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ((e.1, 0) : physParam 2 S) ∈
      physVq S S.a₁ S.ν T.t q := fun e he =>
    fst_zero_mem_physVq S (physVq_subset S _ _ _ _ he) hq0
  have hV := isOpen_physVq S S.a₁ S.ν T.t q hH
  have h𝒰R : ball (0 : ℂ) (3 / 2) ⊆ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num)
  have hR2 : (1 : ℝ) < 2 := by norm_num
  have hseg : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → (r : ℂ) ∈ ball (0 : ℂ) (3 / 2) := fun r hr => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    linarith [hr.2]
  -- the identity with the physical activity, from the two fibre identities of the family
  have hae : ∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
      ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
      (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (1 : ℝ) x +
        (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
      ∑ y, (physAct A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
        ((S.blockSplit 1 hp).restr x) := by
    filter_upwards [h7, h8] with x hx7 hx8
    intro D' hDh hX g hg t ht
    have e7 := hx7 D' hDh hX 1 ⟨zero_le_one, le_rfl⟩
    have e8 := hx8 D' hDh hX g hg t ht
    simp only [Complex.ofReal_one, one_pow, one_mul] at e7
    rw [physAct_total]
    dsimp only
    rw [e7, e8]
    ring
  -- the amplitude
  have hb1 : (1 : ℝ) ≤ β * 3 ^ k := by
    have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hbe : Real.exp 1 ≤ β * 3 ^ k := by
    have := Real.exp_one_lt_three
    have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hbb : b₀ ≤ β * 3 ^ k := by
    have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hlog : 0 ≤ Real.log (β * 3 ^ k) := Real.log_nonneg hb1
  have hsq : 0 ≤ Real.sqrt (β * 3 ^ k) := Real.sqrt_nonneg _
  have hamp : 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
      CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    linarith
  have hεH : 0 < 2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) := by linarith
  have hCFle : q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ≤
      CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    refine div_le_div_of_nonneg_right ?_ hsq
    have h0 : 0 ≤ CF * (Real.log (β * 3 ^ k)) ^ p := mul_nonneg hCF.le (pow_nonneg hlog p)
    calc q * CF * (Real.log (β * 3 ^ k)) ^ p = q * (CF * (Real.log (β * 3 ^ k)) ^ p) := by ring
      _ ≤ 1 * (CF * (Real.log (β * 3 ^ k)) ^ p) := mul_le_mul_of_nonneg_right hq h0
      _ = _ := one_mul _
  have hεb : max (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) + 2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
      (CE + CF) * obsW (p : ℝ) (β * 3 ^ k) ^ 3 / Real.sqrt (β * 3 ^ k) := by
    rw [max_add_self_eq hεH.le]
    exact obs_eps_le_tilt_form hCF.le hbe (hamp.trans (by linarith))
  have hloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
      agreeOn (thickSet S.G' Z) (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : {Y // Y ∈ I.𝒴}), (thickLabels I.𝒴 I.dom).ysite w ⊆ Z →
        (A ((e.1, 0) : physParam 2 S) u).H w = (A ((e'.1, 0) : physParam 2 S) u).H w ∧
        (A e u).H w = (A e' u).H w := by
    intro e he e' he' Z hr hg u w hw
    subst hAeq
    exact ⟨labelActFamilyOn_local_scaled S 1 _ hF hN3 hp0 (by norm_num) hεU T.κ0_ent hKc
        (hsub e he) (hsub e' he') w (agreeOn_mono (thickSet_mono hw) hr) (fun _ _ => rfl) u,
      labelActFamilyOn_local_scaled S 1 _ hF hN3 hp0 (by norm_num) hεU T.κ0_ent hKc he he' w
        (agreeOn_mono (thickSet_mono hw) hr) (fun x hx => hg x (hw hx)) u⟩
  refine ⟨_, inferInstance, _, _, hεH, A, hloc, hamp, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    intro D' hDh hX g hg t ht 𝒴obs hdj Kobs hK
    have hphys := hx D' hDh hX g hg t ht
    refine ⟨?_, fun Rg hR hRg => ?_⟩
    · rw [physActObs_total]
      exact hphys
    · rw [tiltActObs_total_one A hN3 T.κ0_ent (by linarith) hdj hK hR hRg
        (norm_ofReal_lt_of_mem ht (by norm_num : (1 : ℝ) < 3 / 2) |> fun h => by simpa using h)]
      exact hphys
  · intro 𝒴obs hdj Kobs hK
    refine ⟨fun y Φ => physActObs_analyticOnNhd hR2 hsub hhol y Φ,
      fun Rg hR y Φ => tiltActObs_analyticOnNhd hR hR2 hV isOpen_ball h𝒰R hsub hhol y Φ,
      fun Rg hR hRg e he => tiltActObs_fields hR hRg hR2 h𝒰R hsub hhol he, ?_, ?_⟩
    · intro Rg hR hRg
      exact ⟨fun y Φ _ => tiltActObs_holA hR hRg hR2 hV isOpen_ball h𝒰R hsub hhol y Φ,
        fun y θ hθ u hu => (tiltActObs_continuous hR hR2 h𝒰R hsub
          (fun e he u hu => hcont e he u (by simpa using hu)) hθ hu 1 y).continuousOn⟩
    · intro g hg
      have he0 : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
          physVq S S.a₁ S.ν T.t q :=
        ⟨(mk_mem_physFibre S S.hh₀ hXi (g := g) (lt_of_lt_of_le hg hq)).1, hg⟩
      exact hb (β * 3 ^ k) hbb (S.blockSplit 1 hp) _
        (physActObs A hN3 T.κ0_ent hεH.le hdj hK ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ :
          rawSub 2 S.G'), g)) (ball (0 : ℂ) (3 / 2))
        (fun r x => S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
          S.WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x)
        hεb hseg
        (fun y Φ => (physActObs_differentiableOn hR2 hsub hhol he0 y Φ).mono h𝒰R)
        (fun r hr => hae.mono fun x hx => by
          rw [physActObs_total]
          exact hx S.D' S.hh₀ hXi g hg r hr)


/-- **The coefficient family of the observable at the tower, with its locality in the datum and
the source.**  The statement of `obsCoeffFamily_fromTower` with one more clause for every finite set
`T'` of cubes: for `θ, θ'` of `physVq` whose raw data agree on `thickSet S.G' (sitesOf T')` and whose
sources agree on `sitesOf T'`, `obsCoeffParam … θ T' = obsCoeffParam … θ' T'`.  The remaining
clauses are those of `obsCoeffFamily_fromTower` (from which the first paragraph is taken):


Thresholds `β₀, C_E, C_F` are those of `obsTiltLabels_fromTower` for `Θ = stepTheta 3 3 K_obs (2 κ_dec - 1) κ₀ κ'`
with `K_c = K₀ + 1`, `K_obs = K_c + K_c + K₀ + K₀`; `R_g = obsRg CR s p (β 3^k)`.  The labels
`Lab`, the activity `A` and `ε_H` are those of `obsTiltLabels_fromTower` and the family `Ev`
is the sharp-hat family of `obsEv_fromTower` built on the label system `Lab.sum Lab`.  For every
finite set `T'` of cubes: the first-order terms, the kernel sum, the remainder coefficient and
`obsCoeffParam` are analytic on `physVq … q`; for `θ` there, `obsCoeffParam … θ T'` is bounded by
`(B₁ + B₂) e^{-λ dExt T'}` (`λ = min (min (2 κ_dec, κ') - κ₀ - 1) κ'`) and vanishes unless the root cube
of the observable site lies in `T'` and the sites of `T'` form a polymer domain. -/
theorem obsCoeffFamily_local_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        2 * εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
          1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
          obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
            stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁))
            (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
          (LocalCover.fam 1 y)) m)
        (fun _ _ _ => blockMarkC S 1 hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)))
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
            (rootCube (m₀ := 1) (blockIndex y))))
        (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2)
        (physVq S S.a₁ S.ν T.t q) (ball (0 : ℂ) (3 / 2)) (physCarrier S 1 hp))) ∧
      ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ)
        (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (blockMarkC S 1 hp m.1 m.2) S')
        (physVq S S.a₁ S.ν T.t q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (fun m S' => markIntTerm (S.blockSplit 1 hp).μ ((fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ) (obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
        (blockMarkC S 1 hp m.1 m.2) S') T') (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit 1 hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) T')
      (physVq S S.a₁ S.ν T.t q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit 1 hp).μ (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVq S S.a₁ S.ν T.t q) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
          ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q),
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ (physVq S S.a₁ S.ν T.t q), ∀ θ' ∈ (physVq S S.a₁ S.ν T.t q),
        agreeOn (thickSet S.G' (sitesOf T')) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) →
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
        obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T'))
    := by
  classical
  have hK0 := T.marks_K0_pos
  have hc1 : 0 < c1 3 3 := by linarith [one_le_c1 3 3]
  have hKo : 0 < (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0 := by linarith
  have hΘ : 0 < stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ' :=
    div_pos one_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKo 3)) hc1)
      (Real.exp_pos _))
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsTiltLabels_local_fromTower T hA p hCR hs0 hs hΘ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hAloc, hεb, -, hrest⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp (Kc := K0 3 3 T.κ0 + 1) (by linarith)
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, fun y i hdj => ?_⟩
  obtain ⟨-, -, A3, A4, A5⟩ := hrest hdj (le_refl _)
  obtain ⟨h1, hεΘ, hR, -⟩ := A5 0 (by simpa using hq0)
  refine ⟨hR, h1, hεΘ, ?_⟩
  have hhol := (A4 _ hR h1).1
  have hcont := (A4 _ hR h1).2
  have hσ := fun e he => (A3 _ hR h1 e he).2.1
  have hzero := fun e he => (A3 _ hR h1 e he).2.2
  obtain ⟨Ev, ha, hd, hb, hD, fam, hT'⟩ := obsCoeffParam_fromTower T k hk N₁ ν β p₁ Dsc S hS hp y
    h3N Lab hεH A hdj (le_refl _) _ hR hN hνpos hν h1 (le_refl _) hhol hcont hεΘ i
  refine ⟨Ev, ha, hd, hb, hD, fam, fun T' => ⟨(hT' T').1, (hT' T').2.1, (hT' T').2.2.1,
    (hT' T').2.2.2, fun θ hθ => ?_, fun θ hθ => ?_, fun θ hθ θ' hθ' hr hg => ?_⟩⟩
  · exact obsCoeffParam_bound_of_Ev T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH A hdj (le_refl _) _
      hR h1 (le_refl _) hσ hzero hεΘ Ev ha hd hb (fun D hD' => (hD D hD').1) θ hθ T'
  · exact obsCoeffParam_support_of_Ev T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH A hdj (le_refl _) _
      hR h1 (le_refl _) hεΘ Ev ha hd hb (fun D hD' => (hD D hD').1) θ hθ T'
  · exact obsCoeffParam_local_of_Ev T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH A hdj (le_refl _) _
      hR hAloc Ev hd hθ hθ' T' hr hg


end TowerLocal

end Balaban.Inhabited
