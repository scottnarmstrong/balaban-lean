/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1CoeffFamily
public import Balaban.Inhabited.E1ParamFibreValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The energy coefficient family at the tower takes the physical value on the fibre `h ≡ h₀`

`e1CoeffFamily_fromTower` gives, at a scale of the shared tower (`d = L = 3`, `N = 2`, zero
class), one family of decoupling pairs `(F₁, Sol)`, one label system and one activity `A₀`, chosen
before the root and before the datum, whose coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParam … z … θ) C` are analytic in the
parameter `θ`, local in the raw datum, bounded and supported on rooted polymer sets.

`e1CoeffFamily_value_fromTower` is the same statement with one more clause for the same pairs,
labels and activity: for every root `z` and every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)`
with constant field `h₀`, the local energy term `ℰ₁^{(k+1)}(z)` of the step with the datum `D′`
is `∑_C c z (rawOf D′, 0) C`.

The conclusion of `e1CoeffFamily_fromTower` does not contain the amplitude bounds of the activity
(`0 < ε_H`, `ε_H ≤ stepTheta`) nor the holomorphy of the activity and of the marks for every
configuration, which the interpolation record needs; the proof therefore opens the same
existentials in the same order (`e1MarkParam_pairs_fromTower`, then
`zeroSourceActivity_common_fromTower`), repeats the steps of `e1CoeffFamily_fromTower`, and adds
the value clause by `e1Param_fibre_value_of_fields_fromTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **One energy coefficient family at the tower, with its value on the fibre `h ≡ h₀`.**  Beyond
a threshold `β₀`, at every scale datum there are one family of decoupling pairs `(F₁, Sol)`, a
label system `Lab₀` and an activity `A₀` on the common labels (with its identity for the
interpolation integral at every chart datum), chosen before every root and before every datum, such
that for every root `z` the pairs have the eight clauses, the activity and the marks carry a
`ParamMarkFamily` over `physV`, `ball 0 corrU` and `physCarrier`, and the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParam … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 3 3 T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`;
and, for every datum `D′` of the chart with constant field `h₀`,
(v) the local energy term of the step with the datum `D′` is
`ℰ₁^{(k+1)}(z) = ∑_C c z (rawOf D′, 0) C`. -/
theorem e1CoeffFamily_value_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < (T.step k hk N₁ ν β p₁).p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ D : StepScaleData T k hk N₁ ν β p₁,
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ →
          LabelAct (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 T.marksKc'),
      (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
          (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
        XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
          (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).WoneC
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
            ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub 2 (T.step k hk N₁ ν β p₁).G'), g) (s : ℂ)).H y
              (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) ∧
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
          (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
        Nonempty (ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
          (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A₀
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
            commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
          (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0 T k β p₁)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)
          (Metric.ball (0 : ℂ) corrU) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) ∧
        ∃ c : physParam 2 (T.step k hk N₁ ν β p₁) →
            Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
            (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
              (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
            (fun i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c θ C)
              (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → c θ C = c θ' C) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ‖c θ C‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          ∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
              (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
            XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
              (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
            ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
                (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C := by
  classical
  obtain ⟨βa, CE, CF, hβa3, -, -, hact⟩ := zeroSourceActivity_common_fromTower T hHull hA p
  obtain ⟨β₀, hmax, hR, hbud⟩ := exists_beta0_e1 T hA p βa
  refine ⟨β₀, (le_max_left _ _).trans hmax, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  have hβ3 : 3 ≤ β := ((le_max_left _ _).trans hmax).trans hβ
  have hβpos : 0 < β := by linarith
  have hβa : βa ≤ β := ((le_max_right _ _).trans hmax).trans hβ
  have hRU := hR k hk β hβ p₁ hp hp₁
  obtain ⟨F₁, Sol, hF⟩ := e1MarkParam_pairs_fromTower T D h3N hN hν0.le hν hβpos hp hRU
  obtain ⟨Jr, val, I0, hFd, hεU, hval, hεpos, hamp, hθ, hstep, A, hAeq, hW1, hW2, hcom⟩ :=
    hact k hk N₁ h3N hN ν hν0 hν β hβa p₁ hp hp₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨A0, hA0eq, hana, hdiffA, hcont, hsum, hdat, hWstep, hfam0, -⟩ :=
    hcom (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)
  have hU2 : corrU ≤ 2 := by unfold corrU; norm_num
  have hF0 := corrF0_pos T hk hβpos (show 0 < p₁ from hp)
  have hθ' := hstep
  refine ⟨F₁, Sol, {Y // Y ∈ I0.𝒴}, inferInstance, thickLabels I0.𝒴 I0.dom, _, A0, hdat, ?_⟩
  intro z
  obtain ⟨hP, hne, hmeas, hdb, hholG, hcontG⟩ := hF z
  obtain ⟨hdep, hbnd⟩ := hdb {Y // Y ∈ I0.𝒴} (thickLabels I0.𝒴 I0.dom)
  have hfam : ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
          (commonLabels (thickLabels I0.𝒴 I0.dom) (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A0
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
            commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
          (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0 T k β p₁)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)
          (Metric.ball (0 : ℂ) corrU) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp) := by
    obtain ⟨hA'⟩ := hfam0
    exact { isOpenV := hA'.isOpenV
            isOpenU := Metric.isOpen_ball
            seg := fun s hs => by
              rw [mem_ball_zero_iff]
              refine norm_ofReal_lt_of_mem hs ?_
              unfold corrU
              norm_num
            compact := hA'.compact
            measQ := hA'.measQ
            carried := hA'.carried
            meas := hmeas
            bound := hbnd
            holA := fun y Φ hΦ => (hA'.holA y Φ hΦ).mono
              (Set.prod_mono (subset_refl _) (Metric.ball_subset_ball hU2))
            holG := fun i Φ _ => hholG i Φ
            contA := fun y θ hθ u hu => hA'.contA y θ hθ u (Metric.ball_subset_ball hU2 hu)
            contG := fun i θ hθ u hu => hcontG i θ hθ u hu }
  refine ⟨hP, ⟨hfam⟩, _, fun _ _ => rfl, fun C => ?_, fun D' hDh hD => ?_⟩
  swap
  · exact e1Param_fibre_value_of_fields_fromTower T D (by simpa using h3N) (by norm_num) hβpos
      (S := T.step k hk N₁ ν β p₁) rfl hp (e1Dom_isDj T D) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) z hP (thickLabels I0.𝒴 I0.dom) A0 hεpos hstep hdiffA hdat hmeas
      (fun θ _ => hdep θ) hbnd hholG D' hDh hD
  have hp0 : 0 < p₁ := hp
  have hprob := isProbabilityMeasure_fluctMeasure1 2 hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hlab : ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) z},
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
        ((commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
          (commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z
            i)) :=
    fun i => (bridgeFamily_spec hN1 (by norm_num) (e1Dom_isDj T D) z i.2).2.1
  have hAloc : ∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
          (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, (commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite y ⊆
          Yhat Set.univ (sitesOf C) → (A0 θ (s : ℂ)).H y = (A0 θ' (s : ℂ)).H y := by
    intro C
    subst hA0eq
    subst hAeq
    exact commonAct_zeroSourceAct_hA (T.step k hk N₁ ν β p₁) 1 _ hFd hN1 hp0 zero_le_two hεU
      T.κ0_ent T.marks_K0_le (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)
      (by norm_num) (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two one_pos
      (fun θ => physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ)) C
      (fun θ _ θ' _ h Y hY => physRestrict_thickSet_agree _ _ h hY)
  have hGloc : ∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
          (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z},
        (commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
          (commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z
            i) ⊆ Yhat Set.univ (sitesOf C) →
        (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i (s : ℂ) Φ) =
        (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ' i (s : ℂ) Φ) := by
    intro C θ hθ θ' hθ' h s hs i hi
    have hu : ‖(s : ℂ)‖ < corrU := norm_ofReal_lt_of_mem hs (by unfold corrU; norm_num)
    funext Φ
    rw [e1MarkGParam_of_mem _ _ _ _ hp z T.t θ i (s : ℂ) Φ hθ.1 hu,
      e1MarkGParam_of_mem _ _ _ _ hp z T.t θ' i (s : ℂ) Φ hθ'.1 hu]
    exact markedOutDec_decMarkCorrTerm_raw_congr (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) hP (ρ := p₁) hp0 le_rfl hp T.t_pos _ hθ.1 hθ'.1
      (e1_rad_lt T hk hβpos hp0 hRU hu.le) z Φ (physRestrict_thickSet_agree _ _ h hi)
  have hmain := fun C => paramMarked_analytic_local_bound (m₀ := 1) (j := k + 1) (Ω := Set.univ)
    ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ hN1 le_rfl isPiUnion_univ_K hfam
    (fun θ i s => hdep θ i s) T.marks_hκ0 T.marks_hKc hεpos hne (fun _ => hF0) T.marks_hκ'
    T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') C
    (fun θ => physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ))
    (hAloc C) (hGloc C)
  have hgm : ∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁)), ∀ (i : {Y' // Y' ∈ bridgeFamily 1
      (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      Measurable (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) := hmeas
  refine ⟨(hmain C).1, (hmain C).2.1, fun θ hθ => ?_, fun θ hne0 => ?_⟩
  · exact ((hmain C).2.2 θ hθ).trans (mul_le_mul_of_nonneg_right
      (hbud k hk N₁ h3N ν β hβ p₁ hp hp₁ D z) (Real.exp_pos _).le)
  · exact ⟨mem_of_gsumCoeff_ne_zero_of_labels hN1 ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (A0 θ) _ _ (hgm θ) (hdep θ) (hbnd θ) T.marks_hκ0 T.marks_hKc hεpos (fun _ => hF0)
      T.marks_hκ' T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') hlab hne0,
      (gsumCoeff_ne_zero_active hN1 ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (A0 θ) _ _ (hgm θ) (hdep θ) (hbnd θ) T.marks_hκ0 T.marks_hKc hεpos (fun _ => hF0)
      T.marks_hκ' T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') hne0).2⟩

end Balaban.Inhabited
