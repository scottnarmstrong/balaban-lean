/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffAnalytic
public import Balaban.Fluctuation.ObsMarksAssembly
public import Balaban.Fluctuation.ObsIntegrandBridge
public import Balaban.Inhabited.ObsMarksFromTower
public import Balaban.Inhabited.Thm31bFromTower

/-!
# The coefficient of the observable at a chart datum and a source

For a chart datum `D` and a parameter `θ = (rawOf D, g)`, the three parts of the parameterized
coefficient `obsCoeffParam` are the explicit expressions of which the fixed-datum record of
`obsMarks_of_tilt` is built (`ObsMarkHalf` of `obsMarkHalves_of_sharpHat`, with `Lab = obsLab …`):

* kernel: `i T ↦ obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T`  (`hker` of the record);
* first-order terms: `i S' ↦ markIntTerm μ A (y1 i) (blockMark S m₀ hp i.1 i.2) S'`
  (`E1` of the record, `G1 i = blockMark …`);
* remainder: `gsumCoeff μ Lab (fun t => A t 1) yr (obsGr S m₀ hp Ev D 𝒴) T`
  (`Erem` of the record, `Gr = obsGr …`).

The parameterized side uses `hatCoeff (Ev Y) θ.1 (obsUnitVec S i)`, `blockMarkC` and `obsGrFam`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

section Fibre

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
  (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))

/-- **(i) The kernel at `θ = (rawOf D, g)`**: the kernel of the parameterized coefficient is the
kernel `hker i T = obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T` of the record. -/
theorem obsKernel_fibre (D : BgData S.G' N) {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) :
    (fun (i : ObsMarkIdx S) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ)) =>
      obsHker 𝒴 (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        (obsUnitVec S i)) m₀ T) =
    fun i T => obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T := by
  funext i T
  rw [hθ]
  rfl

variable {Lb : Type*} [Fintype Lb] {εH κH κ0 Kc : ℝ}
  {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ Lb}

open Classical in
/-- **(ii) The first-order terms**: the term with the clamped mark `blockMarkC` is the term of the
record, whose mark is `blockMark`, for every activity. -/
theorem markIntTerm_blockMarkC_eq (Act : ℂ → ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (y0 : Lb) (u : S.U) (a : Fin N)
    (S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    markIntTerm (S.blockSplit m₀ hp).μ Act y0 (blockMarkC S m₀ hp u a) S' =
      markIntTerm (S.blockSplit m₀ hp).μ Act y0 (blockMark S m₀ hp u a) S' :=
  markIntTerm_congr_ae _ Act y0 S' (ae_blockMarkC_eq u a)

open Classical in
/-- **(iii) The remainder coefficient** at `θ` with raw datum `rawOf D`: the coefficient with the
family `obsGrFam` is the coefficient `Erem` of the record, with the marks `obsGr`. -/
theorem gsumCoeff_obsGrFam_eq (A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (Act : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc) (y0 : RemIdx 𝒴 → Lb)
    (D : BgData S.G' N) {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) (hD : rawOf D ∈ A)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    gsumCoeff (S.blockSplit m₀ hp).μ Lab Act y0 (obsGrFam S m₀ hp Ev 𝒴 A θ) T =
      gsumCoeff (S.blockSplit m₀ hp).μ Lab Act y0 (obsGr S m₀ hp Ev D 𝒴) T :=
  (gsumCoeff_obsGr_eq_obsGrFam (Ev := Ev) (𝒴 := 𝒴) Act y0 D hθ hD T).symm

open Classical in
/-- **The three parts together**: at `θ` with raw datum `rawOf D` the parameterized coefficient is
`kernelMarkSum (fun i T => obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T)
  (fun i S' => markIntTerm μ (Aact θ) (y1 i) (blockMark S m₀ hp i.1 i.2) S') T
  + gsumCoeff μ Lab (fun t => Aact θ t 1) yr (obsGr S m₀ hp Ev D 𝒴) T`,
that is `kernelMarkSum I.hker I.E1 T + I.Erem T` for the record `I` built by `obsMarks_of_tilt`
from the same `Ev` and the activity `Aact θ`. -/
theorem obsCoeffParam_fibre (A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (Aact : physParam N S → ℂ → ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (y1 : ObsMarkIdx S → Lb) (yr : RemIdx 𝒴 → Lb)
    (D : BgData S.G' N) {θ : physParam N S}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) (hD : rawOf D ∈ A)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    obsCoeffParam (S.blockSplit m₀ hp).μ Aact y1 (fun i => blockMarkC S m₀ hp i.1 i.2)
      (fun θ i T' => obsHker 𝒴 (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec S i)) m₀ T')
      yr (fun θ => obsGrFam S m₀ hp Ev 𝒴 A θ) θ T =
    kernelMarkSum (fun (i : ObsMarkIdx S) T' => obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T')
      (fun i S' => markIntTerm (S.blockSplit m₀ hp).μ (Aact θ) (y1 i)
        (blockMark S m₀ hp i.1 i.2) S') T +
    gsumCoeff (S.blockSplit m₀ hp).μ Lab (fun t => Aact θ t 1) yr
      (obsGr S m₀ hp Ev D 𝒴) T := by
  unfold obsCoeffParam
  beta_reduce
  rw [obsKernel_fibre S m₀ Ev 𝒴 D hθ, gsumCoeff_obsGrFam_eq S m₀ hp Ev 𝒴 A _ yr D hθ hD T]
  rw [kernelMarkSum_markIntTerm_congr_ae (S.blockSplit m₀ hp).μ (Aact θ) y1
    (fun i T' => obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T')
    (G := fun i : ObsMarkIdx S => blockMarkC S m₀ hp i.1 i.2)
    (G' := fun i : ObsMarkIdx S => blockMark S m₀ hp i.1 i.2)
    (fun i => ae_blockMarkC_eq i.1 i.2) T]

end Fibre

section Record

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

open Classical in
/-- **The record `ObsMarks` of `obsMarks_of_tilt` for a given `Ev`.**  The construction of
`obsMarks_of_tilt` after its call of `obsMarkHalves_of_sharpHat`, with the family `Ev` and its
two clauses `ObsMarkHalf`, `ObsRayIdentity` (at the datum `D`) as arguments; the record is
built from the same fields.  Besides the record, the conclusion gives its coefficient
`obsCoeff I T` as the explicit expression `kernelMarkSum (obsHker 𝒴 (obsRowCoeff S Ev D ·) m₀)
(markIntTerm μ A (obsY1 ·) (blockMark …)) T + gsumCoeff μ _ (A · 1) yr (obsGr S m₀ hp Ev D 𝒴) T`. -/
theorem obsRecord_of_halves {Lb₀ : Type} [Fintype Lb₀]
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hN : L ^ m₀ ∣ N₁)
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
    (D : BgData S.G' N) (F : (S.U × Fin N → ℂ) → ℂ)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    {cψ C0 Ch κh κ0 κH : ℝ} (hCh : 0 ≤ Ch) (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0h : κ0 ≤ κh)
    (hhalf : ObsMarkHalf S m₀ hp Ev D 𝒴 (obsLab Lab₀ hdj) cψ C0 κH κ0 Ch κh bx)
    (hid : ObsRayIdentity S m₀ hp F Ev D 𝒴)
    (W : ℝ → S.E → ℂ) {εH κ' Kc' Rσ : ℝ}
    (𝒰 : Set ℂ) (hRσ : 1 < Rσ) (hOpen : IsOpen 𝒰)
    (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (h𝒰 : 𝒰 ⊆ ball (0 : ℂ) (3 / 2))
    (A : ℂ → ℂ → LabelAct (obsLab Lab₀ hdj) (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc')
    (holt : ∀ y Φ, DifferentiableOn ℂ (fun t => (A t 1).H y Φ) 𝒰)
    (holσ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ,
      DifferentiableOn ℂ (fun σ => (A (s : ℂ) σ).H y Φ) (ball (0 : ℂ) Rσ))
    (zero : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, (A (s : ℂ) 0).H y Φ = 0)
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      W s x = ∑ y, (A (s : ℂ) 1).H y ((S.blockSplit m₀ hp).restr x))
    (hKc : K0 d L κ0 + 1 ≤ Kc') (hεpos : 0 < εH) (hκ'0 : 0 ≤ κ') (hκ0' : κ0 ≤ κ')
    (hκH' : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    ∃ I : ObsMarks S.nuFl (S.blockSplit m₀ hp) W (fun t x => obsRayFun S F x t) bx,
      ∀ T, obsCoeff I T =
        kernelMarkSum (fun (i : ObsMarkIdx S) T' => obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T')
          (fun i S' => markIntTerm (S.blockSplit m₀ hp).μ A (obsY1 m₀ S Lb₀ 𝒴 i)
            (blockMark S m₀ hp i.1 i.2) S') T +
        gsumCoeff (S.blockSplit m₀ hp).μ (obsLab Lab₀ hdj) (fun t => A t 1)
          (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx))
          (obsGr S m₀ hp Ev D 𝒴) T := by
  obtain ⟨hmeas1, hdep1, -, hbound1, hmean1, hFm, hbm, hcount, hbh, hsh, hxh, hrf⟩ := hhalf
  obtain ⟨hc0, hboundr, hmeasr, hdepr, hholr, hxr, -, -⟩ := hrf
  exact ⟨{
    Lb := ObsLb Lb₀ m₀ 𝒴
    fin := inferInstance
    Lab := obsLab Lab₀ hdj
    εH := εH, κH := κH, κG := κH, κ0 := κ0, κ' := κ', Kc := Kc'
    hN := hN, Rσ := Rσ, hRσ := hRσ, 𝒰 := 𝒰, isOpen := hOpen, seg := hseg
    A := A, holt := holt, holσ := holσ, zero := zero, hW := hW
    ι1 := ObsMarkIdx S
    fin1 := inferInstance
    y1 := obsY1 m₀ S Lb₀ 𝒴
    G1 := fun i => blockMark S m₀ hp i.1 i.2
    meas1 := hmeas1, dep1 := hdep1
    F1 := fun _ => S.p₁, hF1 := fun _ => hp
    bound1 := hbound1, mean1 := hmean1
    Fm := S.p₁, hFm := hFm
    bm := obsMarkCube S m₀, hbm := hbm
    nmax := ((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ), hnmax := Nat.cast_nonneg _
    hcount := hcount
    hker := fun i T => obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T
    Ch := Ch, κh := κh, hCh := hCh
    bound_h := hbh, supp_h := hsh, x_h := hxh, hκh := hκ0h, hFm0 := hp.le
    ιr := RemIdx 𝒴
    finr := inferInstance
    nonemptyr := ⟨none⟩
    yr := obsRemLab _ (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx)
    Gr := obsGr S m₀ hp Ev D 𝒴, measr := hmeasr, depr := hdepr
    Fr := fun _ => 8 * C0 * (S.p₁ / cψ) ^ 2
    hFr := fun _ => hc0, boundr := hboundr
    holGr := fun r Φ => (hholr r Φ).mono h𝒰
    x_r := hxr
    hκ0 := hκ0, hKc := hKc, hεpos := hεpos, hκ' := hκ'0, hκ0' := hκ0'
    hκG := le_rfl, hκ := hκH', hε := hε
    hF := hid }, fun T => rfl⟩

end Record

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- **The value of the observable coefficient at every chart datum and source, from one `Ev` and
one activity.**  (Statement: see the module docstring.) -/
theorem obsCoeff_fibreValue_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ (Dsc : StepScaleData T k hk N₁ ν β p₁),
      let S := T.step k hk N₁ ν β p₁;
      ∀ hp : 0 < S.p₁, ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1))
        (hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k)),
        1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
        obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH ≤
          stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' ∧
        ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
            RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
          (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)})) ∧
          (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}, ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
            AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
          (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
            ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
              Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
          ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
            ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i', ‖g x' i'‖ < q →
              (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit 1 hp).μ
                  (fun (θ : physParam 2 S) (t σ : ℂ) => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le (obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1) (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
                  (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
                  (fun m => blockMarkC S 1 hp m.1 m.2)
                  (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y' => hatCoeff (Ev Y')
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) (obsUnitVec S m)) 1 T'')
                  (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y' => Sum.inl (Sum.inr Y'))
                    (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))))
                  (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ)
                  ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) T' := by
  classical
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : ℝ, Θ = stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) +
      K0 3 3 T.κ0 + K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' := ⟨_, rfl⟩
  have hK0 : 0 < K0 3 3 T.κ0 := T.marks_K0_pos
  have hΘ : 0 < Θ := by
    rw [hΘdef]; unfold stepTheta; have := one_le_c1 3 3; positivity
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, hfam⟩ := obsTiltLabels_fromTower T hA p hCR hs0 hs hΘ
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hp y i
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, hamp, hae, h2⟩ := hfam k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0
    hp₁ q hq0 hq1 Dsc S rfl hp (Kc := K0 3 3 T.κ0 + 1) (by linarith)
  have hdj := obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl (Dsc.covers.2 (y, i)).1
    (Dsc.covers.2 (y, i)).2.2.1
  obtain ⟨-, -, hA3, -, hA5⟩ := h2 hdj (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) +
    K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl
  have hg0 : ∑ x', ∑ i', ‖(0 : Fld 3 3 N₁ T.m₁ (k + 1) 2) x' i'‖ < q := by simpa using hq0
  obtain ⟨hRg1, hRgΘ, hR, -⟩ := hA5 0 hg0
  refine ⟨Lb, hLb, Lab, εH, hεH, A, hR, hRg1, by rw [← hΘdef]; exact hRgΘ, ?_⟩
  obtain ⟨Ev, ha, hd, hb, hEv⟩ := obsEv_fromTower T k hk N₁ ν β p₁ hN hνpos hν Dsc hp y i
    (Lab.sum Lab)
  refine ⟨Ev, ha, hd, hb, ?_⟩
  intro D hDh hD g hg
  have hDx : XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D := hD
  obtain ⟨hhalf, hid⟩ := hEv D hDx
  have hmemθ : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
      physVq S S.a₁ S.ν T.t q := ⟨⟨⟨D, hD, rfl⟩, lt_of_lt_of_le hg hq1⟩, hg⟩
  obtain ⟨hholt, hholσ, hzero⟩ := hA3 (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR hRg1 _ hmemθ
  have hν0 := hνpos.le
  obtain ⟨R0⟩ := Dsc.ray
  have hr0 := Dsc.r_pos
  have hcψ0 := Dsc.cψ_pos
  have hC := Dsc.core
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hmem := compWeight_three_mem hk
  have hCs : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) T.κ
  have hbU : 0 ≤ S.betaU := R0.betaU_pos.le
  have hβ3 : 3 ≤ β := le_trans hβ₀ hβ
  have hpc : 2 * p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ := mul_pos hr0 hp
    linarith [Dsc.ray_margin]
  have hδp : Real.sqrt ((2 : ℕ) : ℝ) *
      (S.betaU ^ (-(1 / 2 : ℝ)) *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * (2 * p₁))) < T.t := by
    refine lt_of_le_of_lt ?_ Dsc.fl_radius
    rw [S.norm_betaU_rpow (show 0 ≤ β by linarith)]
    have hb := Real.rpow_nonneg hbU (-(1 / 2 : ℝ))
    have hs := Real.sqrt_nonneg ((2 : ℕ) : ℝ)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpc.le hCs) hb) hs
  obtain ⟨Jr⟩ := S.nonempty_jointRep (pp := 2 * p₁) hC T.large_block T.dom_margin T.coer_margin
    T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap (by
      show 0 ≤ β
      linarith) (by linarith) hδp
  have hCh : 0 ≤ cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k) :=
    div_nonneg (cK2'_famConst_mul_t_pos T k hk N₁ ν β p₁ Dsc).le hcψ0.le
  have hκ0h : T.κ0 ≤ 2 * T.κdec := by
    have := T.marks_κ0_le_κH; linarith
  have hεpos : 0 < obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εH + εH) εH :=
    mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  obtain ⟨I, hI⟩ := obsRecord_of_halves S 1 hp (Lab.sum Lab) _ hdj hN3 Ev D _ _ hCh T.κ0_ent
    hκ0h hhalf hid
    (fun r x => (S.withDatum D hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 1 x +
      (S.withDatum D hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g r x)
    (ball (0 : ℂ) (3 / 2)) hRg1 isOpen_ball (fun r hr => seg_mem_ball_three_halves r hr)
    subset_rfl
    (fun t σ => tiltActObs A hN3 T.κ0_ent hεH.le hdj
      (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl
      (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) t σ)
    hholt (fun r hr => hholσ _ (seg_mem_ball_three_halves r hr)) (fun r _ => hzero _)
    (fun r hr => by
      filter_upwards [hae] with x hx
      exact (hx D hDh hD g hg r hr hdj (Kobs := (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) +
        K0 3 3 T.κ0 + K0 3 3 T.κ0) le_rfl).2 _ hR hRg1)
    (by linarith) hεpos T.marks_hκ' T.marks_κ0_le_κ' T.marks_hκ
    (by rw [hΘdef] at hRgΘ; exact hRgΘ)
  let hI' := ObsMarks.toConsumer (Jr.withDatum D hDh) hC one_pos hHB T.c7_cap (R := 2) le_rfl
    T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin T.coer_margin
    T.δc_small hcψ0.le Dsc.fl_radius hp Dsc.p_lt hpc hD g y i (S.blockSplit 1 hp) I
  have hval := (thm31b_coeff hI' (κb := min hI'.κh hI'.κ' - hI'.κ0 - 1) le_rfl).1
  have hM : (S.withDatum D hDh).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeff hI' T' := by
    rw [← hval]; rfl
  rw [hM]
  congr 1
  refine Finset.sum_congr rfl fun T' _ => ?_
  have := (obsCoeffParam_fibre S 1 hp Ev _ (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) _ _ _ D
    (θ := ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g)) rfl ⟨D, hD, rfl⟩ T').trans
    (hI T').symm
  exact this.symm

end Balaban.Inhabited
