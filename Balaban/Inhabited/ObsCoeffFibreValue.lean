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

end Balaban.Inhabited
