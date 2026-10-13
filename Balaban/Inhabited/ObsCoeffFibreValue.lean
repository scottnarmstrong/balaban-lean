/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffAnalytic

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

end Balaban.Fluctuation
