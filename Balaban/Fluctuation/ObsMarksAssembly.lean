/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsHkerSupport
public import Balaban.Fluctuation.ObsRemainderMarks
public import Balaban.Fluctuation.Thm31b
public import Balaban.Polymer.LabelExtend

/-!
# The mark half of `ObsMarks` on one label system

Zero class of the step, generator-neutral.  The tilt family (the activity half of `ObsMarks`) and
the unconditional `ObsMarks` inhabitant are NOT constructed here.

## The label system

For a label system `Lab₀` of activity labels (any type `Lb₀`) and the family `𝒴` of polymer
domains of the sharp hat expansion, the common labels are the iterated sum
`ObsLb Lb₀ m₀ 𝒴 = (Lb₀ ⊕ {Y // Y ∈ 𝒴}) ⊕ {Z // Z ∈ cubeFamily}`
with the system `obsLab = (Lab₀.sum (thickLabels 𝒴 _)).sum (cubeLabels (k+1))`.  A remainder mark of
the domain `Y` has the label `Sum.inl (Sum.inr Y)`; a first-order mark has the label
`Sum.inr (obsCubeLab c)` of the single cube `c` of its mark cube; the dummy remainder index has the
label `Sum.inr (obsCubeLab bx)`.  The equalities `ysite = Y`, `dl = d^cov(Y)` and `dl = 0` for the
cube labels hold by `rfl`.

## Contents

* `ObsMarkHalf`: the fields of the first-order marks, the kernel and the remainder marks of
  `ObsMarks`, on the common labels, for one family `Ev` and one datum `D`.
* `ObsRayIdentity`: the almost-everywhere identity of the record field `hF`, for the derivative
  `obsRayFun` of the expanded function along the ray `ζ ↦ ζ • ψ̂(x)`.
* `obsMarkHalves_of_sharpHat`: both, for one `Ev`, under the premises of the sharp hat expansion.
* `obsMarks_of_tilt`: the record `ObsMarks`, given the activity half on the same labels.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

/-! ### The common label system -/

section Labels

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- **The common label type**: activity labels, labels of the domains `𝒴`, labels of single
cubes. -/
abbrev ObsLb (Lb₀ : Type) (m₀ : ℕ) (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) : Type :=
  (Lb₀ ⊕ {Y // Y ∈ 𝒴}) ⊕ {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (K := k + 1) (m₀ := m₀) (k + 1)}

/-- **The common label system.** -/
noncomputable def obsLab {Lb₀ : Type} {m₀ : ℕ} {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀) (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ
      (ObsLb Lb₀ m₀ 𝒴) :=
  (Lab₀.sum (thickLabels 𝒴 hdj)).sum
    (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1))

variable (m₀ : ℕ)

/-- The single-cube label containing the cube `c`. -/
noncomputable def obsCubeLab
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀)
      (k + 1)} :=
  Classical.choose (block_mem_cubeLabel (m₀ := m₀) (m₁ := m₁) (K := k + 1) (d := d) (L := L)
    (N₁ := N₁) c)

theorem obsCubeLab_mem
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    c ∈ blocksOf m₀ (k + 1) Set.univ
      ((cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1)).ysite
        (obsCubeLab m₀ c)) :=
  Classical.choose_spec (block_mem_cubeLabel (m₀ := m₀) (m₁ := m₁) (K := k + 1) (d := d) (L := L)
    (N₁ := N₁) c)

theorem obsCubeLab_dl
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1)).dl
      (obsCubeLab m₀ c) = 0 :=
  cubeLabels_dl _

/-- The label of the first-order mark `i`: the single-cube label of its mark cube. -/
noncomputable def obsY1 {ϱ : ℝ} {N : ℕ} (S : StepSetting d L N₁ m₁ k N ϱ) (Lb₀ : Type)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (i : ObsMarkIdx S) : ObsLb Lb₀ m₀ 𝒴 :=
  Sum.inr (obsCubeLab m₀ (obsMarkCube S m₀ i))

/-- The label of the dummy remainder index: the single-cube label of the root cube. -/
noncomputable def obsY0 (Lb₀ : Type) (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    ObsLb Lb₀ m₀ 𝒴 :=
  Sum.inr (obsCubeLab m₀ bx)

end Labels

/-! ### The fields and the identity -/

section Fields

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

open Classical in
/-- **The fields of groups (II)–(III) of `ObsMarks`** on the common labels, for the family `Ev` and
the datum `D`: the first-order marks `blockMark` (index `ObsMarkIdx S`, `F1 = Fm = p₁`), their cubes
with the multiplicity `n_* = N L^{d(m₀+m₁+1)}`, the kernel `obsHker` of the coefficients
`obsRowCoeff` (decay `Ch e^{-κh dExt T}`, both support clauses), and the remainder family
(`ObsRemFields`, labelled by `Sum.inl (Sum.inr Y)` and the dummy label `obsY0`). -/
def ObsMarkHalf {Lb₀ : Type}
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ) (D : BgData S.G' N)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ
      (ObsLb Lb₀ m₀ 𝒴))
    (cψ C0 κG κ0 Ch κh : ℝ)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    Prop :=
  (∀ i : ObsMarkIdx S, Measurable (blockMark S m₀ hp i.1 i.2)) ∧
  (∀ i : ObsMarkIdx S, DepOn (Ω := (S.blockSplit m₀ hp).Ωb)
    (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ
      (Lab.ysite (obsY1 m₀ S Lb₀ 𝒴 i))) (blockMark S m₀ hp i.1 i.2)) ∧
  0 < S.p₁ ∧
  (∀ (i : ObsMarkIdx S) Φ, ‖blockMark S m₀ hp i.1 i.2 Φ‖ ≤
    S.p₁ * Real.exp (-κG * Lab.dl (obsY1 m₀ S Lb₀ 𝒴 i))) ∧
  (∀ i : ObsMarkIdx S, ∫ Φ, blockMark S m₀ hp i.1 i.2 Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0) ∧
  (∀ i : ObsMarkIdx S, S.p₁ * Real.exp (-κ0 * Lab.dl (obsY1 m₀ S Lb₀ 𝒴 i)) ≤ S.p₁) ∧
  (∀ i : ObsMarkIdx S, obsMarkCube S m₀ i ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (K := k + 1) m₀ (k + 1) Set.univ (Lab.ysite (obsY1 m₀ S Lb₀ 𝒴 i))) ∧
  (∀ c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ,
    ((Finset.univ.filter fun i : ObsMarkIdx S => obsMarkCube S m₀ i = c).card : ℝ) ≤
      ((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ)) ∧
  (∀ (i : ObsMarkIdx S) T, ‖obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T‖ ≤ Ch * Real.exp (-κh * dExt T)) ∧
  (∀ (i : ObsMarkIdx S) T, obsMarkCube S m₀ i ∉ T → obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T = 0) ∧
  (∀ (i : ObsMarkIdx S) T, bx ∉ T → obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T = 0) ∧
  ObsRemFields S m₀ hp Ev D 𝒴 cψ C0 κG κ0 Lab (fun Y => Sum.inl (Sum.inr Y))
    (obsY0 m₀ Lb₀ 𝒴 bx) bx

/-- **The point hat configuration**: the coordinates of `x` as complex numbers. -/
noncomputable def obsHatPt (x : S.E) : S.U × Fin N → ℂ := fun q => ((x q.1 q.2 : ℝ) : ℂ)

/-- **The observable integrand**: the derivative at `t` of the expanded function `F` along the
ray `ζ ↦ ζ • ψ̂(x)`. -/
noncomputable def obsRayFun (F : (S.U × Fin N → ℂ) → ℂ) (x : S.E) (t : ℝ) : ℂ :=
  deriv (fun ζ : ℂ => F (ζ • obsHatPt S x)) (t : ℂ)

open Classical in
/-- **The identity field `hF` of `ObsMarks`**: for `s ∈ [0,1]` and `ν_{p₁}`-almost every `x`,
the integrand is the kernel part plus the remainder marks, in the exact form of the record. -/
def ObsRayIdentity (F : (S.U × Fin N → ℂ) → ℂ)
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ) (D : BgData S.G' N)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) : Prop :=
  ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
    obsRayFun S F x s =
      ∑ i : ObsMarkIdx S, (∑ T, obsHker 𝒴 (obsRowCoeff S Ev D i) m₀ T) *
          blockMark S m₀ hp i.1 i.2 ((S.blockSplit m₀ hp).restr x) +
        ∑ r, obsGr S m₀ hp Ev D 𝒴 r (s : ℂ) ((S.blockSplit m₀ hp).restr x)

end Fields

/-! ### Under the premises of the sharp hat expansion -/

section SharpHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The polymer domains of the sharp hat expansion.** -/
noncomputable abbrev obsDomains (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) : Finset (Set (CTorus d L N₁ m₁ (k + 1))) :=
  polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
    S.G' m₀ (X1 S.G' m₀ j 𝒦X)

theorem obsDomains_isDj (hd3 : 3 ≤ d) (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X) :
    ∀ Y ∈ obsDomains S X₁f m₀ j 𝒦X, IsDj m₀ (k + 1) Y := fun _ hY =>
  isDj_of_polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
    S.hG' hcov hd3 (fun i => i.1.2) hopt hY

/-- **The mark half and the identity of `ObsMarks`, with the three clauses of `Ev`.**

The conclusion of `obsMarkHalves_of_sharpHat`, together with, for the same `Ev`, the analyticity of
each `Ev Y` on `XiCRaw … ×ˢ` the hat ball, the `AgHatDir` locality and the decay bound
`Q δ₁ · exp(-2 κdec · treeLenCov)` there (the shapes of `obsHker_param_of_Ev`).


Premises: exactly those of the landed `obsRowCoeff_of_sharpHat` (the premises of
`fsite_expansion_hat_dir` with `Gp = S.G'`, and `0 < cψ`), `0 < p₁`, `p₁ ≤ cψ / 4`, an arbitrary
label system `Lab₀` of activity labels, and the rates `κG ≤ 2 κdec`, `a_ent + 1 ≤ κ0 ≤ 2 κdec`.
Conclusion: there is one family `Ev` (that of the landed theorem) such that for every datum `D` of
`Ξ`, with the expanded function `F` of the site functional `svec ... y iy`:

* `ObsMarkHalf` on the common labels `obsLab Lab₀ _`, with `C0 = Q δ₁`, `Ch = Q δ₁ / cψ`,
  `κh = 2 κdec`, root cube `bx = rootCube (blockIndex y)`;
* `ObsRayIdentity` for `F`;
* the sum identity `Σ_T hker i T = Σ_Y a_Y(i)` and the expansion `F = Σ_Y Ev Y` on the hat ball. -/
theorem obsMarkHalves_of_sharpHat_param (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N)
    (hp : 0 < S.p₁) (hq : S.p₁ / cψ ≤ 1 / 4)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    {κG κ0 : ℝ} (hκG : κG ≤ 2 * κdec) (hκ0 : aEnt d L + 1 ≤ κ0) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) ∧
      ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ObsMarkHalf S m₀ hp Ev D (obsDomains S X₁f m₀ j 𝒦X)
          (obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt)) cψ
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) κG κ0
          (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) (2 * κdec)
          (rootCube (m₀ := m₀) (blockIndex y)) ∧
        ObsRayIdentity S m₀ hp
          (fun ψh => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D
            (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy) Ev D (obsDomains S X₁f m₀ j 𝒦X) := by
  classical
  obtain ⟨Ev, hs, hd, hb, ha, hrow'⟩ := obsRowCoeff_of_sharpHat S hC hk hG cc hcψ hMX hdm hα hsm
    hδ₁ hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy
  refine ⟨Ev, ha, hd, hb, fun D hD => ?_⟩
  have hd3 : 3 ≤ d := hC.HBp.hd
  have hdj := obsDomains_isDj (S := S) (X₁f := X₁f) hd3 hcov hopt
  have hrem := obsRemainder_of_sharpHat S hC cc hcψ hcov hX₁ hopt y hy iy hp hq Ev hs hd hb ha
    (obsLab Lab₀ hdj) (fun Y => Sum.inl (Sum.inr Y))
    (obsY0 m₀ Lb₀ _ (rootCube (m₀ := m₀) (blockIndex y))) (fun Y => rfl) (fun Y => rfl)
    (obsCubeLab_mem m₀ _) hκG hκ0 D hD
  obtain ⟨hfields, hdecomp⟩ := hrem
  have hrowD := hrow' D hD
  have hbf : ∀ i : ObsMarkIdx S, Measurable (blockMark S m₀ hp i.1 i.2) ∧
      DepOn (Ω := (S.blockSplit m₀ hp).Ωb)
        (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ
          ((obsLab Lab₀ hdj).ysite (obsY1 m₀ S Lb₀ _ i))) (blockMark S m₀ hp i.1 i.2) ∧
      0 < S.p₁ ∧
      (∀ Φ, ‖blockMark S m₀ hp i.1 i.2 Φ‖ ≤
        S.p₁ * Real.exp (-κG * (obsLab Lab₀ hdj).dl (obsY1 m₀ S Lb₀ _ i))) ∧
      ∫ Φ, blockMark S m₀ hp i.1 i.2 Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0 := fun i =>
    blockMark_fields S m₀ hp i.1 i.2 (obsLab Lab₀ hdj) (obsY1 m₀ S Lb₀ _ i)
      (obsCubeLab_mem m₀ (obsMarkCube S m₀ i)) (obsCubeLab_dl m₀ _) κG
  have hexp : ∀ i : ObsMarkIdx S, Real.exp (-κ0 * (obsLab Lab₀ hdj).dl (obsY1 m₀ S Lb₀ _ i)) = 1 :=
    fun i => by
      have : (obsLab Lab₀ hdj).dl (obsY1 m₀ S Lb₀ _ i) = 0 := obsCubeLab_dl m₀ _
      rw [this]; simp
  refine ⟨⟨fun i => (hbf i).1, fun i => (hbf i).2.1, hp, fun i => (hbf i).2.2.2.1,
    fun i => (hbf i).2.2.2.2, fun i => by rw [hexp i, mul_one], fun i =>
    obsCubeLab_mem m₀ (obsMarkCube S m₀ i), fun c => ?_, fun i T => (hrowD i).2.2.2.2.2.2 T,
    fun i T hT => ?_, fun i T hT => ?_, hfields⟩, ?_⟩
  · have := card_markIdx_cell_le_pow S c
    exact_mod_cast this
  · by_contra hne
    exact hT ((hrowD i).2.2.2.2.2.1 T hne).1
  · by_contra hne
    exact hT ((hrowD i).2.2.2.2.2.1 T hne).2
  · intro s hs
    have hpre := ae_obsHat_eq_true S m₀ hp
    rw [← (S.blockSplit m₀ hp).map_eq] at hpre
    have hae := ae_of_ae_map (S.blockSplit m₀ hp).meas.aemeasurable hpre
    filter_upwards [hae] with x hx
    have hs32 : ‖(s : ℂ)‖ < 3 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    have hpt : obsHatPt S x = obsHat S m₀ hp ((S.blockSplit m₀ hp).restr x) := hx.symm
    unfold obsRayFun
    rw [hpt, hdecomp _ _ hs32]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_obsHker (𝒴 := obsDomains S X₁f m₀ j 𝒦X) (c := obsRowCoeff S Ev D i) (m₀ := m₀)]
    rw [mul_comm]
    rfl

/-- **The mark half and the identity of `ObsMarks`, on one label system and one `Ev`.**

Premises: exactly those of the landed `obsRowCoeff_of_sharpHat` (the premises of
`fsite_expansion_hat_dir` with `Gp = S.G'`, and `0 < cψ`), `0 < p₁`, `p₁ ≤ cψ / 4`, an arbitrary
label system `Lab₀` of activity labels, and the rates `κG ≤ 2 κdec`, `a_ent + 1 ≤ κ0 ≤ 2 κdec`.
Conclusion: there is one family `Ev` (that of the landed theorem) such that for every datum `D` of
`Ξ`, with the expanded function `F` of the site functional `svec ... y iy`:

* `ObsMarkHalf` on the common labels `obsLab Lab₀ _`, with `C0 = Q δ₁`, `Ch = Q δ₁ / cψ`,
  `κh = 2 κdec`, root cube `bx = rootCube (blockIndex y)`;
* `ObsRayIdentity` for `F`;
* the sum identity `Σ_T hker i T = Σ_Y a_Y(i)` and the expansion `F = Σ_Y Ev Y` on the hat ball. -/
theorem obsMarkHalves_of_sharpHat (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N)
    (hp : 0 < S.p₁) (hq : S.p₁ / cψ ≤ 1 / 4)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    {κG κ0 : ℝ} (hκG : κG ≤ 2 * κdec) (hκ0 : aEnt d L + 1 ≤ κ0) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ObsMarkHalf S m₀ hp Ev D (obsDomains S X₁f m₀ j 𝒦X)
          (obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt)) cψ
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) κG κ0
          (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) (2 * κdec)
          (rootCube (m₀ := m₀) (blockIndex y)) ∧
        ObsRayIdentity S m₀ hp
          (fun ψh => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D
            (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy) Ev D (obsDomains S X₁f m₀ j 𝒦X) := by
  obtain ⟨Ev, -, -, -, hEv⟩ := obsMarkHalves_of_sharpHat_param S hC hk hG cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy hp hq Lab₀ hκG hκ0
  exact ⟨Ev, hEv⟩

/-- **`obsMarks_of_tilt` with the support of the kernel.**  As `obsMarks_of_tilt`, and moreover
the kernel `I.hker i T` vanishes unless `dOmega (sitesOf T) ≠ ⊤` (it is `obsHker` of the domains of
the expansion, supported on their labels). -/
theorem obsMarks_of_tilt_ksupp (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N)
    (hp : 0 < S.p₁) (hq : S.p₁ / cψ ≤ 1 / 4)
    {Lb₀ : Type} [Fintype Lb₀] (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    {κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0h : κ0 ≤ 2 * κdec)
    (D : BgData S.G' N) (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    (W : ℝ → S.E → ℂ) {εH κH κ' Kc' Rσ : ℝ} (hκH : κH ≤ 2 * κdec)
    (𝒰 : Set ℂ) (hRσ : 1 < Rσ) (hOpen : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (h𝒰 : 𝒰 ⊆ ball (0 : ℂ) (3 / 2))
    (A : ℂ → ℂ → LabelAct (obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt))
      (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc')
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
    ∃ I : ObsMarks S.nuFl (S.blockSplit m₀ hp) W (fun t x => obsRayFun S (fun ψh =>
          svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy) x t)
        (rootCube (m₀ := m₀) (blockIndex y)),
        I.Kc = Kc' ∧ I.κH = κH ∧ I.κG = κH ∧ I.κ0 = κ0 ∧ I.κ' = κ' ∧ I.εH = εH ∧ I.Rσ = Rσ ∧
        I.κh = 2 * κdec ∧ I.Ch = cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ ∧ I.Fm = S.p₁ ∧
        I.nmax = ((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ) ∧
        I.B2 ≤ CPE d L Kc' κH κ0 κ' *
          (8 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) * (S.p₁ / cψ) ^ 2 * (K0 d L κ0 + 1)) ∧
        I.B1 = cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ *
          (CPE d L Kc' κH κ0 κ' * S.p₁ / Rσ) *
          (((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kc' ^ 2 *
          Real.exp ((min (2 * κdec) κ' - κ0) * cG d L) ∧
        ∀ (i : I.ι1) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
          m₀ (k + 1) Set.univ)),
          I.hker i T ≠ 0 → dOmega m₀ (k + 1) Set.univ (sitesOf T) ≠ ⊤ := by
  classical
  obtain ⟨Ev, hEv⟩ := obsMarkHalves_of_sharpHat S hC hk hG cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁
    hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy hp hq Lab₀ (κG := κH) hκH hκ0
  obtain ⟨hhalf, hid⟩ := hEv D hD
  obtain ⟨hmeas1, hdep1, -, hbound1, hmean1, hFm, hbm, hcount, hbh, hsh, hxh, hrf⟩ := hhalf
  obtain ⟨hc0, hboundr, hmeasr, hdepr, hholr, hxr, hsum, -⟩ := hrf
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hCh : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ :=
    div_nonneg (mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le) hcψ.le
  have hCPE : 0 ≤ CPE d L Kc' κH κ0 κ' := by
    unfold CPE; have := one_le_c1 d L
    have hK0 : 0 < K0 d L κ0 := by
      unfold K0
      have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
      exact div_pos (Real.exp_pos _) (by linarith)
    have : 0 ≤ Kc' := by linarith
    positivity
  refine ⟨{
                Lb := ObsLb Lb₀ m₀ (obsDomains S X₁f m₀ j 𝒦X)
                fin := inferInstance
                Lab := obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt)
                εH := εH, κH := κH, κG := κH, κ0 := κ0, κ' := κ', Kc := Kc'
                hN := hcov.hN, Rσ := Rσ, hRσ := hRσ, 𝒰 := 𝒰, isOpen := hOpen, seg := hseg
                A := A, holt := holt, holσ := holσ, zero := zero, hW := hW
                ι1 := ObsMarkIdx S
                fin1 := inferInstance
                y1 := obsY1 m₀ S Lb₀ _
                G1 := fun i => blockMark S m₀ hp i.1 i.2
                meas1 := hmeas1, dep1 := hdep1
                F1 := fun _ => S.p₁, hF1 := fun _ => hp
                bound1 := hbound1, mean1 := hmean1
                Fm := S.p₁, hFm := hFm
                bm := obsMarkCube S m₀, hbm := hbm
                nmax := ((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ), hnmax := Nat.cast_nonneg _
                hcount := hcount
                hker := fun i T => obsHker (obsDomains S X₁f m₀ j 𝒦X) (obsRowCoeff S Ev D i) m₀ T
                Ch := cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ, κh := 2 * κdec, hCh := hCh
                bound_h := hbh, supp_h := hsh, x_h := hxh, hκh := hκ0h, hFm0 := hp.le
                ιr := RemIdx (obsDomains S X₁f m₀ j 𝒦X)
                finr := inferInstance
                nonemptyr := ⟨none⟩
                yr := obsRemLab _ (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 m₀ Lb₀ _ (rootCube (m₀ := m₀) (blockIndex y)))
                Gr := obsGr S m₀ hp Ev D _, measr := hmeasr, depr := hdepr
                Fr := fun _ => 8 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) * (S.p₁ / cψ) ^ 2
                hFr := fun _ => hc0, boundr := hboundr
                holGr := fun r Φ => (hholr r Φ).mono h𝒰
                x_r := hxr
                hκ0 := hκ0, hKc := hKc, hεpos := hεpos, hκ' := hκ'0, hκ0' := hκ0'
                hκG := le_rfl, hκ := hκH', hε := hε
                hF := hid }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
  show CPE d L Kc' κH κ0 κ' * ∑ r : RemIdx (obsDomains S X₁f m₀ j 𝒦X),
      (8 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) * (S.p₁ / cψ) ^ 2) *
        Real.exp (-κ0 * (obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt)).dl
          (obsRemLab _ (fun Y => Sum.inl (Sum.inr Y))
            (obsY0 m₀ Lb₀ _ (rootCube (m₀ := m₀) (blockIndex y))) r)) ≤ _
  exact mul_le_mul_of_nonneg_left hsum hCPE
  · intro i T h
    exact dOmega_ne_top_of_obsHker_ne_zero (c := obsRowCoeff S Ev D i) hcov.hN
      (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt) h

/-- **The record `ObsMarks`, conditional on the activity half on the common labels.**

Premises: those of `obsMarkHalves_of_sharpHat`, a datum `D` of `Ξ`, the exponent `W`, and the
activity half on the common labels `obsLab Lab₀ _` (for example the zero extension of a tilt family
on `Lab₀`): an open `𝒰 ⊆ B(0, 3/2)` containing `[0,1]`, `1 < Rσ`, the family `A` with the fields
`holt`, `holσ`, `zero`, `hW` of `ObsMarks`; and the numerical conditions of Theorem 3.4 for the
constants `εH, κH, Kc, κ', κ0` (the record fields `hKc, hεpos, hκ', hκ0', hκ, hε`), with
`κG = κH ≤ 2 κdec`, `κ0 ≤ κh = 2 κdec`.  Conclusion: a record `I` for the integrand
`f t x = obsRayFun S F x t` with `Ch = Q δ₁ / cψ`, `κh = 2 κdec`, `Fm = p₁`, `nmax = N L^{d(m₀+m₁+1)}`,
whose constants `B₂ ≤ C_PE · c₀ (K0 + 1)` (`c₀ = 8 Q δ₁ (p₁/cψ)²`) and `B₁` have the displayed
values. -/
theorem obsMarks_of_tilt (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N)
    (hp : 0 < S.p₁) (hq : S.p₁ / cψ ≤ 1 / 4)
    {Lb₀ : Type} [Fintype Lb₀] (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    {κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0h : κ0 ≤ 2 * κdec)
    (D : BgData S.G' N) (hD : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    (W : ℝ → S.E → ℂ) {εH κH κ' Kc' Rσ : ℝ} (hκH : κH ≤ 2 * κdec)
    (𝒰 : Set ℂ) (hRσ : 1 < Rσ) (hOpen : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (h𝒰 : 𝒰 ⊆ ball (0 : ℂ) (3 / 2))
    (A : ℂ → ℂ → LabelAct (obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt))
      (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc')
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
    ∃ I : ObsMarks S.nuFl (S.blockSplit m₀ hp) W (fun t x => obsRayFun S (fun ψh =>
          svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy) x t)
        (rootCube (m₀ := m₀) (blockIndex y)),
        I.Kc = Kc' ∧ I.κH = κH ∧ I.κG = κH ∧ I.κ0 = κ0 ∧ I.κ' = κ' ∧ I.εH = εH ∧ I.Rσ = Rσ ∧
        I.κh = 2 * κdec ∧ I.Ch = cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ ∧ I.Fm = S.p₁ ∧
        I.nmax = ((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ) ∧
        I.B2 ≤ CPE d L Kc' κH κ0 κ' *
          (8 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) * (S.p₁ / cψ) ^ 2 * (K0 d L κ0 + 1)) ∧
        I.B1 = cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ *
          (CPE d L Kc' κH κ0 κ' * S.p₁ / Rσ) *
          (((N * L ^ (d * (m₀ + m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kc' ^ 2 *
          Real.exp ((min (2 * κdec) κ' - κ0) * cG d L) := by
  obtain ⟨I, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := obsMarks_of_tilt_ksupp S hC hk hG cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy hp hq Lab₀ hκ0 hκ0h D hD W hκH 𝒰 hRσ hOpen hseg h𝒰 A holt holσ zero hW hKc hεpos hκ'0 hκ0' hκH' hε
  exact ⟨I, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end SharpHat

end Balaban.Fluctuation
