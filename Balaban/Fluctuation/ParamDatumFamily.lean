/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffA
public import Balaban.Fluctuation.StepComplexThm31
public import Balaban.Fluctuation.StepComplexJoint
public import Balaban.Fluctuation.HatLabelsDep
public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Fluctuation.StepComplexOutWitness
import Mathlib.Tactic.Linarith

/-!
# The fluctuation step as a family over the block datum (PARAM.md, package 1)

A step setting `S` fixes the block datum `D'`.  For another datum `D` of the same generating set with
the same constant field, `h ≡ h₀` (`hD`), the step `S.withDatum D hD` changes **only** `D'` (and the
proof `hh₀`); everything else is the same structure field.  This file records what does not vary.

## Contents

* Invariance (`withDatum_*`): the generating set, the unit lattice and the fluctuation space, the
  numbers `a₁, ν, β, p₁, δ, h₀`, the weights `a_n`, `β_k` in `η`-units, the fluctuation measure
  `ν_{p₁}`, the block split (hence the cube labels `CubeB`, the block variables and the restriction
  maps) and the hat variable.  They are definitionally equal, so one product measure and one label
  system serve the whole family.  What does vary (`withDatum_covSqrtC`, `withDatum_KC`,
  `withDatum_shiftUC`): the covariance square root `C^{(k)1/2}` of the datum, hence the substitution
  `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` of (2.7), the exponents `W₁, W₂` and the activities built from it.
* The slice (`paramSlice`): the raw data `Θ = (Ψ, h̃)` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` whose field
  `h̃` is the constant `h₀`.  The family `Θ ↦ S_Θ` (`sliceStep`) is a family over this slice and
  **not** over the whole chart: a general point of the chart has a nonconstant complex `h̃`, and then
  no step setting of `StepSetting` has it as its datum (`StepSetting.hh₀` demands a constant real
  field).  `rawOf` is injective on `BgData` (`BgData.eq_of_raw`), so a slice point determines its datum
  uniquely (`existsUnique_datum_of_slice`) and `S_Θ` is defined after that theorem.  Whether the slice
  is a proper subset of the chart is not proved (it needs a datum of the chart with a nonconstant
  `h`, absent from the landed witnesses, all of which have `h ≡ e₀`).
* The complex coefficient of Theorem 3.1 (a) (`e1CoeffC`): `D.term T + interpCoeff I T` for
  `I : E1MarksC` and `D : DetExpansionC`, with `thm31aC_coeff`, the complex form of `thm31a_coeff`
  (formula (P1) at one datum), and `e1CoeffC_eq_e1Coeff_of_match`, its agreement with the real
  `e1Coeff` under an explicit matching hypothesis.
* The non-vacuity instance `exists_family_two_data`.

## Scope

Nothing here proves analyticity or locality in the datum.  Those are the later packages
(`ParamMarkedHolomorphy`, `ParamMarksPhysical`, `ParamMarkedLocalBound` and the determinant
packages).  The coefficients are at a fixed datum; no generating set is chosen for the class terms
and nothing depends on such a choice.

## Findings (T6)

* `E1MarksC` has no inhabitant in the landed tree: it is only used as a hypothesis in
  `StepComplexThm31`.  `DetExpansionC` is inhabited at every step (`nonempty_detExpansionC`), by the
  single term at `T = ∅` carrying the whole trace.
* `StepSetting.K` is `matMap S.U N (S.covSqrt.map Complex.re)`: it takes the real parts of the
  entries of `covSqrt`, and `Complex.re` is not holomorphic, so it cannot be a holomorphic function of
  a complex datum.  The complex object is `KC = Matrix.mulVecLin covSqrtC` (no real part), entering
  `shiftUC x = β_k^{-1/2} • KC (yhat x)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  MeasureTheory

section Invariance

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (D : BgData S.G' N)
  (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))

/-- The generating set of the new level is the same for every datum of the family. -/
theorem withDatum_G' : (S.withDatum D hD).G' = S.G' := rfl

/-- The datum of `S.withDatum D hD` is `D`. -/
theorem withDatum_D' : (S.withDatum D hD).D' = D := rfl

/-- The constant field `h₀` is the same. -/
theorem withDatum_h₀ : (S.withDatum D hD).h₀ = S.h₀ := rfl

/-- The numbers `a₁, ν, β, p₁, δ` are the same. -/
theorem withDatum_numbers :
    (S.withDatum D hD).a₁ = S.a₁ ∧ (S.withDatum D hD).ν = S.ν ∧ (S.withDatum D hD).β = S.β ∧
      (S.withDatum D hD).p₁ = S.p₁ ∧ (S.withDatum D hD).δ = S.δ := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The weights `a_n` are the same. -/
theorem withDatum_a : (S.withDatum D hD).a = S.a := rfl

/-- `β_k` in `η`-units is the same. -/
theorem withDatum_betaU : (S.withDatum D hD).betaU = S.betaU := rfl

/-- The unit lattice `T^{(k)}_1` is the same type. -/
theorem withDatum_U : (S.withDatum D hD).U = S.U := rfl

/-- The space `ℝ^N`-valued fluctuation variables `ψ̂` is the same type. -/
theorem withDatum_E : (S.withDatum D hD).E = S.E := rfl

/-- The complex fluctuation fields form the same type. -/
theorem withDatum_EC : (S.withDatum D hD).EC = S.EC := rfl

/-- **The fluctuation measure `ν_{p₁}` is the same measure on the same space** for every datum of
the family: one product measure serves the whole family. -/
theorem withDatum_nuFl : (S.withDatum D hD).nuFl = S.nuFl := rfl

/-- The block split of the fluctuation measure (block variables, one-site measures, restriction)
is the same, hence so are the cube labels and the type of `E1Marks`-type input. -/
theorem withDatum_blockSplit (m₀ : ℕ) (hp : 0 < S.p₁) :
    (S.withDatum D hD).blockSplit m₀ hp = S.blockSplit m₀ hp := rfl

/-- The type of block splits is the same for the whole family (so is the type `CubeB` of cubes
that index the terms `T`). -/
theorem withDatum_BlockSplit (m₀ : ℕ) :
    BlockSplit (S.withDatum D hD) m₀ = BlockSplit S m₀ := rfl

/-- The hat variable `ψ̂ ↦ ψ̂_Φ` built from a block configuration is the same. -/
theorem withDatum_hatOf (m₀ : ℕ) (ρ : ℝ) (hp : 0 < S.p₁) :
    (S.withDatum D hD).hatOf m₀ ρ hp = S.hatOf m₀ ρ hp := rfl

/-- **What varies: `C^{(k)1/2}`.**  The complex covariance square root of the step with the datum
`D` is the one built from the complex background field and multiplier of `D`. -/
theorem withDatum_covSqrtC :
    (S.withDatum D hD).covSqrtC =
      decCovSqrt S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G') := rfl

/-- The substitution operator of (2.7) of the step with the datum `D` is the matrix of
`covSqrtC` of that datum. -/
theorem withDatum_KC : (S.withDatum D hD).KC = Matrix.mulVecLin (S.withDatum D hD).covSqrtC := rfl

/-- The substitution `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` of the step with the datum `D`: the datum
enters through `KC`, the factor `β_k^{-1/2}` is the same. -/
theorem withDatum_shiftUC (x : S.E) :
    (S.withDatum D hD).shiftUC x =
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.withDatum D hD).KC (yhat x) := rfl

end Invariance

section Slice

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (eps : ℝ)

/-- **The slice `U_{h₀}` of the chart.**  The raw data `Θ = (Ψ, h̃)` of the chart
`Ξ^c(𝔹_{k+1}; 1, ε)` whose field `h̃` is the constant `h₀` of the step.  This is a subset of the
chart, in general proper: a general point of the chart has a nonconstant complex `h̃`. -/
def paramSlice : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
  {Θ | Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps ∧ Θ.2 = fun _ i => (S.h₀ i : ℂ)}

variable {S eps}

theorem paramSlice_subset : paramSlice S eps ⊆ XiCRaw S.G' S.a S.ν (k + 1) 1 eps :=
  fun _ h => h.1

/-- The raw datum of a block datum of the chart with `h ≡ h₀` lies in the slice. -/
theorem rawOf_mem_paramSlice {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) : rawOf D ∈ paramSlice S eps :=
  ⟨⟨D, hX, rfl⟩, funext fun y => funext fun i => hD y i⟩

/-- **A slice point is the raw datum of exactly one block datum of the chart** (`rawOf` is
injective, `BgData.eq_of_raw`), and that datum has `h ≡ h₀`. -/
theorem existsUnique_datum_of_slice {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ paramSlice S eps) :
    ∃! D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D ∧ rawOf D = Θ := by
  obtain ⟨⟨D, hX, rfl⟩, -⟩ := hΘ
  exact ⟨D, ⟨hX, rfl⟩, fun D' hD' => BgData.eq_of_raw hD'.2⟩

open Classical in
/-- **The block datum of a slice point** (the unique datum of the chart with this raw datum). -/
noncomputable def sliceDatum {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ paramSlice S eps) : BgData S.G' N :=
  (existsUnique_datum_of_slice hΘ).exists.choose

/-- Characterization of `sliceDatum`: it is in the chart, and its raw datum is `Θ`. -/
theorem sliceDatum_spec {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ paramSlice S eps) :
    XiCData S.G' S.a S.ν (k + 1) 1 eps (sliceDatum hΘ) ∧ rawOf (sliceDatum hΘ) = Θ :=
  (existsUnique_datum_of_slice hΘ).exists.choose_spec

/-- The datum of a slice point has `h ≡ h₀`. -/
theorem sliceDatum_h {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ paramSlice S eps)
    (y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) (i : Fin N) :
    (sliceDatum hΘ).h y i = (S.h₀ i : ℂ) := by
  have h1 := (congrArg Prod.snd (sliceDatum_spec hΘ).2).trans hΘ.2
  exact congrFun (congrFun h1 y) i

/-- **The step setting `S_Θ` of a point `Θ` of the slice**: `S.withDatum` at the datum of `Θ`. -/
noncomputable def sliceStep {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ paramSlice S eps) : StepSetting d L N₁ m₁ k N ϱ :=
  S.withDatum (sliceDatum hΘ) (sliceDatum_h hΘ)

/-- **`S_D` depends only on `rawOf D`**: two data with the same raw datum give the same step. -/
theorem withDatum_congr_raw {D D' : BgData S.G' N} (h : rawOf D = rawOf D')
    (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)) :
    S.withDatum D hD = S.withDatum D' hD' := by
  cases BgData.eq_of_raw h
  rfl

/-- The step of the slice point `rawOf D` is `S.withDatum D hD`. -/
theorem sliceStep_rawOf {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) :
    sliceStep (rawOf_mem_paramSlice hX hD) = S.withDatum D hD :=
  withDatum_congr_raw (sliceDatum_spec (rawOf_mem_paramSlice hX hD)).2 _ _

/-- The step of a slice point has the same fluctuation measure as `S`. -/
theorem sliceStep_nuFl {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ paramSlice S eps) :
    (sliceStep hΘ).nuFl = S.nuFl := rfl

end Slice

section Coeff

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

/-- **The canonical term `ℰ₀(z, T)` of Theorem 3.1 (a) for the complex step** (formula (P1) at one
datum): the determinant term `D.term T` of `-½ ∑_{y ∈ B(z)} tr 𝕃(y,y)` plus the interpolation term
`interpCoeff I T` of the integral of the marks of `I : E1MarksC`. -/
noncomputable def e1CoeffC (I : E1MarksC S C BS z) {κ'' cdet : ℝ}
    (D : DetExpansionC S m₀ z κ'' cdet)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  D.term T + interpCoeff I T

/-- The complex term unfolds to the determinant term plus `gsumCoeff` of the data of `I`. -/
theorem e1CoeffC_eq (I : E1MarksC S C BS z) {κ'' cdet : ℝ} (D : DetExpansionC S m₀ z κ'' cdet)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    e1CoeffC I D T = D.term T + gsumCoeff BS.μ I.Lab I.A I.y0 I.G T := rfl

open Classical in
/-- **Theorem 3.1 (a) for the complex step with the canonical coefficients `e1CoeffC`** (the complex
form of `thm31a_coeff`): the interpolation part `E1locC`, the expansion of `E0locC`, and the bound. -/
theorem thm31aC_coeff (I : E1MarksC S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'')
    (D : DetExpansionC S m₀ z κ'' cdet) :
    S.E1locC C z = ∑ T, interpCoeff I T ∧
    S.E0locC C z = ∑ T, e1CoeffC I D T ∧
    ∀ T, ‖e1CoeffC I D T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) := by
  obtain ⟨h1, h2⟩ := interpCoeff_spec I
  refine ⟨h1, ?_, fun T => ?_⟩
  · unfold e1CoeffC
    rw [Finset.sum_add_distrib, ← D.sum_eq, ← h1]
    rfl
  · unfold e1CoeffC
    refine (norm_add_le _ _).trans ?_
    have hd : ‖D.term T‖ ≤ cdet * Real.exp (-I.κ' * dExt T) := by
      refine (D.bound T).trans ?_
      have hc : 0 ≤ cdet := by
        have := (D.bound T).trans' (norm_nonneg _)
        rcases le_or_gt 0 cdet with h | h
        · exact h
        · nlinarith [Real.exp_pos (-κ'' * dExt T)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
      nlinarith [dExt_nonneg (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T]
    nlinarith [h2 T]

/-- Theorem 3.1 (a) at a datum of the family: the same statement for the step `S.withDatum D hD`,
whose fluctuation measure and block split are those of `S`. -/
theorem thm31aC_coeff_withDatum (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (BS' : BlockSplit (S.withDatum D hD) m₀) (C' : StepClass d L N₁ m₁ k N ϱ)
    (z' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (I : E1MarksC (S.withDatum D hD) C' BS' z') {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'')
    (T0 : DetExpansionC (S.withDatum D hD) m₀ z' κ'' cdet) :
    (S.withDatum D hD).E0locC C' z' = ∑ T, e1CoeffC I T0 T :=
  (thm31aC_coeff I hκ'' T0).2.1

/-- **`gsumCoeff` for two label systems that agree up to equality of types** (the form of the
matching in `e1CoeffC_eq_e1Coeff_of_match`): the label types, mark index types, label systems,
base labels, activities and marks are identified by (heterogeneous) equalities, the latter two on
real interpolation parameters `s ∈ [0,1]`. -/
theorem gsumCoeff_heq {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {Lb Lb' : Type} [fL : Fintype Lb] [fL' : Fintype Lb'] {ι ι' : Type} [fi : Fintype ι]
    [fi' : Fintype ι']
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ Lb}
    {Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ Lb'}
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (A' : ℂ → LabelAct Lab' Ωb εH' κH' κ0' Kc')
    (y0 : ι → Lb) (y0' : ι' → Lb') (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (G' : ι' → ℂ → (∀ b, Ωb b) → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hGdep : ∀ i s, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i))) (G i s))
    (hLb : Lb = Lb') (hι : ι = ι') (hLab : HEq Lab Lab') (hy0 : HEq y0 y0')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → HEq (fun y => (A (s : ℂ)).H y) (fun y => (A' (s : ℂ)).H y))
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → HEq (fun i => G i (s : ℂ)) (fun i => G' i (s : ℂ))) :
    gsumCoeff μ Lab A y0 G T = gsumCoeff μ Lab' A' y0' G' T := by
  subst hLb hι
  obtain rfl := eq_of_heq hLab
  obtain rfl := eq_of_heq hy0
  obtain rfl := Subsingleton.elim fL fL'
  obtain rfl := Subsingleton.elim fi fi'
  exact gsumCoeff_congr μ A A' y0 G G' T hGdep
    (fun s hs y _ => congrFun (eq_of_heq (hA s hs)) y)
    (fun s hs i _ => congrFun (eq_of_heq (hG s hs)) i)

/-- **Real compatibility** (`…_of_match`): let `I` be marks of the complex step and `J` marks of the
real step at the same setting `S`, `DC`, `DR` determinant expansions.  Suppose the label systems
agree (`I.Lb = J.Lb`, `I.ι = J.ι`, `I.Lab ≅ J.Lab`, `I.y0 ≅ J.y0`), the activities `H(Y; s, ·)` and
the marks `G_i(s, ·)` agree as functions for every real interpolation parameter `s ∈ [0,1]`, and
the determinant terms agree at `T`.  Then the complex and the real coefficient agree at `T`.

Matching hypotheses already available: `WoneC_eq`, `WtwoC_eq` (`StepComplexAgree`) identify the
exponents `WoneC = Wone` on `s ∈ [0,1]` where `χ_fl(ψ̂) = 1`; they do not identify the activities,
which are only determined through `hW` almost everywhere, so the activity and mark agreement here
is not discharged by them. -/
theorem e1CoeffC_eq_e1Coeff_of_match (I : E1MarksC S C BS z) (J : E1Marks S C BS z)
    {κ'' cdet κ₂ cdet₂ : ℝ} (DC : DetExpansionC S m₀ z κ'' cdet)
    (DR : DetExpansion S m₀ z κ₂ cdet₂)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hLb : I.Lb = J.Lb) (hι : I.ι = J.ι) (hLab : HEq I.Lab J.Lab) (hy0 : HEq I.y0 J.y0)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HEq (fun y => (I.A (s : ℂ)).H y) (fun y => (J.A (s : ℂ)).H y))
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HEq (fun i => I.G i (s : ℂ)) (fun i => J.G i (s : ℂ)))
    (hdet : DC.term T = DR.term T) :
    e1CoeffC I DC T = e1Coeff J DR T := by
  rw [e1CoeffC_eq, e1Coeff_eq, hdet]
  congr 1
  clear hdet
  exact gsumCoeff_heq BS.μ I.A J.A I.y0 J.y0 I.G J.G T I.dep hLb hι hLab hy0 hA hG

end Coeff

section Witness

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **Non-vacuity: two different data in one family** (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`).
For the landed chart parameters there are a step setting `S` and a radius `t` such that the chart
`Ξ^c(𝔹_2; 1, t)` contains two different block data with `h ≡ h₀`: the nonreal datum `S.D'` and the
real datum `D`; both raw data lie in the slice, the steps `S` and `S.withDatum D hD` have the same
fluctuation measure and different block data, and a determinant expansion exists at each. -/
theorem exists_family_two_data :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (t : ℝ) (D : BgData S.G' 2)
      (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν 2 1 t S.D' ∧ XiCData S.G' S.a S.ν 2 1 t D ∧
      ¬ S.D'.IsReal ∧ D.IsReal ∧ D ≠ S.D' ∧
      rawOf S.D' ∈ paramSlice S t ∧ rawOf D ∈ paramSlice S t ∧
      (S.withDatum D hD).nuFl = S.nuFl ∧ (S.withDatum D hD).D' ≠ S.D' ∧
      (∀ (m₀ : ℕ) (z : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (κ'' : ℝ), 0 ≤ κ'' →
        (∃ c, Nonempty (DetExpansionC S m₀ z κ'' c)) ∧
        (∃ c, Nonempty (DetExpansionC (S.withDatum D hD) m₀ z κ'' c))) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, hFl, hMX, hdm, hα, hsm, hc7, hsmR⟩ :=
    exists_chart_params
  obtain ⟨Dn, hXn, hDn, hnr⟩ := exists_nonreal_xiCData (bgHyp_rho m₁) (GP m₁ (rhoSep m₁))
    (fun x => (isLevel_GP m₁ x).1) (by norm_num : 1 < 2) (by simp) ht0
  have hX := exists_xiC (bgHyp_rho m₁) (GP m₁ (rhoSep m₁)) hN2 (by simp) ht0
  have hΩ : ∀ x, x ∈ (GP m₁ (rhoSep m₁)).Ω 1 := fun x => (isLevel_GP m₁ x).1
  have hDh : ∀ x i, (witnessD m₁).h x i = (unitVec hN2 i : ℂ) := fun x i =>
    unitBg_h_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) (hΩ x) i
  have hXr : XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t (witnessD m₁) :=
    ⟨_, _, 0, 0, hX, fun x hx i => by
      rw [show (witnessD m₁).Ψ x i = (unitVec hN2 i : ℂ) from
        unitBg_Ψ_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i]
      simp, fun x hx i => by rw [hDh x i]; simp⟩
  have hreal : (witnessD m₁).IsReal :=
    isReal_of_inDomainR (witnessData_domain (m₁ := m₁) (β := 1) (δ := 1) (δ' := 1) one_pos)
  let S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := chartSetting m₁ Dn hDn 1 1
  have hne : witnessD m₁ ≠ Dn := fun h => hnr (h ▸ hreal)
  refine ⟨m₁, S, t, witnessD m₁, hDh, hXn, hXr, hnr, hreal, hne,
    rawOf_mem_paramSlice hXn hDn, rawOf_mem_paramSlice hXr hDh, rfl, hne, fun m₀ z κ'' hκ => ?_⟩
  exact ⟨nonempty_detExpansionC S m₀ z hκ, nonempty_detExpansionC (S.withDatum _ hDh) m₀ z hκ⟩

end Witness

end Balaban.Fluctuation
