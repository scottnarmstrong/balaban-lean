/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseStep
public import Balaban.Spine.HistCanon
public import Balaban.Spine.BaseCarrier
public import Balaban.Spine.BudgetSetupOfRun
public import Balaban.Spine.PrefixBudget
public import Balaban.Spine.LFStep

/-!
# The first step in regime (A) from its parts (A3-1)

The data of the first step are one record per class point (`BaseRaw`): the small-field data `sf` at
the scale `1`, the constants `cs, P`, the radii `R` and geometry `geo`, and on every torus of the
family the exponents, step data, kept data and boundary terms; the histories are the canonical
complete set (`canonHist`). The map `Γ` (`BaseMap`) is a parameter of the sub-spine, defined by the
provider. The parts are properties of `Γ`:

* `BaseSFInput` (A3-1 (a), (g)): the small-field data (D2) with the allowance `preFac`, (D8), (D9),
  the free flow of `a_1`, `β_0 = β`, `ν_0 = ν`, (I.2) at the scale `0`, `z₁ > 0`, `β_j ≥ e⁻¹`;
* `BaseConstsInput`: the ties of the constants, `Coh`, `FieldClauses`;
* `BaseKernelInput` (b): the step data carry the base kernel `K_0` of a physical carrier;
* `BaseCorrInput`, `BaseFormInput` (c), `BaseBdryInput` (a), `BaseOpBoundInput`,
  `BaseCoherenceInput` (f).

Proved inside `basePreStepInput_of_parts`: completeness of the histories (`canonHist`), the pin
`D4Pin 1` (no scale `j` with `1 ≤ j < 1`), the budget (H6′)^pre (LF-2 (i) on the budget setup of
(I.2) up to the scale `1`, from (H.6) at `1` and `FlowRateInput`), the vacuum flow `E ≡ 0`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale RegionHistory

namespace Balaban.RootFSpine

/-- **The data of the first step at one class point**: no proofs, only the objects. -/
structure BaseRaw (d N : ℕ) (T : Typing) (C7 : Consts7) (ϱ β ν : ℝ) (kf : ℕ) (aKer : ℝ)
    [NeZero T.L] [NeZero T.M] where
  z₁ : ℝ
  R : ℕ → ℝ
  geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, aKer] (sides T.L (kf + 1) nK) R T.M
  cs : OpConsts
  P : BudgetConsts
  sf : SFData d T.L C7.m₁ 1 N ϱ
  κK : ∀ (nK : ℕ) [NeZero nK],
    ℕ → LocalHistory 𝒮[d, T, β, aKer] (sides T.L (kf + 1) nK) T.M (kf + 1) → ℝ
  SD : ∀ (nK : ℕ) [NeZero nK], StepData (kZero d T.L β ν) (geo nK) cs N
    (kappaStepLoc (K := kf + 1) 𝒮[d, T, β, aKer] P T.M)
  KD : ∀ (nK : ℕ) [NeZero nK], KeptData (kZero d T.L β ν) (geo nK) cs N (κK nK)
    (Setting.lam 𝒮[d, T, β, aKer])
  B : ∀ (nK : ℕ) [NeZero nK], BTerms 𝒮[d, T, β, aKer] (sides T.L (kf + 1) nK) R
    (kZero d T.L β ν) (kf + 1) T.M N 1
  St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ 1 N
  vc : CorrCoef d

/-- The family of representations of the first step: the canonical histories on every torus. -/
noncomputable def BaseRaw.fam {d N : ℕ} {T : Typing} {C7 : Consts7} {ϱ β ν : ℝ} {kf : ℕ}
    {aKer : ℝ} [NeZero T.L] [NeZero T.M] (Γ : BaseRaw d N T C7 ϱ β ν kf aKer) :
    RepFam 𝒮[d, T, β, aKer] Γ.R (kZero d T.L β ν) (kf + 1) T.M N Γ.geo Γ.cs Γ.P 1 C7.m₁ ϱ where
  sf := Γ.sf
  lf := fun nK _ =>
    { hist := canonHist 𝒮[d, T, β, aKer] (sides T.L (kf + 1) nK) Γ.R (kZero d T.L β ν) (kf + 1) 1 1
      κK := Γ.κK nK
      SD := Γ.SD nK
      KD := Γ.KD nK
      B := Γ.B nK }

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The first-step map** (a parameter of the sub-spine, defined by the provider). -/
abbrev BaseMap :=
  ∀ (κ c₉ β ν : ℝ) (_ : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M], BaseRaw d N (T κ c₉) (C7 κ c₉) (ϱ κ c₉) β ν kf (cs₀ κ c₉).aKer

/-- **The form of the parts of the first step**: a property `Q` of the first-step record, for
`β ≥ β₀(κ, c₉)`, `0 < ν ≤ 7/8 L⁻²`, every unit field and the horizon `kf`, in regime (A). -/
def BaseImageInput (Γ : BaseMap d N T C7 cs₀ ϱ)
    (Q : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M], BaseRaw d N (T κ c₉) (C7 κ c₉) (ϱ κ c₉) β ν kf (cs₀ κ c₉).aKer →
        Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  1 ≤ kZero d (T κ c₉).L β ν → Q κ c₉ β ν h kf (Γ κ c₉ β ν h kf)

/-- **A3-1 (a), (g): the small-field data of the first step.** (D2) with the allowance `preFac`,
(D8), (D9), the free flow of `a_1`, `β_0 = β`, `ν_0 = ν`, (I.2) at the scale `0`, `z₁ > 0` equal to
`z_1`, and `β_j ≥ e⁻¹` for `j ≤ 1`. Open: Proposition II.7.9 (the first fluctuation integral). -/
def BaseSFInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun κ c₉ β ν _ _ _ _ Γ =>
    D2SF2 (P6 κ c₉) (kZero d (T κ c₉).L β ν) Γ.sf (preFac ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) ∧
    D8SF (P6 κ c₉).m₀ Γ.sf ∧ D9Coeff (P6 κ c₉) (kZero d (T κ c₉).L β ν) Γ.sf ∧
    (∀ j, 1 ≤ j → j ≤ 1 → Γ.sf.a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j) ∧
    Γ.sf.β 0 = β ∧ Γ.sf.ν 0 = ν ∧
    RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) Γ.sf.β Γ.sf.ν 0 ∧
    0 < Γ.z₁ ∧ Γ.sf.z 1 = Γ.z₁ ∧ (∀ j, j ≤ 1 → -1 ≤ Real.log (Γ.sf.β j))

/-- **The constants of the first step**: the ties to the outer constants, the coherence `Coh` and
the field clauses. -/
def BaseConstsInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun κ c₉ β ν h kf _ _ Γ =>
    (∀ (nK : ℕ) [NeZero nK], (Γ.geo nK).M1 = M1 κ c₉ ∧ (Γ.geo nK).c = c κ c₉) ∧
    Γ.cs.aKer = (cs₀ κ c₉).aKer ∧ Γ.cs.Cpsi = (cs₀ κ c₉).Cpsi ∧ Γ.cs.Cb = (cs₀ κ c₉).Cb ∧
    Γ.cs.aw = (cs₀ κ c₉).aw ∧ Γ.P.c1 = (PB κ c₉).c1 ∧ Γ.P.c2 = (PB κ c₉).c2 ∧
    Γ.P.H0 = (PB κ c₉).H0 ∧
    Coh 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] Γ.R (kZero d (T κ c₉).L β ν) (T κ c₉).M Γ.cs Γ.P
      (P6 κ c₉) (C7 κ c₉) β ν 1 Γ.sf ∧
    FieldClauses 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (kZero d (T κ c₉).L β ν) 1 Γ.cs Γ.sf h

/-- **A3-1 (b): the step kernels of the first step are the base kernels.** On every torus there is a
physical carrier whose base kernel `K_0` is the kernel of the step data at the scale `0`. -/
def BaseKernelInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun κ c₉ β ν _ kf _ _ Γ =>
    ∀ (nK : ℕ) [NeZero nK],
      ∃ inp : BaseSmallFieldInput (T κ c₉).M (kf + 1) (kZero d (T κ c₉).L β ν) (Γ.geo nK) Γ.cs N,
        ∀ (H : RegionHistory _ (sides (T κ c₉).L (kf + 1) nK) Γ.R (kZero d (T κ c₉).L β ν) (kf + 1))
          (hH : H.Admissible) (Z' : H.Comp 1) o x hv,
          ((Γ.SD nK).ker 0 (H.localHistory (T κ c₉).M (kf + 1) 1 Z')).K o x hv =
            baseK0 inp H hH Z' o x hv

/-- **A3-1 (h): the coefficient data of the first step** (P1 (3.106)–(3.110), P5 (1.8)): the
source-form terms `St` and the limits `vc` (`D1CorrLim`). -/
def BaseCorrInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun κ c₉ _ _ h _ _ _ Γ =>
    D1CorrLim (P6 κ c₉).m₀ Γ.sf Γ.St h Γ.vc

/-- **A3-1 (c): the transform relation.** On every torus the density of the first step is the sum
over the histories of the pre-`R` terms (`D1PreForm2`). -/
def BaseFormInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun κ c₉ β ν h kf _ _ Γ =>
    ∀ (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (nK : ℕ) [NeZero nK],
      D1PreForm2 (Γ.fam.ctx hM6 (by omega) nK) Γ.vc (Γ.fam.lf nK) h
        (firstDensity d N (T κ c₉) β (cs₀ κ c₉).aKer Γ.z₁ ν h kf nK)

/-- **A3-1 (a): the boundary terms `ℬ^{(1)}`** of rate `3κ/2` and constant `B_st` (D7). -/
def BaseBdryInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun κ c₉ β _ h kf _ _ Γ =>
    ∀ (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (nK : ℕ) [NeZero nK],
      D7Bdry2 (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
          (kf + 1) hM6) (sides_hnn (T κ c₉).L (kf + 1) nK) (by omega) (Γ.fam.lf nK)
        (fun A => A.H.F.Zpre 1) Γ.fam.weights Γ.cs.mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉)) Γ.cs.nu (C7 κ c₉).Bst
        (3 / 2 * (P6 κ c₉).κ) h (rH κ c₉)

/-- **A3-1 (b): the operator bound at the scale `1`** ((D5) of the first step). -/
def BaseOpBoundInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun _ _ _ _ _ _ _ _ Γ =>
    ∀ (nK : ℕ) [NeZero nK], D5Bound 1 (by omega) (Γ.fam.lf nK)

/-- **A3-1 (f): the torus coherence (D8)** of the large-field half of the first step. -/
def BaseCoherenceInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ Γ fun _ _ _ _ _ _ _ _ Γ => LFCoherent Γ.fam

end Inputs

end Balaban.RootFSpine
