/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BasePre
public import Balaban.Spine.FrozenSFBudget
public import Balaban.Spine.FrozenStep

/-!
# The first step in regime (B) from its parts (A3-2)

`baseFlatStepInput_of_parts` is the frozen counterpart of `basePreStepInput_of_parts`
(`Spine/BasePre.lean`), with the same data record `BaseRaw`/`BaseMap` and the same parts wherever
the statement does not depend on the regime: `BaseConstsInput`, `BaseCorrInput`, `BaseOpBoundInput 2`
and `BaseCoherenceInput 2` (the family with the histories complete up to `(1, 2)`: `Γ.famR 2`). The
regime-dependent parts are `BaseFlatSFInput` ((D2♭) `SFFlat2`, (D9♭)), `BaseFlatFormInput`
(`D1Form2`) and `BaseFlatBdryInput` (`D7Bdry2Post`). Proved inside: completeness, the pin `D4Pin 2`
(no component is kept above `k₀ = 0`), the budget (H6♭) at the scale `1` (`frozenBudget_of_pin`), (I.2)
at the scale `1` and the mass bound `ν₁ ≤ 9/10` (`nu_succ_le_of_coeffBounds`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale RegionHistory

namespace Balaban.RootFSpine

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A3-2: the small-field data of the first step in regime (B)** (complete backgrounds): (D2♭),
(D8), (D9♭), the free flow of `a_1`, `β_0 = β`, `ν_0 = ν`, (I.2) at the scale `0`, `z₁ > 0`. -/
def BaseFlatSFInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ (fun k => k = 0) Γ fun κ c₉ β ν _ _ _ _ Γ =>
    SFFlat2 (P6 κ c₉) (kZero d (T κ c₉).L β ν) Γ.sf ∧
    D8SF (P6 κ c₉).m₀ Γ.sf ∧ D9Flat (P6 κ c₉) Γ.sf ∧
    (∀ j, 1 ≤ j → j ≤ 1 → Γ.sf.a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j) ∧
    Γ.sf.β 0 = β ∧ Γ.sf.ν 0 = ν ∧
    RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) Γ.sf.β Γ.sf.ν 0 ∧
    0 < Γ.z₁ ∧ Γ.sf.z 1 = Γ.z₁

/-- **A3-2 (c): the transform relation of the first step in regime (B)** (`D1Form2`). -/
def BaseFlatFormInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ (fun k => k = 0) Γ fun κ c₉ β ν h kf _ _ Γ =>
    ∀ (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (nK : ℕ) [NeZero nK],
      D1Form2 ((Γ.famR 2).ctx hM6 (by omega) nK) Γ.vc ((Γ.famR 2).lf nK) h
        (firstDensity d N (T κ c₉) β (cs₀ κ c₉).aKer Γ.z₁ ν h kf nK)

/-- **A3-2 (a): the boundary terms of the first step in regime (B)** (`D7Bdry2Post`, constant
`B₀`, rate `κ`). -/
def BaseFlatBdryInput (Γ : BaseMap d N T C7 cs₀ ϱ) : Prop :=
  BaseImageInput d N T C7 cs₀ ϱ (fun k => k = 0) Γ fun κ c₉ β _ h kf _ _ Γ =>
    ∀ (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (nK : ℕ) [NeZero nK],
      D7Bdry2Post (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
          (kf + 1) hM6) (sides_hnn (T κ c₉).L (kf + 1) nK) (by omega) ((Γ.famR 2).lf nK)
        (fun A => (A.H.step 1).Z) (Γ.famR 2).weights Γ.cs.mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉)) Γ.cs.nu (C7 κ c₉).B0
        (P6 κ c₉).κ h (rH κ c₉)

end Inputs

section Assembly

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}

/-- **The first step in regime (B) from its parts** (LFR Theorem II.7.10 with `k₀ = 0`). -/
theorem baseFlatStepInput_of_parts {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMap d N T C7 cs₀ ϱ) (hS : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ)
    (hC : BaseConstsInput d N T P6 C7 PB cs₀ M1 c ϱ (fun k => k = 0) Γ)
    (hCo : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ)
    (hF : BaseFlatFormInput d N T P6 C7 cs₀ ϱ Γ) (hB : BaseFlatBdryInput d N T P6 C7 cs₀ rH ϱ Γ)
    (hO : BaseOpBoundInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ)
    (hCh : BaseCoherenceInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ) :
    BaseFlatStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₁, h₁⟩ := hS κ hκ c₉ hc₉
  obtain ⟨b₂, h₂⟩ := hC κ hκ c₉ hc₉
  obtain ⟨b₄, h₄⟩ := hCo κ hκ c₉ hc₉
  obtain ⟨b₅, h₅⟩ := hF κ hκ c₉ hc₉
  obtain ⟨b₆, h₆⟩ := hB κ hκ c₉ hc₉
  obtain ⟨b₇, h₇⟩ := hO κ hκ c₉ hc₉
  obtain ⟨b₈, h₈⟩ := hCh κ hκ c₉ hc₉
  obtain ⟨b₀, h₀⟩ := prefixBudgetFacts d δ T P6 C7 PB cs₀ M1 c ϱ hP κ hκ c₉ hc₉
  obtain ⟨-, -, -, -, -, -, -, hM6, -, -, -, -, -, -, -, -, -, hflow, -⟩ := hP κ hκ c₉ hc₉
  refine ⟨max (max (max b₁ b₂) (max b₄ b₅)) (max (max b₆ b₇) (max b₈ b₀)), ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ hk0
  simp only [max_le_iff] at hβ
  obtain ⟨⟨⟨hb₁, hb₂⟩, hb₄, hb₅⟩, ⟨hb₆, hb₇⟩, hb₈, hb₀⟩ := hβ
  obtain ⟨hsf2, hD8, hD9, hafree, hβ0, hν0, hrun0, hz1, hz⟩ := h₁ β hb₁ ν hν hνL h hh kf hkf hk0
  obtain ⟨hgeo, o1, o2, o3, o4, o5, o6, o7, hcoh, hfield⟩ := h₂ β hb₂ ν hν hνL h hh kf hkf hk0
  have hcorr := h₄ β hb₄ ν hν hνL h hh kf hkf hk0
  have hform := h₅ β hb₅ ν hν hνL h hh kf hkf hk0
  have hbdry := h₆ β hb₆ ν hν hνL h hh kf hkf hk0
  have hop := h₇ β hb₇ ν hν hνL h hh kf hkf hk0
  have hcoher := h₈ β hb₈ ν hν hνL h hh kf hkf hk0
  have facts := h₀ β hb₀ ν hν kf hkf
  set G := Γ κ c₉ β ν h kf with hG
  have hL3 : (3 : ℝ) ≤ (T κ c₉).L := by exact_mod_cast (hP κ hκ c₉ hc₉).1
  have hkf1 : 0 < kf := by
    by_contra hcon
    obtain rfl : kf = 0 := by omega
    have := hkf.1
    simp only [mul_zero, zero_add] at this
    linarith
  have hrun1 : RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) G.sf.β G.sf.ν 1 :=
    runningHypTo_succ_of_coeffBounds_core (k := 0) (P := massOne (P6 κ c₉))
      hsf2.admissible.γ_pos hsf2.admissible.c₈_pos hflow hsf2.coeff hβ0 hν0 hrun0
  have hmass : G.sf.ν 1 ≤ 9 / 10 := by
    have hL2 : 2 ≤ (T κ c₉).L := by exact_mod_cast (show 2 ≤ (T κ c₉).L by
      have := (hP κ hκ c₉ hc₉).1; omega)
    have h1 := nu_succ_le_of_coeffBounds (k := 0) (P := massOne (P6 κ c₉)) hL2
      hsf2.admissible.γ_pos hflow hsf2.coeff (show 0 < G.sf.ν 0 by rw [hν0]; exact hν)
    rw [hν0] at h1
    nlinarith
  have hpin : ∀ (nK : ℕ) [NeZero nK], D4Pin (1 + 1) ((G.famR 2).lf nK) := by
    intro nK _ A _ j hj1 hjt Z hK
    exact absurd hK.2.1 (by omega)
  have hbudget : ∀ (nK : ℕ) [NeZero nK], D6Flat kf ((G.famR 2).lf nK) := fun nK _ =>
    frozenBudget_of_pin (k := 0) ((G.famR 2).lf nK) facts o5 o6 o7 (fun j hj => hcoh.beta_P j hj)
      hrun1 (hpin nK) (by omega) hkf1
  refine ⟨G.z₁, hz1, G.sf.ν 1, ?_⟩
  refine ⟨hM6, by omega, G.R, G.geo, G.cs, G.P, G.famR 2, G.St, G.vc, hgeo, o1, o2, o3, o4, o5, o6,
    o7, ?_, hβ0, hν0, rfl, hrun1, hcoher, hmass⟩
  exact
    { range := by omega
      coh := hcoh
      field := hfield
      complete := fun nK _ => canonHist_complete 1 2
      form := fun nK _ => hform hM6 nK
      corr := hcorr
      sfData := hsf2
      pin := hpin
      opBound := fun nK _ => hop nK
      budget := hbudget
      bdry := fun nK _ => hbdry hM6 nK
      coherent := hD8
      coeff := hD9 }

/-- **`BaseStepInput` from the first-step map and its parts** (LFR Theorem II.7.10): regime (A) from
`basePreStepInput_of_parts` and the operation `R` at the scale `1`, regime (B) from
`baseFlatStepInput_of_parts`. -/
theorem baseStepInput_of_maps {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Γ : BaseMap d N T C7 cs₀ ϱ) (hR : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hQ : FlowRateInput T P6)
    (hS : BaseSFInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ)
    (hC : BaseConstsInput d N T P6 C7 PB cs₀ M1 c ϱ (fun k => 1 ≤ k) Γ)
    (hCo : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ)
    (hF : BaseFormInput d N T P6 C7 cs₀ ϱ (fun k => 1 ≤ k) Γ)
    (hB : BaseBdryInput d N T P6 C7 cs₀ rH ϱ (fun k => 1 ≤ k) Γ)
    (hO : BaseOpBoundInput d N T C7 cs₀ ϱ 1 (fun k => 1 ≤ k) Γ)
    (hCh : BaseCoherenceInput d N T C7 cs₀ ϱ 1 (fun k => 1 ≤ k) Γ)
    (hV : BaseVacuumInput d N T C7 cs₀ ϱ (fun k => 1 ≤ k) Γ)
    (hSf : BaseFlatSFInput d N T P6 C7 cs₀ ϱ Γ)
    (hCf : BaseConstsInput d N T P6 C7 PB cs₀ M1 c ϱ (fun k => k = 0) Γ)
    (hCof : BaseCorrInput d N T P6 C7 cs₀ ϱ (fun k => k = 0) Γ)
    (hFf : BaseFlatFormInput d N T P6 C7 cs₀ ϱ Γ) (hBf : BaseFlatBdryInput d N T P6 C7 cs₀ rH ϱ Γ)
    (hOf : BaseOpBoundInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ)
    (hChf : BaseCoherenceInput d N T C7 cs₀ ϱ 2 (fun k => k = 0) Γ) :
    BaseStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  baseStepInput_of_parts d N T P6 C7 PB cs₀ M1 c rH ϱ
    (basePreStepInput_of_parts hP Γ hS hC hCo hF hB hO hCh hV) hR hQ
    (baseFlatStepInput_of_parts hP Γ hSf hCf hCof hFf hBf hOf hChf)

end Assembly

end Balaban.RootFSpine
