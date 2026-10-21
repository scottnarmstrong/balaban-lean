/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FrozenSFClauses
public import Balaban.Spine.SFStep
public import Balaban.LargeField.Def7v2Interface

/-!
# The sub-inputs of the frozen small-field step (A4f-1, parts 2 and 3)

The frozen step runs on complete backgrounds at every scale `k₀ ≤ k < k̂_f` (FLUCT-A: for every `k`,
including `k = k₀`, one complete small-field fluctuation step followed by the complete P4 recursion;
the "switch at `k₀`" of the first version of FLUCTUATION Lemma 2.9 is withdrawn). The sub-inputs are
therefore the statements A4-1a–f, i of `Spine/SFStep.lean` for the maps `Φ♭` at the flat class:

* `FrozenImageInput`: `SFImageInputGen` over the scales `max(k₀, 1) ≤ k < k̂_f` (`ν L^{2k+2} < 1`) and
  the class `SFFlatClassAt` with `ν_k L² ≤ 7/8` (the hypotheses of `FrozenSFStepInput`);
* `FrozenInheritInput`, `FrozenNewLevelInput`, `FrozenRenormInput` (coefficient bounds at the constants
  `massOne P6`), `FrozenDensityInput`, `FrozenRemainderInput` (allowance `1`: no operation `R`),
  `FrozenCoherenceInput`: the same properties `SFInheritQ`, … as in the pre-`R` steps, no copies;
* `FrozenIntegrableInput`: `StepIntegrableInputGen` for the class `ℛ♭_k`;
* A4-1g (the vacuum constant) has no frozen analogue: a member of `ℛ♭_k` carries no vacuum flow, and
  the frozen step has no operation `R` whose weights read one;
* `FrozenSwitchInput` (the SF/LF interface at the first frozen scale `k = k₀`, `OPEN-SF-LF-INTERFACE`
  of `notes/phase1/FLUCT-A.md`; `SFtoLFInterface`, `Def7v2Interface.lean`): at every scale `k > k₀` the
  interface is trivial (`sfToLFInterface_complete`); at `k = k₀` it is the exact density conversion
  between the free reference of the large-field region and the complete background, for the small-field
  data of the class member at the switching scale. `frozenSwitch_of_lt` proves the case `k > k₀`.

Rule 10: `FrozenImageInput` and `FrozenIntegrableInput` are statements about the class `SFFlatClassAt`
(`sfFlatClassAt_witness`); the Q-properties are the landed ones (`Spine/SFStep.lean`). The inputs need
the exemption of the seven inputs.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale

namespace Balaban.RootFSpine

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **The form of the frozen small-field sub-inputs**: a property `Q` of the image `Φ sf` of the
small-field data `sf` of every member of `ℛ♭_k`, `max(k₀, 1) ≤ k < k̂_f`, with `ν_k L² ≤ 7/8`, for
`β ≥ β₀(κ, c₉)`, `0 < ν ≤ 7/8 L⁻²`. `Φ` is the small-field step at the complete backgrounds
(`Φ♭`). -/
def FrozenImageInput (Q : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉) → Prop) : Prop :=
  SFImageInputGen d N T C7 ϱ Φ
    (fun κ c₉ β ν k X => 1 ≤ k → kZero d (T κ c₉).L β ν ≤ k →
      ν * ((T κ c₉).L : ℝ) ^ (2 * k + 2) < 1 → X)
    (fun κ c₉ β ν k _ sf =>
      SFFlatClassAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉) (cs₀ κ c₉).aKer β ν k sf ∧ sf.ν k * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8) Q

/-- **A4-1a for the frozen steps** (the inherited data; ruling R6; the free flow). -/
def FrozenInheritInput : Prop :=
  FrozenImageInput d N T P6 C7 cs₀ ϱ Φ (SFInheritQ d N T C7 ϱ cs₀)

/-- **A4-1b for the frozen steps** (the new level on the local generating set of each polymer). -/
def FrozenNewLevelInput : Prop :=
  FrozenImageInput d N T P6 C7 cs₀ ϱ Φ (SFNewLevelQ d N T P6 C7 ϱ)

/-- **A4-1c for the frozen steps** (the counterterm system; (H.6) with the mass range `ν ≤ 1`,
`massOne P6`, and (H.5) at `k + 1`). -/
def FrozenRenormInput : Prop :=
  FrozenImageInput d N T P6 C7 cs₀ ϱ Φ (SFRenormQ d N T P6 C7 ϱ (fun κ c₉ => massOne (P6 κ c₉)))

/-- **A4-1d for the frozen steps** (the density of the new level is real). -/
def FrozenDensityInput : Prop :=
  FrozenImageInput d N T P6 C7 cs₀ ϱ Φ (SFDensityQ d N T P6 C7 ϱ)

/-- **A4-1e for the frozen steps** (the remainders `ℛ^{(k+1)}_n` satisfy P5 H4 with the allowance
`1`: there is no operation `R`, so no half of the allowance is kept for `ℛ''`). -/
def FrozenRemainderInput : Prop :=
  FrozenImageInput d N T P6 C7 cs₀ ϱ Φ (SFRemainderQ d N T P6 ϱ C7 (fun _ _ _ => 1))

/-- **A4-1f for the frozen steps** (torus coherence (D8) of the new level and of `ℛ^{(k+1)}`). -/
def FrozenCoherenceInput : Prop :=
  FrozenImageInput d N T P6 C7 cs₀ ϱ Φ (SFCoherenceQ d N T P6 C7 ϱ)

/-- **A4-1i for the frozen steps** (the members of `ℛ♭_k`, `max(k₀, 1) ≤ k < k̂_f`, with
`ν_k L² ≤ 7/8`, are integrable on every torus of the family). -/
def FrozenIntegrableInput : Prop :=
  StepIntegrableInputGen d N T cs₀
    (fun _ _ _ _ kf k X => 1 ≤ k → k < kf → X)
    (fun κ c₉ β ν h kf k _ _ ρ νk =>
      kZero d (T κ c₉).L β ν ≤ k ∧
      FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk ∧ νk * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8)

/-- **The SF/LF interface at the first frozen scale** (`k = k₀`; FLUCT-A, `OPEN-SF-LF-INTERFACE`;
INTERFACE-A): for the small-field data of a member of `ℛ♭_{k₀}` and every Def-6 torus there is kernel
data `SFtoLFData` satisfying `SFtoLFInterface` for the regime `(k₀, ν)`, the constants `ifc` of the
interface: the chord, `ΔE` and `ΔF` sums of the large-field comparison, their localized bounds and the
budget (3.7) at the pre-`k₀` scales. -/
def FrozenSwitchInput (ifc : ℝ → ℝ → IfConsts) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 → ∀ [NeZero (T κ c₉).L],
  ∀ sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ (kZero d (T κ c₉).L β ν) N (ϱ κ c₉),
    SFFlatClassAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉) (cs₀ κ c₉).aKer β ν
      (kZero d (T κ c₉).L β ν) sf →
    ∀ (N₁ : ℕ) [NeZero N₁], ∃ X : SFtoLFData d (T κ c₉).L N₁ (C7 κ c₉).m₁
        (kZero d (T κ c₉).L β ν) N (ϱ κ c₉),
      SFtoLFInterface (P6 κ c₉) (⟨kZero d (T κ c₉).L β ν, sf.ν⟩ : Regime (T κ c₉).L) sf.β sf.a
        (sf.Tm N₁) X (ifc κ c₉)

end Inputs

/-- **The interface above the switching scale is trivial**: for the small-field data of a frozen step
at a scale `k > k₀` the interface clause holds with the zero kernel data (`sfToLFInterface_complete`). -/
theorem frozenSwitch_of_lt {d L m₁ k N N₁ : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Def6.Consts}
    {k0 : ℕ} {sf : SFData d L m₁ k N ϱ} (h : k0 < k) (c : IfConsts) (hCD : 0 ≤ c.CD)
    (hCE : 0 ≤ c.CE) (hCF : 0 ≤ c.CF) (hβ : 0 ≤ sf.β k) (hν : 0 ≤ sf.ν k) (hE : 0 ≤ P.E₀)
    (hε : 0 ≤ P.eps d L k) :
    SFtoLFInterface P (⟨k0, sf.ν⟩ : Regime L) sf.β sf.a (sf.Tm N₁)
      ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩ c :=
  sfToLFInterface_complete (sf.Tm N₁) h hCD hCE hCF hβ hν hE hε

end Balaban.RootFSpine
