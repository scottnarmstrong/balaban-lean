/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerTransport
public import Balaban.Polymer.TwoTorusE1Coef
public import Balaban.Analysis.SourceRay
import Mathlib.Tactic.Linarith

/-!
# Agreement of the cluster terms on two tori

* `presum_transport`, `Pst_transport`: the local term `P(S) = Pst μ Lab H S` of the cluster expansion on a
  first torus agrees with `P'(σ '' S) = Pst μ' Lab' H' (σ '' S)` of a second torus, for `S ⊆ B` and a map of
  blocks `σ` injective on `S`, whenever (i) the measures correspond (a relation `Rel` between
  configurations carries integrals of functions of the blocks of `Z ⊆ S`, `hint`), (ii) the active
  labels with blocks in `S` correspond bijectively to those with blocks in `σ '' S`, with
  `blocks (ψ y) = σ '' blocks y` and the activities agree on related configurations.  This is the unmarked
  analogue of `Gst_transport` (`PY_mayer_transport`).
* `srcM_transport`: the source coefficients `ℳ_{x,i}` of the two systems agree, when the sources are
  related by a linear map `T` (not increasing the `ℓ¹` norm, carrying unit sources to unit sources) with
  `F' ∘ T = F` on the ball.

**What must be supplied for the chart family** (`chartPst_src_increment`): the activities
`chartTerm + defTerm` of corresponding labels agree for related configurations, which holds when, on a
ball around the blocks of `S`, the decoupled backgrounds `F(s, e)` of the two tori correspond
(C3's `baseBackground_twoTorus`), the whitenings `W` and the defect matrices `D` correspond (finite range
`ρ`; `walkW` / defect transport), the source rows `g` correspond, and the fields `fld Φ`, `fld' Φ'` agree
on related configurations; the labels (`chartLabels ∪ defLabels`) correspond because the hulls of the
translated seeds are translated hulls (`labelSet`), and the measures correspond blockwise.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Analysis Balaban.Localization Balaban.Fluctuation Balaban.Polymer Balaban.Polymer.TwoTorusStep
  MeasureTheory Finset

open scoped Classical

section PstTransport

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {m₀ j : ℕ}
  {Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)} {Ω' : Set (Balaban.Localization.CTorus d L N₁' m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω
local notation "𝔅'" => CubeB (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) m₀ j Ω'

/-- **Transport of the pre-summed terms.**  Let `σ` map the blocks of the first system to those of the
second, injectively on `S`; let the labels be split into active ones (`P`, `P'`) and labels of zero
activity; let the active labels with blocks in `S` correspond bijectively (`ψ`) to the active labels with
blocks in `σ '' S`, with `blocks (ψ y) = σ '' blocks y`, and the activities agree on related
configurations.  Then the pre-summed term of `t ⊆ S` and of `σ '' t` agree on related configurations. -/
theorem presum_transport {Ωb : 𝔅 → Type*} {Ωb' : 𝔅' → Type*}
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀ j Ω' Lb')
    (H : Lb → (∀ b, Ωb b) → ℂ) (H' : Lb' → (∀ b, Ωb' b) → ℂ)
    (σ : 𝔅 → 𝔅') (S : Finset 𝔅) (hσ : Set.InjOn σ (S : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (P : Lb → Prop) (P' : Lb' → Prop) (hH0 : ∀ y, ¬ P y → ∀ Φ, H y Φ = 0)
    (hH0' : ∀ y', ¬ P' y' → ∀ Φ', H' y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ j Ω (Lab.ysite y) ⊆ S → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ S.image σ →
      ∃ y hP hy, ψ y hP hy = y')
    (hH : ∀ y hP hy, ∀ Φ Φ', Rel Φ Φ' → H' (ψ y hP hy) Φ' = H y Φ)
    (t : NePoly 𝔅) (htS : t.1 ⊆ S) (Φ : ∀ b, Ωb b) (Φ' : ∀ b, Ωb' b) (hR : Rel Φ Φ') :
    presum Lab' H' ⟨t.1.image σ, t.2.image σ⟩ Φ' = presum Lab H t Φ := by
  unfold presum
  rw [← Finset.sum_filter_of_ne (p := P') (fun y' _ h => by_contra fun hn => h (hH0' y' hn Φ')),
    ← Finset.sum_filter_of_ne (p := P) (fun y _ h => by_contra fun hn => h (hH0 y hn Φ))]
  symm
  have hyS : ∀ y ∈ (Finset.univ.filter (fun y => blocksOf m₀ j Ω (Lab.ysite y) = t.1)).filter P,
      P y ∧ blocksOf m₀ j Ω (Lab.ysite y) ⊆ S := fun y hy =>
    ⟨(Finset.mem_filter.1 hy).2, (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2 ▸ htS⟩
  refine Finset.sum_bij (fun y hy => ψ y (hyS y hy).1 (hyS y hy).2) (fun y hy => ?_)
    (fun y₁ hy₁ y₂ hy₂ h => hψinj y₁ _ _ y₂ _ _ h) (fun y' hy' => ?_)
    (fun y hy => (hH y _ _ Φ Φ' hR).symm)
  · have hyt : blocksOf m₀ j Ω (Lab.ysite y) = t.1 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hψP _ _ _⟩
    rw [hψb y _ _, hyt]
  · have h' : blocksOf m₀ j Ω' (Lab'.ysite y') = t.1.image σ :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 hy').1).2
    obtain ⟨y, hP, hyS', rfl⟩ := hψsurj y' (Finset.mem_filter.1 hy').2
      (h' ▸ Finset.image_subset_image htS)
    have hyt : blocksOf m₀ j Ω (Lab.ysite y) = t.1 :=
      eq_of_image_eq_of_injOn hσ hyS' htS ((hψb y hP hyS').symm.trans h')
    exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hyt⟩, hP⟩, rfl⟩

/-- **D8: transport of the local term `P(S)` of the cluster expansion between two tori.**  In the setting of
`presum_transport`, let `Rel` carry integrals of functions of the blocks of `Z ⊆ S` to integrals of the
corresponding functions (`hint`), and let each activity depend on the blocks of its label.  Then
`P'(σ '' S) = P(S)`: the local terms of the two cluster expansions agree. -/
theorem Pst_transport {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb' b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀ j Ω' Lb')
    (H : Lb → (∀ b, Ωb b) → ℂ) (H' : Lb' → (∀ b, Ωb' b) → ℂ)
    (hHdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y))
    (σ : 𝔅 → 𝔅') (S : Finset 𝔅) (hσ : Set.InjOn σ (S : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (hint : ∀ Z ⊆ S, ∀ (F : (∀ b, Ωb b) → ℂ) (F' : (∀ b, Ωb' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (P : Lb → Prop) (P' : Lb' → Prop) (hH0 : ∀ y, ¬ P y → ∀ Φ, H y Φ = 0)
    (hH0' : ∀ y', ¬ P' y' → ∀ Φ', H' y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf m₀ j Ω (Lab.ysite y) ⊆ S → Lb')
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hP hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ S.image σ →
      ∃ y hP hy, ψ y hP hy = y')
    (hH : ∀ y hP hy, ∀ Φ Φ', Rel Φ Φ' → H' (ψ y hP hy) Φ' = H y Φ) :
    Pst μ' Lab' H' (S.image σ) = Pst μ Lab H S := by
  unfold Pst
  exact PY_mayer_transport μ μ' σ S hσ (presum Lab H) (presum Lab' H') Rel hint
    (fun t => presum_depOn Lab hHdep t)
    (fun t ht Φ Φ' hR => presum_transport Lab Lab' H H' σ S hσ Rel P P' hH0 hH0' ψ hψP hψb hψinj
      hψsurj hH t ht Φ Φ' hR)

end PstTransport


section SrcTransport

variable {ι J ι' : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
  [Fintype ι'] [DecidableEq ι']

/-- **Transport of the source coefficients `ℳ`.**  Let `T` be a linear map of the sources of a first
system to those of a second, not increasing the `ℓ¹` norm, with `F' ∘ T = F` on the `ℓ¹` ball of radius `G`
(`F'` analytic there), and carrying the unit source at `(x, i)` to the unit source at `(x', i)`.  Then
`ℳ_{x,i}(g) = ℳ'_{x',i}(T g)` for `‖g‖₁ < G`. -/
theorem srcM_transport {F : (ι → J → ℂ) → ℂ} {F' : (ι' → J → ℂ) → ℂ} {G : ℝ}
    (T : (ι → J → ℂ) →L[ℂ] (ι' → J → ℂ)) (hl1 : ∀ g, l1src (T g) ≤ l1src g)
    (hF' : AnalyticOnNhd ℂ F' {g | l1src g < G})
    (hFT : ∀ g, l1src g < G → F' (T g) = F g) {g : ι → J → ℂ} (hg : l1src g < G)
    (x : ι) (x' : ι') (i : J) (hT : T (unitSrc x i) = unitSrc x' i) :
    srcM F g x i = srcM F' (T g) x' i := by
  unfold srcM
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hh : l1src ((t : ℂ) • g) < G := l1_smul_lt hg ht.1 ht.2
  have hTh : l1src (T ((t : ℂ) • g)) < G := (hl1 _).trans_lt hh
  have hopen : IsOpen {g : ι → J → ℂ | l1src g < G} := isOpen_lt continuous_l1src continuous_const
  have hev : F =ᶠ[nhds ((t : ℂ) • g)] fun h => F' (T h) := by
    filter_upwards [hopen.mem_nhds hh] with h hh' using (hFT h hh').symm
  have hdiff : DifferentiableAt ℂ F' (T ((t : ℂ) • g)) := (hF' _ hTh).differentiableAt
  have hchain : fderiv ℂ (fun h => F' (T h)) ((t : ℂ) • g) =
      (fderiv ℂ F' (T ((t : ℂ) • g))).comp T := by
    have := (hdiff.hasFDerivAt.comp ((t : ℂ) • g) T.hasFDerivAt)
    exact this.fderiv
  rw [hev.fderiv_eq, hchain, ContinuousLinearMap.comp_apply, hT, map_smul]

end SrcTransport

end Balaban.LargeField.Base
