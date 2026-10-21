/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootMarkGeom
public import Balaban.Polymer.LabelSum
public import Balaban.Polymer.MarkedCubesVanish

/-!
# The cluster term of one mark (FLUCTUATION Theorem 3.4; P6 (4.32)–(4.34))

For an interaction `A(u)` on a label system `Lab` of the cubes of a `π'`-union `Ω` (Proposition 3.3)
and one mark `G` reading the cubes of a site `V` (a set of `𝒟_j`), the marked cluster expansion of
Theorem 3.4 gives the terms `G*(V, S)` of the sets `S` of cubes.  This file states the bound and the
support of the term `∫₀¹ G*(V, S) du` of one mark without enlarging the label system of `A`: the
mark's site is added as one more label of zero activity (`singleLabel`, `LabelAct.addMark`, entropy
constant `K_c + 1`), and the term does not see the extension (`Gst_extendByZero`).

* `singleLabel`: the label system with the one site `V` (size `treeLenCovOne V`);
* `entropy_sum_single`, `LabelAct.addMark`: the interaction extended by zero to the mark's label;
* `markTerm`: **the cluster term `∫₀¹ G*(V, S) du` of one mark**;
* `markTerm_spec`: **its bound** `C_PE F₀ e^{-κ₀ 𝗱(V)} e^{-κ' d_Ω(S)}` and **its support** (it vanishes
  unless the cubes of `V` lie in `S`), from `marked_cubes_explicit` at every `u ∈ [0, 1]`;
* `markTerm_eq_zero_of_dOmega_top`: it vanishes when `d_Ω(S) = +∞` (`Gst_eq_zero_of_dOmega_top`);
* `LocInteraction`: **the interaction of a measure on the cubes of a region** (the data of
  Proposition 3.3: labels, activities `A(u)` and the constants of Theorem 3.4 with one mark);
  `markTerm_spec_of_norm_le`: the bound and the support of the cluster term of a mark bounded
  by a constant `B`, `C_PE B e^{(κ_H - κ₀) 𝗱(V)} e^{-κ' d_Ω(S)}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **The label system with one site** `V` of `𝒟_j` meeting `Ω`, of size `treeLenCovOne V`. -/
noncomputable def singleLabel (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V) (hm : (V ∩ Ω).Nonempty) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Unit where
  ysite _ := V
  dl _ := treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V
  isDj _ := hV
  meets _ := hm
  size _ := Or.inl rfl

variable {Lb : Type*} [Fintype Lb]
  {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

open Classical in
/-- **The entropy of the label system with one more site** is at most `K_c + 1` (`κ₀ ≥ 0`). -/
theorem entropy_sum_single (A : LabelAct Lab Ωb εH κH κ0 Kc) (hκ0 : 0 ≤ κ0)
    (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V) (hm : (V ∩ Ω).Nonempty) (b : 𝔅) :
    ∑ y : Lb ⊕ Unit, (if box b.1 (cellSide L m₀ m₁ j) ⊆ (Lab.sum (singleLabel V hV hm)).ysite y then
      Real.exp (-κ0 * (Lab.sum (singleLabel V hV hm)).dl y) else 0) ≤ Kc + 1 := by
  rw [Fintype.sum_sum_type]
  refine add_le_add (A.entropy b) ?_
  simp only [Finset.univ_unique, Finset.sum_singleton, CubeLabels.sum_ysite_inr,
    CubeLabels.sum_dl_inr]
  have hle : Real.exp (-κ0 *
      treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V) ≤ 1 := by
    have := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V
    exact Real.exp_le_one_iff.2 (by nlinarith)
  by_cases h : box b.1 (cellSide L m₀ m₁ j) ⊆ (singleLabel V hV hm).ysite default
  · simp only [h, ↓reduceIte]
    exact hle
  · simp only [h, ↓reduceIte]
    exact zero_le_one

open Classical in
/-- **The interaction extended by zero to the label of a mark** (entropy constant `K_c + 1`). -/
noncomputable def LabelAct.addMark (A : LabelAct Lab Ωb εH κH κ0 Kc) (hε : 0 ≤ εH) (hκ0 : 0 ≤ κ0)
    (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V) (hm : (V ∩ Ω).Nonempty) :
    LabelAct (Lab.sum (singleLabel V hV hm)) Ωb εH κH κ0 (Kc + 1) :=
  labelActExtend Lab (Lab.sum (singleLabel V hV hm)) Sum.inl_injective (fun _ => rfl) (fun _ => rfl)
    hε (entropy_sum_single A hκ0 V hV hm) A

/-- **The cluster term of one mark** `∫₀¹ G*(V, S) du` (Theorem 3.4 at every `u`): the mark `G`
reading the cubes of `V`, the interaction `A(u)`, the set `S` of cubes. -/
noncomputable def markTerm (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (V : Set (CTorus d L N₁ m₁ K))
    (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) : ℂ :=
  ∫ u in (0 : ℝ)..1, Gst μ Lab (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S

/-- **The bound and the support of the cluster term of one mark** (Theorem 3.4 with the mark's site
added to the labels, `marked_cubes_explicit`): with the numerical hypotheses of Theorem 3.4 at the
entropy constant `K_c + 1`, `|∫₀¹ G*(V, S) du| ≤ C_PE F₀ e^{-κ₀ 𝗱(V)} e^{-κ' d_Ω(S)}`, and the term
vanishes unless the cubes of `V` lie in `S`. -/
theorem markTerm_spec (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V)
    (hm : (V ∩ Ω).Nonempty) (G : (∀ b, Ωb b) → ℂ) (hGm : Measurable G)
    (hGdep : DepOn (blocksOf m₀ j Ω V) G) {κG κ' F0 : ℝ}
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG *
      treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc + 1) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG) (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (Kc + 1) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) (S : Finset 𝔅) :
    ‖markTerm μ A V G S‖ ≤ CPE d L (Kc + 1) κH κ0 κ' * F0 *
        Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V) *
        Real.exp (-κ' * dExt S) ∧
      (¬ blocksOf m₀ j Ω V ⊆ S → markTerm μ A V G S = 0) := by
  have hκ0' : 0 ≤ κ0 := by have := aEnt_nonneg d L; linarith
  have hspec := fun u : ℂ => marked_cubes_explicit μ hN hj hΩ
    ((A u).addMark hεpos.le hκ0' V hV hm) (Sum.inr ()) G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε
  have hext : ∀ u : ℂ, ∀ S' : Finset 𝔅,
      Gst μ (Lab.sum (singleLabel V hV hm)) ((A u).addMark hεpos.le hκ0' V hV hm).H
        (blocksOf m₀ j Ω V) G S' = Gst μ Lab (A u).H (blocksOf m₀ j Ω V) G S' :=
    fun u S' => Gst_extendByZero Lab (Lab.sum (singleLabel V hV hm)) Sum.inl_injective
      (fun _ => rfl) μ (A u).H _ G S'
  refine ⟨?_, fun hsub => ?_⟩
  · unfold markTerm
    have hb : ∀ u ∈ Set.uIoc (0 : ℝ) 1, ‖Gst μ Lab (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S‖ ≤
        CPE d L (Kc + 1) κH κ0 κ' * F0 *
          Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V) *
          Real.exp (-κ' * dExt S) := by
      intro u _
      rw [← hext]
      exact (hspec (u : ℂ)).2.2.2.2 S
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    simp
  · unfold markTerm
    have h0 : ∀ u : ℝ, Gst μ Lab (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S = 0 := fun u => by
      rw [← hext]
      exact (hspec (u : ℂ)).2.2.2.1 S hsub
    simp [h0]

/-- **The cluster term of one mark vanishes when `d_Ω(S) = +∞`** (`Gst_eq_zero_of_dOmega_top`). -/
theorem markTerm_eq_zero_of_dOmega_top (μ : ∀ b, Measure (Ωb b))
    [∀ b, IsProbabilityMeasure (μ b)] (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V)
    (hm : (V ∩ Ω).Nonempty) (G : (∀ b, Ωb b) → ℂ) {S : Finset 𝔅}
    (hS : dOmega m₀ j Ω (sitesOf S) = ⊤) : markTerm μ A V G S = 0 := by
  unfold markTerm
  have h0 : ∀ u : ℝ, Gst μ Lab (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S = 0 := fun u => by
    rw [← Gst_extendByZero Lab (Lab.sum (singleLabel V hV hm)) Sum.inl_injective (fun _ => rfl) μ
      (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S]
    exact Gst_eq_zero_of_dOmega_top μ hN hj hΩ (Lab.sum (singleLabel V hV hm))
      (extendByZero Sum.inl (A (u : ℂ)).H) (Sum.inr ()) G S hS
  simp [h0]

/-- **The interaction of a measure on the cubes of a region** (the data of Proposition 3.3 on a
region): a label system `Lab` of the cubes of `Ω`, the activities `A(u)` of the labels for the
parameters `u`, and the constants of Theorem 3.4 with one mark added (entropy constant `K_c + 1`). -/
structure LocInteraction (Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*)
    [∀ b, MeasurableSpace (Ωb b)] where
  /-- the labels -/
  Lb : Type
  [fin : Fintype Lb]
  /-- their sites and sizes -/
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb
  εH : ℝ
  κH : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  /-- the activities at the parameter `u` -/
  A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 ≤ Kc
  hεpos : 0 < εH
  hκ' : 0 ≤ κ'
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * (Kc + 1) ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))

attribute [instance] LocInteraction.fin

/-- `LocInteraction` is inhabited (rule 10): no labels, with constants satisfying the numerical
hypotheses. -/
instance (Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*)
    [∀ b, MeasurableSpace (Ωb b)] : Nonempty (LocInteraction Ωb) := by
  have hc1 := one_le_c1 d L
  have hKc0 : (0 : ℝ) ≤ max (K0 d L (aEnt d L + 1)) 0 := le_max_right _ _
  refine ⟨{ Lb := Empty
            Lab := { ysite := fun y => y.elim, dl := fun y => y.elim, isDj := fun y => y.elim,
                     meets := fun y => y.elim, size := fun y => y.elim }
            εH := 1 / (8 * (max (K0 d L (aEnt d L + 1)) 0 + 1) ^ 3 * c1 d L *
              Real.exp ((3 * (aEnt d L + 1) + c1 d L + 3 / 2 - 2 * (aEnt d L + 1)) * cG d L +
                c1 d L + 0 * cG d L))
            κH := 3 * (aEnt d L + 1) + c1 d L + 3 / 2
            κ0 := aEnt d L + 1
            κ' := 0
            Kc := max (K0 d L (aEnt d L + 1)) 0
            A := fun _ => { H := fun y => y.elim, meas := fun y => y.elim, dep := fun y => y.elim,
                            bound := fun y => y.elim, entropy := fun _ => by simp }
            hκ0 := le_rfl
            hKc := le_max_left _ _
            hεpos := by positivity
            hκ' := le_rfl
            hκ := by linarith
            hε := le_rfl }⟩

/-- **The bound and the support of the cluster term of a mark bounded by a constant** (Theorem 3.4
with the mark's site added to the labels of the interaction `I`, `markTerm_spec` at `κ_G = κ_H`): if
`|G| ≤ B`, then `|∫₀¹ G*(V, S) du| ≤ C_PE B e^{(κ_H - κ₀) 𝗱(V)} e^{-κ' d_Ω(S)}`, and the term
vanishes unless the cubes of `V` lie in `S`. -/
theorem markTerm_spec_of_norm_le
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (I : LocInteraction Ωb) (μ : ∀ b, Measure (Ωb b))
    [∀ b, IsProbabilityMeasure (μ b)] (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (V : Set (CTorus d L N₁ m₁ K)) (hV : IsDj m₀ j V) (hm : (V ∩ Ω).Nonempty)
    (G : (∀ b, Ωb b) → ℂ) (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω V) G) {B : ℝ}
    (hB : 0 < B) (hG : ∀ Φ, ‖G Φ‖ ≤ B)
    (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    ‖markTerm μ I.A V G S‖ ≤ CPE d L (I.Kc + 1) I.κH I.κ0 I.κ' * B *
        Real.exp ((I.κH - I.κ0) *
          treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V) *
        Real.exp (-I.κ' * dExt S) ∧
      (¬ blocksOf m₀ j Ω V ⊆ S → markTerm μ I.A V G S = 0) := by
  set t := treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V
  have hG' : ∀ Φ, ‖G Φ‖ ≤ B * Real.exp (I.κH * t) * Real.exp (-I.κH * t) := fun Φ => by
    rw [mul_assoc, ← Real.exp_add, show I.κH * t + -I.κH * t = 0 by ring, Real.exp_zero, mul_one]
    exact hG Φ
  obtain ⟨h1, h2⟩ := markTerm_spec μ hN hj hΩ I.A V hV hm G hGm hGdep hG' I.hκ0
    (by linarith [I.hKc]) I.hεpos (by positivity) I.hκ' le_rfl I.hκ I.hε S
  refine ⟨h1.trans (le_of_eq ?_), h2⟩
  rw [show (I.κH - I.κ0) * t = I.κH * t + -I.κ0 * t by ring, Real.exp_add]
  ring

end Balaban.Fluctuation
