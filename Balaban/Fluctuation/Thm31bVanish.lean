/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesVanish
public import Balaban.Polymer.MarkedCubesHolo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): the marked terms vanish at zero interaction (FLUCTUATION.md §3.5 (b))

At `σ = 0` the interaction (3.3) vanishes, and "only the polymer of the mark survives, and its
derivative is `∫ ψ̂(y) dν = 0`".  This file proves that statement for the marked cluster
expansion: if all label activities `H(Y)` vanish and the mark `G` has mean zero for the product
measure, then every local term `G*(Y₀, S)` (`Gst`) vanishes.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Vanish

omit [NeZero N₁] [NeZero L] in
/-- A union of copies of one set (instance-implicit-free form of `Finset.biUnion_const`). -/
theorem biUnion_eq_const_of_forall {α β : Type*} {inst : DecidableEq β} {s : Finset α}
    {f : α → Finset β} {c : Finset β} (hne : s.Nonempty) (h : ∀ a ∈ s, f a = c) :
    @Finset.biUnion α β inst s f = c := by
  obtain ⟨a0, ha0⟩ := hne
  ext b
  rw [Finset.mem_biUnion]
  exact ⟨fun ⟨a, ha, hb⟩ => (h a ha) ▸ hb, fun hb => ⟨a0, ha0, (h a0 ha0).symm ▸ hb⟩⟩

variable {Lb : Type*} [Fintype Lb]

/-- With vanishing activities, the activity of a polymer other than the one of the mark vanishes. -/
theorem marksK_zero_interaction_eq_zero {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) (S0 : Finset 𝔅) (G : (∀ b, Ωb b) → ℂ)
    (a : NePoly 𝔅 → (∀ b, Ωb b) → ℂ) (ha : ∀ t Φ, a t Φ = 0) (l : Unit → ℂ)
    (Z : NePoly 𝔅) (hZ : Z.1 ≠ S0) :
    marksK μ Subtype.val a (gMark S0 G) Z l = 0 := by
  unfold marksK mayerK mayerAct polyAct
  have : (fun Φ => ∑ C ∈ Cfam (Subtype.val : NePoly 𝔅 → Finset 𝔅) (fun _ : Finset (NePoly 𝔅) => True) Z.1,
      ∏ t ∈ C, (Complex.exp (Hlam a (gMark S0 G) l t Φ) - 1)) = fun _ => 0 := by
    funext Φ
    refine Finset.sum_eq_zero (fun C hC => ?_)
    obtain ⟨hconn, -, hun⟩ := mem_Cfam.1 hC
    by_contra hne
    apply hZ
    rw [← hun]
    have hall : ∀ t ∈ C, t.1 = S0 := by
      intro t ht
      by_contra htS
      apply hne
      refine Finset.prod_eq_zero ht ?_
      have : Hlam a (gMark S0 G) l t Φ = 0 := by
        simp [Hlam, ha, gMark, htS]
      simp [this]
    exact biUnion_eq_const_of_forall hconn.1 hall
  simp only [this]
  simp

/-- With vanishing activities, `Ff` vanishes at every set other than the one of the mark. -/
theorem Ff_zero_interaction_eq_zero {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (hH : ∀ y Φ, H y Φ = 0) (S0 : Finset 𝔅)
    (G : (∀ b, Ωb b) → ℂ) (Y : Finset 𝔅) (hY : Y ≠ S0) (l : Unit → ℂ) :
    Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark S0 G)) Y l = 0 := by
  unfold Ff PY
  have hn : ∀ n, Pterm (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (fun Z => marksK μ Subtype.val (presum Lab H) (gMark S0 G) Z l) Y n = 0 := by
    intro n
    unfold Pterm
    rw [mul_eq_zero]
    right
    refine Finset.sum_eq_zero (fun X hX => ?_)
    have hX2 : unionOf Subtype.val X = Y := by simpa using hX
    have : ∃ i, (X i).1 ≠ S0 := by
      by_contra hall
      push Not at hall
      apply hY
      rw [← hX2]
      unfold unionOf
      exact biUnion_eq_const_of_forall Finset.univ_nonempty (fun i _ => hall i)
    obtain ⟨i, hi⟩ := this
    have hk : marksK μ Subtype.val (presum Lab H) (gMark S0 G) (X i) l = 0 :=
      marksK_zero_interaction_eq_zero μ S0 G _ (fun t Φ => by
        unfold presum
        exact Finset.sum_eq_zero (fun y _ => hH y Φ)) l (X i) hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hk, mul_zero]
  simp [hn]

end Vanish

section Vanish2

variable {Lb : Type*} [Fintype Lb]

/-- **Mayer-level vanishing at zero interaction** (§3.5 (b)): if all label activities vanish and
the mark has mean zero for the product measure, then `G*(Y₀, S) = 0` for every `S`.  The
hypotheses are those of Theorem 3.4 (`marked_cubes_explicit`), the vanishing of the interaction
and the evenness of the mark. -/
theorem Gst_eq_zero_of_zero_interaction {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hA0 : ∀ y Φ, A.H y Φ = 0) (hmean : ∫ Φ, G Φ ∂(Measure.pi μ) = 0) (Y : Finset 𝔅) :
    Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y0)) G Y = 0 := by
  have hS0 : (blocksOf m₀ j Ω (Lab.ysite y0)).Nonempty := Lab.blocksOf_nonempty hN hj hΩ y0
  obtain ⟨-, -, h3⟩ := marked_cubes_explicit μ hN hj hΩ A y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε
  obtain ⟨hsum, -, -⟩ := h3
  have hzero : ∀ Y' : Finset 𝔅, Y' ≠ blocksOf m₀ j Ω (Lab.ysite y0) →
      Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y0)) G Y' = 0 := by
    intro Y' hY'
    unfold Gst
    have : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
        (marksK μ Subtype.val (presum Lab A.H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) Y' =
        fun _ => 0 :=
      funext fun l => Ff_zero_interaction_eq_zero μ Lab A.H hA0 _ G Y' hY' l
    rw [this]
    simp [D1]
  by_cases hY : Y = blocksOf m₀ j Ω (Lab.ysite y0)
  · subst hY
    have hs : ∑ Y' : Finset 𝔅, Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y0)) G Y' = 0 := by
      rw [← hsum]
      simp [hA0, hmean]
    rw [Finset.sum_eq_single (blocksOf m₀ j Ω (Lab.ysite y0)) (fun Y' _ hY' => hzero Y' hY')
      (fun h => absurd (Finset.mem_univ _) h)] at hs
    exact hs
  · exact hzero Y hY

end Vanish2

end Balaban.Fluctuation
