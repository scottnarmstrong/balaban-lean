/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesHolo
public import Balaban.Polymer.MarkedCubesVanish
public import Balaban.Polymer.MarkedCubesTwo
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 3.3 of OBSERVABLES.md: the marked expansion, coupling-dependent form

The instance of the abstract marked expansion (`marked_cubes`) consumed by the fluctuation
integrals of the observable layer.  The measure `⟨·⟩_σ` carries the coupling `σ` (`|σ| < R`): its
label activities `H(Y; Φ, σ)` are holomorphic in `σ` with the bounds of `marked_cubes` uniform in
`σ` (`CoupledAct`).  For the marks (the localized pieces of the observable terms) one has, for all
`|σ| < R`, `⟨G_σ⟩_σ = ∑_S G*(σ; S)` with support `S ⊇ blocks(Y₀ ∩ Ω)`, finite `d_Ω(S)`, the bound
`C_PE F₀ e^{-κ₀ 𝗱(Y₀)} e^{-κ' d_Ω(S)}` and `G*(·; S)` holomorphic (`coupled_marked_cubes`).

**The Schwarz step (the `σ`-trick, P9 (3.14)-(3.15), P6 (4.63)).**  If the interaction vanishes at
`σ = 0` and the mark has mean zero under the product measure there (the measure (2.5) is even,
`ψ̂` odd), then every `G*(0; S)` vanishes (`Gst_zero_of_interaction_zero`), and for `R > 1` the
Schwarz lemma gives `|G*(1; S)| ≤ R⁻¹ C_PE F₀ e^{-κ₀ 𝗱(Y₀)} e^{-κ' d_Ω(S)}`
(`coupled_marked_cubes_schwarz`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Localization Balaban.Polymer Balaban.Fluctuation MeasureTheory Metric

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Coupled

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- The entropy bound of the labels: `∑_{Y ⊃ b} e^{-κ₀ 𝗱(Y)} ≤ K_c` for every block `b`. -/
def LabelEntropy (Lab : CubeLabels m₀ j Ω Lb) (κ0 Kc : ℝ) : Prop :=
  ∀ b : 𝔅, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
    Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc

/-- **A coupling-dependent family of label activities** `H(Y; Φ, σ)` on `|σ| < R`: measurable and
localized for each `σ`, holomorphic in `σ`, with the bounds of `LabelAct` (`ε_H e^{-κ_H 𝗱(Y)}` and
the entropy bound) uniform in `σ`. -/
structure CoupledAct (Lab : CubeLabels m₀ j Ω Lb) (Ωb : 𝔅 → Type*)
    [∀ b, MeasurableSpace (Ωb b)] (R εH κH κ0 Kc : ℝ) where
  /-- the activity `H(Y; Φ, σ)` -/
  H : ℂ → Lb → (∀ b, Ωb b) → ℂ
  meas : ∀ σ, ‖σ‖ < R → ∀ y, Measurable (H σ y)
  dep : ∀ σ, ‖σ‖ < R → ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H σ y)
  bound : ∀ σ, ‖σ‖ < R → ∀ y Φ, ‖H σ y Φ‖ ≤ εH * Real.exp (-κH * Lab.dl y)
  entropy : LabelEntropy Lab κ0 Kc
  holo : ∀ y Φ, DifferentiableOn ℂ (fun σ => H σ y Φ) (ball 0 R)

variable {Lab : CubeLabels m₀ j Ω Lb}

/-- **Inhabitation of `CoupledAct`.**  For every label system satisfying the entropy bound the zero
activity is a coupling-dependent family (so the hypothesis is non-vacuous whenever the label system
is admissible), for every `R`, `κ_H`, and every `ε_H ≥ 0`. -/
theorem nonempty_coupledAct {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {R εH κH κ0 Kc : ℝ} (hε : 0 ≤ εH) (hent : LabelEntropy Lab κ0 Kc) :
    Nonempty (CoupledAct Lab Ωb R εH κH κ0 Kc) := by
  refine ⟨{ H := fun _ _ _ => 0
            meas := fun _ _ _ => measurable_const
            dep := fun _ _ _ _ _ _ => rfl
            bound := fun _ _ y Φ => ?_
            entropy := hent
            holo := fun _ _ => differentiableOn_const _ }⟩
  simp only [norm_zero]
  positivity

/-- The `LabelAct` at the coupling `σ` (the zero activity outside the disc). -/
noncomputable def CoupledAct.at {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {R εH κH κ0 Kc : ℝ} (A : CoupledAct Lab Ωb R εH κH κ0 Kc) (hε : 0 ≤ εH) (σ : ℂ) :
    LabelAct Lab Ωb εH κH κ0 Kc where
  H := fun y => if ‖σ‖ < R then A.H σ y else fun _ => 0
  meas := fun y => by
    by_cases h : ‖σ‖ < R
    · simpa [h] using A.meas σ h y
    · simp [h]
  dep := fun y => by
    by_cases h : ‖σ‖ < R
    · simpa [h] using A.dep σ h y
    · simp only [h, ite_false]
      exact fun Φ Φ' _ => rfl
  bound := fun y Φ => by
    by_cases h : ‖σ‖ < R
    · simpa [h] using A.bound σ h y Φ
    · simp only [h, ite_false, norm_zero]
      positivity
  entropy := A.entropy

theorem CoupledAct.at_H_of_lt {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {R εH κH κ0 Kc : ℝ} (A : CoupledAct Lab Ωb R εH κH κ0 Kc) (hε : 0 ≤ εH) {σ : ℂ}
    (h : ‖σ‖ < R) : (A.at hε σ).H = A.H σ := by
  funext y
  simp [CoupledAct.at, h]

open Classical in
/-- **Proposition 3.3 (one function), coupling-dependent form.**  Let `A` be a coupling-dependent
family of label activities on `|σ| < R` and `G_σ` a mark (measurable, localized to the cubes of
`Y₀ ∩ Ω`, `|G_σ| ≤ F₀ e^{-κ_G 𝗱(Y₀)}`, holomorphic in `σ`), under the numerical conditions of
`marked_cubes`.  Then for every `|σ| < R` the partition function is nonzero,
`⟨G_σ⟩_σ = ∑_S G*(σ; S)`, `G*(σ; S) = 0` unless `S ⊇ blocks(Y₀ ∩ Ω)` and unless `d_Ω(S) < ∞`,
`|G*(σ; S)| ≤ C_PE F₀ e^{-κ₀ 𝗱(Y₀)} e^{-κ' d_Ω(S)}`, and each `G*(·; S)` is holomorphic on
`|σ| < R`. -/
theorem coupled_marked_cubes {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {R εH κH κG κ0 κ' Kc F0 : ℝ} (A : CoupledAct Lab Ωb R εH κH κ0 Kc) (y0 : Lb)
    (G : ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ σ, ‖σ‖ < R → Measurable (G σ))
    (hGdep : ∀ σ, ‖σ‖ < R → DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ))
    (hG : ∀ σ, ‖σ‖ < R → ∀ Φ, ‖G σ Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hGhol : ∀ Φ, DifferentiableOn ℂ (fun σ => G σ Φ) (ball 0 R))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    (∀ σ, ‖σ‖ < R →
      (∫ Φ, Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ) ≠ 0) ∧
      ((∫ Φ, G σ Φ * Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ)) /
          (∫ Φ, Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ)) =
          ∑ S, Gst μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ) S) ∧
      (∀ S : Finset 𝔅, ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S →
          Gst μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ) S = 0) ∧
      (∀ S : Finset 𝔅, Gst μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ) S ≠ 0 →
          dOmega m₀ j Ω (sitesOf S) ≠ ⊤) ∧
      (∀ S : Finset 𝔅, ‖Gst μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ) S‖ ≤
          CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S))) ∧
    (∀ S : Finset 𝔅, DifferentiableOn ℂ
      (fun σ => Gst μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ) S) (ball 0 R)) := by
  have hε0 : 0 ≤ εH := hεpos.le
  set G' : ℂ → (∀ b, Ωb b) → ℂ := fun u => if ‖u‖ < R then G u else fun _ => 0 with hG'
  have hGm' : ∀ u, Measurable (G' u) := fun u => by
    by_cases h : ‖u‖ < R
    · simpa [hG', h] using hGm u h
    · simp [hG', h]
  have hGb' : ∀ u Φ, ‖G' u Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0) := fun u Φ => by
    by_cases h : ‖u‖ < R
    · simpa [hG', h] using hG u h Φ
    · simp only [hG', h, ite_false, norm_zero]
      positivity
  have hGhol' : ∀ Φ, DifferentiableOn ℂ (fun u => G' u Φ) (ball 0 R) := fun Φ => by
    refine (hGhol Φ).congr (fun u hu => ?_)
    have : ‖u‖ < R := by simpa using hu
    simp [hG', this]
  have hAhol' : ∀ y Φ, DifferentiableOn ℂ (fun u => (A.at hε0 u).H y Φ) (ball 0 R) :=
    fun y Φ => (A.holo y Φ).congr (fun u hu => by
      have : ‖u‖ < R := by simpa using hu
      simp [CoupledAct.at, this])
  have hholo := fun Y => Pst_Gst_differentiableOn μ hN hj hΩ (isOpen_ball (x := (0 : ℂ)) (ε := R))
    (fun u => A.at hε0 u) y0 G' hGm' hGb' hAhol' hGhol' hκ0 hKc hεpos hF0 hκ' hκG hκ hε Y
  refine ⟨fun σ hσ => ?_, fun S => ?_⟩
  · have hH := A.at_H_of_lt hε0 hσ
    have hG1 : G' σ = G σ := by simp [hG', hσ]
    have hmain := marked_cubes_explicit μ hN hj hΩ (A.at hε0 σ) y0 (G σ) (hGm σ hσ) (hGdep σ hσ)
      (hG σ hσ) hκ0 hKc hεpos hF0 hκ' hκG hκ hε
    rw [hH] at hmain
    obtain ⟨hne, -, hsum, hsupp, hbd⟩ := hmain
    refine ⟨hne, hsum, hsupp, fun S hS => ?_, hbd⟩
    by_contra htop
    exact hS (Gst_eq_zero_of_dOmega_top μ hN hj hΩ Lab (A.H σ) y0 (G σ) S (by simpa using htop))
  · have := (hholo S).2
    refine this.congr (fun u hu => ?_)
    have hu' : ‖u‖ < R := by simpa using hu
    simp only [A.at_H_of_lt hε0 hu', hG', hu', ite_true]

/-- **Schwarz lemma at radius `R`.**  A function holomorphic on `|σ| < R`, bounded there by `B`
and vanishing at `0`, satisfies `|f(σ)| ≤ B |σ| / R`. -/
theorem norm_le_mul_div_of_vanish_zero {f : ℂ → ℂ} {R B : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hB : ∀ σ, ‖σ‖ < R → ‖f σ‖ ≤ B) (h0 : f 0 = 0)
    {σ : ℂ} (hσ : ‖σ‖ < R) : ‖f σ‖ ≤ B * ‖σ‖ / R := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hR))
  rcases hB0.eq_or_lt with hBz | hBp
  · have := hB σ hσ
    rw [← hBz] at this ⊢
    simpa using this
  · set g : ℂ → ℂ := fun w => (B : ℂ)⁻¹ * f ((R : ℂ) * w) with hg
    have hmem : ∀ w : ℂ, w ∈ ball (0 : ℂ) 1 → (R : ℂ) * w ∈ ball (0 : ℂ) R := fun w hw => by
      simp only [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR] at hw ⊢
      nlinarith
    have hgd : DifferentiableOn ℂ g (ball 0 1) := by
      refine DifferentiableOn.const_mul ?_ _
      exact hf.comp (differentiable_const _ |>.mul differentiable_id).differentiableOn hmem
    have hmaps : Set.MapsTo g (ball 0 1) (closedBall 0 1) := fun w hw => by
      have := hB ((R : ℂ) * w) (mem_ball_zero_iff.1 (hmem w hw))
      simp only [mem_closedBall_zero_iff, hg, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hBp]
      rw [inv_mul_le_iff₀ hBp]
      simpa using this
    have hg0 : g 0 = 0 := by simp [hg, h0]
    have hw : ‖σ / (R : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_lt_one hR]
      exact hσ
    have := Complex.norm_le_norm_of_mapsTo_ball hgd hmaps hg0 (z := σ / (R : ℂ)) hw
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    simp only [hg, mul_div_cancel₀ _ hR', norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hBp, norm_div, abs_of_pos hR] at this
    rw [inv_mul_le_iff₀ hBp] at this
    calc ‖f σ‖ ≤ B * (‖σ‖ / R) := this
      _ = B * ‖σ‖ / R := by ring

section Vanishing

open Classical in
/-- With vanishing interaction, the activity of a polymer `Z ≠ blocks(Y₀ ∩ Ω)` is zero: only the
term of the mark survives. -/
theorem marksK_eq_zero_of_ne {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (H : Lb → (∀ b, Ωb b) → ℂ) (hH : ∀ y Φ, H y Φ = 0) (S0 : Finset 𝔅)
    (G : (∀ b, Ωb b) → ℂ) (Z : NePoly 𝔅) (hZ : Z.1 ≠ S0) (l : Unit → ℂ) :
    marksK μ Subtype.val (presum Lab H) (gMark S0 G) Z l = 0 := by
  unfold marksK mayerK
  have hpre : ∀ (t : NePoly 𝔅) Φ, presum Lab H t Φ = 0 := fun t Φ =>
    Finset.sum_eq_zero (fun y _ => hH y Φ)
  have : mayerAct (Subtype.val : NePoly 𝔅 → Finset 𝔅) (Hlam (presum Lab H) (gMark S0 G) l) Z =
      fun _ => 0 := by
    funext Φ
    unfold mayerAct polyAct
    refine Finset.sum_eq_zero (fun C hC => ?_)
    obtain ⟨-, -, hun⟩ := mem_Cfam.1 hC
    by_cases hex : ∃ t ∈ C, t.1 ≠ S0
    · obtain ⟨t, htC, htS⟩ := hex
      refine Finset.prod_eq_zero htC ?_
      have : Hlam (presum Lab H) (gMark S0 G) l t Φ = 0 := by
        simp [Hlam, hpre, gMark, htS]
      simp [this]
    · push Not at hex
      exfalso
      apply hZ
      obtain ⟨b, hb⟩ := Z.2
      rw [← hun] at hb
      obtain ⟨t0, ht0, -⟩ := mem_unionCs.1 hb
      apply Finset.Subset.antisymm
      · rw [← hun]
        intro x hx
        obtain ⟨t, ht, hxt⟩ := mem_unionCs.1 hx
        rw [← hex t ht]; exact hxt
      · rw [← hex t0 ht0, ← hun]
        intro x hx
        exact mem_unionCs.2 ⟨t0, ht0, hx⟩
  rw [this]
  simp

open Classical in
/-- With vanishing interaction, `G*(Y₀; S) = 0` for `S ≠ blocks(Y₀ ∩ Ω)`. -/
theorem Gst_eq_zero_of_ne {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (H : Lb → (∀ b, Ωb b) → ℂ) (hH : ∀ y Φ, H y Φ = 0) (S0 : Finset 𝔅)
    (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) (hS : S ≠ S0) :
    Gst μ Lab H S0 G S = 0 := by
  unfold Gst
  have hF : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark S0 G)) S = fun _ => 0 := by
    funext l
    unfold Ff
    refine PY_eq_zero_of_forall _ _ _ S (fun n X hXS hconn => ?_)
    by_contra hne
    apply hS
    rw [← hXS]
    have hall : ∀ i, (X i).1 = S0 := fun i => by
      by_contra hi
      exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
        (marksK_eq_zero_of_ne μ H hH S0 G (X i) hi l))
    unfold unionOf
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hall]
    exact ⟨fun h => h.elim (fun _ hx => hx), fun h => ⟨0, h⟩⟩
  rw [hF]
  simp [D1]

/-- If moreover the sum of the local terms vanishes, all of them vanish. -/
theorem Gst_eq_zero_of_sum {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (H : Lb → (∀ b, Ωb b) → ℂ) (hH : ∀ y Φ, H y Φ = 0) (S0 : Finset 𝔅)
    (G : (∀ b, Ωb b) → ℂ) (hsum : ∑ S, Gst μ Lab H S0 G S = 0) (S : Finset 𝔅) :
    Gst μ Lab H S0 G S = 0 := by
  classical
  by_cases hS : S = S0
  · subst hS
    rw [Finset.sum_eq_single S (fun T _ hT => Gst_eq_zero_of_ne μ H hH S G T hT)
      (fun h => absurd (Finset.mem_univ S) h)] at hsum
    exact hsum
  · exact Gst_eq_zero_of_ne μ H hH S0 G S hS

end Vanishing

open Classical in
/-- **The `σ`-trick (Schwarz step of P9 (3.14)-(3.15), P6 (4.63)).**  In the setting of
`coupled_marked_cubes`, assume the interaction vanishes at `σ = 0` and the mark has mean zero under
the product measure there (the measure (2.5) is even and the mark `ψ̂(y)` is odd).  Then
`G*(0; S) = 0` for every `S`, and for `|σ| < R`
`|G*(σ; S)| ≤ (|σ| / R) C_PE F₀ e^{-κ₀ 𝗱(Y₀)} e^{-κ' d_Ω(S)}`. -/
theorem coupled_marked_cubes_schwarz {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {R εH κH κG κ0 κ' Kc F0 : ℝ} (hR : 0 < R) (A : CoupledAct Lab Ωb R εH κH κ0 Kc) (y0 : Lb)
    (G : ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ σ, ‖σ‖ < R → Measurable (G σ))
    (hGdep : ∀ σ, ‖σ‖ < R → DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ))
    (hG : ∀ σ, ‖σ‖ < R → ∀ Φ, ‖G σ Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hGhol : ∀ Φ, DifferentiableOn ℂ (fun σ => G σ Φ) (ball 0 R))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hH0 : ∀ y Φ, A.H 0 y Φ = 0) (hmean : ∫ Φ, G 0 Φ ∂(Measure.pi μ) = 0) :
    (∀ S : Finset 𝔅, Gst μ Lab (A.H 0) (blocksOf m₀ j Ω (Lab.ysite y0)) (G 0) S = 0) ∧
    ∀ σ, ‖σ‖ < R → ∀ S : Finset 𝔅,
      ‖Gst μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y0)) (G σ) S‖ ≤
        CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S) *
          (‖σ‖ / R) := by
  obtain ⟨hpt, hhol⟩ := coupled_marked_cubes μ hN hj hΩ A y0 G hGm hGdep hG hGhol hκ0 hKc hεpos
    hF0 hκ' hκG hκ hε
  have h0R : ‖(0 : ℂ)‖ < R := by simpa using hR
  have hzero : ∀ S : Finset 𝔅,
      Gst μ Lab (A.H 0) (blocksOf m₀ j Ω (Lab.ysite y0)) (G 0) S = 0 := by
    obtain ⟨-, hsum, -, -, -⟩ := hpt 0 h0R
    refine Gst_eq_zero_of_sum μ (A.H 0) hH0 _ (G 0) ?_
    rw [← hsum]
    simp [hH0, hmean]
  refine ⟨hzero, fun σ hσ S => ?_⟩
  have hbd := fun τ (hτ : ‖τ‖ < R) => (hpt τ hτ).2.2.2.2 S
  have := norm_le_mul_div_of_vanish_zero hR (hhol S) hbd (hzero S) hσ
  calc _ ≤ _ := this
    _ = _ := by ring

open Classical in
/-- **Proposition 3.3 (truncated expectation of two functions), coupling-dependent form.**
Under the stronger activity bound `ε_H ≤ ε_PE / 2` of `marked_cubes_two`, for every `|σ| < R` the
truncated expectation `⟨G₀; G₁⟩^T_σ` is `∑_S G**(σ; S)` with `G**(σ; S) = 0` unless `S` contains
both `blocks(Y₀ ∩ Ω)` and `blocks(Y₁ ∩ Ω)` and unless `d_Ω(S) < ∞`, and
`|G**(σ; S)| ≤ C_PE2 F₀ F₁ e^{-κ₀ (𝗱(Y₀) + 𝗱(Y₁))} e^{-κ' d_Ω(S)}`. -/
theorem coupled_marked_cubes_two {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {R εH κH κG₀ κG₁ κ0 κ' Kc F₀ F₁ : ℝ} (A : CoupledAct Lab Ωb R εH κH κ0 Kc) (y₀ y₁ : Lb)
    (G₀ G₁ : ℂ → (∀ b, Ωb b) → ℂ)
    (hG₀m : ∀ σ, ‖σ‖ < R → Measurable (G₀ σ)) (hG₁m : ∀ σ, ‖σ‖ < R → Measurable (G₁ σ))
    (hG₀dep : ∀ σ, ‖σ‖ < R → DepOn (blocksOf m₀ j Ω (Lab.ysite y₀)) (G₀ σ))
    (hG₁dep : ∀ σ, ‖σ‖ < R → DepOn (blocksOf m₀ j Ω (Lab.ysite y₁)) (G₁ σ))
    (hG₀ : ∀ σ, ‖σ‖ < R → ∀ Φ, ‖G₀ σ Φ‖ ≤ F₀ * Real.exp (-κG₀ * Lab.dl y₀))
    (hG₁ : ∀ σ, ‖σ‖ < R → ∀ Φ, ‖G₁ σ Φ‖ ≤ F₁ * Real.exp (-κG₁ * Lab.dl y₁))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF₀ : 0 < F₀) (hF₁ : 0 < F₁) (hκ' : 0 ≤ κ') (hκG₀ : κH ≤ κG₀) (hκG₁ : κH ≤ κG₁)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (16 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    ∀ σ, ‖σ‖ < R →
      (∫ Φ, Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ) ≠ 0) ∧
      (((∫ Φ, G₀ σ Φ * (G₁ σ Φ * Complex.exp (∑ y, A.H σ y Φ)) ∂(Measure.pi μ)) /
          (∫ Φ, Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ)) -
        ((∫ Φ, G₀ σ Φ * Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ)) /
          (∫ Φ, Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ))) *
        ((∫ Φ, G₁ σ Φ * Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ)) /
          (∫ Φ, Complex.exp (∑ y, A.H σ y Φ) ∂(Measure.pi μ)))) =
          ∑ S, Gst2 μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y₀))
            (blocksOf m₀ j Ω (Lab.ysite y₁)) (G₀ σ) (G₁ σ) S) ∧
      (∀ S : Finset 𝔅, ¬ (blocksOf m₀ j Ω (Lab.ysite y₀) ⊆ S ∧
          blocksOf m₀ j Ω (Lab.ysite y₁) ⊆ S) →
        Gst2 μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y₀))
          (blocksOf m₀ j Ω (Lab.ysite y₁)) (G₀ σ) (G₁ σ) S = 0) ∧
      (∀ S : Finset 𝔅, Gst2 μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y₀))
          (blocksOf m₀ j Ω (Lab.ysite y₁)) (G₀ σ) (G₁ σ) S ≠ 0 →
          dOmega m₀ j Ω (sitesOf S) ≠ ⊤) ∧
      (∀ S : Finset 𝔅, ‖Gst2 μ Lab (A.H σ) (blocksOf m₀ j Ω (Lab.ysite y₀))
          (blocksOf m₀ j Ω (Lab.ysite y₁)) (G₀ σ) (G₁ σ) S‖ ≤
        CPE2 d L Kc κH κ0 κ' * F₀ * F₁ * Real.exp (-κ0 * (Lab.dl y₀ + Lab.dl y₁)) *
          Real.exp (-κ' * dExt S)) := by
  intro σ hσ
  have hε0 : 0 ≤ εH := hεpos.le
  have hH := A.at_H_of_lt hε0 hσ
  have hmain := marked_cubes_two μ hN hj hΩ (A.at hε0 σ) y₀ y₁ (G₀ σ) (G₁ σ) (hG₀m σ hσ)
    (hG₁m σ hσ) (hG₀dep σ hσ) (hG₁dep σ hσ) (hG₀ σ hσ) (hG₁ σ hσ) hκ0 hKc hεpos hF₀ hF₁ hκ'
    hκG₀ hκG₁ hκ hε
  rw [hH] at hmain
  obtain ⟨hne, hsum, hsupp, hbd⟩ := hmain
  refine ⟨hne, hsum, hsupp, fun S hS => ?_, hbd⟩
  by_contra htop
  exact hS (Gst2_eq_zero_of_dOmega_top μ hN hj hΩ Lab (A.H σ) y₀ y₁ (G₀ σ) (G₁ σ) S
    (by simpa using htop))

omit [NeZero N₁] [NeZero L] in
/-- A set of blocks `S` with `d_Ω(S) < ∞` has connected `Ŷ(S)` (the polymer `Ŷ(S)` of the output
expansion lies in `𝒟_{k+1}`-type connectivity): `d_Ω(S) = +∞` otherwise. -/
theorem siteConnected_yhat_of_dOmega_ne_top {S : Finset 𝔅}
    (h : dOmega m₀ j Ω (sitesOf S) ≠ ⊤) : SiteConnected (Yhat Ω (sitesOf S)) := by
  by_contra hc
  exact h (by simp [dOmega, hc])

end Coupled

end Balaban.Observables
