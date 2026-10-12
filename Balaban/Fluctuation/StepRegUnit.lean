/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.BgDataStructures
public import Balaban.Fluctuation.Lemma25Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The background of the constant unit datum

For a whole-lattice generating set `G` of level `n` and the constant unit datum
`Ψ ≡ h ≡ e₀` (`unitBg`) with mass `ν = 0`, the field `φ ≡ e₀` has action `0`, hence is the minimizer;
if the datum lies in the real domain, `bgField = φ ≡ e₀` (`bgField_unitBg`), and the five tests of
`χ_u` reduce to the bound on the multiplier (`chiUBounds_unitBg`).  These are the ingredients of the
non-degenerate witness of `RayData` (`StepRegWitness`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The constant unit field `φ ≡ e₀` on `Ω₁`. -/
noncomputable def unitPhi (G : GeneratingSet d L N₀ K ϱ) (hN : 0 < N) :
    G.Ω 1 × Fin N → ℂ := fun p => (unitVec hN p.2 : ℂ)

theorem svec_unitPhi {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) (y : Torus d (N₀ * L ^ K))
    (i : Fin N) : svec G (unitPhi G hN) y i = (unitVec hN i : ℂ) := by
  rw [svec_of_mem G _ ⟨y, (hG y).1⟩ i]
  rfl

theorem barField_unit {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) (D : BgData G N)
    (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    barField G D.Ψ (unitPhi G hN) y i = (unitVec hN i : ℂ) := by
  rw [barField_eq_svec hG, svec_unitPhi hG hN]

theorem blockAvg_unit {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) (x : Torus d (N₀ * L ^ K))
    (i : Fin N) : blockAvg G (unitPhi G hN) x i = (unitVec hN i : ℂ) := by
  have hb : blockAvg G (unitPhi G hN) x i =
      blockMean G n (fun y => svec G (unitPhi G hN) y i) x := by
    unfold blockAvg blockMean
    rw [(hG x).2]
  rw [hb]
  have : (fun y => svec G (unitPhi G hN) y i) = fun _ => (unitVec hN i : ℂ) :=
    funext fun y => svec_unitPhi hG hN y i
  rw [this]
  exact blockMean_const G (hG.bounds.2) _ x

theorem isRealUnitField_unitPhi (hN : 0 < N) : IsRealUnitField G (unitPhi G hN) := by
  intro x
  refine ⟨fun i => by simp [unitPhi], ?_⟩
  have := sum_sq_unitVec hN
  simpa [unitPhi, Complex.norm_real, sq_abs] using this

theorem action_unitBg_eq_zero {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) (a : ℕ → ℝ) (h : Fin N → ℝ) :
    action G a 0 (unitBg G hN h) (unitPhi G hN) = 0 := by
  unfold action
  have h1 : ∀ x : G.Ω 1, ∀ i, (unitBg G hN h).Ψ x i - blockAvg G (unitPhi G hN) x i = 0 := by
    intro x i
    rw [blockAvg_unit hG hN, unitBg_Ψ_of_mem G hN h ((mem_dataSites G).2 (Or.inl x.2)), sub_self]
  have h2 : ∀ (y : Torus d (N₀ * L ^ K)) (μ : Fin d) (i : Fin N),
      barField G (unitBg G hN h).Ψ (unitPhi G hN) (y + Pi.single μ 1) i -
        barField G (unitBg G hN h).Ψ (unitPhi G hN) y i = 0 := by
    intro y μ i
    rw [barField_unit hG hN, barField_unit hG hN, sub_self]
  simp [h1, h2]

theorem action_nonneg_of {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {ν : ℝ} (hν : 0 ≤ ν) (D : BgData G N)
    (σ : G.Ω 1 × Fin N → ℂ) : 0 ≤ action G a ν D σ := by
  unfold action
  have t1 : 0 ≤ (1 / 2 : ℝ) * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G σ x i‖ ^ 2 := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => mul_nonneg ?_ ?_)
    · exact div_nonneg (ha _) (by positivity)
    · exact Finset.sum_nonneg fun i _ => by positivity
  have t2 : 0 ≤ (1 / 2 : ℝ) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ σ (x + Pi.single μ 1) i - barField G D.Ψ σ x i‖ ^ 2 else 0) := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => ?_)
    split_ifs
    · exact Finset.sum_nonneg fun i _ => by positivity
    · exact le_rfl
  have t3 : 0 ≤ ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖σ (x, i) - D.h x i‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => by positivity)
  linarith

theorem isMinimizer_unitBg {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (h : Fin N → ℝ) : IsMinimizer G a 0 (unitBg G hN h) (unitPhi G hN) := by
  refine ⟨fun x i => ?_, isRealUnitField_unitPhi hN, fun σ _ => ?_⟩
  · refine ⟨?_, ?_⟩
    · by_cases hx : x ∈ dataSites G
      · rw [unitBg_Ψ_of_mem G hN h hx]; simp
      · simp [unitBg, BgData.clip, hx]
    · by_cases hx : x ∈ G.Ω 1
      · rw [unitBg_h_of_mem G hN h hx]; simp
      · simp [unitBg, BgData.clip, hx]
  · rw [action_unitBg_eq_zero hG hN a h]
    exact action_nonneg_of ha le_rfl _ _

/-- **The background field of the constant unit datum is the constant unit field** (when the datum
lies in the real domain, so that the minimizer is unique). -/
theorem bgField_unitBg {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (h : Fin N → ℝ) (H : BgHyp d L K ϱ a 0)
    (hD : InUnionDomainR G (bgC1 d L N) 0 (unitBg G hN h)) :
    bgField G a 0 (unitBg G hN h) = unitPhi G hN := by
  have hmin := isMinimizer_unitBg hG hN ha h
  exact bgField_eq hmin fun φ' hφ' => ((theorem71 H hD).1.unique hφ' hmin)

/-- **The tests of `χ_u` for the constant unit datum**: everything vanishes except the multiplier
test, which is a hypothesis on `α`. -/
theorem chiUBounds_unitBg {n : ℕ} (hG : IsLevel G n) (hN : 0 < N) (h : Fin N → ℝ) {δ : ℝ}
    (hδ : 0 < δ) {φ₁ : G.Ω 1 × Fin N → ℂ} (hφ : φ₁ = unitPhi G hN) {α : G.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖α x‖ < δ / 2) :
    ChiUBounds G 0 δ (unitBg G hN h) φ₁ α := by
  subst hφ
  have hv0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := by
    simp only [vn]
    simp [EuclideanSpace.norm_eq]
  have hsp : ∀ x : Torus d (N₀ * L ^ K), 0 < G.spacing x := fun x => spacing_pos G
  refine ⟨fun x hx => ?_, fun x hx μ => ?_, fun x hx => ?_, hα, fun z => ?_⟩
  · have : (fun i => (unitBg G hN h).Ψ x i - blockAvg G (unitPhi G hN) x i) =
        fun _ => (0 : ℂ) := by
      funext i
      rw [blockAvg_unit hG hN, unitBg_Ψ_of_mem G hN h ((mem_dataSites G).2 (Or.inl hx)), sub_self]
    rw [this, hv0]; positivity
  · have e : ∀ y : Torus d (N₀ * L ^ K), (fun i =>
        barField G (unitBg G hN h).Ψ (unitPhi G hN) y i -
          barField G (unitBg G hN h).Ψ (unitPhi G hN) x i) = fun _ => (0 : ℂ) := by
      intro y; funext i
      rw [barField_unit hG hN, barField_unit hG hN, sub_self]
    rw [e, hv0, e, hv0]
    have := hsp x
    exact ⟨by positivity, by positivity⟩
  · have e : (fun i => ∑ μ : Fin d,
        (barField G (unitBg G hN h).Ψ (unitPhi G hN) (x + Pi.single μ 1) i +
          barField G (unitBg G hN h).Ψ (unitPhi G hN) (x - Pi.single μ 1) i -
          2 * barField G (unitBg G hN h).Ψ (unitPhi G hN) x i)) = fun _ => (0 : ℂ) := by
      funext i
      simp only [barField_unit hG hN]
      simp
      ring
    rw [e, hv0]
    have := hsp x
    positivity
  · simp only [Real.sqrt_zero, zero_mul]
    positivity

end Balaban.Fluctuation
