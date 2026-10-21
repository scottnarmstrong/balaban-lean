/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalRegroup
public import Balaban.Spine.RootFInputs

/-!
# The regrouped activities of scale `k + 1`

A6-3 (c), over abstract activities. Given terms `t ℓ Y g` indexed by finite sets `Y` of sites of the
torus `𝕋_ℓ` (the scale-`k` polymers of the cut expansion), the regrouped activity of scale `k + 1` is
`p_{k+1}(X; g) = ∑_{Y : Ȳ = X} t(Y; g)` with `Ȳ = hullT (M L^{k+1}) Y` (`regroupFam`). If the terms
vanish (in the increment) off scale-`k` polymers, are analytic in the unit `ℓ¹` ball, depend on
`g|_Y` only, and obey the bound `B e^{-κ'|Y|/(M L^k)^d}` for scale-`k` polymers, the regrouped
activity has the four one-torus clauses of `ObservableActivities` at top scale `k + 1`
(`regroup_clauses`), with the decay rate `κ' - L^d log 2` of the hull.
-/

@[expose] public section

open Finset Balaban

namespace Balaban.RootFSpine

variable {d N : ℕ}

/-- The regrouped activity of scale `k + 1` on one torus. -/
noncomputable def regroupAt (M L k : ℕ)
    (t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (ℓ : ℕ) [NeZero ℓ]
    (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ := by
  classical
  exact ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d ℓ))).filter
    (fun Y => hullT (M * L ^ k * L) Y = X), t ℓ Y g

/-- The family of activities with the regrouped activity at the scale `k + 1` and `0` elsewhere. -/
noncomputable def regroupFam (M L k : ℕ)
    (t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
  fun ℓ j X g => by
    classical
    exact if h : NeZero ℓ ∧ j = k + 1 then (haveI := h.1; regroupAt M L k t ℓ X g) else 0

theorem regroupFam_succ (M L k : ℕ)
    (t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (ℓ : ℕ) [NeZero ℓ]
    (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) :
    regroupFam M L k t ℓ (k + 1) X g = regroupAt M L k t ℓ X g := by
  unfold regroupFam
  rw [dite_eq_left_of_eq_true (eq_true ⟨inferInstance, rfl⟩)]

theorem regroupFam_ne (M L k : ℕ)
    (t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (ℓ j : ℕ)
    (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) (hj : j ≠ k + 1) :
    regroupFam M L k t ℓ j X g = 0 := by
  unfold regroupFam
  rw [dite_eq_right_of_eq_false (eq_false (fun h => hj h.2))]

section Clauses

variable {M L k : ℕ} {t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}
  {ℓ : ℕ} [NeZero ℓ]

/-- A scale-`k` polymer of the hull of which is a scale-`(k+1)` polymer. -/
theorem hull_polymer_of {Y : Finset (Torus d ℓ)} (hY : IsPolymer d ℓ (M * L ^ k) Y) :
    IsPolymer d ℓ (M * L ^ (k + 1)) (hullT (M * L ^ k * L) Y) := by
  rw [show M * L ^ (k + 1) = M * L ^ k * L by ring]
  exact hullT_isPolymer hY

/-- **Support of the regrouped activity.** -/
theorem regroup_support
    (hS : ∀ Y, ¬ IsPolymer d ℓ (M * L ^ k) Y → ∀ g, t ℓ Y g = t ℓ Y 0) :
    ActSupportAt d N L M (k + 1) ℓ (regroupFam M L k t) := by
  intro j X hX g
  by_cases hj : j = k + 1
  · subst hj
    rw [regroupFam_succ, regroupFam_succ]
    unfold regroupAt
    refine Finset.sum_congr rfl fun Y hY => ?_
    have hY' := (Finset.mem_filter.1 hY).2
    refine hS Y (fun hpoly => hX ⟨Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, ?_⟩) g
    rw [← hY']
    exact hull_polymer_of hpoly
  · rw [regroupFam_ne _ _ _ _ _ _ _ _ hj, regroupFam_ne _ _ _ _ _ _ _ _ hj]

/-- **Analyticity of the regrouped activity** (a finite sum). -/
theorem regroup_analytic
    (hA : ∀ Y, AnalyticOnNhd ℂ (t ℓ Y) {g : Torus d ℓ → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) :
    ActAnalyticAt d N ℓ (regroupFam M L k t) := by
  intro j X
  by_cases hj : j = k + 1
  · subst hj
    have : regroupFam M L k t ℓ (k + 1) X = regroupAt M L k t ℓ X :=
      funext fun g => regroupFam_succ M L k t ℓ X g
    rw [this]
    unfold regroupAt
    have h := Finset.analyticOnNhd_sum (Finset.filter (fun Y => hullT (M * L ^ k * L) Y = X)
      (Finset.univ : Finset (Finset (Torus d ℓ)))) fun Y _ => hA Y
    convert h using 1
    funext g
    simp [Finset.sum_apply]
  · have : regroupFam M L k t ℓ j X = fun _ => 0 := funext fun g => regroupFam_ne _ _ _ _ _ _ _ _ hj
    rw [this]
    exact analyticOnNhd_const

/-- **Locality of the regrouped activity**: `Y ⊆ Ȳ = X`. -/
theorem regroup_local
    (hLoc : ∀ Y (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ Y, g y = g' y) → t ℓ Y g = t ℓ Y g') :
    ActLocalAt d N ℓ (regroupFam M L k t) := by
  intro j X g g' hgg
  by_cases hj : j = k + 1
  · subst hj
    rw [regroupFam_succ, regroupFam_succ]
    unfold regroupAt
    refine Finset.sum_congr rfl fun Y hY => hLoc Y g g' fun y hy => hgg y ?_
    rw [← (Finset.mem_filter.1 hY).2]
    exact subset_hullT _ Y hy
  · rw [regroupFam_ne _ _ _ _ _ _ _ _ hj, regroupFam_ne _ _ _ _ _ _ _ _ hj]

open Classical in
/-- **The bound of the regrouped activity**: the weights `B e^{-κ'|Y|/(M L^k)^d}` of the scale-`k`
polymers with hull `X` sum to at most `B e^{-κ|X|/(M L^{k+1})^d}` when `κ' ≥ κ + L^d log 2`. -/
theorem regroup_bound {m' : ℕ} [NeZero m'] [NeZero (L * m')] (hℓ : ℓ = M * L ^ k * (L * m'))
    (hs : 0 < M * L ^ k) {B κ' κ c₉ δ : ℝ} (hB0 : 0 ≤ B) (hc₉ : 0 ≤ c₉) (hκ' : 0 ≤ κ')
    (hκ : κ + (L : ℝ) ^ d * Real.log 2 ≤ κ')
    (hBc : B ≤ c₉ / 2 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))))
    (hS : ∀ Y, ¬ IsPolymer d ℓ (M * L ^ k) Y → ∀ g, t ℓ Y g = t ℓ Y 0)
    (hB : ∀ Y, IsPolymer d ℓ (M * L ^ k) Y → ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖t ℓ Y g - t ℓ Y 0‖ ≤ B * Real.exp (-κ' * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d)) :
    ActBoundAt d N L M κ c₉ δ (k + 1) ℓ (regroupFam M L k t) := by
  intro j hj X g hg
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have hL0 : (0 : ℝ) < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · exfalso; subst h0; simp at hℓ; exact NeZero.ne ℓ hℓ
    · exact_mod_cast h0
  have hrhs : 0 ≤ c₉ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
      Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) := by positivity
  by_cases hj' : j = k + 1
  · subst hj'
    rw [regroupFam_succ, regroupFam_succ]
    unfold regroupAt
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hsum := regroup_sum_bound (s := M * L ^ k) (L' := L) (m' := m') hℓ hs X hκ'
    set F := (Finset.univ : Finset (Finset (Torus d ℓ))).filter
      (fun Y => hullT (M * L ^ k * L) Y = X) with hF
    have h1 : ∑ Y ∈ F, ‖t ℓ Y g - t ℓ Y 0‖ ≤ ∑ Y ∈ F, (if IsPolymer d ℓ (M * L ^ k) Y then
        B * Real.exp (-κ' * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d) else 0) := by
      refine Finset.sum_le_sum fun Y _ => ?_
      by_cases hp : IsPolymer d ℓ (M * L ^ k) Y
      · simp only [hp, ↓reduceIte]; exact hB Y hp g hg
      · simp only [hp, ↓reduceIte]; rw [hS Y hp g, sub_self, norm_zero]
    have h2 : ∑ Y ∈ F, (if IsPolymer d ℓ (M * L ^ k) Y then
        B * Real.exp (-κ' * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d) else 0) =
        B * ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d ℓ))).filter
          (fun Y => hullT (M * L ^ k * L) Y = X ∧ IsPolymer d ℓ (M * L ^ k) Y),
          Real.exp (-κ' * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d) := by
      rw [← Finset.sum_filter, hF, Finset.filter_filter, Finset.mul_sum]
    have hcast : ((M * L ^ k * L : ℕ) : ℝ) = (M : ℝ) * (L : ℝ) ^ (k + 1) := by push_cast; ring
    have h3 : B * Real.exp (-(κ' - (L : ℝ) ^ d * Real.log 2) * (X.card : ℝ) /
          ((M * L ^ k * L : ℕ) : ℝ) ^ d) ≤
        B * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0
      rw [hcast]
      have hP : 0 ≤ (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d := by positivity
      have e1 : -(κ' - (L : ℝ) ^ d * Real.log 2) * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d
          = -(κ' - (L : ℝ) ^ d * Real.log 2) * ((X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) := by
        ring
      have e2 : -κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d
          = -κ * ((X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) := by ring
      rw [e1, e2]
      nlinarith
    calc ∑ Y ∈ F, ‖t ℓ Y g - t ℓ Y 0‖ ≤ _ := h1
      _ = _ := h2
      _ ≤ B * Real.exp (-(κ' - (L : ℝ) ^ d * Real.log 2) * (X.card : ℝ) /
          ((M * L ^ k * L : ℕ) : ℝ) ^ d) := mul_le_mul_of_nonneg_left hsum hB0
      _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right hBc (Real.exp_pos _).le
  · rw [regroupFam_ne _ _ _ _ _ _ _ _ hj', regroupFam_ne _ _ _ _ _ _ _ _ hj']
    simpa using hrhs

open Classical in
/-- **The four one-torus clauses of the regrouped activity** (A6-3 (c)). -/
theorem regroup_clauses {m' : ℕ} [NeZero m'] [NeZero (L * m')] (hℓ : ℓ = M * L ^ k * (L * m'))
    (hs : 0 < M * L ^ k) {B κ' κ c₉ δ : ℝ} (hB0 : 0 ≤ B) (hc₉ : 0 ≤ c₉) (hκ' : 0 ≤ κ')
    (hκ : κ + (L : ℝ) ^ d * Real.log 2 ≤ κ')
    (hBc : B ≤ c₉ / 2 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))))
    (hS : ∀ Y, ¬ IsPolymer d ℓ (M * L ^ k) Y → ∀ g, t ℓ Y g = t ℓ Y 0)
    (hA : ∀ Y, AnalyticOnNhd ℂ (t ℓ Y) {g : Torus d ℓ → Fin N → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1})
    (hLoc : ∀ Y (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ Y, g y = g' y) → t ℓ Y g = t ℓ Y g')
    (hB : ∀ Y, IsPolymer d ℓ (M * L ^ k) Y → ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖t ℓ Y g - t ℓ Y 0‖ ≤ B * Real.exp (-κ' * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d)) :
    ActSupportAt d N L M (k + 1) ℓ (regroupFam M L k t) ∧
      ActAnalyticAt d N ℓ (regroupFam M L k t) ∧ ActLocalAt d N ℓ (regroupFam M L k t) ∧
      ActBoundAt d N L M κ c₉ δ (k + 1) ℓ (regroupFam M L k t) :=
  ⟨regroup_support hS, regroup_analytic hA, regroup_local hLoc,
    regroup_bound hℓ hs hB0 hc₉ hκ' hκ hBc hS hB⟩

end Clauses

end Balaban.RootFSpine
