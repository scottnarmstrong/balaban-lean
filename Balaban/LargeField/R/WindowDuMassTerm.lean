/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuRead
public import Balaban.LargeField.R.CoeffResponseBudgetCount

/-!
# The mass term of the window action (blocker 4)

`massTerm_norm_le`: `‖c · (ν/2) ⟨u, u⟩_X‖ ≤ (|c||ν|/2) B ∑_i |X_i|` when `X ⊆ ⋃ X_i` and
`∑_j ‖u_j(x)‖² ≤ B` on `X`; `StepDecomp.card_budget`: `β|ν| |X| ≤ κ |X|_{mix}` from the cube budgets.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem massPair_norm_le (X : Region G) (u : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ‖X.massPair u u‖ ≤ ∑ x ∈ X.sites, ∑ j, ‖u x j‖ ^ 2 := by
  unfold Region.massPair
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, sq]

/-- Two unit vectors differ by at most `2`: `∑_j ‖a_j - b_j‖² ≤ 4`. -/
theorem sum_norm_sub_sq_le_four (a b : Fin N → ℂ) (ha : ∑ j, ‖a j‖ ^ 2 = 1)
    (hb : ∑ j, ‖b j‖ ^ 2 = 1) : ∑ j, ‖a j - b j‖ ^ 2 ≤ 4 := by
  have h : ∀ j, ‖a j - b j‖ ^ 2 ≤ 2 * ‖a j‖ ^ 2 + 2 * ‖b j‖ ^ 2 := fun j => by
    have := norm_sub_le (a j) (b j)
    nlinarith only [this, norm_nonneg (a j), norm_nonneg (b j), norm_nonneg (a j - b j),
      sq_nonneg (‖a j‖ - ‖b j‖)]
  calc ∑ j, ‖a j - b j‖ ^ 2 ≤ ∑ j, (2 * ‖a j‖ ^ 2 + 2 * ‖b j‖ ^ 2) := Finset.sum_le_sum fun j _ => h j
    _ = 2 * ∑ j, ‖a j‖ ^ 2 + 2 * ∑ j, ‖b j‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 4 := by rw [ha, hb]; norm_num

theorem massTerm_norm_le {ι : Type*} [Fintype ι] (Xwin : Region G) (Xw : ι → Region G)
    (hsub : Xwin.sites ⊆ Finset.univ.biUnion fun i => (Xw i).sites)
    (u : Torus d (N₀ * L ^ K) → Fin N → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ x ∈ Xwin.sites, ∑ j, ‖u x j‖ ^ 2 ≤ B) (c ν : ℝ) :
    ‖(c : ℂ) * ((ν : ℂ) / 2 * Xwin.massPair u u)‖ ≤
      |c| * |ν| / 2 * (B * ∑ i, ((Xw i).sites.card : ℝ)) := by
  have h1 : ‖Xwin.massPair u u‖ ≤ B * ∑ i, ((Xw i).sites.card : ℝ) := by
    refine (massPair_norm_le Xwin u).trans ?_
    calc ∑ x ∈ Xwin.sites, ∑ j, ‖u x j‖ ^ 2 ≤ ∑ _x ∈ Xwin.sites, B := Finset.sum_le_sum hu
      _ = B * (Xwin.sites.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ B * ∑ i, ((Xw i).sites.card : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ hB
          have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
          exact_mod_cast this
  have e : ‖(c : ℂ) * ((ν : ℂ) / 2 * Xwin.massPair u u)‖ =
      |c| * (|ν| / 2 * ‖Xwin.massPair u u‖) := by
    simp
  rw [e]
  calc |c| * (|ν| / 2 * ‖Xwin.massPair u u‖) ≤ |c| * (|ν| / 2 * (B * ∑ i, ((Xw i).sites.card : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (abs_nonneg c)
    _ = |c| * |ν| / 2 * (B * ∑ i, ((Xw i).sites.card : ℝ)) := by ring

theorem StepDecomp.card_budget {X : Region G} (Dc : StepDecomp X) {β κ : ℝ} (ν : ℝ)
    (h : ∀ c, β * ∑ _x ∈ (Dc.cube c).sites, |ν| ≤ κ * Dc.wt c) :
    β * |ν| * (X.sites.card : ℝ) ≤ κ * Dc.total := by
  have := Dc.sum_sites_le (fun _ => β * |ν|) (κ := κ) (fun c => by
    rw [Finset.sum_const, nsmul_eq_mul]
    have h2 := h c
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    linarith only [h2])
  rwa [Finset.sum_const, nsmul_eq_mul, mul_comm] at this

end Balaban.LargeField.ActionConv
