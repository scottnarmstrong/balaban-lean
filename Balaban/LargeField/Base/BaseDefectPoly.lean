/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseHullTwoTorus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The defect-determinant terms regrouped onto polymers

Let `ι` be a finite set of sites with positions `pos : ι → C` in the torus `C` of the first step,
and `D` a matrix of range `r`: `D a b ≠ 0` forces `pos b - pos a` into the ℓ∞ box of radius `r`.
The label of the set `S` of sites visited by a walk from `x` is the polymer hull
`walkLab pos m₀ r x S = hullOf m₀ (blockIndex (pos x)) (walkJ r (pos '' S))`.

* `sum_norm_walkLab_le`: the polymer terms of `BaseDefectWalks` for this label satisfy
  `∑_Y |t_Y| e^{κ dExt Y} ≤ e^{2 κ c} q`, `c = 2 d L (2r+1)^d`, when `q e^{κ c} ≤ 1/2`
  (`dExt_walkHull_le` gives `dExt ≤ c |S|`);
* `walkLab_twoTorus`: the labels of corresponding visited sets of two tori correspond under
  `cubeMap`; with `walkTerm_transport` the terms of corresponding walks agree.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.Polymer Balaban.Fluctuation Balaban.Polymer.TwoTorusStep

section Instance

open scoped Classical

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The polymer of the sites visited by a walk from `x`.** -/
noncomputable def walkLab (pos : ι → Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (m₀ r : ℕ)
    (x : ι) (S : Finset ι) :=
  hullOf m₀ (blockIndex (pos x)) (walkJ r (S.image pos))

/-- **Decay of the defect-determinant terms regrouped onto polymers.** -/
theorem sum_norm_walkLab_le (pos : ι → Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    {m₀ r : ℕ} (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (hn : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ (k + 1)) (D : Matrix ι ι ℂ)
    (hr : ∀ a b, D a b ≠ 0 → InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (pos b - pos a))
    {q κ : ℝ} (hq0 : 0 ≤ q) (hκ : 0 ≤ κ)
    (hρ : q * Real.exp (κ * (2 * d * L * (2 * r + 1) ^ d : ℝ)) ≤ 1 / 2)
    (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι) :
    ∑ Y, ‖walkPolyTerm (walkLab pos m₀ r x) D x Y‖ * Real.exp (κ * dExt Y) ≤
      Real.exp (2 * κ * (2 * d * L * (2 * r + 1) ^ d : ℝ)) * q := by
  refine sum_norm_walkPolyTerm_le (walkLab pos m₀ r x) (fun Y => dExt Y) D hq0 hκ
    (by positivity) hρ hK x ?_
  intro S hxS hch
  have hc0 : (0 : ℝ) ≤ 2 * d * L * (2 * r + 1) ^ d := by positivity
  have hA : ∀ a ∈ S.image pos, Relation.ReflTransGen
      (fun p q : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) =>
        p ∈ S.image pos ∧ q ∈ S.image pos ∧ InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (q - p))
      (pos x) a := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ha
    refine Relation.ReflTransGen.lift pos (fun u v ⟨hu, hv, huv⟩ => ?_) _ _ (hch s hs)
    exact ⟨Finset.mem_image_of_mem _ hu, Finset.mem_image_of_mem _ hv, hr u v huv⟩
  have h := dExt_walkHull_le hN hL hn (blockIndex (pos x)) (Finset.mem_image_of_mem pos hxS)
    (mem_rootSet_blockIndex (pos x)) hA
  have hcard : ((S.image pos).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
  exact h.trans (mul_le_mul_of_nonneg_left hcard hc0)

end Instance

section TwoTori

open scoped Classical

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {m₀ : ℕ}
  {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] in
/-- **The polymer of a walk on two tori.**  If `σ : ι → ι'` carries the positions on `S`
(`pos' (σ u) = bm (pos u)`), the label of `σ '' S` is the image under `cubeMap` of the label of
`S`, for `S` in the box of radius `ρ`. -/
theorem walkLab_twoTorus (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (pos : ι → Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    (pos' : ι' → Balaban.Localization.CTorus d L N₁' m₁ (k + 1)) (σ : ι → ι') {ρ r : ℕ}
    {x : ι} {S : Finset ι} (hxS : x ∈ S) (hpos : ∀ u ∈ S, pos' (σ u) = bm (pos u))
    (hS : ∀ u ∈ S, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (pos u))
    (hM1 : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hM1' : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hM2 : 2 * (ρ + r + L ^ (0 + m₁)) + 5 * (L * cellSide L 0 m₁ 0) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hM3 : 2 * (ρ + aK) + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (ρ + r + L ^ (0 + m₁) + aK + 2 * (L * aK)) + L * aK <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (ρ + r + L ^ (0 + m₁) + aK + 2 * (L * aK)) + L * aK <
      (N₁' * L ^ m₁) * L ^ (k + 1)) :
    walkLab pos' m₀ r (σ x) (S.image σ) =
      (walkLab pos m₀ r x S).image
        (Balaban.Polymer.TwoTorusStep.cubeMap hN hN' (le_refl (k + 1))) := by
  unfold walkLab
  have himg : (S.image σ).image pos' = (S.image pos).image bm := by
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun u hu => hpos u hu
  rw [himg, hpos x hxS]
  exact walkHull_image hN hN' (S.image pos)
    (fun a ha => by obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha; exact hS u hu)
    (Finset.mem_image_of_mem pos hxS) hM1 hM1' hM2 hM3 hnH hnH'

end TwoTori

end Balaban.LargeField.Base
