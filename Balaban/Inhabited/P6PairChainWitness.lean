/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairChain
public import Balaban.Inhabited.P6FsharpRootedWitness

/-!
# Non-vacuity of the chain patch graph and parameter-free centres

Counting and geometry only.

* `sum_instance`: for the cover `F♯` of the P6 pair with `d = L = 3`, `k + 1 = 2`, `m₁ = 7`
  (`M₁ = 3^7`, `c = 15`; `m₁ = 7` is the smallest exponent for which the separation row
  `2 d log L ≤ agmonRate d / 16 (5 L M₁ - 1)` of the landed `CoverGeom` holds, the slab with
  `m₁ = 2` does not satisfy `4 L² ≤ L^{m₁}`), the premises of `p6_chainPatch_rooted_sum_le` hold
  (cube alignment, sup-separation, `d < 5 L³ M₁`, `4 L² ≤ M₁`), and `pairChainD² e^{-120} < 1`; so the
  rooted sum over the chain patch graph at a seed of one site is bounded by `e^{h}`, `h = -log(1 - z)`.
  The constant `pairChainD 3 3 = (detDeg 3 3 + 1)^3 + 1` is about `10^25` (`detDeg 3 3 = 214991877`),
  so the rate requirement is `κ₂ > 2 log pairChainD ≈ 115`.
* `slab_paramFree`: on the slab cover `F♯` (`m₁ = 2`) the top centre `(2, ustar)` is parameter-free
  for `X₁ = univ` and is not parameter-free for `X₁ = ∅`.

No instance of the joint-closure statement `p6_jointParams_rooted` is given: it needs
`Dec2.CoverGeom (coverOf F♯)` for both operators, which has no landed instance (the separation row
forces `m₁ ≥ 7`, and the slab has `m₁ = 2`).
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6PairChainWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Localization.Dec2 Balaban.Fluctuation
open Slab

/-- The cover `F♯` of the `m₁ = 7` setting. -/
noncomputable abbrev Fs7 (n1 : ℕ) [NeZero n1] :
    GeneratingSet 3 3 ((15 * n1) * 3 ^ 7) (1 + 1) (minSep 3 (3 ^ 7)) :=
  p6FsharpC (k := 1) (m₁ := 7) (n0 := 3 * n1) (M1 := 3 ^ 7) (c := 15) (n1 := n1) (L := 3)
    (ρ' := 9) (Z := Set.univ) rfl (by norm_num) (by norm_num) rfl

theorem hD : pairChainD 3 3 = (214991878 : ℕ) ^ 3 + 1 := by
  norm_num [pairChainD, pairChainDeg, detDeg, N0]

/-- `pairChainD² e^{-120} < 1`. -/
theorem hz120 : ((pairChainD 3 3 : ℕ) : ℝ) ^ 2 * Real.exp (-120) < 1 := by
  rw [hD, Real.exp_neg]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 120 < Real.exp 1 ^ 120 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : Real.exp 120 = Real.exp 1 ^ 120 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← h3] at h2
  have h4 : (0 : ℝ) < Real.exp 120 := Real.exp_pos _
  rw [mul_inv_lt_iff₀ h4]
  push_cast
  have h5 : (((214991878 : ℝ) ^ 3 + 1) ^ 2) < (2.7 : ℝ) ^ 120 := by norm_num
  linarith

/-- **Slab instance of the rooted sum for the chain patch graph of `F♯`.** -/
theorem sum_instance (n1 : ℕ) [NeZero n1] :
    ∑ C ∈ rootedSets (G := chainPatchGraph (Fs7 n1))
        (⋃ s ∈ ({0} : Finset (CTorus 3 3 (15 * n1) 7 (1 + 1))),
          (pairRootNbhd (G := Fs7 n1) s : Set _)), Real.exp (-120 * C.card)
      ≤ Real.exp (-Real.log (1 - ((pairChainD 3 3 : ℕ) : ℝ) ^ 2 * Real.exp (-120)) * 1) *
        Real.exp (-Real.log (1 - ((pairChainD 3 3 : ℕ) : ℝ) ^ 2 * Real.exp (-120)) * 1 * 0) :=
  p6_chainPatch_rooted_sum_le (k := 1) (m₁ := 7) (n0 := 3 * n1) (M1 := 3 ^ 7) (c := 15)
    (n1 := n1) (L := 3) (ρ' := 9) rfl (by norm_num) (by norm_num) Set.univ rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) {0} hz120 (by simp)

/-- **Parameter-free centres on the slab.**  The top centre `(2, ustar)` of `F♯` is parameter-free
for `X₁ = univ` and is not parameter-free for `X₁ = ∅`. -/
theorem slab_paramFree (n1 : ℕ) [NeZero n1] (hn1 : n1 = 100) :
    PairParamFree (C := coverOf (P6FsharpRootedWitness.Fs n1))
      (X₁ := (Finset.univ : Finset (CTorus 3 3 (15 * n1) 2 (1 + 1)))) (1 + 1, ustar n1) ∧
    ¬ PairParamFree (C := coverOf (P6FsharpRootedWitness.Fs n1))
      (X₁ := (∅ : Finset (CTorus 3 3 (15 * n1) 2 (1 + 1)))) (1 + 1, ustar n1) := by
  refine ⟨paramFree_of_univ rfl _, not_paramFree_of_cell (top_mem_cubeIdx n1 hn1) ?_⟩
  intro h
  have : (ustar n1) ∈ cubeP ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)) :=
    mem_cubeP.2 (SameCell.refl _ _)
  simpa using h this

end P6PairChainWitness

end Balaban.Inhabited
