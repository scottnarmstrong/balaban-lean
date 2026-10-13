/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairParamDegree
public import Balaban.Inhabited.P6ActiveSeedWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# An instance of the sharp rootedness and the sharp rooted sum for the P6 pair

On the parameters of `P6ActiveSeedWitness` (`d = L = 3`, `m₀ = 3`, `c = 27`, `m₁ = 7`, `k = 1`,
`a ≡ 1`, `ν = 0`), where `Dec2.CoverGeom` and `Dec2.FootLocal` hold for both operators of the pair
(`sw_pair_instance`):

* `sw_jointParams_rooted_sharp`: the joint-closure rootedness theorem
  `p6_jointParams_rooted_sharp` has all its geometric premises discharged; the free data are the
  uncut core `X₁`, the marked set `𝒞` and the seed `U`.
* `sw_patch_sum`: the sharp rooted sum indexed by patches, with `κ₂ = 40`
  (`(D + 1)² e^{-40} < 1`, `D + 1 = 214 991 878`).
* `sw_cells_sum`: the sharp rooted sum indexed by the active cells of `swSeed`, with `κ₂ = 70`
  (`D♯ = (D + 1) · 3^3 (3^3)^3 = 214 991 878 · 531 441`).

Counting only (`OPEN-P6-ACTIVE-COMPOSITE-LOC`, `OPEN-P6-X1-INSTANTIATION`).
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6ActiveSeedWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Localization.Dec2 Balaban.Fluctuation

/-- The cover `F♯` of the instance, unfolded (so that the statements below elaborate with the
landed ones). -/
noncomputable abbrev swCov :=
  p6FsharpC (k := swk) (m₁ := swm₁) (n0 := swn0) (M1 := swM1) (c := swc) swHn swHρ swH5
    swSt.Z (rfl : swM1 = swS.L ^ swm₁)

theorem sw_p6SharpDPatch : p6SharpDPatch swS.d swS.L = 214991878 := by
  show p6SharpDPatch swd swL = 214991878
  rw [swd_eq, swL_eq]
  unfold p6SharpDPatch
  rw [detDeg_three]

theorem sw_p6SharpD : p6SharpD swS.d swS.L swm₀ = 214991878 * 531441 := by
  show p6SharpD swd swL 3 = 214991878 * 531441
  rw [swd_eq, swL_eq]
  unfold p6SharpD
  rw [detDeg_three]
  norm_num

/-- `(D + 1)² e^{-40} < 1`. -/
theorem sw_hz40 : ((p6SharpDPatch swS.d swS.L : ℕ) : ℝ) ^ 2 * Real.exp (-40) < 1 := by
  rw [sw_p6SharpDPatch, Real.exp_neg]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 40 < Real.exp 1 ^ 40 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : Real.exp 40 = Real.exp 1 ^ 40 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← h3] at h2
  have h4 : (0 : ℝ) < Real.exp 40 := Real.exp_pos _
  rw [mul_inv_lt_iff₀ h4]
  push_cast
  nlinarith [h2]

/-- `D♯² e^{-70} < 1`. -/
theorem sw_hz70 : ((p6SharpD swS.d swS.L swm₀ : ℕ) : ℝ) ^ 2 * Real.exp (-70) < 1 := by
  rw [sw_p6SharpD, Real.exp_neg]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 70 < Real.exp 1 ^ 70 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : Real.exp 70 = Real.exp 1 ^ 70 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← h3] at h2
  have h4 : (0 : ℝ) < Real.exp 70 := Real.exp_pos _
  rw [mul_inv_lt_iff₀ h4]
  push_cast
  nlinarith [h2]

/-- **Instance of the sharp rootedness of the joint closure.**  All geometric premises of
`p6_jointParams_rooted_sharp` hold on the instance; the uncut core `X₁`, the marked set `𝒞` and the
seed `U ⊇ X₁` (inside the domain of `F♯`) are arbitrary. -/
theorem sw_jointParams_rooted_sharp (X₁ : Finset swCT)
    (𝒞 : Finset (ℕ × swCT)) (U : Set swCT) (hX : ∀ x ∈ X₁, x ∈ U)
    (hU : ∀ s ∈ U, s ∈ swCover.Ω 1) :
    Rooted (paramGraph swCover) (pairRootSetSharp swCover U)
      ((jointParams (coverOf swCover) swHbd swHold (fun _ : ℕ => (1 : ℝ)) 0 X₁ 𝒞 U).subtype
        (fun P => P ∈ cubeIdx swCover)) :=
  p6_jointParams_rooted_sharp (k := swk) swSt (by show 14 ≤ swL ^ 3; rw [swL_eq]; norm_num) swHn
    (by show 2 ≤ swL; rw [swL_eq]; norm_num) swHρ subset_rfl rfl swHm swHM swH3d swH3L le_rfl
    swHnu P6TopWitness.Pair.hadm swHsep X₁ 𝒞 U hX hU

/-- **Instance of the sharp rooted sum indexed by patches** (`κ₂ = 40`). -/
theorem sw_patch_sum (S : Finset (cubeIdx swCov)) :
    ∑ C ∈ rootedSets (G := paramGraph swCov) (⋃ Q ∈ S, ((closedNbhd Q : Finset _) : Set _)),
        Real.exp (-40 * C.card)
      ≤ Real.exp (-Real.log (1 - ((p6SharpDPatch swS.d swS.L : ℕ) : ℝ) ^ 2 * Real.exp (-40)) *
          (S.card : ℝ)) *
        Real.exp (-Real.log (1 - ((p6SharpDPatch swS.d swS.L : ℕ) : ℝ) ^ 2 * Real.exp (-40)) *
          (S.card : ℝ) * 0) :=
  p6_sharp_rooted_sum_le (k := swk) (m₁ := swm₁) (n0 := swn0) (M1 := swM1) (c := swc)
    swHn swHρ swH5 swSt.Z rfl swHm swHd swHM (by show 1 ≤ swL; rw [swL_eq]; norm_num) S
    sw_hz40 (by simp)

/-- **Instance of the sharp rooted sum indexed by the active cells of `swSeed`** (`κ₂ = 70`). -/
theorem sw_cells_sum :
    swSeed.Nonempty ∧
    ∑ C ∈ rootedSets (G := paramGraph swCov)
        (⋃ u ∈ swSeed, ((p6SharpRootNbhd (k := swk) (m₁ := swm₁) (n0 := swn0) (M1 := swM1)
          (c := swc) swm₀ swHn swHρ swH5 swSt.Z rfl u : Finset _) : Set (cubeIdx swCov))),
        Real.exp (-70 * C.card)
      ≤ (1 / (1 - ((p6SharpD swS.d swS.L swm₀ : ℕ) : ℝ) ^ 2 * Real.exp (-70))) ^ swSeed.card := by
  refine ⟨swSeed_nonempty, ?_⟩
  have hterm : ∀ C : Finset (cubeIdx swCov), Real.exp (-70 * C.card) =
      Real.exp (-70) ^ C.card := fun C => by rw [← Real.exp_nat_mul]; ring_nf
  simp only [hterm]
  exact p6_sharp_cells_sum_le (k := swk) (m₁ := swm₁) (n0 := swn0) (M1 := swM1) (c := swc)
    (m₀ := swm₀) swSt rfl dvd_rfl swHn (by show 0 < swL; rw [swL_eq]; norm_num) swHρ swH5 swHm swHd
    swHM swSeed
    (fun u hu => d7ActiveSeed_image_cast_subset swF swHside swSt Set.univ Finset.univ _
      (Finset.mem_image_of_mem _ hu))
    (Real.exp_pos _).le sw_hz70

end P6ActiveSeedWitness

end Balaban.Inhabited
