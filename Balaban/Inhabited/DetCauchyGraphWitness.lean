/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LocalizationSettings
public import Balaban.Inhabited.YregBlocksWitness
public import Balaban.Fluctuation.DetCauchyGraph
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of `DetCauchyGraph`

On the positive witness geometry of `LocalizationSettings.lean` (`d = L = 3`, `N₁ = 6`, `k = 1`,
`G = GP m₁ (rhoSep m₁)`, a single layer, `Ω₁ = Ω₂ = 𝕋`):

* the unit block `y` of the site `0` is attached to the centre `(2, 0)`, so the footprint `J` of
  that centre satisfies the conclusion of the support theorem (`RootChain`), is rooted in the
  parameter graph, and `rootParam G y` is a single parameter cube;
* every footprint has at least two cubes (`(2, 0)` and the cube next to it), so for the singleton
  `J'' = {(2, 0)}` no centre is active with footprint in `J''`, no chain exists, and the support
  theorem gives `mixDiff J''` of the rooted trace `= 0` for fixed constant admissible fields
  (`φ ≡ e₀`, `α = 0`).

The torus has six cubes per coordinate and the thickened cube of a centre spans most of them: a
parameter cube far from the root block, in the sense of the Moore graph, is not exhibited.  The
vanishing instance is for a singleton at the root's own cube, whose switching alone activates no
centre.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Fluctuation Balaban.Analysis

section Witness

variable (m₁ : ℕ)

/-- The base of the cube next to the cube of `(2, 0)` in the first coordinate. -/
def nextBase : CTorus 3 3 6 m₁ (1 + 1) := fun μ =>
  if μ = 0 then (((3 : ℕ) ^ (2 + m₁) : ℕ) : ZMod ((6 * 3 ^ m₁) * 3 ^ (1 + 1))) else 0

theorem nextBase_val0 : ((nextBase m₁) 0).val = 3 ^ (2 + m₁) := by
  unfold nextBase
  simp only [ite_true]
  rw [ZMod.val_natCast_of_lt]
  have h1 : 0 < 3 ^ m₁ := by positivity
  have h2 : (3 : ℕ) ^ (1 + 1) = 9 := by norm_num
  have h3 : (3 : ℕ) ^ (2 + m₁) = 9 * 3 ^ m₁ := by ring
  rw [h2, h3]
  omega

theorem nextBase_val_ne {μ : Fin 3} (h : μ ≠ 0) : ((nextBase m₁) μ).val = 0 := by
  unfold nextBase
  simp [h]

theorem nextBase_mem_cubeIdx :
    ((2 : ℕ), nextBase m₁) ∈ cubeIdx (GP m₁ (rhoSep m₁)) := by
  rw [mem_cubeIdx]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, fun μ => ?_⟩
  · show nextBase m₁ ∈ (GP m₁ (rhoSep m₁)).layer 2
    rw [GP_layer_two]; exact Finset.mem_univ _
  · by_cases h : μ = 0
    · subst h
      show ((nextBase m₁) 0).val % 3 ^ (2 + m₁) = 0
      rw [nextBase_val0, Nat.mod_self]
    · show ((nextBase m₁) μ).val % 3 ^ (2 + m₁) = 0
      rw [nextBase_val_ne m₁ h]; simp

theorem nextBase_mem_Qset :
    ((2 : ℕ), nextBase m₁) ∈ Qset (GP m₁ (rhoSep m₁)) ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) := by
  refine mem_Qset.2 ⟨nextBase_mem_cubeIdx m₁, nextBase m₁, SameCell.refl _ _, fun μ => ⟨0, ?_⟩⟩
  have hB : (1 : ℝ) ≤ (3 : ℝ) ^ (2 + m₁) := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ 2 := by positivity
  have h0 : (((0 : CTorus 3 3 6 m₁ (1 + 1)) μ).val : ℝ) = 0 := by simp
  simp only [Int.cast_zero, zero_mul, add_zero, h0, zero_add]
  unfold hatRad
  by_cases h : μ = 0
  · subst h
    have := nextBase_val0 m₁
    rw [show (((nextBase m₁) 0).val : ℝ) = (3 : ℝ) ^ (2 + m₁) by
      rw [this]; push_cast; rfl]
    rw [abs_of_nonneg (by linarith)]
    push_cast
    linarith
  · rw [nextBase_val_ne m₁ h]
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by linarith)]
    push_cast
    linarith

theorem nextBase_ne : ((2 : ℕ), nextBase m₁) ≠ ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) := by
  intro h
  have h2 : nextBase m₁ = 0 := (Prod.mk.inj h).2
  have := congrArg (fun f : CTorus 3 3 6 m₁ (1 + 1) => (f 0).val) h2
  simp only [nextBase_val0] at this
  simp at this

theorem witness_mem_cubeIdx :
    ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) ∈ cubeIdx (GP m₁ (rhoSep m₁)) := by
  rw [mem_cubeIdx]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, fun μ => by simp⟩
  show (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ (GP m₁ (rhoSep m₁)).layer 2
  rw [GP_layer_two]; exact Finset.mem_univ _

/-- The singleton at the cube of `(2, 0)` activates no centre: no chain reaches it. -/
theorem witness_hnc (y : unitPts (GP m₁ (rhoSep m₁))) :
    ∀ q, RootChain (GP m₁ (rhoSep m₁))
        {(⟨((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))), witness_mem_cubeIdx m₁⟩ :
          cubeIdx (GP m₁ (rhoSep m₁)))} y q →
      (⟨((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))), witness_mem_cubeIdx m₁⟩ :
          cubeIdx (GP m₁ (rhoSep m₁))) ∉ QsetP (GP m₁ (rhoSep m₁)) q := by
  intro q hq _
  obtain ⟨⟨hqc, hsub⟩, -⟩ := hq
  have hself : (⟨q, hqc⟩ : cubeIdx (GP m₁ (rhoSep m₁))) ∈ QsetP (GP m₁ (rhoSep m₁)) q :=
    mem_QsetP.2 (self_mem_Qset_zeroCuts hqc)
  have hqp := Finset.mem_singleton.1 (hsub hself)
  have hqq : q = ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) := congrArg Subtype.val hqp
  have h2 : (⟨((2 : ℕ), nextBase m₁), nextBase_mem_cubeIdx m₁⟩ : cubeIdx (GP m₁ (rhoSep m₁))) ∈
      QsetP (GP m₁ (rhoSep m₁)) q := mem_QsetP.2 (hqq ▸ nextBase_mem_Qset m₁)
  have h3 := Finset.mem_singleton.1 (hsub h2)
  exact nextBase_ne m₁ (congrArg Subtype.val h3)

end Witness

section Main

/-- **Non-vacuity of the support theorem and of the parameter graph.**  There is a witness geometry,
a unit block `y`, a non-empty cut set `J` (the footprint of the centre `(2, 0)`) with non-empty
`Yreg` at its cut point, all of whose parameter cubes are joined to `y` by a chain (`RootChain`),
which is rooted in the parameter graph at the single parameter cube `rootParam G y`; and, for fixed
admissible constant fields, the singleton `{p₀}` at the cube of `(2, 0)` activates no centre, so
the support theorem gives `mixDiff {p₀} = 0` for the rooted trace of `{y}`. -/
theorem detCauchyGraph_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ) (y : unitPts G)
      (J : Finset (cubeIdx G)) (p₀ : cubeIdx G),
      XSetting G (compWeight 3 1) 1 0 ∧ HatConn G ∧ J.Nonempty ∧
      (Yreg G (extS G (cutPt J))).Nonempty ∧
      (∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q) ∧
      Polymer.Rooted (paramGraph G) ((rootParam G y : Finset (cubeIdx G)) : Set (cubeIdx G)) J ∧
      (rootParam G y).card = 1 ∧
      ∃ (κ δ : ℝ) (φ : CTorus 3 3 6 m₁ (1 + 1) → Fin 3 → ℂ) (α : G.Ω 1 → ℂ),
        0 < κ ∧ cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁ ∧ 0 ≤ δ ∧
        δ ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧ IsConstraintFieldStrict G δ φ ∧
        (∀ w, ‖α w‖ < coerciveConst 3 / (2 * (G.spacing (w : CTorus 3 3 6 m₁ (1 + 1))) ^ 2)) ∧
        mixDiff ({p₀} : Finset (cubeIdx G))
          (fun s => rootTrace G (compWeight 3 1) 1 0 (unitQ G) (unitP G) {y} s φ α) = 0 := by
  classical
  obtain ⟨m₁, h4, hc⟩ := exists_m₁ (cstarX 3 3 * Real.exp (N0 3 3 * 1))
  have S := xSetting_pos h4
  set G := GP m₁ (rhoSep m₁) with hG
  have hz : ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) ∈ cubeIdx G := by
    rw [mem_cubeIdx]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, fun μ => by simp⟩
    show (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.layer 2
    rw [hG, GP_layer_two]; exact Finset.mem_univ _
  have hl0 : (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.layer (1 + 1) := by
    rw [hG]; exact (Finset.ext_iff.1 (GP_layer_two (m₁ := m₁) (ϱ := rhoSep m₁)) _).2 (Finset.mem_univ _)
  have hΩ0 : (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.Ω 1 := by rw [hG, GP_Ω]; simp
  have hmem : (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ hatBox ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) := by
    unfold hatBox
    rw [mem_boxSet]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (3 : ℝ) ^ (2 + m₁) := one_le_pow₀ (by norm_num)
    simp only [Int.cast_zero, zero_mul, add_zero]
    unfold hatRad
    have h0 : (((0 : CTorus 3 3 6 m₁ (1 + 1)) μ).val : ℝ) = 0 := by simp
    rw [h0, zero_add, zero_sub, abs_neg, abs_of_nonneg (by push_cast; linarith)]
    push_cast
    have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ 2 := by positivity
    linarith
  set y : unitPts G := ⟨unitBlock (0 : CTorus 3 3 6 m₁ (1 + 1)), (mem_unitPts G).2 ⟨0, hl0, rfl⟩⟩
    with hy
  set q0 : ℕ × CTorus 3 3 6 m₁ (1 + 1) := (2, 0) with hq0
  set J : Finset (cubeIdx G) := QsetP G q0 with hJ
  have hqQ : (⟨q0, hz⟩ : cubeIdx G) ∈ J := mem_QsetP.2 (self_mem_Qset_zeroCuts hz)
  have hatt : HatAttached G y q0 := ⟨⟨0, hΩ0⟩, rfl, hmem⟩
  have hchain : RootChain G J y q0 :=
    RootChain.of_attached ⟨hz, Finset.Subset.refl _⟩ hatt
  have hall : ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q := fun p hp => ⟨q0, hchain, hp⟩
  have hcube : CubeAligned G m₁ := GP_cubeAligned (by omega)
  -- the root parameter
  obtain ⟨P0, hP0, hxP0⟩ := exists_cube_of_mem_Omega hcube hΩ0
  have hroot : (rootParam G y).card = 1 := by
    refine le_antisymm (card_rootParam_le hcube y) (Finset.card_pos.2 ⟨⟨P0, hP0⟩, ?_⟩)
    exact mem_rootParam.2 ⟨⟨0, hΩ0⟩, rfl, hxP0⟩
  -- the analytic data
  obtain ⟨hκM⟩ : Nonempty (cstarX 3 3 * Real.exp (N0 3 3 * 1) ≤ (3 : ℝ) ^ m₁) := ⟨hc⟩
  set c : ℝ := |smallConstX 3 3 1| with hcdef
  set δ : ℝ := 1 / (2 * (c + 1)) with hδdef
  have hc0 : 0 ≤ c := abs_nonneg _
  have hδpos : 0 < δ := by positivity
  have hsm : δ ^ 2 * smallConstX 3 3 1 ≤ 1 / 4 := by
    have h1 : δ ^ 2 * smallConstX 3 3 1 ≤ δ ^ 2 * c :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have h2 : δ ^ 2 * c = c / (4 * (c + 1) ^ 2) := by
      rw [hδdef]; field_simp; ring
    have h3 : c / (4 * (c + 1) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hφ : IsConstraintFieldStrict G δ (fun _ => (Pi.single 0 1 : Fin 3 → ℂ)) := by
    have hv0 : vn (0 : Fin 3 → ℂ) = 0 := by simp [vn]
    refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have hs := spacing_pos G (x := x)
      simp only [sub_self, hv0]
      exact ⟨by positivity, by positivity⟩
    · have hs := spacing_pos G (x := x)
      have : (fun i : Fin 3 => ∑ μ : Fin 3, ((Pi.single 0 1 : Fin 3 → ℂ) i +
          (Pi.single 0 1 : Fin 3 → ℂ) i - 2 * (Pi.single 0 1 : Fin 3 → ℂ) i)) = 0 := by
        funext i; simp; ring
      rw [this, hv0]; positivity
    · have : vn (Pi.single 0 1 : Fin 3 → ℂ) = 1 := by
        unfold vn
        show ‖EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ = 1
        simp
      rw [this]; norm_num
    · have : ∑ i : Fin 3, (Pi.single 0 1 : Fin 3 → ℂ) i * (Pi.single 0 1 : Fin 3 → ℂ) i - 1 = 0 := by
        simp [Pi.single_apply]
      rw [this, norm_zero]; exact hδpos
  have hα : ∀ w : G.Ω 1, ‖(0 : G.Ω 1 → ℂ) w‖ <
      coerciveConst 3 / (2 * (G.spacing (w : CTorus 3 3 6 m₁ (1 + 1))) ^ 2) := by
    intro w
    simp only [Pi.zero_apply, norm_zero]
    have := coerciveConst_pos (by norm_num : 0 < 3)
    have hs := spacing_pos G (x := (w : CTorus 3 3 6 m₁ (1 + 1)))
    positivity
  set p₀ : cubeIdx G := ⟨q0, hz⟩ with hp₀
  have hnc := witness_hnc m₁ y
  refine ⟨m₁, rhoSep m₁, G, y, J, p₀, S, GP_hatConn, ⟨_, hqQ⟩, ?_, hall,
    rooted_of_rootChain hcube hall, hroot, 1, δ, fun _ => Pi.single 0 1, 0, one_pos, hc, hδpos.le,
    hsm, hφ, hα, ?_⟩
  · exact ⟨0, hatI_subset_Yreg_cutPt hz (by
      unfold hatI; rw [Finset.mem_filter]; exact ⟨hmem, hΩ0⟩)⟩
  · exact mixDiff_rootTrace_single_eq_zero S one_pos hc hδpos.le hsm hφ hα GP_hatConn
      (Finset.mem_singleton_self p₀) y hnc

end Main

end Balaban.Inhabited
