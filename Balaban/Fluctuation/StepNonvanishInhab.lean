/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepNonvanishBound
public import Balaban.Fluctuation.Thm31Inhab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `StepActivityBound` is inhabited

For a step datum with `β > 0`, `p₁ > 0` on the torus with `N₁ = 1` (one block `π_{k+1}`-cube) whose
truncated exponents `W₁(s) + W₂(t)` on the two segments are measurable and uniformly below the
cluster threshold `stepActivityThreshold` (the activities are the truncated exponents themselves,
in general nonzero), `StepActivityBound` holds (`nonempty_stepActivityBound`).  The smallness is the
physical content of the structure and is a hypothesis of the witness only.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField.Def6
  Balaban.Background Balaban.SmallField MeasureTheory

section Inhab

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- With `N₁ = 1` the torus is a single `π_{k+1}`-cube: the block type is a singleton. -/
theorem nonempty_unique_cubeB (hN₁ : N₁ = 1) :
    Nonempty (Unique (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
      Set.univ)) := by
  subst hN₁
  have hn : (1 * L ^ m₁ * L ^ (k + 1)) = cellSide L 0 m₁ (k + 1) := by
    unfold cellSide; rw [one_mul, ← pow_add]; congr 1; omega
  have hz : ∀ b : CTorus d L 1 m₁ (k + 1), Aligned (cellSide L 0 m₁ (k + 1)) b →
      b = 0 := by
    intro b hb
    funext μ
    have h1 := hb μ
    have h2 : (b μ).val < cellSide L 0 m₁ (k + 1) := by
      rw [← hn]; exact ZMod.val_lt _
    have h3 : (b μ).val = 0 := by
      rw [Nat.mod_eq_of_lt h2] at h1; exact h1
    have : b μ = 0 := (ZMod.val_eq_zero _).1 h3
    simpa using this
  refine ⟨{
    default := ⟨cbase (cellSide L 0 m₁ (k + 1)) 0, aligned_cbase 0, Set.subset_univ _⟩
    uniq := fun b => Subtype.ext ((hz _ b.2.1).trans (hz _ (aligned_cbase 0)).symm) }⟩

open Classical in
/-- The cluster-threshold bound for the activities in the witness: `ε_H e^{-κ_H 𝗱({𝕋})}` for the
admissible constants `κ₀ = a_ent + 1`, `K_c = K₀ + 1`, `κ' = 0`, `κ_H = 3κ₀ + c₁ + 3/2`. -/
noncomputable def stepActivityThreshold (d L N₁ m₁ K : ℕ) [NeZero L] [NeZero N₁] : ℝ :=
  (1 / (8 * (K0 d L (aEnt d L + 1) + 1) ^ 3 * c1 d L *
    Real.exp (((3 * (aEnt d L + 1) + c1 d L + 3 / 2) - 2 * (aEnt d L + 1)) * cG d L + c1 d L +
      0 * cG d L))) *
    Real.exp (-(3 * (aEnt d L + 1) + c1 d L + 3 / 2) *
      treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ)

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  (g : Fld d L N₁ m₁ (k + 1) N)

open Classical in
/-- **`StepActivityBound` is inhabited** (non-vacuity): on the one-cube torus, for every `β` (in particular `β > 0`),
`p₁ > 0`, measurable truncated exponents whose sum is below the cluster threshold along the
segments.  The activities are `W₁(s) + W₂(t)` truncated to the support of `ν_{p₁}`. -/
theorem nonempty_stepActivityBound (hN₁ : N₁ = 1) (hp₁ : 0 < S.p₁)
    (hmeas : ∀ p ∈ stepSegments, Measurable (fun x => S.WoneT C p.1 x + S.WtwoT C g p.2 x))
    (hsmall : ∀ p ∈ stepSegments, ∀ x,
      ‖S.WoneT C p.1 x + S.WtwoT C g p.2 x‖ ≤ stepActivityThreshold d L N₁ m₁ (k + 1)) :
    Nonempty (StepActivityBound S C g) := by
  have hprob : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  obtain ⟨hU⟩ := nonempty_unique_cubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hN₁
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hc1 := one_le_c1 d L
  set κ0 := aEnt d L + 1 with hκ0
  set Kc := K0 d L κ0 + 1 with hKc
  have hKc1 : 1 ≤ Kc := by linarith
  set κH := 3 * κ0 + c1 d L + 3 / 2 with hκH
  set εH := 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + 0 * cG d L)) with hεH
  have hεpos : 0 < εH := by positivity
  let Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1) Set.univ
      Unit :=
    { ysite := fun _ => Set.univ
      dl := fun _ => treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
        Set.univ
      isDj := fun _ => isDj_univ d L N₁ m₁ (k + 1) 0 (k + 1)
      meets := fun _ => by simp
      size := fun _ => Or.inl rfl }
  let BS : BlockSplit S 0 :=
    { Ωb := fun _ => S.E
      μ := fun _ => S.nuFl
      restr := fun x _ => x
      meas := Measurable.of_eval fun _ => measurable_id
      map_eq := by
        have := (measurePreserving_funUnique S.nuFl
          (α := CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
            Set.univ)).symm (MeasurableEquiv.funUnique _ _)
        convert this.map_eq
        rfl }
  let A : ℝ × ℝ → LabelAct Lab BS.Ωb εH κH κ0 Kc := fun p =>
    { H := fun _ Φ => if p ∈ stepSegments then
        S.WoneT C p.1 (Φ default) + S.WtwoT C g p.2 (Φ default) else 0
      meas := fun _ => by
        by_cases hp : p ∈ stepSegments
        · simp only [hp, ite_true]
          exact (hmeas p hp).comp (measurable_pi_apply _)
        · simp only [hp, ite_false]; exact measurable_const
      dep := fun _ Φ Φ' h => by
        have hb : default ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0 (k + 1)
            Set.univ (Lab.ysite ()) := by
          rw [mem_blocksOf]; exact Set.subset_univ _
        simp only [h default hb]
      bound := fun _ Φ => by
        by_cases hp : p ∈ stepSegments
        · simp only [hp, ite_true]
          refine (hsmall p hp _).trans (le_of_eq ?_)
          simp [stepActivityThreshold, εH, κH, κ0, Kc, Lab]
        · simp only [hp, ite_false, norm_zero]; positivity
      entropy := fun b => by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        split_ifs
        · have h0 : 0 ≤ treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 0
              (k + 1) Set.univ := treeLenCovOne_nonneg _ _ _
          have : Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (K := k + 1) 0 (k + 1) Set.univ) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [aEnt_nonneg d L])
          linarith
        · linarith }
  refine ⟨{
    m₀ := 0
    hN := by simp
    BS := BS
    Lb := Unit
    Lab := Lab
    εH := εH
    κH := κH
    κ0 := κ0
    κ' := 0
    Kc := Kc
    A := A
    hκ0 := le_rfl
    hKc := le_rfl
    hεpos := hεpos
    hκ' := le_rfl
    hκ := by rw [hκH]; linarith
    hε := le_rfl
    hW := fun p hp => ?_ }⟩
  filter_upwards [S.ae_ball hp₁] with x hx
  simp only [A, hp, ite_true, Finset.univ_unique, Finset.sum_singleton, BS]
  rw [S.WoneT_of_chi C p.1 x hx, S.WtwoT_of_chi C g p.2 x hx]

end Inhab

end Balaban.Fluctuation
