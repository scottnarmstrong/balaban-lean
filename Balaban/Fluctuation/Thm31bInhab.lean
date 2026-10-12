/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31b
public import Balaban.Fluctuation.Thm31Inhab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): non-vacuity of `ObsMarks`

`ObsMarks` is inhabited for zero interaction, zero marks and zero kernel, the label `{𝕋}` and the
admissible constants `κ₀ = a_ent + 1`, `K_c = K₀ + 1`, `κ' = κ₀`, `R_σ = 2`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric

section Witness

variable (d L N₁ m₁ K : ℕ) [NeZero N₁] [NeZero L]

open Classical in
/-- **`ObsMarks` is inhabited** for an admissible choice of parameters. -/
theorem nonempty_obsMarks :
    ∃ (ν : Measure (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ → Unit))
      (BS : ProdSplit ν d L N₁ m₁ K 0) (W f : ℝ → _ → ℂ)
      (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ),
      Nonempty (ObsMarks ν BS W f bx) := by
  obtain ⟨ν, ⟨BS⟩⟩ := nonempty_prodSplit d L N₁ m₁ K 0
  have hNZ : NeZero (N₁ * L ^ m₁ * L ^ K) :=
    ⟨Nat.pos_iff_ne_zero.1 (by have := NeZero.pos N₁; have := NeZero.pos L; positivity)⟩
  let z0 : CTorus d L N₁ m₁ K := 0
  let bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ :=
    ⟨cbase (cellSide L 0 m₁ K) z0, aligned_cbase z0, Set.subset_univ _⟩
  refine ⟨ν, BS, fun _ _ => 0, fun _ _ => 0, bx, ?_⟩
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hc1 := one_le_c1 d L
  set κ0 := aEnt d L + 1 with hκ0
  set Kc := K0 d L κ0 + 1 with hKc
  have hKc1 : 1 ≤ Kc := by linarith
  have hκ0' : 0 ≤ κ0 := by linarith [aEnt_nonneg d L]
  set κ' := κ0 with hκ'def
  set κH := κ' + 3 * κ0 + c1 d L + 3 / 2 with hκH
  set εH := 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) with hεH
  have hεpos : 0 < εH := by positivity
  let Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ Unit :=
    { ysite := fun _ => Set.univ
      dl := fun _ => treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ
      isDj := fun _ => isDj_univ d L N₁ m₁ K 0 K
      meets := fun _ => by simp
      size := fun _ => Or.inl rfl }
  have hdl : 0 ≤ treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K
      Set.univ := treeLenCovOne_nonneg _ _ _
  let A : ℂ → ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc := fun _ _ =>
    { H := fun _ _ => 0
      meas := fun _ => measurable_const
      dep := fun _ _ _ _ => rfl
      bound := fun y Φ => by
        simp only [norm_zero]; positivity
      entropy := fun b => by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        split_ifs
        · have : Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
              0 K Set.univ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          linarith
        · linarith }
  have hbx : bx ∈ blocksOf 0 K (Set.univ : Set (CTorus d L N₁ m₁ K)) (Set.univ) := by
    rw [mem_blocksOf]; exact Set.subset_univ _
  exact ⟨{
    Lb := Unit
    Lab := Lab
    εH := εH
    κH := κH
    κG := κH
    κ0 := κ0
    κ' := κ'
    Kc := Kc
    hN := by simp
    Rσ := 2
    hRσ := by norm_num
    𝒰 := Set.univ
    isOpen := isOpen_univ
    seg := fun _ _ => trivial
    A := A
    holt := fun _ _ => differentiableOn_const _
    holσ := fun _ _ _ _ => differentiableOn_const _
    zero := fun _ _ _ _ => rfl
    hW := fun s _ => Filter.Eventually.of_forall fun x => by simp [A]
    ι1 := Unit
    y1 := fun _ => ()
    G1 := fun _ _ => 0
    meas1 := fun _ => measurable_const
    dep1 := fun _ _ _ _ => rfl
    F1 := fun _ => 1
    hF1 := fun _ => one_pos
    bound1 := fun i Φ => by simp only [norm_zero]; positivity
    mean1 := fun _ => by simp
    Fm := 1
    hFm := fun _ => by
      have : Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
          0 K Set.univ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simpa [Lab] using this
    bm := fun _ => bx
    hbm := fun _ => hbx
    nmax := 1
    hnmax := zero_le_one
    hcount := fun c => by
      have : (Finset.univ.filter fun _ : Unit => bx = c).card ≤ 1 :=
        (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    hker := fun _ _ => 0
    Ch := 0
    κh := κ0
    hCh := le_rfl
    bound_h := fun _ _ => by simp
    supp_h := fun _ _ _ => rfl
    x_h := fun _ _ _ => rfl
    hκh := le_rfl
    hFm0 := zero_le_one
    ιr := Unit
    nonemptyr := ⟨()⟩
    yr := fun _ => ()
    Gr := fun _ _ _ => 0
    measr := fun _ _ => measurable_const
    depr := fun _ _ _ _ _ => rfl
    Fr := fun _ => 1
    hFr := fun _ => one_pos
    boundr := fun i u Φ => by simp only [norm_zero]; positivity
    holGr := fun _ _ => differentiableOn_const _
    x_r := fun _ => hbx
    hκ0 := le_rfl
    hKc := le_rfl
    hεpos := hεpos
    hκ' := hκ0'
    hκ0' := le_rfl
    hκG := le_rfl
    hκ := le_rfl
    hε := le_rfl
    hF := fun s _ => Filter.Eventually.of_forall fun x => by simp }⟩

end Witness

end Balaban.Fluctuation
