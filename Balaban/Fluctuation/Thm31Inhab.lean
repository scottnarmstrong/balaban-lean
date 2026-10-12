/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31cde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1: non-vacuity of the typing structures

`SiteConnected` of the whole torus, the label set `{𝕋}`, and `ProdSplit` of a product measure.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

section Conn

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
theorem reach_single (x : Torus d n) (μ : Fin d) (c : ℕ) :
    Relation.ReflTransGen (fun u v : Torus d n => u ∈ Set.univ ∧ v ∈ Set.univ ∧ Nbr u v) x
      (x + Pi.single μ (c : ZMod n)) := by
  induction c with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ c ih =>
    refine ih.tail ⟨trivial, trivial, μ, Or.inl ?_⟩
    ext ν
    by_cases h : ν = μ
    · subst h; simp; ring
    · simp [h]

theorem reach_sum (x : Torus d n) (v : Fin d → ZMod n) (T : Finset (Fin d)) :
    Relation.ReflTransGen (fun u v : Torus d n => u ∈ Set.univ ∧ v ∈ Set.univ ∧ Nbr u v) x
      (x + ∑ μ ∈ T, Pi.single μ (v μ)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := reach_single (x + ∑ μ ∈ T, Pi.single μ (v μ)) a (v a).val
    rw [ZMod.natCast_zmod_val] at h1
    have e : x + (Pi.single a (v a) + ∑ μ ∈ T, Pi.single μ (v μ)) =
        x + ∑ μ ∈ T, Pi.single μ (v μ) + Pi.single a (v a) := by abel
    rw [e]
    exact ih.trans h1

end Conn

theorem siteConnected_univ {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] :
    SiteConnected (Set.univ : Set (CTorus d L N₁ m₁ K)) := by
  have : NeZero (N₁ * L ^ m₁ * L ^ K) :=
    ⟨Nat.pos_iff_ne_zero.1 (by have := NeZero.pos N₁; have := NeZero.pos L; positivity)⟩
  intro x _ y _
  have := reach_sum (n := N₁ * L ^ m₁ * L ^ K) x (y - x) Finset.univ
  rw [Finset.univ_sum_single] at this
  simpa using this

section Witness

variable (d L N₁ m₁ K : ℕ) [NeZero N₁] [NeZero L]

theorem isDj_univ (m₀ j : ℕ) :
    IsDj m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) := by
  refine ⟨?_, ?_, siteConnected_univ⟩
  · exact Set.univ_nonempty
  · intro z _
    refine ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, ?_, Set.subset_univ _⟩
    refine box_mono _ ?_ (mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z)
    have : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    nlinarith [cellSide_pos (L := L) m₀ m₁ j]

/-- **`ProdSplit` is inhabited**: a product measure is the product of its blocks. -/
theorem nonempty_prodSplit (m₀ : ℕ) :
    ∃ (ν : Measure (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ →
        Unit)), Nonempty (ProdSplit ν d L N₁ m₁ K m₀) := by
  refine ⟨Measure.pi fun _ => Measure.dirac (), ⟨{
    Ωb := fun _ => Unit
    μ := fun _ => Measure.dirac ()
    restr := id
    meas := measurable_id
    map_eq := Measure.map_id }⟩⟩

open Classical in
/-- **`InterpMarks` is inhabited** (zero interaction, zero marks, the label `{𝕋}`; all numerical
hypotheses of Theorem 3.4 hold for the admissible constants `κ₀ = a_ent + 1`, `K_c = K₀ + 1`,
`κ' = 0`). -/
theorem nonempty_interpMarks :
    ∃ (ν : Measure (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ → Unit))
      (BS : ProdSplit ν d L N₁ m₁ K 0) (W f : ℝ → _ → ℂ), Nonempty (InterpMarks ν BS W f) := by
  obtain ⟨ν, ⟨BS⟩⟩ := nonempty_prodSplit d L N₁ m₁ K 0
  refine ⟨ν, BS, fun _ _ => 0, fun _ _ => 0, ?_⟩
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hc1 := one_le_c1 d L
  set κ0 := aEnt d L + 1 with hκ0
  set Kc := K0 d L κ0 + 1 with hKc
  have hKc1 : 1 ≤ Kc := by linarith
  have hκ0' : 0 ≤ κ0 := by linarith [aEnt_nonneg d L]
  set κH := 3 * κ0 + c1 d L + 3 / 2 with hκH
  set εH := 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + 0 * cG d L)) with hεH
  have hεpos : 0 < εH := by positivity
  let Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ Unit :=
    { ysite := fun _ => Set.univ
      dl := fun _ => treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K Set.univ
      isDj := fun _ => isDj_univ d L N₁ m₁ K 0 K
      meets := fun _ => by simp
      size := fun _ => Or.inl rfl }
  let A : ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc := fun _ =>
    { H := fun _ _ => 0
      meas := fun _ => measurable_const
      dep := fun _ _ _ _ => rfl
      bound := fun y Φ => by
        simp only [norm_zero]; positivity
      entropy := fun b => by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        split_ifs
        · have h0 : 0 ≤ treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 0 K
              Set.univ := treeLenCovOne_nonneg _ _ _
          have : Real.exp (-κ0 * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
              0 K Set.univ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          linarith
        · linarith }
  exact ⟨{
    Lb := Unit
    Lab := Lab
    ι := Unit
    nonempty := ⟨()⟩
    εH := εH
    κH := κH
    κG := κH
    κ0 := κ0
    κ' := 0
    Kc := Kc
    F0 := fun _ => 1
    hN := by simp
    𝒰 := Set.univ
    isOpen := isOpen_univ
    seg := fun _ _ => trivial
    A := A
    y0 := fun _ => ()
    G := fun _ _ _ => 0
    meas := fun _ _ => measurable_const
    dep := fun _ _ _ _ _ => rfl
    bound := fun i u Φ => by simp only [norm_zero]; positivity
    holA := fun _ _ => differentiableOn_const _
    holG := fun _ _ => differentiableOn_const _
    hκ0 := le_rfl
    hKc := le_rfl
    hεpos := hεpos
    hF0 := fun _ => one_pos
    hκ' := le_rfl
    hκG := le_rfl
    hκ := by rw [hκH]; linarith
    hε := le_rfl
    hW := fun s _ => Filter.Eventually.of_forall fun x => by simp [A]
    hF := fun s _ => Filter.Eventually.of_forall fun x => by simp }⟩

end Witness

end Balaban.Fluctuation
