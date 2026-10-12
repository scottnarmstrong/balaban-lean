/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledAlg

/-!
# Periodic boxes are nearest-neighbour connected

The set `{x | InBox m₁ j y₀ R x}` of the cover (the cubes `P`, `C_z`, `□_z`, `□̂_z`) is connected
for the nearest-neighbour adjacency inside the set, as soon as `R ≥ 1`
(`boxSet_connected`): every point is joined to the (lattice) centre of the box by unit steps that
move one coordinate towards the centre.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- The box as a finite set. -/
noncomputable def boxSet (m₁ j : ℕ) (y0 : CTorus d L N₁ m₁ K) (R : ℝ) :
    Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => InBox m₁ j y0 R x

theorem mem_boxSet {j : ℕ} {y0 x : CTorus d L N₁ m₁ K} {R : ℝ} :
    x ∈ boxSet m₁ j y0 R ↔ InBox m₁ j y0 R x := by
  classical
  simp [boxSet]

/-- The centre of the box in coordinate `μ`. -/
noncomputable def boxCtr (L m₁ j : ℕ) (y0 : CTorus d L N₁ m₁ K) (μ : Fin d) : ℝ :=
  ((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2

theorem exists_lift_of_inBox {j : ℕ} {y0 x : CTorus d L N₁ m₁ K} {R : ℝ}
    (h : InBox m₁ j y0 R x) :
    ∃ X : Fin d → ℤ, (∀ μ, |(X μ : ℝ) - boxCtr L m₁ j y0 μ| < R) ∧
      (intTorus X : CTorus d L N₁ m₁ K) = x := by
  choose p hp using h
  refine ⟨fun μ => ((x μ).val : ℤ) + p μ * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ), fun μ => ?_, ?_⟩
  · have := hp μ
    unfold boxCtr
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    exact this
  · funext μ
    have hN : (((N₁ * L ^ m₁) * L ^ K : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = 0 :=
      ZMod.natCast_self _
    simp only [intTorus_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast, hN, mul_zero,
      add_zero, ZMod.natCast_zmod_val]

theorem inBox_intTorus {j : ℕ} {y0 : CTorus d L N₁ m₁ K} {R : ℝ} {X : Fin d → ℤ}
    (h : ∀ μ, |(X μ : ℝ) - boxCtr L m₁ j y0 μ| < R) :
    InBox m₁ j y0 R (intTorus X : CTorus d L N₁ m₁ K) := by
  intro μ
  refine ⟨X μ / (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ), ?_⟩
  have hv : (((intTorus X : CTorus d L N₁ m₁ K) μ).val : ℤ) =
      X μ % (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) := by
    simp only [intTorus_apply]
    exact ZMod.val_intCast (X μ)
  have hdm := Int.emod_add_mul_ediv (X μ) (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ)
  have hr : (((intTorus X : CTorus d L N₁ m₁ K) μ).val : ℝ) +
      ((X μ / (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) : ℤ) : ℝ) * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) =
      (X μ : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hdm
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
    have hv' : (((intTorus X : CTorus d L N₁ m₁ K) μ).val : ℝ) =
        ((X μ % (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) : ℤ) : ℝ) := by
      rw [← hv]; push_cast; rfl
    rw [hv']
    simpa [mul_comm] using this
  have := h μ
  unfold boxCtr at this
  have e : (((intTorus X : CTorus d L N₁ m₁ K) μ).val : ℝ) +
      ((X μ / (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) : ℤ) : ℝ) * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) =
      (X μ : ℝ) - (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) := by rw [hr]
  rw [e]
  exact this

/-- A nearest-neighbour step inside the finite set `S`. -/
def stepIn (S : Finset (CTorus d L N₁ m₁ K)) (a b : CTorus d L N₁ m₁ K) : Prop :=
  a ∈ S ∧ b ∈ S ∧ Adj a b

omit [NeZero N₁] [NeZero L] in
theorem stepIn_symm (S : Finset (CTorus d L N₁ m₁ K)) {a b : CTorus d L N₁ m₁ K}
    (h : stepIn S a b) : stepIn S b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- **Boxes are nearest-neighbour connected** (`R ≥ 1`). -/
theorem boxSet_connected {j : ℕ} (y0 : CTorus d L N₁ m₁ K) {R : ℝ} (hR : 1 ≤ R) :
    ∀ x ∈ boxSet m₁ j y0 R, ∀ y ∈ boxSet m₁ j y0 R,
      Relation.ReflTransGen (stepIn (boxSet m₁ j y0 R)) x y := by
  classical
  set S := boxSet m₁ j y0 R with hS
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hB1 : 1 ≤ L ^ (j + m₁) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  -- the integer centre
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, 2 * m ≤ L ^ (j + m₁) - 1 ∧ L ^ (j + m₁) - 1 < 2 * m + 2 :=
    ⟨(L ^ (j + m₁) - 1) / 2, by omega, by omega⟩
  set T : Fin d → ℤ := fun μ => ((y0 μ).val : ℤ) + (m : ℤ) with hT
  have hTc : ∀ μ, |(T μ : ℝ) - boxCtr L m₁ j y0 μ| < R := by
    intro μ
    have h2 : ((2 * m : ℕ) : ℝ) ≤ ((L ^ (j + m₁) - 1 : ℕ) : ℝ) := by exact_mod_cast hm1
    have h3 : ((L ^ (j + m₁) - 1 : ℕ) : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by exact_mod_cast hm2
    have h4 : ((L ^ (j + m₁) - 1 : ℕ) : ℝ) = (L : ℝ) ^ (j + m₁) - 1 := by
      rw [Nat.cast_sub hB1]; push_cast; ring
    rw [h4] at h2 h3
    push_cast at h2 h3
    unfold boxCtr
    simp only [hT, Int.cast_add, Int.cast_natCast]
    rw [abs_lt]
    constructor <;> nlinarith
  have hmem : ∀ X : Fin d → ℤ, (∀ μ, |(X μ : ℝ) - boxCtr L m₁ j y0 μ| < R) →
      (intTorus X : CTorus d L N₁ m₁ K) ∈ S := fun X hX => mem_boxSet.2 (inBox_intTorus hX)
  have claim : ∀ n : ℕ, ∀ X : Fin d → ℤ, (∀ μ, |(X μ : ℝ) - boxCtr L m₁ j y0 μ| < R) →
      ∑ μ, (X μ - T μ).natAbs = n →
      Relation.ReflTransGen (stepIn S) (intTorus X : CTorus d L N₁ m₁ K) (intTorus T) := by
    intro n
    induction n with
    | zero =>
      intro X hX hs
      have : X = T := by
        funext μ
        have := (Finset.sum_eq_zero_iff.1 hs) μ (Finset.mem_univ μ)
        omega
      rw [this]
    | succ n ih =>
      intro X hX hs
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ μ, (X μ - T μ).natAbs ≠ 0)
      have hne : X μ ≠ T μ := by omega
      have hstep : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) →
          (X μ + δ - T μ).natAbs + 1 = (X μ - T μ).natAbs →
          |((X μ + δ : ℤ) : ℝ) - boxCtr L m₁ j y0 μ| < R →
          Relation.ReflTransGen (stepIn S) (intTorus X : CTorus d L N₁ m₁ K) (intTorus T) := by
        intro δ hδ hlen hbd
        set X' : Fin d → ℤ := X + Pi.single μ δ with hX'
        have hX'μ : X' μ = X μ + δ := by simp [hX']
        have hX'ν : ∀ ν, ν ≠ μ → X' ν = X ν := fun ν hν => by simp [hX', hν]
        have hbd' : ∀ ν, |(X' ν : ℝ) - boxCtr L m₁ j y0 ν| < R := by
          intro ν
          by_cases hν : ν = μ
          · subst hν; rw [hX'μ]; exact hbd
          · rw [hX'ν ν hν]; exact hX ν
        have hsum : ∑ ν, (X' ν - T ν).natAbs = n := by
          have e1 := Finset.sum_erase_add Finset.univ (fun ν => (X ν - T ν).natAbs) (Finset.mem_univ μ)
          have e2 := Finset.sum_erase_add Finset.univ (fun ν => (X' ν - T ν).natAbs) (Finset.mem_univ μ)
          have e3 : ∑ ν ∈ Finset.univ.erase μ, (X' ν - T ν).natAbs =
              ∑ ν ∈ Finset.univ.erase μ, (X ν - T ν).natAbs :=
            Finset.sum_congr rfl fun ν hν => by rw [hX'ν ν (Finset.ne_of_mem_erase hν)]
          rw [hX'μ] at e2
          omega
        have hrest := ih X' hbd' hsum
        refine Relation.ReflTransGen.head ?_ hrest
        refine ⟨hmem X hX, hmem X' hbd', ?_⟩
        rcases hδ with rfl | rfl
        · refine ⟨μ, Or.inl ?_⟩
          rw [hX', ← intTorus_add_aux]
          congr 1
          simp [intTorus_single_aux]
        · refine ⟨μ, Or.inr ?_⟩
          rw [hX', ← intTorus_add_aux]
          have : (intTorus (Pi.single μ (-1 : ℤ)) : CTorus d L N₁ m₁ K) = -Pi.single μ 1 := by
            funext ν
            by_cases hν : ν = μ <;> simp [intTorus_apply, hν]
          rw [add_assoc, this, neg_add_cancel, add_zero]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine hstep 1 (Or.inl rfl) (by omega) ?_
        have h1 := hX μ
        have h2 := hTc μ
        rw [abs_lt] at h1 h2 ⊢
        have hlt' : (X μ : ℝ) + 1 ≤ T μ := by exact_mod_cast (by omega : X μ + 1 ≤ T μ)
        push_cast
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · refine hstep (-1) (Or.inr rfl) (by omega) ?_
        have h1 := hX μ
        have h2 := hTc μ
        rw [abs_lt] at h1 h2 ⊢
        have hgt' : (T μ : ℝ) + 1 ≤ X μ := by exact_mod_cast (by omega : T μ + 1 ≤ X μ)
        push_cast
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  intro x hx y hy
  obtain ⟨X, hX, rfl⟩ := exists_lift_of_inBox (mem_boxSet.1 hx)
  obtain ⟨Y, hY, rfl⟩ := exists_lift_of_inBox (mem_boxSet.1 hy)
  have hx' := claim _ X hX rfl
  have hy' := claim _ Y hY rfl
  have : Std.Symm (stepIn S) := ⟨fun _ _ h => stepIn_symm S h⟩
  exact hx'.trans (Std.Symm.symm _ _ hy')

end Balaban.Localization
