module

public import Balaban.LargeField.Geometry.Small
public import Balaban.LargeField.Geometry.LemmaS
public import Balaban.LargeField.Geometry.DomainsMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lifting a small box of the cube torus to `ℤ^d` (Part I, Lemma I.2.10 (e) and Lemma I.3.13, torus
version)

For a box `Q = box a s` of `𝕋_k` with `2 s_i < n`, `boxLift a : 𝕋_k → ℤ^d` is the injective lift
`y ↦ (a_i.val + pos_{a_i}(y_i))_i`. It maps `Q` onto the integer box `[a.val, a.val + s - 1]`,
preserves the index distance between points of `Q` (so `*`-adjacency and nn-adjacency inside `Q`),
and maps the interior `Q^{∼-1}` onto the interior of the integer box.

This file proves the facts used to transfer the lattice results of
`Balaban.LatticeGeom` (W31: Lemma S) to the torus; the transferred statements are in
`Balaban.LargeField.Geometry.LemmaSTorus`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ} [NeZero n]

/-- The injective lift to `ℤ^d` of a box with base point `a`: coordinatewise
`(a_i).val + pos_{a_i}(y_i)`. -/
def boxLift (a : Torus d n) (y : Torus d n) : LatticeGeom.Pt d :=
  fun i => ((a i).val : ℤ) + pos (a i) (y i)

theorem boxLift_cast (a y : Torus d n) (i : Fin d) : ((boxLift a y i : ℤ) : ZMod n) = y i := by
  simp only [boxLift]
  push_cast
  rw [natCast_pos]; simp

theorem boxLift_injective (a : Torus d n) : Function.Injective (boxLift a) := by
  intro y y' h
  funext i
  rw [← boxLift_cast a y i, ← boxLift_cast a y' i, h]

variable {a : Torus d n} {s : Fin d → ℕ}

theorem mem_box_iff (hs : ∀ i, 2 * s i < n) {y : Torus d n} :
    y ∈ box a s ↔ ∀ i, pos (a i) (y i) < s i :=
  forall_congr' fun i => mem_cycInt_iff (by have := hs i; omega)

theorem boxLift_mem_Icc (hs : ∀ i, 2 * s i < n) {y : Torus d n} (hy : y ∈ box a s) :
    boxLift a y ∈ Set.Icc (fun i => ((a i).val : ℤ)) (fun i => ((a i).val : ℤ) + s i - 1) := by
  have := (mem_box_iff hs).mp hy
  refine ⟨fun i => ?_, fun i => ?_⟩
  · show ((a i).val : ℤ) ≤ ((a i).val : ℤ) + pos (a i) (y i)
    omega
  · have := this i
    show ((a i).val : ℤ) + pos (a i) (y i) ≤ ((a i).val : ℤ) + s i - 1
    omega

/-- Surjectivity: the cast of an integer point of the box is a point of `Q` with that lift. -/
theorem exists_box_of_mem_Icc (hs : ∀ i, 2 * s i < n) {z : LatticeGeom.Pt d}
    (hz : z ∈ Set.Icc (fun i => ((a i).val : ℤ)) (fun i => ((a i).val : ℤ) + s i - 1)) :
    ∃ y ∈ box a s, boxLift a y = z := by
  have hz1 : ∀ i, ((a i).val : ℤ) ≤ z i := hz.1
  have hz2 : ∀ i, z i ≤ ((a i).val : ℤ) + s i - 1 := hz.2
  have hp : ∀ i, pos (a i) ((z i : ℤ) : ZMod n) = (z i - (a i).val).toNat := fun i => by
    have h1 := hz1 i
    have h2 := hz2 i
    have h3 := hs i
    have e : ((z i : ℤ) : ZMod n) = a i + (((z i - (a i).val).toNat : ℕ) : ZMod n) := by
      have : (((z i - (a i).val).toNat : ℕ) : ℤ) = z i - (a i).val := by omega
      have h3 : ((((z i - (a i).val).toNat : ℕ) : ℤ) : ZMod n) = ((z i - (a i).val : ℤ) : ZMod n) := by
        rw [this]
      rw [Int.cast_natCast] at h3
      rw [h3]; push_cast; simp
    rw [e]
    exact pos_add_natCast _ (by have := hs i; omega)
  refine ⟨fun i => ((z i : ℤ) : ZMod n), ?_, ?_⟩
  · rw [mem_box_iff hs]
    intro i
    rw [hp i]
    have := hz1 i; have := hz2 i
    omega
  · funext i
    show ((a i).val : ℤ) + pos (a i) ((z i : ℤ) : ZMod n) = z i
    rw [hp i]
    have := hz1 i
    omega

/-- The lift preserves the index distance between points of the box. -/
theorem supDist_le_iff_boxLift (hs : ∀ i, 2 * s i < n) {y y' : Torus d n} (hy : y ∈ box a s)
    (hy' : y' ∈ box a s) (m : ℕ) :
    supDist y y' ≤ m ↔ ∀ i, |boxLift a y i - boxLift a y' i| ≤ m := by
  rw [supDist_le_iff]
  refine forall_congr' fun i => ?_
  have hd := cycNorm_sub_of_mem (hs i) (a := a i) (y := y i) (y' := y' i)
    (hy i) (hy' i)
  simp only [boxLift, add_sub_add_left_eq_sub]
  rw [← hd]
  exact (Nat.cast_le (α := ℤ)).symm

theorem boxLift_image (hs : ∀ i, 2 * s i < n) :
    boxLift a '' box a s =
      Set.Icc (fun i => ((a i).val : ℤ)) (fun i => ((a i).val : ℤ) + s i - 1) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact boxLift_mem_Icc hs hy
  · intro hz
    obtain ⟨y, hy, rfl⟩ := exists_box_of_mem_Icc hs hz
    exact ⟨y, hy, rfl⟩

theorem starNear_boxLift_iff (hs : ∀ i, 2 * s i < n) {y y' : Torus d n} (hy : y ∈ box a s)
    (hy' : y' ∈ box a s) :
    supDist y y' ≤ 1 ↔ LatticeGeom.StarNear (boxLift a y) (boxLift a y') := by
  rw [supDist_le_iff_boxLift hs hy hy']
  simp [LatticeGeom.StarNear]

theorem nnAdj_boxLift_iff (hs : ∀ i, 2 * s i < n) {y y' : Torus d n} (hy : y ∈ box a s)
    (hy' : y' ∈ box a s) : NNAdj y y' ↔ LatticeGeom.NN (boxLift a y) (boxLift a y') := by
  have hp := (mem_box_iff hs).mp hy
  have hp' := (mem_box_iff hs).mp hy'
  -- one step in the torus lifts to one step in `ℤ^d`
  have fwd : ∀ y y' : Torus d n, y ∈ box a s → y' ∈ box a s → ∀ μ : Fin d,
      y' = y + Pi.single μ 1 → boxLift a y' = boxLift a y + Pi.single μ 1 := by
    intro y y' hy hy' μ h
    have hp := (mem_box_iff hs).mp hy
    have hp' := (mem_box_iff hs).mp hy'
    funext j
    by_cases hj : j = μ
    · subst hj
      have e : ((pos (a j) (y' j) : ℤ) : ZMod n) = (((pos (a j) (y j) : ℤ) + 1 : ℤ) : ZMod n) := by
        push_cast; rw [natCast_pos, natCast_pos, h]; simp; ring
      have := int_eq_of_cast_eq e (by
        have := hp j; have := hp' j; have := hs j
        rw [abs_lt]; constructor <;> omega)
      simp only [boxLift, Pi.add_apply, Pi.single_eq_same]
      omega
    · have : y' j = y j := by rw [h]; simp [hj]
      simp [boxLift, this, hj]
  have back : ∀ y y' : Torus d n, ∀ μ : Fin d,
      boxLift a y' = boxLift a y + Pi.single μ 1 → y' = y + Pi.single μ 1 := by
    intro y y' μ h
    funext j
    rw [← boxLift_cast a y' j, h]
    simp only [Pi.add_apply]
    push_cast
    rw [boxLift_cast]
    by_cases hj : j = μ
    · subst hj; simp
    · simp [hj]
  constructor
  · rintro ⟨μ, h | h⟩
    · exact ⟨μ, Or.inl (fwd y y' hy hy' μ h)⟩
    · exact ⟨μ, Or.inr (fwd y' y hy' hy μ h)⟩
  · rintro ⟨μ, h | h⟩
    · exact ⟨μ, Or.inl (back y y' μ h)⟩
    · exact ⟨μ, Or.inr (back y' y μ h)⟩

end Balaban.LargeField
