module

public import Balaban.LargeField.History.LocalHistory

/-!
# Descent: ancestors indexed by absolute scales (Part I, Definition I.4.2)

`Desc a b Y Z` says that the component `Y` of `Z^pre_a` is an ancestor of the component `Z` of
`Z^pre_b`: the chain of successors of `Y` ends in `Z` and avoids the removed components at the
scales `a, …, b-1`.  It is `AncRel a (b - a)` without the casts `Comp (a + (b - a)) = Comp b`.
`ancFin a b Z` is the finite set of ancestors at scale `a`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- `Y` (scale `a`) is an ancestor of `Z` (scale `b`). -/
inductive Desc (a : ℕ) : (b : ℕ) → H.Comp a → H.Comp b → Prop
  | refl (Y : H.Comp a) : Desc a a Y Y
  | step (b : ℕ) (Y : H.Comp a) (Y' : H.Comp b) (Y'' : H.Comp (b + 1)) :
      Desc a b Y Y' → (h : Y'.1 ∉ H.rem b) → H.succ b Y' h = Y'' → Desc a (b + 1) Y Y''

variable {H}

theorem Desc.le {a b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | step b _ _ _ _ _ _ ih => exact ih.trans (Nat.le_succ b)

theorem Desc.trans {a b c : ℕ} {Y : H.Comp a} {Y' : H.Comp b} {Z : H.Comp c}
    (h1 : H.Desc a b Y Y') (h2 : H.Desc b c Y' Z) : H.Desc a c Y Z := by
  induction h2 with
  | refl => exact h1
  | step c _ Y'' Z'' _ hrem hs ih => exact Desc.step c Y Y'' Z'' (ih h1) hrem hs

theorem Desc.single {b : ℕ} {Y : H.Comp b} {Z : H.Comp (b + 1)} (h : Y.1 ∉ H.rem b)
    (hs : H.succ b Y h = Z) : H.Desc b (b + 1) Y Z :=
  Desc.step b Y Y Z (Desc.refl Y) h hs

theorem Desc.unique {a b : ℕ} {Y : H.Comp a} {Z Z' : H.Comp b} (h : H.Desc a b Y Z)
    (h' : H.Desc a b Y Z') : Z = Z' := by
  induction h with
  | refl => cases h' with
    | refl => rfl
    | step b' _ Y' _ hd _ _ => exact absurd hd.le (by omega)
  | step b _ Y' Y'' hd hrem hs ih =>
    cases h' with
    | refl => exact absurd hd.le (by omega)
    | step _ _ Y3 _ hd3 hrem3 hs3 =>
      have := ih hd3
      subst this
      rw [← hs, ← hs3]

/-- Inversion of the last step. -/
theorem desc_succ_iff {a b : ℕ} (hab : a ≤ b) {Y : H.Comp a} {Z : H.Comp (b + 1)} :
    H.Desc a (b + 1) Y Z ↔ ∃ c ∈ H.parts b Z, H.Desc a b Y c := by
  constructor
  · intro h
    cases h with
    | refl => omega
    | step _ _ Y' _ hd hrem hs => exact ⟨Y', (H.mem_parts b Y' Z).mpr ⟨hrem, hs⟩, hd⟩
  · rintro ⟨c, hc, hd⟩
    obtain ⟨hrem, hs⟩ := (H.mem_parts b c Z).mp hc
    exact Desc.step b Y c Z hd hrem hs

open Classical in
/-- The ancestors at scale `a` of a component of scale `b`. -/
noncomputable def ancFin (a b : ℕ) (Z : H.Comp b) : Finset (H.Comp a) :=
  Finset.univ.filter fun Y => H.Desc a b Y Z

theorem mem_ancFin {a b : ℕ} {Z : H.Comp b} {Y : H.Comp a} :
    Y ∈ H.ancFin a b Z ↔ H.Desc a b Y Z := by
  classical
  simp [ancFin]

theorem ancFin_succ {a b : ℕ} (hab : a ≤ b) (Z : H.Comp (b + 1)) :
    H.ancFin a (b + 1) Z = (H.parts b Z).biUnion fun c => H.ancFin a b c := by
  ext Y
  simp only [mem_ancFin, Finset.mem_biUnion, desc_succ_iff hab]

theorem ancFin_self (a : ℕ) (Z : H.Comp a) : H.ancFin a a Z = {Z} := by
  ext Y
  simp only [mem_ancFin, Finset.mem_singleton]
  constructor
  · intro h
    exact h.unique (Desc.refl Y) ▸ rfl
  · rintro rfl; exact Desc.refl _

theorem ancFin_disjoint {a b : ℕ} {c c' : H.Comp b} (hne : c ≠ c') :
    Disjoint (H.ancFin a b c) (H.ancFin a b c') := by
  rw [Finset.disjoint_left]
  intro Y h h'
  rw [mem_ancFin] at h h'
  exact hne (h.unique h')

/-- The sets of cubes covered by the ancestors at scale `a` of `Z`. -/
noncomputable def lin (a b : ℕ) (Z : H.Comp b) : Finset (Torus S.d (n a)) :=
  (H.ancFin a b Z).biUnion fun Y => Y.1

theorem mem_lin {a b : ℕ} {Z : H.Comp b} {x : Torus S.d (n a)} :
    x ∈ H.lin a b Z ↔ ∃ Y : H.Comp a, H.Desc a b Y Z ∧ x ∈ Y.1 := by
  simp [lin, mem_ancFin]

/-- `AncRel` is `Desc`. -/
theorem AncRel.toDesc {a t : ℕ} {Y : H.Comp a} {Z : H.Comp (a + t)} (h : H.AncRel a t Y Z) :
    H.Desc a (a + t) Y Z := by
  induction h with
  | refl => exact Desc.refl _
  | step t Y Y' Y'' _ hrem hs ih => exact Desc.step (a + t) Y Y' Y'' ih hrem hs

theorem Desc.toAncRel {a b : ℕ} {Y : H.Comp a} {Z : H.Comp b} (h : H.Desc a b Y Z) :
    ∃ t : ℕ, ∃ e : a + t = b, H.AncRel a t Y (e ▸ Z) := by
  induction h with
  | refl => exact ⟨0, rfl, AncRel.refl _ _⟩
  | step b Y Y' Y'' hd hrem hs ih =>
    obtain ⟨t, rfl, hA⟩ := ih
    exact ⟨t + 1, rfl, AncRel.step a t Y Y' Y'' hA hrem hs⟩

end RegionHistory

end Balaban.LargeField
