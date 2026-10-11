module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The lattice `ℤ^d`: nearest-neighbour paths and connectivity

Basic vocabulary for the discrete geometry of Lemma I.3.13 (Lemma S) of
`notes/phase1/LF-RECONSTRUCTION.md`: sites `Pt d = Fin d → ℤ`, nearest-neighbour (nn) adjacency
`NN`, `*`-adjacency `StarNear` (sup-distance `≤ 1`), connectivity inside a set along nn steps
(`Conn`), and the moving-one-coordinate lemma `Conn.update`.
-/

@[expose] public section

namespace Balaban.LatticeGeom

/-- Sites of `ℤ^d`. -/
abbrev Pt (d : ℕ) := Fin d → ℤ

variable {d : ℕ}

/-- Nearest-neighbour adjacency: the sites differ by a unit vector. -/
def NN (x y : Pt d) : Prop := ∃ i, y = x + Pi.single i 1 ∨ x = y + Pi.single i 1

/-- `*`-adjacency (and equality): sup-distance at most `1`. -/
def StarNear (x y : Pt d) : Prop := ∀ i, |x i - y i| ≤ 1

theorem NN.symm {x y : Pt d} (h : NN x y) : NN y x := by
  obtain ⟨i, h | h⟩ := h
  · exact ⟨i, Or.inr h⟩
  · exact ⟨i, Or.inl h⟩

theorem NN.starNear {x y : Pt d} (h : NN x y) : StarNear x y := by
  obtain ⟨i, h | h⟩ := h <;> intro k <;> subst h <;> by_cases hk : k = i <;> simp [hk]

theorem StarNear.symm {x y : Pt d} (h : StarNear x y) : StarNear y x := by
  intro i; rw [abs_sub_comm]; exact h i

/-- Connectivity of two sites inside `S` along nn steps. -/
def Conn (S : Set (Pt d)) : Pt d → Pt d → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ NN a b)

namespace Conn

variable {S T : Set (Pt d)} {x y z : Pt d}

theorem refl (x : Pt d) : Conn S x x := Relation.ReflTransGen.refl

theorem trans (h₁ : Conn S x y) (h₂ : Conn S y z) : Conn S x z := Relation.ReflTransGen.trans h₁ h₂

theorem single (hx : x ∈ S) (hy : y ∈ S) (h : NN x y) : Conn S x y :=
  Relation.ReflTransGen.single ⟨hx, hy, h⟩

theorem tail (h : Conn S x y) (hz : z ∈ S) (hy : y ∈ S) (hn : NN y z) : Conn S x z :=
  Relation.ReflTransGen.tail h ⟨hy, hz, hn⟩

theorem symm (h : Conn S x y) : Conn S y x := by
  induction h with
  | refl => exact Conn.refl _
  | tail _ hab ih => exact (Conn.single hab.2.1 hab.1 hab.2.2.symm).trans ih

theorem mono (hST : S ⊆ T) (h : Conn S x y) : Conn T x y := by
  induction h with
  | refl => exact Conn.refl _
  | tail _ hab ih => exact ih.tail (hST hab.2.1) (hST hab.1) hab.2.2

/-- A connection between distinct sites stays in the set. -/
theorem mem_left (h : Conn S x y) (hne : x ≠ y) : x ∈ S := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨hx, _, _⟩, _⟩
  · exact absurd h hne
  · exact hx

theorem mem_right (h : Conn S x y) (hne : x ≠ y) : y ∈ S := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, ⟨_, hy, _⟩⟩
  · exact absurd h.symm hne
  · exact hy

private theorem update_up (S : Set (Pt d)) (j : Fin d) :
    ∀ (k : ℕ) (x : Pt d), (∀ t : ℤ, x j ≤ t → t ≤ x j + k → Function.update x j t ∈ S) →
      Conn S x (Function.update x j (x j + k)) := by
  intro k
  induction k with
  | zero =>
    intro x _
    simp [Conn.refl]
  | succ k ih =>
    intro x hx
    have h1 : Conn S x (Function.update x j (x j + k)) :=
      ih x (fun t h1 h2 => hx t h1 (by push_cast; linarith))
    refine h1.tail ?_ ?_ ⟨j, Or.inl ?_⟩
    · exact hx _ (by push_cast; linarith) (by push_cast; linarith)
    · exact hx _ (by linarith) (by push_cast; linarith)
    · ext l
      by_cases hl : l = j
      · subst hl; simp; ring
      · simp [Function.update, hl]

/-- Moving one coordinate of `x` to `b` along a straight segment inside `S`. -/
theorem update (j : Fin d) (b : ℤ) (x : Pt d)
    (h : ∀ t ∈ Set.uIcc (x j) b, Function.update x j t ∈ S) :
    Conn S x (Function.update x j b) := by
  rcases le_total (x j) b with hb | hb
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hb)
    have hb' : b = x j + k := by omega
    subst hb'
    exact update_up S j k x (fun t h1 h2 => h t (Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)))
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hb)
    have hb' : x j = b + k := by omega
    have hx' : Function.update x j (b + k) = x := by rw [← hb']; simp
    have := update_up S j k (Function.update x j b) (by
      intro t h1 h2
      simp only [Function.update_self] at h1 h2
      have : Function.update (Function.update x j b) j t = Function.update x j t := by simp
      rw [this]
      exact h t (Set.mem_uIcc.mpr (Or.inr ⟨h1, by linarith⟩)))
    simp only [Function.update_self, Function.update_idem] at this
    rw [hx'] at this
    exact this.symm

end Conn

end Balaban.LatticeGeom
