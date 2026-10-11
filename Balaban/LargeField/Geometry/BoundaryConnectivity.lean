module

public import Balaban.LargeField.Geometry.Plaquette
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Boundary connectivity: the plaquette core of Timár's lemma

For a set `S ⊂ ℤ^d` such that both `S` and its complement are nn-connected, the outer vertex
boundary `outerBoundary S = {y ∉ S | y nn-adjacent to S}` is connected through plaquettes
(`MateConn`), hence `*`-connected (`StarConn`).

Proof (Timár, Proc. AMS 141 (2013), Lemma 2, in its cohomological form). If the boundary split into
two nonempty sets `P`, `Q` with no plaquette joining them, the indicator `f` of the edges between
`S` and `P` would be a closed `ZMod 2`-cochain (every plaquette meets the boundary on one side
only), hence exact (`exists_primitive_of_closed`), `f = δh`; but `h` is constant on the connected
sets `S` and `Sᶜ`, while it jumps across the `S`–`P` edges and not across the `S`–`Q` edges.
-/

@[expose] public section

namespace Balaban.LatticeGeom

open Function

variable {d : ℕ}

/-- The four corners of the plaquette at `z` in the directions `i`, `j`. -/
def corners (z : Pt d) (i j : Fin d) : Set (Pt d) :=
  {z, z + Pi.single i 1, z + Pi.single j 1, z + Pi.single i 1 + Pi.single j 1}

/-- Two sites are plaquette mates if they are corners of one plaquette. -/
def Mate (x y : Pt d) : Prop :=
  ∃ z i j, i ≠ j ∧ x ∈ corners z i j ∧ y ∈ corners z i j

/-- The outer vertex boundary of `S`: sites outside `S` nn-adjacent to `S`. -/
def outerBoundary (S : Set (Pt d)) : Set (Pt d) := {y | y ∉ S ∧ ∃ a ∈ S, NN a y}

/-- Connectivity inside `T` along `*`-steps. -/
def StarConn (T : Set (Pt d)) : Pt d → Pt d → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ StarNear a b)

/-- Connectivity inside `T` along plaquette-mate steps. -/
def MateConn (T : Set (Pt d)) : Pt d → Pt d → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ T ∧ b ∈ T ∧ Mate a b)

theorem Mate.starNear {x y : Pt d} (h : Mate x y) : StarNear x y := by
  obtain ⟨z, i, j, hij, hx, hy⟩ := h
  simp only [corners, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  intro k
  by_cases hki : k = i
  · subst hki
    have : k ≠ j := hij
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [this]
  · by_cases hkj : k = j
    · subst hkj
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [hki]
    · rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [hki, hkj]

theorem MateConn.starConn {T : Set (Pt d)} {x y : Pt d} (h : MateConn T x y) : StarConn T x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact ih.tail ⟨hab.1, hab.2.1, hab.2.2.starNear⟩

/-- The indicator of the `S`–`P` edges, as a `ZMod 2` value. -/
noncomputable def edgeInd (S P : Set (Pt d)) (u v : Pt d) : ZMod 2 :=
  open Classical in if (u ∈ S ∧ v ∈ P) ∨ (u ∈ P ∧ v ∈ S) then 1 else 0

theorem edgeInd_comm (S P : Set (Pt d)) (u v : Pt d) : edgeInd S P u v = edgeInd S P v u := by
  unfold edgeInd
  congr 1
  apply propext
  tauto

private theorem z2_tele (a b c e : ZMod 2) : a + b + (b + e) = a + c + (c + e) := by
  revert a b c e; decide

theorem NN_add_single (x : Pt d) (i : Fin d) : NN x (x + Pi.single i 1) := ⟨i, Or.inl rfl⟩


section Core

variable {S P : Set (Pt d)}

/-- On a plaquette none of whose corners lies in `Q`, the `S`–`P` edge indicator is the
coboundary of the indicator of `S`. -/
private theorem edgeInd_eq_of_noQ (hP : P ⊆ outerBoundary S) {u v : Pt d} (huv : NN u v)
    (hu : u ∈ outerBoundary S → u ∈ P) (hv : v ∈ outerBoundary S → v ∈ P) :
    edgeInd S P u v = (open Classical in if u ∈ S then (1 : ZMod 2) else 0)
      + (open Classical in if v ∈ S then (1 : ZMod 2) else 0) := by
  classical
  have hPS : ∀ w ∈ P, w ∉ S := fun w hw => (hP hw).1
  unfold edgeInd
  by_cases huS : u ∈ S
  · by_cases hvS : v ∈ S
    · have : ¬ ((u ∈ S ∧ v ∈ P) ∨ (u ∈ P ∧ v ∈ S)) := by
        rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact hPS _ h hvS
        · exact hPS _ h huS
      have h1 : v ∉ P := fun h => hPS _ h hvS
      have h2 : u ∉ P := fun h => hPS _ h huS
      simp [huS, hvS, h1, h2, CharTwo.add_self_eq_zero]
    · have hvP : v ∈ P := by
        exact hv ⟨hvS, u, huS, huv⟩
      simp [huS, hvS, hvP]
  · by_cases hvS : v ∈ S
    · have huP : u ∈ P := by
        exact hu ⟨huS, v, hvS, huv.symm⟩
      simp [huS, hvS, huP]
    · have : ¬ ((u ∈ S ∧ v ∈ P) ∨ (u ∈ P ∧ v ∈ S)) := by
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact huS h
        · exact hvS h
      simp [huS, hvS]

private theorem edgeInd_eq_zero {u v : Pt d} (hu : u ∉ P) (hv : v ∉ P) : edgeInd S P u v = 0 := by
  unfold edgeInd
  have : ¬ ((u ∈ S ∧ v ∈ P) ∨ (u ∈ P ∧ v ∈ S)) := by
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact hv h
    · exact hu h
  simp [this]

/-- The edge indicator is closed on every plaquette. -/
theorem edgeInd_closed (hP : P ⊆ outerBoundary S)
    (hmate : ∀ x ∈ P, ∀ y ∈ outerBoundary S, Mate x y → y ∈ P)
    (x : Pt d) (i j : Fin d) (hij : i ≠ j) :
    edgeInd S P x (x + Pi.single i 1) + edgeInd S P (x + Pi.single i 1) (x + Pi.single i 1 + Pi.single j 1)
      = edgeInd S P x (x + Pi.single j 1) + edgeInd S P (x + Pi.single j 1) (x + Pi.single j 1 + Pi.single i 1) := by
  have e2 : x + Pi.single j 1 + Pi.single i 1 = x + Pi.single i 1 + Pi.single j 1 := by abel
  rw [e2]
  have hc1 : x ∈ corners x i j := by simp [corners]
  have hc2 : x + Pi.single i 1 ∈ corners x i j := by simp [corners]
  have hc3 : x + Pi.single j 1 ∈ corners x i j := by simp [corners]
  have hc4 : x + Pi.single i 1 + Pi.single j 1 ∈ corners x i j := by simp [corners]
  have n12 : NN x (x + Pi.single i 1) := NN_add_single x i
  have n23 : NN (x + Pi.single i 1) (x + Pi.single i 1 + Pi.single j 1) := NN_add_single _ j
  have n14 : NN x (x + Pi.single j 1) := NN_add_single x j
  have n43 : NN (x + Pi.single j 1) (x + Pi.single i 1 + Pi.single j 1) := by
    rw [← e2]; exact NN_add_single _ i
  by_cases hQ : ∃ v ∈ corners x i j, v ∈ outerBoundary S ∧ v ∉ P
  · obtain ⟨v, hv, hvb, hvP⟩ := hQ
    have hnP : ∀ u ∈ corners x i j, u ∉ P := fun u hu huP =>
      hvP (hmate u huP v hvb ⟨x, i, j, hij, hu, hv⟩)
    rw [edgeInd_eq_zero (hnP _ hc1) (hnP _ hc2), edgeInd_eq_zero (hnP _ hc2) (hnP _ hc4),
      edgeInd_eq_zero (hnP _ hc1) (hnP _ hc3), edgeInd_eq_zero (hnP _ hc3) (hnP _ hc4)]
  · have hQ' : ∀ v ∈ corners x i j, v ∈ outerBoundary S → v ∈ P := fun v hv hvb =>
      Classical.byContradiction fun hvP => hQ ⟨v, hv, hvb, hvP⟩
    have h12 := edgeInd_eq_of_noQ hP n12 (hQ' _ hc1) (hQ' _ hc2)
    have h23 := edgeInd_eq_of_noQ hP n23 (hQ' _ hc2) (hQ' _ hc4)
    have h14 := edgeInd_eq_of_noQ hP n14 (hQ' _ hc1) (hQ' _ hc3)
    have h43 := edgeInd_eq_of_noQ hP n43 (hQ' _ hc3) (hQ' _ hc4)
    rw [h12, h23, h14, h43]
    exact z2_tele _ _ _ _

/-- Core dichotomy: if `S` and `Sᶜ` are nn-connected, a plaquette-closed subset `P` of the outer
boundary is empty or everything. -/
theorem boundary_clopen (hS : ∀ a ∈ S, ∀ b ∈ S, Conn S a b)
    (hSc : ∀ a ∈ Sᶜ, ∀ b ∈ Sᶜ, Conn Sᶜ a b) (hP : P ⊆ outerBoundary S)
    (hmate : ∀ x ∈ P, ∀ y ∈ outerBoundary S, Mate x y → y ∈ P) :
    P = ∅ ∨ P = outerBoundary S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hp⟩ := hcon.1
  obtain ⟨q, hq, hqP⟩ : ∃ q ∈ outerBoundary S, q ∉ P := by
    by_contra hno
    push Not at hno
    exact hcon.2 (Set.Subset.antisymm hP hno)
  obtain ⟨h, hh⟩ := exists_primitive_of_closed
    (fun x i => edgeInd S P x (x + Pi.single i 1))
    (fun x i j hij => edgeInd_closed hP hmate x i j hij)
  -- `h` jumps by `edgeInd` along every nn step
  have hstep : ∀ u v, NN u v → h v = h u + edgeInd S P u v := by
    intro u v ⟨i, huv⟩
    rcases huv with rfl | rfl
    · exact hh u i
    · rw [edgeInd_comm]
      have := hh v i
      rw [this]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hconst : ∀ T : Set (Pt d), (∀ u ∈ T, ∀ v ∈ T, edgeInd S P u v = 0) →
      ∀ a b, Conn T a b → h b = h a := by
    intro T hT a b hab
    induction hab with
    | refl => rfl
    | tail _ hbc ih =>
      rw [hstep _ _ hbc.2.2, hT _ hbc.1 _ hbc.2.1, add_zero, ih]
  have hSzero : ∀ u ∈ S, ∀ v ∈ S, edgeInd S P u v = 0 := fun u hu v hv =>
    edgeInd_eq_zero (fun h' => (hP h').1 hu) (fun h' => (hP h').1 hv)
  have hSczero : ∀ u ∈ Sᶜ, ∀ v ∈ Sᶜ, edgeInd S P u v = 0 := by
    intro u hu v hv
    unfold edgeInd
    have : ¬ ((u ∈ S ∧ v ∈ P) ∨ (u ∈ P ∧ v ∈ S)) := by
      rintro (⟨h', _⟩ | ⟨_, h'⟩)
      · exact hu h'
      · exact hv h'
    simp [this]
  obtain ⟨hpS, a, haS, hap⟩ := hP hp
  obtain ⟨hqS, a', ha'S, ha'q⟩ := hq
  have e1 : h p = h a + 1 := by
    rw [hstep a p hap]
    unfold edgeInd
    simp [haS, hp]
  have e2 : h q = h a' := by
    rw [hstep a' q ha'q]
    unfold edgeInd
    have : ¬ ((a' ∈ S ∧ q ∈ P) ∨ (a' ∈ P ∧ q ∈ S)) := by
      rintro (⟨_, h'⟩ | ⟨h', _⟩)
      · exact hqP h'
      · exact (hP h').1 ha'S
    simp [this]
  have e3 : h a' = h a := hconst S hSzero a a' (hS a haS a' ha'S)
  have e4 : h q = h p := hconst Sᶜ hSczero p q (hSc p hpS q hqS)
  have : (1 : ZMod 2) = 0 := by
    have h5 : h a + 1 = h a := by rw [← e1, ← e4, e2, e3]
    simp at h5
  exact absurd this (by decide)

/-- If `S` and `Sᶜ` are nn-connected, the outer boundary of `S` is connected through plaquettes. -/
theorem outerBoundary_mateConn (hS : ∀ a ∈ S, ∀ b ∈ S, Conn S a b)
    (hSc : ∀ a ∈ Sᶜ, ∀ b ∈ Sᶜ, Conn Sᶜ a b) {x y : Pt d}
    (hx : x ∈ outerBoundary S) (hy : y ∈ outerBoundary S) :
    MateConn (outerBoundary S) x y := by
  let P : Set (Pt d) := {z | z ∈ outerBoundary S ∧ MateConn (outerBoundary S) x z}
  have hPsub : P ⊆ outerBoundary S := fun z hz => hz.1
  have hmate : ∀ u ∈ P, ∀ v ∈ outerBoundary S, Mate u v → v ∈ P := fun u hu v hv hm =>
    ⟨hv, hu.2.tail ⟨hu.1, hv, hm⟩⟩
  rcases boundary_clopen hS hSc hPsub hmate with h | h
  · have : x ∈ P := ⟨hx, Relation.ReflTransGen.refl⟩
    rw [h] at this
    exact absurd this (Set.notMem_empty _)
  · have : y ∈ P := by rw [h]; exact hy
    exact this.2

/-- If `S` and `Sᶜ` are nn-connected, the outer boundary of `S` is `*`-connected. -/
theorem outerBoundary_starConn (hS : ∀ a ∈ S, ∀ b ∈ S, Conn S a b)
    (hSc : ∀ a ∈ Sᶜ, ∀ b ∈ Sᶜ, Conn Sᶜ a b) {x y : Pt d}
    (hx : x ∈ outerBoundary S) (hy : y ∈ outerBoundary S) :
    StarConn (outerBoundary S) x y :=
  (outerBoundary_mateConn hS hSc hx hy).starConn

end Core

end Balaban.LatticeGeom
