module

public import Balaban.LargeField.Geometry.BoundaryConnectivity
public import Balaban.LargeField.Geometry.Escape
import Mathlib.Tactic.Linarith

/-!
# Timár's boundary-connectivity lemma in `ℤ^d`

For a finite nn-connected set `A ⊂ ℤ^d`, `d ≥ 2`, the exterior vertex boundary
`exteriorBoundary A = {y ∉ A | y nn-adjacent to A, y joined to infinity in ℤ^d ∖ A}` is
`*`-connected (indeed connected through plaquettes, `exteriorBoundary_mateConn`).

Reference: Á. Timár, *Boundary-connectivity via graph theory*, Proc. AMS 141 (2013) 475–480,
Lemma 2; Lemma I.3.13 (Lemma S) of `notes/phase1/LF-RECONSTRUCTION.md`, open item O-1.

Route: put `S = {y | ¬ JoinedToInf A y}` (`A` with its finite holes filled). Then `S` and `Sᶜ` are
nn-connected (`Sᶜ` because the complement of a large cube is, `conn_shell`), `exteriorBoundary A
= outerBoundary S`, and `outerBoundary_mateConn` (a closed `ZMod 2`-cochain on `ℤ^d` is exact)
applies.
-/

@[expose] public section

namespace Balaban.LatticeGeom

open Function Filter

variable {d : ℕ} {A : Set (Pt d)}

/-- The exterior vertex boundary of `A`. -/
def exteriorBoundary (A : Set (Pt d)) : Set (Pt d) :=
  {y | y ∉ A ∧ (∃ a ∈ A, NN a y) ∧ JoinedToInf A y}

theorem box_mono {R R' : ℤ} (h : R ≤ R') : (box R : Set (Pt d)) ⊆ box R' :=
  fun _ hx i => (hx i).trans h

/-- Filling the finite holes of `A` gives a set whose complement is nn-connected. -/
theorem conn_joined (hd : 2 ≤ d) (hA : A.Finite) {a b : Pt d} (ha : JoinedToInf A a)
    (hb : JoinedToInf A b) : Conn {y | JoinedToInf A y} a b := by
  obtain ⟨R₀, hR₀⟩ := Set.Finite.subset_box hA
  set R := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hAR : A ⊆ box R := hR₀.trans (box_mono (le_max_left _ _))
  have far : ∀ y, JoinedToInf A y → ∃ z ∉ box R, Conn {y | JoinedToInf A y} y z := by
    intro y hy
    obtain ⟨p, hp, hpA⟩ := hy
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.esc _ (box_finite (d := d) R))
    refine ⟨p N, hN N le_rfl, ?_⟩
    have : ∀ n, Conn {y | JoinedToInf A y} y (p n) := by
      intro n
      induction n with
      | zero => rw [hp.zero]; exact Conn.refl _
      | succ n ih =>
        exact ih.tail (JoinedToInf.shift hp hpA (n + 1)) (JoinedToInf.shift hp hpA n) (hp.step n)
    exact this N
  obtain ⟨z, hz, hz'⟩ := far a ha
  obtain ⟨w, hw, hw'⟩ := far b hb
  have hsub : (box R : Set (Pt d))ᶜ ⊆ {y | JoinedToInf A y} := fun y hy =>
    joinedToInf_of_far hAR hy
  exact (hz'.trans ((conn_shell hd hR hz hw).mono hsub)).trans hw'.symm

/-- Filling the finite holes of `A` gives an nn-connected set when `A` is. -/
theorem conn_filled (hd : 2 ≤ d) (hAc : ∀ a ∈ A, ∀ b ∈ A, Conn A a b)
    {a b : Pt d} (ha : ¬ JoinedToInf A a) (hb : ¬ JoinedToInf A b) :
    Conn {y | ¬ JoinedToInf A y} a b := by
  have hAS : A ⊆ {y | ¬ JoinedToInf A y} := fun y hy h => h.not_mem hy
  let i0 : Fin d := ⟨0, by omega⟩
  have toA : ∀ z, ¬ JoinedToInf A z → ∃ a ∈ A, Conn {y | ¬ JoinedToInf A y} z a := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact ⟨z, hzA, Conn.refl _⟩
    · have hex : ∃ n, ray z i0 1 n ∈ A := by
        by_contra h
        push Not at h
        exact hz ⟨ray z i0 1, ray_isEscPath z i0 (Or.inl rfl), h⟩
      classical
      set t := Nat.find hex with ht
      have hmem : ray z i0 1 t ∈ A := Nat.find_spec hex
      have hlt : ∀ k < t, ray z i0 1 k ∉ A := fun k hk => Nat.find_min hex hk
      have hcA : ∀ k < t, Conn Aᶜ z (ray z i0 1 k) := by
        intro k
        induction k with
        | zero => intro _; rw [ray_zero]; exact Conn.refl _
        | succ k ih =>
          intro hk
          exact (ih (by omega)).tail (hlt _ hk) (hlt _ (by omega)) (ray_nn z i0 (Or.inl rfl) k)
      have hS : ∀ k < t, ray z i0 1 k ∈ {y | ¬ JoinedToInf A y} := fun k hk h =>
        hz (JoinedToInf.of_conn (hcA k hk) h)
      have hc : ∀ k ≤ t, Conn {y | ¬ JoinedToInf A y} z (ray z i0 1 k) := by
        intro k
        induction k with
        | zero => intro _; rw [ray_zero]; exact Conn.refl _
        | succ k ih =>
          intro hk
          refine (ih (by omega)).tail ?_ (hS k (by omega)) (ray_nn z i0 (Or.inl rfl) k)
          rcases Nat.lt_or_ge (k + 1) t with h | h
          · exact hS _ h
          · have : k + 1 = t := by omega
            rw [this]; exact hAS hmem
      exact ⟨_, hmem, hc t le_rfl⟩
  obtain ⟨a', ha', hca⟩ := toA a ha
  obtain ⟨b', hb', hcb⟩ := toA b hb
  exact (hca.trans ((hAc a' ha' b' hb').mono hAS)).trans hcb.symm

theorem exteriorBoundary_eq (A : Set (Pt d)) :
    exteriorBoundary A = outerBoundary {y | ¬ JoinedToInf A y} := by
  ext y
  constructor
  · rintro ⟨hyA, ⟨a, haA, hn⟩, hj⟩
    exact ⟨fun h => h hj, a, fun h => h.not_mem haA, hn⟩
  · rintro ⟨hy, a, ha, hn⟩
    have hj : JoinedToInf A y := by simpa using hy
    have haA : a ∈ A := by
      by_contra haA
      exact ha (JoinedToInf.of_conn (Conn.single haA hj.not_mem hn) hj)
    exact ⟨hj.not_mem, ⟨a, haA, hn⟩, hj⟩

/-- **Timár's lemma**: the exterior boundary of a finite nn-connected set in `ℤ^d`, `d ≥ 2`, is
connected through plaquettes. -/
theorem exteriorBoundary_mateConn (hd : 2 ≤ d) (hA : A.Finite)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, Conn A a b) {x y : Pt d} (hx : x ∈ exteriorBoundary A)
    (hy : y ∈ exteriorBoundary A) : MateConn (exteriorBoundary A) x y := by
  rw [exteriorBoundary_eq] at hx hy ⊢
  refine outerBoundary_mateConn (fun a ha b hb => conn_filled hd hAc ha hb)
    (fun a ha b hb => ?_) hx hy
  have : ({y | ¬ JoinedToInf A y} : Set (Pt d))ᶜ = {y | JoinedToInf A y} := by
    ext; simp
  rw [this]
  exact conn_joined hd hA (by simpa using ha) (by simpa using hb)

/-- **Timár's lemma** (Proc. AMS 141 (2013), Lemma 2): the exterior vertex boundary of a finite
nn-connected set `A ⊂ ℤ^d`, `d ≥ 2`, is `*`-connected. -/
theorem exteriorBoundary_starConn (hd : 2 ≤ d) (hA : A.Finite)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, Conn A a b) {x y : Pt d} (hx : x ∈ exteriorBoundary A)
    (hy : y ∈ exteriorBoundary A) : StarConn (exteriorBoundary A) x y :=
  (exteriorBoundary_mateConn hd hA hAc hx hy).starConn

end Balaban.LatticeGeom
