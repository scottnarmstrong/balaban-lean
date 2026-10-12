module

public import Balaban.LargeField.Geometry.LemmaSTorus
public import Balaban.LargeField.Geometry.Continuous
import Mathlib.Tactic.Linarith

/-!
# Paths on the torus (Part III, Lemma III.4.3, geometric core)

* `exists_first_hit`: an nearest-neighbour chain from `x ∉ E` to a point of `E` inside `S₀`
  contains a path whose only point in `E` is the last one;
* `fine_box_margin`: a point of a cyclic interval and its neighbours lie in the interval extended by
  one site on each side;
* `exists_shell_path_of_small_components`: if the obstacle `⋃ A_j` is a union of pairwise
  `*`-separated pieces of sup-diameter less than the side `t` of a box `Q' ∋ x`, then `x` is joined to
  the boundary of `Q` by a nn path avoiding the obstacle (Lemma S (a), (b) on the torus).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section FirstHit

variable {d N : ℕ}

/-- A chain from `x ∉ E` to a point of `E` in `S₀` contains a path whose last point is its only
point in `E`. -/
theorem exists_first_hit {S₀ E : Set (Torus d N)} {x z : Torus d N} (hx : x ∉ E) (hxS : x ∈ S₀)
    (h : TConn S₀ x z) (hz : z ∈ E) :
    ∃ (M : ℕ) (p : ℕ → Torus d N), 0 < M ∧ p 0 = x ∧ (∀ m < M, NNAdj (p m) (p (m + 1))) ∧
      (∀ m < M, p m ∈ S₀ ∧ p m ∉ E) ∧ p M ∈ E ∧ p M ∈ S₀ := by
  classical
  have key : ∀ w, TConn S₀ x w →
      (∃ (M : ℕ) (p : ℕ → Torus d N), 0 < M ∧ p 0 = x ∧ (∀ m < M, NNAdj (p m) (p (m + 1))) ∧
        (∀ m < M, p m ∈ S₀ ∧ p m ∉ E) ∧ p M ∈ E ∧ p M ∈ S₀) ∨
      (∃ (M : ℕ) (p : ℕ → Torus d N), p 0 = x ∧ (∀ m < M, NNAdj (p m) (p (m + 1))) ∧
        (∀ m ≤ M, p m ∈ S₀ ∧ p m ∉ E) ∧ p M = w) := by
    intro w hw
    induction hw with
    | refl => exact Or.inr ⟨0, fun _ => x, rfl, by simp, by simpa [hxS] using hx, rfl⟩
    | @tail b c _ hbc ih =>
      rcases ih with hit | ⟨M, p, h0, hadj, hmem, hpb⟩
      · exact Or.inl hit
      · by_cases hcE : c ∈ E
        · refine Or.inl ⟨M + 1, fun m => if m ≤ M then p m else c, by omega, by simpa using h0, ?_,
            ?_, ?_, ?_⟩
          · intro m hm
            by_cases hmM : m < M
            · simp only [hmM.le, show m + 1 ≤ M by omega, ite_true]
              exact hadj m hmM
            · have : m = M := by omega
              subst this
              simp only [le_refl, ite_true, show ¬ (m + 1 ≤ m) by omega, ite_false]
              rw [hpb]; exact hbc.2.2
          · intro m hm
            have : m ≤ M := by omega
            simpa [this] using hmem m this
          · simp [show ¬ (M + 1 ≤ M) by omega, hcE]
          · simpa [show ¬ (M + 1 ≤ M) by omega] using hbc.2.1
        · refine Or.inr ⟨M + 1, fun m => if m ≤ M then p m else c, by simpa using h0, ?_, ?_, ?_⟩
          · intro m hm
            by_cases hmM : m < M
            · simp only [hmM.le, show m + 1 ≤ M by omega, ite_true]
              exact hadj m hmM
            · have : m = M := by omega
              subst this
              simp only [le_refl, ite_true, show ¬ (m + 1 ≤ m) by omega, ite_false]
              rw [hpb]; exact hbc.2.2
          · intro m hm
            by_cases hmM : m ≤ M
            · simpa [hmM] using hmem m hmM
            · have : m = M + 1 := by omega
              subst this
              simpa [show ¬ (M + 1 ≤ M) by omega, hcE] using hbc.2.1
          · simp
  rcases key z h with hit | ⟨M, p, -, -, hmem, hpz⟩
  · exact hit
  · exact absurd (hpz ▸ hz) (hmem M le_rfl).2

end FirstHit

section Margin

variable {N : ℕ} [NeZero N]

/-- A neighbour (within cyclic distance `1`) of a point of a cyclic interval lies in the interval
enlarged by one site on each side. -/
theorem mem_cycInt_margin {c y z : ZMod N} {s : ℕ} (hy : y ∈ cycInt c s)
    (h : cycNorm N (y - z) ≤ 1) : z ∈ cycInt (c - 1) (s + 2) := by
  obtain ⟨j, hj, rfl⟩ := hy
  obtain ⟨t, ht, htc⟩ := (cycNorm_le_iff _ _).mp h
  have ht' : -1 ≤ t ∧ t ≤ 1 := by
    have := abs_le.mp ht
    constructor <;> push_cast at this <;> omega
  refine ⟨(j + 1 - t).toNat, ?_, ?_⟩
  · omega
  · have hnn : 0 ≤ (j : ℤ) + 1 - t := by omega
    have : (((j + 1 - t).toNat : ℕ) : ℤ) = (j : ℤ) + 1 - t := by omega
    have hc : ((((j + 1 - t).toNat : ℕ) : ℤ) : ZMod N) = (((j : ℤ) + 1 - t : ℤ) : ZMod N) := by
      rw [this]
    push_cast at hc
    have e : z = c + (j : ZMod N) - (t : ZMod N) := by rw [htc]; ring
    rw [e]
    have : (((j + 1 - t).toNat : ℕ) : ZMod N) = (j : ZMod N) + 1 - (t : ZMod N) := by
      exact_mod_cast hc
    rw [this]; ring

/-- The `1`-interior of a box of sites contains the box shrunk by one site. -/
theorem mem_nbhdNeg_box_margin {d : ℕ} {c : Torus d N} {s : Fin d → ℕ} {y : Torus d N}
    (hy : y ∈ box c s) : y ∈ nbhdNeg 1 (box (fun i => c i - 1) (fun i => s i + 2)) := by
  rw [mem_nbhdNeg]
  intro z hz i
  exact mem_cycInt_margin (hy i) (supDist_le_iff.mp hz i)

end Margin

section Enclosure

variable {d n : ℕ} [NeZero n] {a : Torus d n} {s : Fin d → ℕ} {ι : Type*} [Finite ι]

/-- **Lemma S (a), (b), consequence**: if the obstacle is a union of pairwise `*`-separated pieces
`A_j` of sup-diameter `≤ t_{i₀}` (for one coordinate `i₀`), and a box `Q' ∋ x` of side `t` lies in
`Q ∖ ⋃ A_j`, then `x` is joined to the boundary of `Q` by an nn path in `Q ∖ ⋃ A_j`. -/
theorem exists_shell_path_of_small_pieces (hd : 2 ≤ d) (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < n)
    {A : ι → Set (Torus d n)} (hA : ∀ j, A j ⊆ nbhdNeg 1 (box a s))
    (hsep : ∀ j k, j ≠ k → ∀ y ∈ A j, ∀ y' ∈ A k, 2 ≤ supDist y y')
    {x : Torus d n} (hx : x ∈ nbhdNeg 1 (box a s)) (hxA : x ∉ ⋃ j, A j)
    {c : Torus d n} {t : Fin d → ℕ} (ht1 : ∀ i, 1 ≤ t i) (ht2 : ∀ i, 2 * t i < n)
    (hQ' : box c t ⊆ box a s \ ⋃ j, A j) (hxQ' : x ∈ box c t) (i₀ : Fin d)
    (hdiam : ∀ j, ∀ y ∈ A j, ∀ z ∈ A j, supDist y z < t i₀ + 1) :
    ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧ TConn (box a s \ ⋃ j, A j) x z := by
  by_contra hno
  obtain ⟨j, p, hp, -, hext⟩ := torus_enclosed_component_diam hd hs hA hsep hx hxA hno ht1 ht2 hQ'
    hxQ'
  obtain ⟨y, hy, z, hz, hle⟩ := hext i₀
  have := hdiam j y hy.1 z hz.1
  omega

end Enclosure

end Balaban.LargeField
