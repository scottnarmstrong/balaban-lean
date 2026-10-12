module

public import Balaban.LargeField.History.SpineOps
public import Balaban.LargeField.Geometry.Components
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Joining a connected family of spined cube sets (Part I, proof of Lemma I.4.8)

* `exists_join_cubes`: two sets of cubes `V₁ ⊆ N_r(Γ₁)`, `V₂ ⊆ N_r(Γ₂)` containing cubes at index
  distance `≤ w` lie in `N_r(Γ)` for a spine `Γ` of length at most `ℓ₁ + ℓ₂ + D`, where
  `D ≥ √d (2r + w + 2)`;
* `exists_spine_family`: the same for a family whose "contact graph" is connected (in the
  cut form), with total length `≤ ∑ ℓ_i + (|I| - 1) D`;
* `cut_of_cover`: a cover of a chain-connected set of cubes by sets `V_i` has connected contact
  graph (cut form).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ} [NeZero n]

theorem norm_cube_sub_le {a a' : Torus d n} {q q' : CTorus d n} (hq : q ∈ cube a)
    (hq' : q' ∈ cube a') : ‖q - q'‖ ≤ supDist a a' + 1 := by
  obtain ⟨q'', hq'', h1⟩ := exists_shift a a' hq
  have h2 : ‖q'' - q'‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    obtain ⟨t, ht, e1⟩ := hq'' i
    obtain ⟨t', ht', e2⟩ := hq' i
    have : (q'' - q') i = (((t - t' : ℝ)) : AddCircle (n : ℝ)) := by
      simp only [Pi.sub_apply, e1, e2, AddCircle.coe_sub]; abel
    rw [this]
    refine (norm_coe_le_iff _ _).mpr ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, sub_zero]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  calc ‖q - q'‖ = ‖(q - q'') + (q'' - q')‖ := by congr 1; abel
    _ ≤ ‖q - q''‖ + ‖q'' - q'‖ := norm_add_le _ _
    _ ≤ supDist a a' + 1 := by linarith

/-- Two spined sets of cubes with close cubes are spined together. -/
theorem exists_join_cubes (A B : Spine d) {r w D : ℝ} {V₁ V₂ : Set (Torus d n)}
    (h1 : V₁ ⊆ NR r (A.proj n)) (h2 : V₂ ⊆ NR r (B.proj n)) {a a' : Torus d n} (ha : a ∈ V₁)
    (ha' : a' ∈ V₂) (hw : (supDist a a' : ℝ) ≤ w) (hD : Real.sqrt d * (2 * r + w + 2) ≤ D) :
    ∃ C : Spine d, V₁ ∪ V₂ ⊆ NR r (C.proj n) ∧ C.length ≤ A.length + B.length + D := by
  obtain ⟨γ, ⟨P, hP, rfl⟩, q, hq, hγq⟩ := h1 ha (1 / 2) (by norm_num)
  obtain ⟨γ', ⟨Q, hQ, rfl⟩, q', hq', hγq'⟩ := h2 ha' (1 / 2) (by norm_num)
  have hqq := norm_cube_sub_le hq hq'
  have hw0 : (0 : ℝ) ≤ w := (Nat.cast_nonneg _).trans hw
  have hPQ : ‖cl n P - cl n Q‖ ≤ 2 * r + w + 2 := by
    have e : cl n P - cl n Q = (cl n P - q) + (q - q') + (q' - cl n Q) := by abel
    rw [e]
    have h3 : ‖q' - cl n Q‖ = ‖cl n Q - q'‖ := norm_sub_rev _ _
    calc ‖(cl n P - q) + (q - q') + (q' - cl n Q)‖
        ≤ ‖cl n P - q‖ + ‖q - q'‖ + ‖q' - cl n Q‖ := norm_add₃_le
      _ ≤ 2 * r + w + 2 := by
        have h4 : ‖cl n P - q‖ < r + 1 / 2 := hγq
        have h5 : ‖cl n Q - q'‖ < r + 1 / 2 := hγq'
        rw [h3]
        linarith
  obtain ⟨C, hAC, hBC, hlen⟩ := exists_join A B hP hQ hPQ
  refine ⟨C, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact NR_mono le_rfl hAC (h1 hx)
    · exact NR_mono le_rfl hBC (h2 hx)
  · linarith

/-- A family of spined sets with connected contact graph is spined by one spine. -/
theorem exists_spine_family {ι : Type*} [DecidableEq ι] (I : Finset ι) (hI : I.Nonempty)
    (V : ι → Set (Torus d n)) (Γ : ι → Spine d) {r w D : ℝ}
    (hV : ∀ i ∈ I, V i ⊆ NR r ((Γ i).proj n))
    (hadj : ∀ T ⊆ I, T.Nonempty → T ≠ I →
      ∃ i ∈ T, ∃ j ∈ I \ T, ∃ a ∈ V i, ∃ a' ∈ V j, (supDist a a' : ℝ) ≤ w)
    (hD : Real.sqrt d * (2 * r + w + 2) ≤ D) :
    ∃ C : Spine d, (⋃ i ∈ I, V i) ⊆ NR r (C.proj n) ∧
      C.length ≤ ∑ i ∈ I, (Γ i).length + ((I.card : ℝ) - 1) * D := by
  have key : ∀ m, 1 ≤ m → m ≤ I.card → ∃ T ⊆ I, T.card = m ∧ ∃ C : Spine d,
      (⋃ i ∈ T, V i) ⊆ NR r (C.proj n) ∧
      C.length ≤ ∑ i ∈ T, (Γ i).length + ((m : ℝ) - 1) * D := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨i0, hi0⟩ := hI
      refine ⟨{i0}, by simpa using hi0, by simp, Γ i0, ?_, by simp⟩
      simpa using hV i0 hi0
    | succ m hm ih =>
      intro hmI
      obtain ⟨T, hTI, hTc, C, hC, hCl⟩ := ih (by omega)
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hTneI : T ≠ I := fun h => by rw [h] at hTc; omega
      obtain ⟨i, hi, j, hj, a, ha, a', ha', hd⟩ := hadj T hTI hTne hTneI
      obtain ⟨hjI, hjT⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨C', hC'1, hC'2⟩ := exists_join_cubes C (Γ j) (V₁ := ⋃ i ∈ T, V i) (V₂ := V j)
        hC (hV j hjI) (a := a) (a' := a')
        (Set.mem_biUnion hi ha) ha' hd hD
      refine ⟨insert j T, Finset.insert_subset hjI hTI, by rw [Finset.card_insert_of_notMem hjT, hTc],
        C', ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Set.mem_iUnion, exists_prop] at hx
        apply hC'1
        rcases hx with ⟨k, rfl | hk, hxk⟩
        · exact Or.inr hxk
        · exact Or.inl (Set.mem_biUnion hk hxk)
      · rw [Finset.sum_insert hjT]
        push_cast
        linarith
  obtain ⟨T, hTI, hTc, C, hC, hCl⟩ := key I.card (Finset.card_pos.mpr hI) le_rfl
  have : T = I := Finset.eq_of_subset_of_card_le hTI (by omega)
  subst this
  exact ⟨C, hC, hCl⟩

/-- A cover of a chain-connected set by sets `V_i ⊆ C` has connected contact graph. -/
theorem cut_of_cover {ω : ℕ} (hω : 0 < ω) {C : Finset (Torus d n)} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (V : ι → Set (Torus d n))
    (hconn : ∀ x ∈ C, ∀ y ∈ C, Linked ω (C : Set (Torus d n)) x y)
    (hcover : ∀ x ∈ C, ∃ i ∈ I, x ∈ V i) (hsub : ∀ i ∈ I, V i ⊆ C)
    (hne : ∀ i ∈ I, (V i).Nonempty) :
    ∀ T ⊆ I, T.Nonempty → T ≠ I →
      ∃ i ∈ T, ∃ j ∈ I \ T, ∃ a ∈ V i, ∃ a' ∈ V j, supDist a a' ≤ ω - 1 := by
  intro T hTI hTne hTneI
  obtain ⟨i0, hi0⟩ := hTne
  obtain ⟨j0, hj0I, hj0T⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hTI hTneI)
  obtain ⟨x0, hx0⟩ := hne i0 (hTI hi0)
  obtain ⟨y0, hy0⟩ := hne j0 hj0I
  have hx0C : x0 ∈ C := hsub _ (hTI hi0) hx0
  have hy0C : y0 ∈ C := hsub _ hj0I hy0
  have hchain := hconn x0 hx0C y0 hy0C
  have key : ∀ z, Linked ω (C : Set (Torus d n)) x0 z →
      (∃ i ∈ T, ∃ j ∈ I \ T, ∃ a ∈ V i, ∃ a' ∈ V j, supDist a a' ≤ ω - 1) ∨ ∃ i ∈ T, z ∈ V i := by
    intro z hz
    induction hz with
    | refl => exact Or.inr ⟨i0, hi0, hx0⟩
    | @tail b c _ hbc ih =>
      rcases ih with h | ⟨i, hi, hb⟩
      · exact Or.inl h
      · obtain ⟨j, hjI, hcj⟩ := hcover c hbc.2.1
        by_cases hjT : j ∈ T
        · exact Or.inr ⟨j, hjT, hcj⟩
        · exact Or.inl ⟨i, hi, j, Finset.mem_sdiff.mpr ⟨hjI, hjT⟩, b, hb, c, hcj, by
            have := hbc.2.2; omega⟩
  rcases key y0 hchain with h | ⟨i, hi, hyi⟩
  · exact h
  · exact ⟨i, hi, j0, Finset.mem_sdiff.mpr ⟨hj0I, hj0T⟩, y0, hyi, y0, hy0, by
      rw [supDist_self]; exact Nat.zero_le _⟩

end Balaban.LargeField
