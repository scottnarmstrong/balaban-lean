module

public import Balaban.LargeField.Counter.LemmaV
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Operations on spines (Part I, Definition I.4.5)

Point spines, translation by a vector, contraction `Γ/L`, and the join of two spines through a
connecting segment.  The join of two spines whose projections to the torus `(ℝ/nℤ)^d` contain
points at torus distance `≤ B` is a spine of length at most `ℓ₁ + ℓ₂ + √d B` whose projection
contains both projections (`exists_join`): the second spine is translated by a lattice vector
`n ℤ^d` to bring a lift of its point next to the lift of the first.
-/

@[expose] public section

open Set

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

variable {d : ℕ}

theorem segLen_self (a : Fin d → ℝ) : segLen a a = 0 := by simp [segLen]

theorem segLen_add_left (v a b : Fin d → ℝ) : segLen (v + a) (v + b) = segLen a b := by
  simp [segLen]

theorem segLen_le_sqrt_mul {a b : Fin d → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ‖b - a‖ ≤ B) :
    segLen a b ≤ Real.sqrt d * B := by
  unfold segLen
  have h1 : ∀ i, (b i - a i) ^ 2 ≤ B ^ 2 := fun i => by
    have := (norm_le_pi_norm (b - a) i).trans h
    rw [Real.norm_eq_abs] at this
    simpa using sq_le_sq' (by linarith [abs_le.mp this]) (abs_le.mp this).2
  calc Real.sqrt (∑ i, (b i - a i) ^ 2) ≤ Real.sqrt (∑ _i : Fin d, B ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h1 i)
    _ = Real.sqrt d * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]

namespace Spine

/-- The one-point spine. -/
def point (p : Fin d → ℝ) : Spine d where
  segs := {(p, p)}
  nonempty := Finset.singleton_nonempty _
  conn := by simpa using isPreconnected_singleton

theorem carrier_point (p : Fin d → ℝ) : (point p).carrier = {p} := by
  ext x; simp [carrier, point]

theorem length_point (p : Fin d → ℝ) : (point p).length = 0 := by
  simp [length, point, segLen_self]

theorem mem_carrier_point (p : Fin d → ℝ) : p ∈ (point p).carrier := by
  rw [carrier_point]; rfl

theorem biUnion_translate (sp : Spine d) (v : Fin d → ℝ) :
    (⋃ s ∈ sp.segs.image (fun s => (v + s.1, v + s.2)), segment ℝ s.1 s.2) =
      (fun x => v + x) '' (⋃ s ∈ sp.segs, segment ℝ s.1 s.2) := by
  ext x
  simp only [Finset.mem_image, Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
    rw [← segment_translate_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨s, hs, hy⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
    rw [← segment_translate_image]
    exact ⟨y, hy, rfl⟩

/-- Translation of a spine by a vector. -/
noncomputable def translate (sp : Spine d) (v : Fin d → ℝ) : Spine d where
  segs := sp.segs.image (fun s => (v + s.1, v + s.2))
  nonempty := sp.nonempty.image _
  conn := by
    rw [biUnion_translate]
    exact sp.conn.image _ (by fun_prop)

theorem carrier_translate (sp : Spine d) (v : Fin d → ℝ) :
    (sp.translate v).carrier = (fun x => v + x) '' sp.carrier := by
  unfold carrier translate
  exact biUnion_translate sp v

theorem length_translate (sp : Spine d) (v : Fin d → ℝ) :
    (sp.translate v).length = sp.length := by
  unfold length translate
  rw [Finset.sum_image]
  · simp [segLen_add_left]
  · intro s _ t _ h
    simp only [Prod.mk.injEq, add_right_inj] at h
    exact Prod.ext h.1 h.2

theorem image_smul_segment' (c : ℝ) (a b : Fin d → ℝ) :
    (fun x => c • x) '' segment ℝ a b = segment ℝ (c • a) (c • b) := by
  have := image_segment ℝ (c • (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))).toAffineMap a b
  simpa using this

theorem biUnion_contract (c : ℝ) (sp : Spine d) :
    (⋃ s ∈ sp.segs.image (fun s => (c • s.1, c • s.2)), segment ℝ s.1 s.2) =
      (fun x => c • x) '' (⋃ s ∈ sp.segs, segment ℝ s.1 s.2) := by
  ext x
  simp only [Finset.mem_image, Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
    rw [← image_smul_segment'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨s, hs, hy⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨_, ⟨s, hs, rfl⟩, ?_⟩
    rw [← image_smul_segment']
    exact ⟨y, hy, rfl⟩

/-- Contraction `Γ/c`, the lift multiplied by `c`. -/
noncomputable def contract (c : ℝ) (sp : Spine d) : Spine d where
  segs := sp.segs.image (fun s => (c • s.1, c • s.2))
  nonempty := sp.nonempty.image _
  conn := by
    rw [biUnion_contract]
    exact sp.conn.image _ (by fun_prop)

theorem carrier_contract (c : ℝ) (sp : Spine d) :
    (sp.contract c).carrier = (fun x => c • x) '' sp.carrier := by
  unfold carrier contract
  exact biUnion_contract c sp

theorem segLen_smul (c : ℝ) (a b : Fin d → ℝ) : segLen (c • a) (c • b) = |c| * segLen a b := by
  unfold segLen
  have : ∀ i, ((c • b) i - (c • a) i) ^ 2 = c ^ 2 * (b i - a i) ^ 2 := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem length_contract_le (c : ℝ) (sp : Spine d) :
    (sp.contract c).length ≤ |c| * sp.length := by
  classical
  unfold length contract
  refine (Finset.sum_image_le_of_nonneg ?_).trans ?_
  · intro s _; exact segLen_nonneg _ _
  · rw [Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun s _ => by simp [segLen_smul])

/-- The join of two spines through the segment `[P, Q]`, `P ∈ A`, `Q ∈ B`. -/
noncomputable def join (A B : Spine d) (P Q : Fin d → ℝ) (hP : P ∈ A.carrier) (hQ : Q ∈ B.carrier) :
    Spine d where
  segs := insert (P, Q) (A.segs ∪ B.segs)
  nonempty := ⟨(P, Q), Finset.mem_insert_self _ _⟩
  conn := by
    have e : (⋃ s ∈ insert (P, Q) (A.segs ∪ B.segs), segment ℝ s.1 s.2) =
        segment ℝ P Q ∪ (A.carrier ∪ B.carrier) := by
      ext x; simp [carrier, or_and_right, exists_or]
    rw [e]
    have h1 : IsPreconnected (segment ℝ P Q) := (convex_segment P Q).isPreconnected
    have h2 : IsPreconnected (A.carrier ∪ segment ℝ P Q) :=
      A.conn.union P hP (left_mem_segment ℝ P Q) h1
    have h3 : IsPreconnected (B.carrier ∪ segment ℝ P Q) :=
      B.conn.union Q hQ (right_mem_segment ℝ P Q) h1
    have h4 : IsPreconnected ((A.carrier ∪ segment ℝ P Q) ∪ (B.carrier ∪ segment ℝ P Q)) :=
      h2.union P (Or.inl hP) (Or.inr (left_mem_segment ℝ P Q)) h3
    convert h4 using 1
    ext x; simp only [mem_union]; tauto

theorem carrier_join (A B : Spine d) (P Q : Fin d → ℝ) (hP : P ∈ A.carrier)
    (hQ : Q ∈ B.carrier) :
    (A.join B P Q hP hQ).carrier = segment ℝ P Q ∪ (A.carrier ∪ B.carrier) := by
  ext x; simp [carrier, join, or_and_right, exists_or]

theorem length_join_le (A B : Spine d) (P Q : Fin d → ℝ) (hP : P ∈ A.carrier)
    (hQ : Q ∈ B.carrier) :
    (A.join B P Q hP hQ).length ≤ A.length + B.length + segLen P Q := by
  classical
  have hdef : (A.join B P Q hP hQ).length =
      ∑ s ∈ insert (P, Q) (A.segs ∪ B.segs), segLen s.1 s.2 := rfl
  rw [hdef]
  have hnn : ∀ s : (Fin d → ℝ) × (Fin d → ℝ), 0 ≤ segLen s.1 s.2 := fun s => segLen_nonneg _ _
  have h1 : ∑ s ∈ A.segs ∪ B.segs, segLen s.1 s.2 ≤
      ∑ s ∈ A.segs, segLen s.1 s.2 + ∑ s ∈ B.segs, segLen s.1 s.2 := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun s _ => hnn s)
  have hAB : A.length = ∑ s ∈ A.segs, segLen s.1 s.2 := rfl
  have hBB : B.length = ∑ s ∈ B.segs, segLen s.1 s.2 := rfl
  rw [hAB, hBB]
  by_cases hm : (P, Q) ∈ A.segs ∪ B.segs
  · rw [Finset.insert_eq_of_mem hm]
    linarith [segLen_nonneg P Q]
  · rw [Finset.sum_insert hm]
    linarith

/-- Two points of a spine are at sup-distance at most twice the length. -/
theorem sup_dist_le (sp : Spine d) {p q : Fin d → ℝ} (hp : p ∈ sp.carrier) (hq : q ∈ sp.carrier) :
    ‖p - q‖ ≤ 2 * sp.length := by
  classical
  by_contra h
  push Not at h
  have hl := sp.length_nonneg
  have hpq : p ≠ q := by
    rintro rfl
    simp at h
    linarith
  set ρ : ℝ := (2 * sp.length + ‖p - q‖) / 2 with hρ
  have hρ1 : 2 * sp.length < ρ := by rw [hρ]; linarith
  have hρ2 : ρ < ‖p - q‖ := by rw [hρ]; linarith
  have key := sp.sep_card_le (ρ := ρ) (by linarith) {p, q}
    (by intro a ha; rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hp
        · rw [Finset.mem_singleton.mp ha]; exact hq)
    (by intro a ha b hb hab
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact hρ2
        · rw [norm_sub_rev]; exact hρ2
        · exact absurd rfl hab)
  rw [Finset.card_pair hpq] at key
  push_cast at key
  linarith

end Spine

section Torus

variable {n : ℕ} [NeZero n]

/-- The class in the continuous torus of a real point. -/
def cl (n : ℕ) (p : Fin d → ℝ) : CTorus d n := fun i => ((p i : ℝ) : AddCircle (n : ℝ))

theorem cl_mem_proj {sp : Spine d} {p : Fin d → ℝ} (hp : p ∈ sp.carrier) : cl n p ∈ sp.proj n :=
  ⟨p, hp, rfl⟩

theorem norm_cl_le {p : Fin d → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ‖p‖ ≤ B) : ‖cl n p‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  intro i
  refine (norm_coe_le_iff (n := n) (p i) B).mpr ⟨0, ?_⟩
  simpa using (norm_le_pi_norm p i).trans h

theorem cl_sub (p q : Fin d → ℝ) : cl n p - cl n q = cl n (p - q) := by
  funext i; simp [cl]

theorem cl_add_lattice (p v : Fin d → ℝ) (hv : ∀ i, ∃ k : ℤ, v i = k * n) :
    cl n (v + p) = cl n p := by
  funext i
  obtain ⟨k, hk⟩ := hv i
  simp only [cl, Pi.add_apply, hk]
  rw [add_comm]; exact coe_add_int_mul (n := n) (p i) k

theorem exists_lattice_shift {P Q : Fin d → ℝ} {B : ℝ} (h : ‖cl n P - cl n Q‖ ≤ B) :
    ∃ v : Fin d → ℝ, (∀ i, ∃ k : ℤ, v i = k * n) ∧ ‖(v + Q) - P‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans h
  have hi : ∀ i, ∃ k : ℤ, |P i - Q i - k * n| ≤ B := fun i => by
    have h1 := (norm_le_pi_norm (cl n P - cl n Q) i).trans h
    have h2 : (cl n P - cl n Q) i = ((P i - Q i : ℝ) : AddCircle (n : ℝ)) := by
      simp [cl]
    rw [h2] at h1
    exact (norm_coe_le_iff _ _).mp h1
  choose k hk using hi
  refine ⟨fun i => k i * n, fun i => ⟨k i, rfl⟩, ?_⟩
  rw [pi_norm_le_iff_of_nonneg hB]
  intro i
  rw [Real.norm_eq_abs]
  have := hk i
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [← abs_neg]
  convert this using 2
  ring

/-- **Join of two spines** through points `P ∈ A`, `Q ∈ B` whose classes are at torus distance
`≤ B₀`: a spine whose projection contains both and whose length is at most
`ℓ(A) + ℓ(B) + √d B₀`. -/
theorem exists_join (A B : Spine d) {P Q : Fin d → ℝ} (hP : P ∈ A.carrier) (hQ : Q ∈ B.carrier)
    {B₀ : ℝ} (h : ‖cl n P - cl n Q‖ ≤ B₀) :
    ∃ C : Spine d, A.proj n ⊆ C.proj n ∧ B.proj n ⊆ C.proj n ∧
      C.length ≤ A.length + B.length + Real.sqrt d * B₀ := by
  obtain ⟨v, hv, hvB⟩ := exists_lattice_shift h
  have hB0 : 0 ≤ B₀ := (norm_nonneg _).trans h
  have hQ' : v + Q ∈ (B.translate v).carrier := by
    rw [Spine.carrier_translate]; exact ⟨Q, hQ, rfl⟩
  refine ⟨A.join (B.translate v) P (v + Q) hP hQ', ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [Spine.carrier_join]; exact Or.inr (Or.inl hx)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨v + x, ?_, ?_⟩
    · rw [Spine.carrier_join, Spine.carrier_translate]; exact Or.inr (Or.inr ⟨x, hx, rfl⟩)
    · exact cl_add_lattice x v hv
  · refine (Spine.length_join_le _ _ _ _ _ _).trans ?_
    rw [Spine.length_translate]
    have := segLen_le_sqrt_mul hB0 (a := P) (b := v + Q) hvB
    linarith

/-- A spine of length `≤ 1` has its projection inside `N_2` of any of its points. -/
theorem NR_subset_point {sp : Spine d} (hl : sp.length ≤ 1) {P0 : Fin d → ℝ}
    (hP0 : P0 ∈ sp.carrier) (r : ℝ) : NR r (sp.proj n) ⊆ NR (r + 2) {cl n P0} := by
  intro x hx ε hε
  obtain ⟨γ, ⟨P, hP, rfl⟩, q, hq, hlt⟩ := hx ε hε
  refine ⟨cl n P0, rfl, q, hq, ?_⟩
  have h1 : ‖cl n P0 - cl n P‖ ≤ 2 := by
    rw [cl_sub]
    refine norm_cl_le (by norm_num) ?_
    have := sp.sup_dist_le hP0 hP
    linarith
  have h2 : ‖cl n P - q‖ < r + ε := hlt
  calc ‖cl n P0 - q‖ = ‖(cl n P0 - cl n P) + (cl n P - q)‖ := by congr 1; abel
    _ ≤ ‖cl n P0 - cl n P‖ + ‖cl n P - q‖ := norm_add_le _ _
    _ < r + 2 + ε := by linarith

/-- Every point of the continuous torus is the projection of a point spine. -/
theorem exists_point_spine (p : CTorus d n) :
    ∃ Γ : Spine d, Γ.length = 0 ∧ Γ.proj n = {p} := by
  have hrep : ∀ i, ∃ P : ℝ, (P : AddCircle (n : ℝ)) = p i := fun i =>
    QuotientAddGroup.mk_surjective (p i)
  choose P hP using hrep
  refine ⟨Spine.point P, Spine.length_point P, ?_⟩
  unfold Spine.proj
  rw [Spine.carrier_point, Set.image_singleton]
  congr 1
  funext i; exact hP i

end Torus

end Balaban.LargeField
