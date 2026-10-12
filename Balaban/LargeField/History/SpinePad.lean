module

public import Balaban.LargeField.History.SpineOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Padding a spine to a prescribed length (Part I, Definition I.4.5)

A spine can be lengthened by any amount `δ ≥ 0` by adding one segment of length `δ` starting at a
point of it (when `2 ≤ d`); the carrier only grows, so the projection and every neighbourhood
containment are preserved.  This is used to choose the spine of a component of prescribed (canonical)
length, `RegionHistory.nextSpine`.
-/

@[expose] public section

open Set

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

namespace Spine

variable {d : ℕ}

/-- The vector of Euclidean length `δ` in the plane of the first two axes with slope `m`. -/
noncomputable def padVec (d : ℕ) (δ : ℝ) (m : ℕ) : Fin d → ℝ := fun i =>
  if i.val = 0 then δ / Real.sqrt (1 + (m : ℝ) ^ 2)
  else if i.val = 1 then (m : ℝ) * (δ / Real.sqrt (1 + (m : ℝ) ^ 2)) else 0

theorem segLen_padVec (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) (P : Fin d → ℝ) :
    segLen P (P + padVec d δ m) = δ := by
  unfold segLen
  have hs : 0 < Real.sqrt (1 + (m : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (1 + (m : ℝ) ^ 2) ^ 2 = 1 + (m : ℝ) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsum : ∑ i : Fin d, ((P + padVec d δ m) i - P i) ^ 2 = δ ^ 2 := by
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hz : ∀ i ∈ (Finset.univ \ {i0, i1}), ((P + padVec d δ m) i - P i) ^ 2 = 0 := by
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or] at hi
      have h0 : i.val ≠ 0 := fun h => hi.1 (Fin.ext h)
      have h1 : i.val ≠ 1 := fun h => hi.2 (Fin.ext h)
      simp [padVec, h0, h1]
    rw [← Finset.sum_sdiff (Finset.subset_univ {i0, i1}), Finset.sum_eq_zero hz, zero_add,
      Finset.sum_pair h01]
    simp only [Pi.add_apply, padVec, i0, i1, add_sub_cancel_left]
    simp only [one_ne_zero, ↓reduceIte]
    field_simp
    rw [hsq]
  rw [hsum]; exact Real.sqrt_sq hδ

/-- Lengthen a spine by one segment of length `δ` at the point `P` of its carrier. -/
noncomputable def padWith (sp : Spine d) (P v : Fin d → ℝ) (hP : P ∈ sp.carrier) : Spine d where
  segs := insert (P, P + v) sp.segs
  nonempty := ⟨(P, P + v), Finset.mem_insert_self _ _⟩
  conn := by
    have e : (⋃ s ∈ insert (P, P + v) sp.segs, segment ℝ s.1 s.2) =
        segment ℝ P (P + v) ∪ sp.carrier := by
      ext x; simp [carrier]
    rw [e]
    rw [union_comm]
    exact sp.conn.union P hP (left_mem_segment ℝ P _) (convex_segment P _).isPreconnected

theorem carrier_padWith (sp : Spine d) (P v : Fin d → ℝ) (hP : P ∈ sp.carrier) :
    (padWith sp P v hP).carrier = segment ℝ P (P + v) ∪ sp.carrier := by
  ext x; simp [carrier, padWith]

theorem length_padWith (sp : Spine d) (P v : Fin d → ℝ) (hP : P ∈ sp.carrier)
    (hnew : (P, P + v) ∉ sp.segs) :
    (padWith sp P v hP).length = sp.length + segLen P (P + v) := by
  classical
  have : (padWith sp P v hP).length = ∑ s ∈ insert (P, P + v) sp.segs, segLen s.1 s.2 := rfl
  rw [this, Finset.sum_insert hnew]
  show _ = sp.length + _
  rw [add_comm]; rfl

/-- A spine can be lengthened to any larger length, keeping its carrier. -/
theorem exists_pad (hd : 2 ≤ d) (sp : Spine d) {ℓ : ℝ} (h : sp.length ≤ ℓ) :
    ∃ sp' : Spine d, sp.carrier ⊆ sp'.carrier ∧ sp'.length = ℓ := by
  classical
  have hδ : 0 ≤ ℓ - sp.length := sub_nonneg.mpr h
  rcases eq_or_lt_of_le hδ with h0 | hpos
  · exact ⟨sp, subset_rfl, by linarith⟩
  obtain ⟨s0, hs0⟩ := sp.nonempty
  have hP : s0.1 ∈ sp.carrier := (sp.mem_carrier).mpr ⟨s0, hs0, left_mem_segment _ _ _⟩
  have hinj : Function.Injective (fun m : ℕ => ((s0.1, s0.1 + padVec d (ℓ - sp.length) m) :
      (Fin d → ℝ) × (Fin d → ℝ))) := by
    intro m m' hmm
    have hv : padVec d (ℓ - sp.length) m = padVec d (ℓ - sp.length) m' := by
      have := congrArg Prod.snd hmm
      simpa using this
    have e0 := congrFun hv ⟨0, by omega⟩
    have e1 := congrFun hv ⟨1, by omega⟩
    simp only [padVec, ↓reduceIte, one_ne_zero] at e0 e1
    have hpos' : ∀ m : ℕ, 0 < (ℓ - sp.length) / Real.sqrt (1 + (m : ℝ) ^ 2) := fun m =>
      div_pos hpos (Real.sqrt_pos.mpr (by positivity))
    rw [← e0] at e1
    have := mul_right_cancel₀ (hpos' m).ne' e1
    exact_mod_cast this
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset sp.segs
  refine ⟨padWith sp s0.1 (padVec d (ℓ - sp.length) m) hP, ?_, ?_⟩
  · rw [carrier_padWith]; exact subset_union_right
  · rw [length_padWith _ _ _ _ (by simpa using hm), segLen_padVec hd hδ]; ring

end Spine

end Balaban.LargeField
