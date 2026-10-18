/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Two general facts on series

A series whose finite partial sums are bounded in norm has its sum bounded in norm, and a
vanishing sum over a set of indices splits into a finite part and the sum over the remaining
indices.
-/

@[expose] public section

open Filter

namespace Balaban.SmallField.Def6

/-- A series whose finite partial sums are bounded in norm has sum bounded in norm. -/
theorem norm_tsum_le_of_forall_sum_le {ι : Type*} (f : ι → ℂ) (hs : Summable f) {B : ℝ}
    (h : ∀ G : Finset ι, ‖∑ i ∈ G, f i‖ ≤ B) : ‖∑' i, f i‖ ≤ B := by
  have h1 : Tendsto (fun G : Finset ι => ‖∑ i ∈ G, f i‖) atTop (nhds ‖∑' i, f i‖) :=
    (continuous_norm.tendsto _).comp hs.hasSum
  exact le_of_tendsto' h1 h

open Classical in
/-- Splitting off a finite set of terms from a vanishing sum over a set of indices. -/
theorem sum_add_tsum_indicator_diff {ι : Type*} (S : Set ι) (f : ι → ℂ) (C : Finset ι)
    (hC : (C : Set ι) ⊆ S) (hs : Summable (fun x : S => f x.1))
    (h0 : ∑' x : S, f x.1 = 0) :
    Summable ((S \ (C : Set ι)).indicator f) ∧
      ∑ x ∈ C, f x + ∑' x, (S \ (C : Set ι)).indicator f x = 0 := by
  have hind : Summable (S.indicator f) := (summable_subtype_iff_indicator).1 hs
  have hsplit : S.indicator f = (C : Set ι).indicator f + (S \ (C : Set ι)).indicator f := by
    funext x
    by_cases hxC : x ∈ (C : Set ι)
    · have hxS := hC hxC
      simp [Set.indicator, hxC, hxS]
    · by_cases hxS : x ∈ S
      · simp [Set.indicator, hxC, hxS]
      · simp [Set.indicator, hxC, hxS]
  have hfin : Summable ((C : Set ι).indicator f) := by
    refine summable_of_ne_finset_zero (s := C) fun x hx => ?_
    exact Set.indicator_of_notMem (by simpa using hx) f
  have hdiff : Summable ((S \ (C : Set ι)).indicator f) := by
    have := hind.sub hfin
    convert this using 1
    rw [hsplit]
    funext x
    simp
  refine ⟨hdiff, ?_⟩
  have h2 : ∑' x, S.indicator f x = 0 := by rw [← tsum_subtype S f]; exact h0
  rw [hsplit] at h2
  simp only [Pi.add_apply] at h2
  rw [Summable.tsum_add hfin hdiff] at h2
  have h3 : ∑' x, (C : Set ι).indicator f x = ∑ x ∈ C, f x := by
    rw [← tsum_subtype (C : Set ι) f]
    exact Finset.tsum_subtype' C f
  rw [h3] at h2
  exact h2


open Classical in
/-- **The difference of a finite sum and a vanishing infinite sum is a sum over the unmatched
shapes**: `Lfin` is the finite set of the shapes of the torus, `polys` the set of the shapes of
the infinite volume, the two terms agree on the common shapes, and the infinite sum vanishes.
The norm of the finite sum is at most the norm of the sum over the shapes of the torus that are not
shapes of the infinite volume plus the bound of the finite sums over the shapes of the infinite
volume that are not shapes of the torus. -/
theorem norm_sum_le_of_unmatched {ι : Type*} [DecidableEq ι] (Lfin : Finset ι) (polys : Set ι) (fFin fInf : ι → ℂ)
    (hmatch : ∀ X ∈ Lfin, X ∈ polys → fFin X = fInf X)
    (hs : Summable (fun x : polys => fInf x.1)) (h0 : ∑' x : polys, fInf x.1 = 0)
    {BF BI : ℝ}
    (hF : ‖∑ X ∈ Lfin.filter (fun X => X ∉ polys), fFin X‖ ≤ BF)
    (hI : ∀ G : Finset ι, ‖∑ X ∈ G.filter (fun X => X ∈ polys ∧ X ∉ Lfin), fInf X‖ ≤ BI) :
    ‖∑ X ∈ Lfin, fFin X‖ ≤ BF + BI := by
  set C : Finset ι := Lfin.filter (fun X => X ∈ polys) with hC
  have hCS : (C : Set ι) ⊆ polys := fun X hX => (Finset.mem_filter.1 hX).2
  obtain ⟨hd, hid⟩ := sum_add_tsum_indicator_diff polys fInf C hCS hs h0
  have hsplit : ∑ X ∈ Lfin, fFin X = ∑ X ∈ C, fFin X +
      ∑ X ∈ Lfin.filter (fun X => X ∉ polys), fFin X :=
    (Finset.sum_filter_add_sum_filter_not Lfin (fun X => X ∈ polys) fFin).symm
  have hCeq : ∑ X ∈ C, fFin X = ∑ X ∈ C, fInf X :=
    Finset.sum_congr rfl fun X hX => hmatch X (Finset.mem_filter.1 hX).1
      (Finset.mem_filter.1 hX).2
  have htail : ‖∑' X, (polys \ (C : Set ι)).indicator fInf X‖ ≤ BI := by
    refine norm_tsum_le_of_forall_sum_le _ hd fun G => ?_
    have : ∑ X ∈ G, (polys \ (C : Set ι)).indicator fInf X =
        ∑ X ∈ G.filter (fun X => X ∈ polys ∧ X ∉ Lfin), fInf X := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun X _ => ?_
      simp only [Set.indicator_apply, Set.mem_sdiff, Finset.mem_coe, hC, Finset.mem_filter]
      by_cases h1 : X ∈ polys <;> by_cases h2 : X ∈ Lfin <;> simp [h1, h2]
    rw [this]
    exact hI G
  have hcomb : ∑ X ∈ Lfin, fFin X =
      ∑ X ∈ Lfin.filter (fun X => X ∉ polys), fFin X -
        ∑' X, (polys \ (C : Set ι)).indicator fInf X := by
    rw [hsplit, hCeq]
    linear_combination hid
  rw [hcomb]
  exact (norm_sub_le _ _).trans (add_le_add hF htail)

end Balaban.SmallField.Def6
