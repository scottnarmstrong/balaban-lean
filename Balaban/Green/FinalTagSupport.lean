/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalPathDefect
public import Balaban.Localization.AbstractExpansion

/-!
# What the tags of the last-integral parametrix localize (FINALFAM2, T3)

This construction is proposed in FINALFAM; the papers print no formula (Roland question 18
pending).  Nothing below claims that the tagged family is the papers' construction.

For the tagged matrices of `Balaban/Green/FinalBoxResolvent.lean` (entry `(x, y)` is the sum over
cells `z` of `tagMon (V z x y) s` times an entry attached to `z`) we prove, for a set `C` of cells:

* `tagMon_zero_of_not_subset`: at a parameter supported on `C`, a tag monomial vanishes unless its
  tag set lies in `C`; hence `taggedMat_apply_of_supportedOn`: the entry only sums the cells with
  `V z x y ⊆ C`;
* `taggedMat_congr_supportedOn`, `taggedGfin_congr_supportedOn`: two families whose entries agree
  whenever the tag set lies in `C` give equal tagged matrices (and equal `taggedG`, `taggedK`,
  `taggedGfin`, with the inverse as defined) at every parameter supported on `C`;
* `macTags_cover_box_and_ends`: if `macTags d m M z x y ⊆ C` then the whole box `B_z` and the
  endpoints `x`, `y` lie in the union `Y(C)` of the boxes of the cells of `C`;
* `boxG_congr_of_agree_on_box`, `boxR_apply_congr_of_agree`: the box resolvent and the defect read
  only the stated entries of the matrix, and `taggedGfin_congr_of_agree_on_region` puts these
  together for the macro cover.
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Support

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Pc : Type*} [Fintype Pc] [DecidableEq Pc]

omit [Fintype Pc] [DecidableEq Pc] in
/-- **T1.** At a parameter supported on `C`, a tag monomial whose tag set is not contained in `C`
vanishes. -/
theorem tagMon_zero_of_not_subset {C V : Finset Pc} {s : Pc → ℂ}
    (hs : s ∈ Balaban.Localization.supportedOn C) (hV : ¬ V ⊆ C) : tagMon V s = 0 := by
  obtain ⟨p, hpV, hpC⟩ := Finset.not_subset.1 hV
  exact Finset.prod_eq_zero hpV (hs p hpC)

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
/-- At a parameter supported on `C`, the entry `(x, y)` of a tagged matrix only sums the cells
whose tag set lies in `C`. -/
theorem taggedMat_apply_of_supportedOn (S : Finset Z) (V : Z → ι → ι → Finset Pc)
    (a : Z → Matrix ι ι ℂ) {C : Finset Pc} {s : Pc → ℂ}
    (hs : s ∈ Balaban.Localization.supportedOn C) (x y : ι) :
    taggedMat S V a s x y = ∑ z ∈ S.filter (fun z => V z x y ⊆ C), tagMon (V z x y) s * a z x y := by
  simp only [taggedMat, Matrix.of_apply]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : V z x y ⊆ C
  · simp [h]
  · simp [h, tagMon_zero_of_not_subset hs h]

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
/-- **T2 (tagged matrices).** If the entry families agree whenever the tag set lies in `C`, the
tagged matrices agree at every parameter supported on `C`. -/
theorem taggedMat_congr_supportedOn (S : Finset Z) (V : Z → ι → ι → Finset Pc)
    {a a' : Z → Matrix ι ι ℂ} {C : Finset Pc}
    (h : ∀ z ∈ S, ∀ x y, V z x y ⊆ C → a z x y = a' z x y) {s : Pc → ℂ}
    (hs : s ∈ Balaban.Localization.supportedOn C) :
    taggedMat S V a s = taggedMat S V a' s := by
  ext x y
  rw [taggedMat_apply_of_supportedOn S V a hs, taggedMat_apply_of_supportedOn S V a' hs]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter] at hz
  rw [h z hz.1 x y hz.2]

omit [Fintype Pc] in
/-- **T2 (`taggedGfin`).** For two matrices, if `χ_z G_z (x, y)` and `R_z (x, y)` agree whenever
`V z x y ⊆ C`, then `taggedG`, `taggedK` and `taggedGfin` (the inverse as defined) agree at every
parameter supported on `C`. -/
theorem taggedGfin_congr_supportedOn (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) {U U' : Matrix ι ι ℂ} {t : ℝ} {C : Finset Pc}
    (hG : ∀ z ∈ S, ∀ x y, V z x y ⊆ C →
      (Matrix.diagonal (c z) * boxG U (B z) t) x y = (Matrix.diagonal (c z) * boxG U' (B z) t) x y)
    (hR : ∀ z ∈ S, ∀ x y, V z x y ⊆ C → boxR U (B z) (c z) t x y = boxR U' (B z) (c z) t x y)
    {s : Pc → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C) :
    taggedG S B c V U t s = taggedG S B c V U' t s ∧ taggedK S B c V U t s = taggedK S B c V U' t s ∧
      taggedGfin S B c V U t s = taggedGfin S B c V U' t s := by
  have h1 : taggedG S B c V U t s = taggedG S B c V U' t s :=
    taggedMat_congr_supportedOn S V hG hs
  have h2 : taggedK S B c V U t s = taggedK S B c V U' t s :=
    taggedMat_congr_supportedOn S V (a := fun z => boxR U (B z) (c z) t)
      (a' := fun z => boxR U' (B z) (c z) t) hR hs
  refine ⟨h1, h2, ?_⟩
  unfold taggedGfin
  rw [h1, h2]

end Support

section Cover

variable {d m M : ℕ} [NeZero m]

/-- The union `Y(C) = ⋃_{p ∈ C} B_p` of the boxes of the cells of `C`. -/
def macRegion (d m M : ℕ) [NeZero m] (C : Finset (MacIdx d m M)) : Set (L1Torus d m) :=
  ⋃ p ∈ C, macBox d m M p

theorem mem_macRegion {C : Finset (MacIdx d m M)} {x : L1Torus d m} :
    x ∈ macRegion d m M C ↔ ∃ p ∈ C, x ∈ macBox d m M p := by
  simp [macRegion]

theorem mem_macBox_of_mem_macCore (hM : 0 < M) {w : MacIdx d m M} {x : L1Torus d m}
    (h : x ∈ macCore d m M w) : x ∈ macBox d m M w := by
  change Metric.infDist x (macCore d m M w) < 2 * M
  rw [Metric.infDist_zero_of_mem h]
  exact_mod_cast Nat.mul_pos two_pos hM

/-- **T3.** If `macTags z x y ⊆ C` then the box `B_z` and the endpoints `x`, `y` lie in `Y(C)`. -/
theorem macTags_cover_box_and_ends (hM : 0 < M) (hd : 0 < d) {z : MacIdx d m M}
    {x y : L1Torus d m} {C : Finset (MacIdx d m M)} (h : macTags d m M z x y ⊆ C) :
    macBox d m M z ⊆ macRegion d m M C ∧ x ∈ macRegion d m M C ∧ y ∈ macRegion d m M C := by
  classical
  have key : ∀ q : L1Torus d m, ∃ w, q ∈ macBox d m M w ∧
      ((q ∈ macBox d m M z → w ∈ macTags d m M z x y) ∧
        (q ∈ macPath d m x y → w ∈ macTags d m M z x y)) := by
    intro q
    obtain ⟨w, hw, -⟩ := macCore_partition (M := M) q
    have hq := mem_macBox_of_mem_macCore hM hw
    refine ⟨w, hq, fun hz => ?_, fun hp => ?_⟩
    · simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨q, hq, hz⟩
    · simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨q, hp, hq⟩
  refine ⟨fun q hq => ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hz, -⟩ := key q
    exact mem_macRegion.2 ⟨w, h (hz hq), hw⟩
  · obtain ⟨w, hw, -, hp⟩ := key x
    exact mem_macRegion.2 ⟨w, h (hp (macPath_start hd x y)), hw⟩
  · obtain ⟨w, hw, -, hp⟩ := key y
    exact mem_macRegion.2 ⟨w, h (hp (macPath_end hd x y)), hw⟩

end Cover

section Locality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem boxP_mul_mul_boxP_apply (B : Finset ι) (A : Matrix ι ι ℂ) (x y : ι) :
    (boxP B * A * boxP B) x y = (if x ∈ B then 1 else 0) * A x y * (if y ∈ B then 1 else 0) := by
  simp [boxP, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- **T4 (box resolvent).** `boxH U B t` reads only the `B × B` block of `U`; so does `boxG`
(no invertibility is needed, the inverse is the one defined for matrices). -/
theorem boxG_congr_of_agree_on_box {U U' : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ}
    (h : ∀ x ∈ B, ∀ y ∈ B, U x y = U' x y) : boxG U B t = boxG U' B t := by
  have hH : boxH U B t = boxH U' B t := by
    ext x y
    simp only [boxH, Matrix.add_apply, boxP_mul_mul_boxP_apply]
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
    · simp only [shiftMat, Matrix.add_apply, h x hx y hy]
    · simp [hy]
    · simp [hx]
    · simp [hx]
  unfold boxG
  rw [hH]

/-- **T4 (defect).** The entry `(x, y)` of `boxR U B c t` (with `c` supported in `B`) reads only
the entries `U x w`, `w ∈ B`, of row `x`, and the block `U|_{B × B}` (through `boxG`). -/
theorem boxR_apply_congr_of_agree {U U' : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} {c : ι → ℂ}
    (hB : ∀ x ∈ B, ∀ y ∈ B, U x y = U' x y) (hc : ∀ w, c w ≠ 0 → w ∈ B) {x : ι}
    (hx : ∀ w ∈ B, U x w = U' x w) (y : ι) :
    boxR U B c t x y = boxR U' B c t x y := by
  have hG := boxG_congr_of_agree_on_box (t := t) hB
  simp only [boxR, Matrix.sub_apply, hG, Matrix.mul_assoc]
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hcw : c u = 0
  · simp [hcw]
  · simp only [shiftMat, Matrix.add_apply, hx u (hc u hcw)]

end Locality

section Combined

variable {d N₀ M : ℕ} [NeZero N₀] {Z : Type*}

/-- The cutoffs of the macro cover as complex diagonals. -/
theorem macChi_ne_zero_mem_macBoxF (hM : 0 < M) {z : MacIdx d N₀ M} {w : L1Torus d N₀}
    (h : ((macChi d N₀ M z w : ℝ) : ℂ) ≠ 0) : w ∈ macBoxF d N₀ M z :=
  mem_macBoxF.2 (macChi_mem_box hM (by exact_mod_cast h))

/-- **T2 + T4 for the macro cover.**  If `U` and `U'` agree on `Y(C) × Y(C)`, then `taggedG`,
`taggedK` and `taggedGfin` of the macro cover (tags `macTags`, boxes `macBoxF`, cutoffs `macChi`)
agree at every parameter supported on `C`. -/
theorem taggedGfin_congr_of_agree_on_region (hM : 0 < M) (hd : 0 < d)
    (S : Finset (MacIdx d N₀ M)) {U U' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {t : ℝ}
    {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C) :
    taggedG S (macBoxF d N₀ M) (fun z x => ((macChi d N₀ M z x : ℝ) : ℂ)) (macTags d N₀ M) U t s =
        taggedG S (macBoxF d N₀ M) (fun z x => ((macChi d N₀ M z x : ℝ) : ℂ)) (macTags d N₀ M)
          U' t s ∧
      taggedK S (macBoxF d N₀ M) (fun z x => ((macChi d N₀ M z x : ℝ) : ℂ)) (macTags d N₀ M)
          U t s =
        taggedK S (macBoxF d N₀ M) (fun z x => ((macChi d N₀ M z x : ℝ) : ℂ)) (macTags d N₀ M)
          U' t s ∧
      taggedGfin S (macBoxF d N₀ M) (fun z x => ((macChi d N₀ M z x : ℝ) : ℂ)) (macTags d N₀ M)
          U t s =
        taggedGfin S (macBoxF d N₀ M) (fun z x => ((macChi d N₀ M z x : ℝ) : ℂ)) (macTags d N₀ M)
          U' t s := by
  have hBB : ∀ z, ∀ x y, macTags d N₀ M z x y ⊆ C → ∀ u ∈ macBoxF d N₀ M z,
      ∀ v ∈ macBoxF d N₀ M z, U u v = U' u v := fun z x y hT u hu v hv =>
    hU u ((macTags_cover_box_and_ends hM hd hT).1 (mem_macBoxF.1 hu))
      v ((macTags_cover_box_and_ends hM hd hT).1 (mem_macBoxF.1 hv))
  refine taggedGfin_congr_supportedOn S (macBoxF d N₀ M) _ (macTags d N₀ M) ?_ ?_ hs
  · intro z _ x y hT
    simp only [Matrix.mul_apply, boxG_congr_of_agree_on_box (t := t) (hBB z x y hT)]
  · intro z _ x y hT
    exact boxR_apply_congr_of_agree (hBB z x y hT) (fun w hw => macChi_ne_zero_mem_macBoxF hM hw)
      (fun w hw => hU x (macTags_cover_box_and_ends hM hd hT).2.1 w
        ((macTags_cover_box_and_ends hM hd hT).1 (mem_macBoxF.1 hw))) y

end Combined

end Balaban.Green
