/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetCross
public import Balaban.Fluctuation.LocalPairDepth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step's level set and a generating set with a deep top layer: the cover at the cut points

The geometric half of the cross lemma for the determinant (`LocalSetDetCrossCut`).  `H` is a level
set of the top level `k + 1` (the step, `IsLevel H (k + 1)`) and `H'` any generating set on the
same torus (a local generating set `𝔹_{k+1}(Y)`) whose top domain `Ω_{k+1}(H')` contains a set `R`
of sites.  A site `z` is *deep* in `R` if the sup-ball of radius `8 M₁ L^{k+1}` around it lies in
`R`.  For cut sets `I` of `H` and `I'` of `H'` with the same cubes (`patches I = patches I'`), all
of them with deep bases:

* `mem_cubeIdx_iff_of_top`, `layer_iff_of_mem_top`: the cubes and the layers of `H` and `H'` agree
  at the sites of `Ω_{k+1}(H')`;
* `qset_eq_of_deep`, `chi_eq_of_deep`: the footprint of a deep centre and the partition of unity on
  its interaction cube are the same for the two covers;
* `sProd_cutPt_cross`, `zs_cutPt_cross`, `hatI_eq_hatBox_of_deep`, `yreg_cutPt_cross`: at the cut
  points `1_I`, `1_{I'}` the cut factors of the deep centres, the active centres, their thickened
  cubes and the region `Yreg` coincide; every active centre is a cube of `I` (deep), and `Yreg`
  lies within `4 M₁ L^{k+1}` of the bases of the cubes of `I`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.LargeField Finset

section Geom

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- At a site of the top domain of `H'`, the layers of the level set `H` and of `H'` agree. -/
theorem layer_iff_of_mem_top (hlev : IsLevel H (k + 1)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ H'.Ω (k + 1)) {n : ℕ} (hn : 1 ≤ n) (hnK : n ≤ k + 1) :
    x ∈ H.layer n ↔ x ∈ H'.layer n :=
  layer_iff_of_level_of_top hlev H'.top hx hn hnK

/-- A pair with base in the top domain of `H'` is a cube of `H` exactly when it is a cube of
`H'`. -/
theorem mem_cubeIdx_iff_of_top (hlev : IsLevel H (k + 1)) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q.2 ∈ H'.Ω (k + 1)) : q ∈ cubeIdx H ↔ q ∈ cubeIdx H' := by
  rw [mem_cubeIdx, mem_cubeIdx]
  constructor
  · rintro ⟨⟨h1, h2⟩, hl, hb⟩
    exact ⟨⟨h1, h2⟩, (layer_iff_of_mem_top hlev hq h1 h2).1 hl, hb⟩
  · rintro ⟨⟨h1, h2⟩, hl, hb⟩
    exact ⟨⟨h1, h2⟩, (layer_iff_of_mem_top hlev hq h1 h2).2 hl, hb⟩

/-- A cube of either cover has scale at most `k + 1`. -/
theorem le_of_mem_cubeIdx_either {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx H ∨ q ∈ cubeIdx H') : 1 ≤ q.1 ∧ q.1 ≤ k + 1 := by
  rcases hq with hq | hq
  · exact ((mem_cubeIdx H).1 hq).1
  · exact ((mem_cubeIdx H').1 hq).1

/-- A cube of the level set `H` has scale `k + 1`. -/
theorem fst_eq_of_mem_cubeIdx_level (hlev : IsLevel H (k + 1)) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx H) : q.1 = k + 1 := by
  obtain ⟨⟨h1, h2⟩, hl, -⟩ := (mem_cubeIdx H).1 hq
  by_contra hne
  exact H.layer_disjoint h1 h2 (by omega) le_rfl hne hl (hlev.mem_layer q.2)

/-! ### Distances -/

/-- A point of a thickened cube of scale `k + 1` is within `4 M₁ L^{k+1}` of the base. -/
theorem supDist_le_of_mem_hatBox_top (hM : 4 * L ^ 2 ≤ L ^ m₁) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq1 : q.1 = k + 1) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ hatBox q) :
    supDist x q.2 ≤ 4 * L ^ (k + 1 + m₁) := by
  have hR : (0 : ℝ) ≤ hatRad L m₁ q.1 := by unfold hatRad; positivity
  have h := supDist_le_of_inBox hR (mem_boxSet.1 hx)
  rw [hq1] at h
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hLk : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by positivity
  have hlam : (L : ℝ) ^ (k + 1 + m₁) = (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := pow_add _ _ _
  have key : hatRad L m₁ (k + 1) + (L : ℝ) ^ (k + 1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (k + 1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_left hM' hLk
    rw [hlam]
    nlinarith
  exact_mod_cast h.trans key

/-- A point of an interaction cube of scale `k + 1` is within `4 M₁ L^{k+1}` of the base. -/
theorem supDist_le_of_mem_intBox_top (hM : 4 * L ^ 2 ≤ L ^ m₁) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq1 : q.1 = k + 1) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q) :
    supDist x q.2 ≤ 4 * L ^ (k + 1 + m₁) :=
  supDist_le_of_mem_hatBox_top hM hq1 (box_subset_hatBox q hx)

/-- The base of a cube of scale `≤ k + 1` is within `M₁ L^{k+1}` of the sites of its cell. -/
theorem supDist_le_of_sameCell_cube {q' : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq' : q'.1 ≤ k + 1)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : SameCell (L ^ (q'.1 + m₁)) y q'.2) :
    supDist y q'.2 ≤ L ^ (k + 1 + m₁) :=
  (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hy).trans
    (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.add_le_add_right hq' m₁))

/-- A site where the bump of a cube of scale `≤ k + 1` does not vanish is within `2 M₁ L^{k+1}` of
its base. -/
theorem supDist_le_of_cubeBump_ne_zero {q' : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq' : q'.1 ≤ k + 1)
    {x : CTorus d L N₁ m₁ (k + 1)} (h : cubeBump m₁ q'.1 q'.2 x ≠ 0) :
    supDist x q'.2 ≤ 2 * L ^ (k + 1 + m₁) := by
  have hR : (0 : ℝ) ≤ 3 / 2 * (L : ℝ) ^ (q'.1 + m₁) := by positivity
  have h1 := supDist_le_of_inBox hR (inBox_of_cubeBump_ne_zero h)
  have h2 : (L : ℝ) ^ (q'.1 + m₁) ≤ (L : ℝ) ^ (k + 1 + m₁) :=
    pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) (by omega)
  have h3 : (supDist x q'.2 : ℝ) ≤ 2 * (L : ℝ) ^ (k + 1 + m₁) := by linarith
  exact_mod_cast h3

/-! ### The cover of a deep centre -/

variable (hlev : IsLevel H (k + 1)) {R : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hR : ∀ x ∈ R, x ∈ H'.Ω (k + 1)) (hM : 4 * L ^ 2 ≤ L ^ m₁)

include hlev hR hM in
/-- **The footprint of a deep centre is the same for the two covers.** -/
theorem qset_eq_of_deep {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx H)
    (hdeep : ∀ z, supDist z q.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    (coverOf H).Qset q = (coverOf H').Qset q := by
  refine qset_coverOf_congr fun q' ⟨y, hy, hbox⟩ => ?_
  by_cases hq' : q' ∈ cubeIdx H ∨ q' ∈ cubeIdx H'
  · have hle := (le_of_mem_cubeIdx_either hq').2
    have h1 := supDist_le_of_sameCell_cube hle hy
    have h2 := supDist_le_of_mem_hatBox_top hM (fst_eq_of_mem_cubeIdx_level hlev hq)
      (mem_boxSet.2 hbox)
    have h3 : supDist q'.2 q.2 ≤ 8 * L ^ (k + 1 + m₁) := by
      have := supDist_triangle q'.2 y q.2
      rw [supDist_comm q'.2 y] at this
      omega
    exact mem_cubeIdx_iff_of_top hlev (hR _ (hdeep _ h3))
  · exact iff_of_false (fun h => hq' (Or.inl h)) (fun h => hq' (Or.inr h))

include hlev hR in
/-- **The partition of unity agrees** at a site within `6 M₁ L^{k+1}` of a deep base. -/
theorem chi_eq_of_deep {z : CTorus d L N₁ m₁ (k + 1)}
    (hdeep : ∀ y, supDist y z ≤ 8 * L ^ (k + 1 + m₁) → y ∈ R) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : supDist x z ≤ 6 * L ^ (k + 1 + m₁)) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    chi H q x = chi H' q x := by
  refine chi_congr_of_active (fun q' hq' => ?_) q
  by_cases hq'' : q' ∈ cubeIdx H ∨ q' ∈ cubeIdx H'
  · have hle := (le_of_mem_cubeIdx_either hq'').2
    have h1 := supDist_le_of_cubeBump_ne_zero hle hq'
    have h3 : supDist q'.2 z ≤ 8 * L ^ (k + 1 + m₁) := by
      have := supDist_triangle q'.2 x z
      rw [supDist_comm q'.2 x] at this
      omega
    exact mem_cubeIdx_iff_of_top hlev (hR _ (hdeep _ h3))
  · exact iff_of_false (fun h => hq'' (Or.inl h)) (fun h => hq'' (Or.inr h))

include hlev hR hM in
/-- The thickened cube of a deep centre is a box inside `Ω₁` of both generating sets. -/
theorem hatI_eq_hatBox_of_deep {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx H)
    (hdeep : ∀ z, supDist z q.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    hatI H q = hatBox q ∧ hatI H' q = hatBox q := by
  classical
  have hq1 := fst_eq_of_mem_cubeIdx_level hlev hq
  constructor
  · unfold hatI
    exact Finset.filter_true_of_mem fun y _ => (hlev y).1
  · unfold hatI
    refine Finset.filter_true_of_mem fun y hy => ?_
    have h := supDist_le_of_mem_hatBox_top hM hq1 hy
    exact H'.Ω_antitone le_rfl (by omega) (by omega)
      (hR _ (hdeep _ (h.trans (Nat.mul_le_mul_right _ (by norm_num)))))

/-! ### General parameters whose switched-on cubes are deep -/

section GenParams

variable {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

include hlev hR hM in
/-- **The cut factor of a deep centre is the same for the two covers**, for parameters agreeing at
the cubes with base in `R`. -/
theorem sProd_cross_of_deep (hag : ∀ P ∈ cubeIdx H, P.2 ∈ R → s' P = s P)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx H)
    (hdeep : ∀ z, supDist z q.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    sProd H s q = sProd H' s' q := by
  have hQ := qset_eq_of_deep hlev hR hM hq hdeep
  rw [← Dec2.sProd_self, ← Dec2.sProd_self]
  unfold DecCover.sProd
  rw [← hQ]
  refine Finset.prod_congr rfl fun P hP => ?_
  obtain ⟨hPc, y, hy, hbox⟩ := (DecCover.mem_Qset _).1 hP
  have h1 := supDist_le_of_sameCell_cube ((mem_cubeIdx H).1 hPc).1.2 hy
  have h2 := supDist_le_of_mem_hatBox_top hM (fst_eq_of_mem_cubeIdx_level hlev hq)
    (mem_boxSet.2 hbox)
  have h3 : supDist P.2 q.2 ≤ 8 * L ^ (k + 1 + m₁) := by
    have := supDist_triangle P.2 y q.2
    rw [supDist_comm P.2 y] at this
    omega
  exact (hag P hPc (hdeep _ h3)).symm

/-- An active centre has its own cube switched on. -/
theorem param_ne_zero_of_active {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {r : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (hne : sProd G r q ≠ 0) : r q ≠ 0 :=
  fun h0 => hne (Finset.prod_eq_zero (self_mem_Qset_zeroCuts hq) h0)

include hlev hR hM in
/-- **The active centres of the two covers coincide** when the switched-on cubes of both sides are
deep and the parameters agree at the cubes with base in `R`. -/
theorem zs_cross_of_deep
    (hon : ∀ P ∈ cubeIdx H, s P ≠ 0 → ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    (hon' : ∀ P ∈ cubeIdx H', s' P ≠ 0 → ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    (hag : ∀ P ∈ cubeIdx H, P.2 ∈ R → s' P = s P) : Zs H s = Zs H' s' := by
  classical
  have h0 : ∀ q : ℕ × CTorus d L N₁ m₁ (k + 1), supDist q.2 q.2 ≤ 8 * L ^ (k + 1 + m₁) := by
    intro q; rw [supDist_self]; exact Nat.zero_le _
  ext q
  constructor
  · intro hq
    obtain ⟨hqc, hne⟩ := Finset.mem_filter.1 hq
    have hd := hon q hqc (param_ne_zero_of_active hqc hne)
    refine Finset.mem_filter.2 ⟨(mem_cubeIdx_iff_of_top hlev (hR _ (hd _ (h0 q)))).1 hqc, ?_⟩
    rw [← sProd_cross_of_deep hlev hR hM hag hqc hd]
    exact hne
  · intro hq
    obtain ⟨hqc', hne⟩ := Finset.mem_filter.1 hq
    have hd := hon' q hqc' (param_ne_zero_of_active hqc' hne)
    have hqc : q ∈ cubeIdx H := (mem_cubeIdx_iff_of_top hlev (hR _ (hd _ (h0 q)))).2 hqc'
    refine Finset.mem_filter.2 ⟨hqc, ?_⟩
    rw [sProd_cross_of_deep hlev hR hM hag hqc hd]
    exact hne

include hlev hR hM in
/-- **The regions `Yreg` of the two covers coincide** (hypotheses of `zs_cross_of_deep`). -/
theorem yreg_cross_of_deep
    (hon : ∀ P ∈ cubeIdx H, s P ≠ 0 → ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    (hon' : ∀ P ∈ cubeIdx H', s' P ≠ 0 → ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    (hag : ∀ P ∈ cubeIdx H, P.2 ∈ R → s' P = s P) : Yreg H s = Yreg H' s' := by
  classical
  unfold Yreg
  rw [← zs_cross_of_deep hlev hR hM hon hon' hag]
  ext x
  simp only [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨q, hq, hx⟩, -⟩
    refine ⟨⟨q, hq, hx⟩, ?_⟩
    obtain ⟨hqc, hne⟩ := Finset.mem_filter.1 hq
    rw [← (hatI_eq_hatBox_of_deep hlev hR hM hqc
      (hon q hqc (param_ne_zero_of_active hqc hne))).2] at hx
    exact (Finset.mem_filter.1 hx).2
  · rintro ⟨⟨q, hq, hx⟩, -⟩
    exact ⟨⟨q, hq, hx⟩, (hlev x).1⟩

include hlev hM in
/-- A site of `Yreg` lies within `4 M₁ L^{k+1}` of the base of an active centre. -/
theorem exists_active_near_of_mem_yreg {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Yreg H s) :
    ∃ q ∈ cubeIdx H, sProd H s q ≠ 0 ∧ supDist x q.2 ≤ 4 * L ^ (k + 1 + m₁) := by
  classical
  unfold Yreg at hx
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.1 (Finset.mem_filter.1 hx).1
  obtain ⟨hqc, hne⟩ := Finset.mem_filter.1 hq
  exact ⟨q, hqc, hne, supDist_le_of_mem_hatBox_top hM (fst_eq_of_mem_cubeIdx_level hlev hqc) hxq⟩

end GenParams

/-! ### The cut points -/

/-- The cubes of a cut set are its patches. -/
theorem mem_patches_iff {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {I : Finset (cubeIdx G)}
    {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx G) :
    (⟨P, hP⟩ : cubeIdx G) ∈ I ↔ P ∈ patches I := by
  rw [mem_patches]
  constructor
  · intro h; exact ⟨hP, h⟩
  · rintro ⟨_, h⟩; exact h

/-- A cube switched on at the extended cut point `1_I` is a cube of `I`. -/
theorem mem_patches_of_extS_cutPt_ne_zero {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {I : Finset (cubeIdx G)} {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx G)
    (hne : extS G (cutPt I) P ≠ 0) : P ∈ patches I := by
  classical
  refine (mem_patches_iff hP).1 ?_
  by_contra hI
  exact hne (by simp only [extS, hP, ↓reduceDIte, cutPt, hI, ite_false])

/-- **The extended cut points agree** at a pair which is a cube of both covers or of neither, for
cut sets with the same cubes. -/
theorem extS_cutPt_cross {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')}
    (hII' : patches I = patches I') {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ cubeIdx H ↔ P ∈ cubeIdx H') : extS H (cutPt I) P = extS H' (cutPt I') P := by
  classical
  unfold extS
  by_cases h : P ∈ cubeIdx H
  · have h' := hP.1 h
    simp only [h, h', ↓reduceDIte]
    unfold cutPt
    have e : (⟨P, h⟩ : cubeIdx H) ∈ I ↔ (⟨P, h'⟩ : cubeIdx H') ∈ I' := by
      rw [mem_patches_iff, mem_patches_iff, hII']
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (e.1 h1) h2
    · exact absurd (e.2 h2) h1
    · rfl
  · have h' : P ∉ cubeIdx H' := fun h2 => h (hP.2 h2)
    simp only [h, h', ↓reduceDIte]

include hlev hR in
/-- The extended cut points agree at the cubes with base in `R`. -/
theorem extS_cutPt_agree {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')}
    (hII' : patches I = patches I') :
    ∀ P ∈ cubeIdx H, P.2 ∈ R → extS H' (cutPt I') P = extS H (cutPt I) P :=
  fun _ _ hPR => (extS_cutPt_cross hII' (mem_cubeIdx_iff_of_top hlev (hR _ hPR))).symm

include hlev hR hM in
/-- **The cut factor of a deep centre is the same at the two cut points.** -/
theorem sProd_cutPt_cross {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')}
    (hII' : patches I = patches I') {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx H)
    (hdeep : ∀ z, supDist z q.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    sProd H (extS H (cutPt I)) q = sProd H' (extS H' (cutPt I')) q :=
  sProd_cross_of_deep hlev hR hM (extS_cutPt_agree hlev hR hII') hq hdeep

/-- An active centre at the cut point `1_I` is a cube of `I`. -/
theorem mem_patches_of_mem_Zs_cutPt {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {I : Finset (cubeIdx G)} {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ Zs G (extS G (cutPt I))) : q ∈ patches I := by
  obtain ⟨hqc, hsub⟩ := mem_Zs_cutPt_iff.1 hq
  exact (mem_patches_iff hqc).1 (hsub (mem_QsetP.2 (self_mem_Qset_zeroCuts hqc)))

include hlev hR hM in
/-- **The active centres at the two cut points coincide** (cut sets with the same deep cubes). -/
theorem zs_cutPt_cross {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')}
    (hII' : patches I = patches I')
    (hdeep : ∀ P ∈ patches I, ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    Zs H (extS H (cutPt I)) = Zs H' (extS H' (cutPt I')) :=
  zs_cross_of_deep hlev hR hM
    (fun P hP hne => hdeep P (mem_patches_of_extS_cutPt_ne_zero hP hne))
    (fun P hP hne => hdeep P (hII' ▸ mem_patches_of_extS_cutPt_ne_zero hP hne))
    (extS_cutPt_agree hlev hR hII')

include hlev hR hM in
/-- **The regions `Yreg` at the two cut points coincide.** -/
theorem yreg_cutPt_cross {I : Finset (cubeIdx H)} {I' : Finset (cubeIdx H')}
    (hII' : patches I = patches I')
    (hdeep : ∀ P ∈ patches I, ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    Yreg H (extS H (cutPt I)) = Yreg H' (extS H' (cutPt I')) :=
  yreg_cross_of_deep hlev hR hM
    (fun P hP hne => hdeep P (mem_patches_of_extS_cutPt_ne_zero hP hne))
    (fun P hP hne => hdeep P (hII' ▸ mem_patches_of_extS_cutPt_ne_zero hP hne))
    (extS_cutPt_agree hlev hR hII')

include hlev hM in
/-- **The region `Yreg` lies near the cubes of the cut set**: a site of `Yreg` at `1_I` is within
`4 M₁ L^{k+1}` of the base of a cube of `I`. -/
theorem exists_patch_near_of_mem_yreg {I : Finset (cubeIdx H)} {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ Yreg H (extS H (cutPt I))) :
    ∃ P ∈ patches I, supDist x P.2 ≤ 4 * L ^ (k + 1 + m₁) := by
  classical
  unfold Yreg at hx
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.1 (Finset.mem_filter.1 hx).1
  have hqc : q ∈ cubeIdx H := (Finset.mem_filter.1 hq).1
  exact ⟨q, mem_patches_of_mem_Zs_cutPt hq,
    supDist_le_of_mem_hatBox_top hM (fst_eq_of_mem_cubeIdx_level hlev hqc) hxq⟩

end Geom

end Balaban.Fluctuation
