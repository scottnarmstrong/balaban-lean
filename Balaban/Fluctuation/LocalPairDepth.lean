/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairLevelInner
public import Balaban.Localization.P6PairLocFinal

/-!
# The replacement at the local generator: depth from a margin, and one pair of constants

The abstract replacement identity `coef_eTermFun_replacement_cross` compares the term of the ambient
pairs `(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, `(coverOf 𝔹_{k+1}, 𝔹_k)` with the term of the local pairs
`(coverOf 𝔹_{k+1}(Y), 𝔹_{k+1}(Y))`, `(coverOf 𝔹_{k+1}(Y), 𝔹_k(Y))` under component hypotheses on
sets `T_b ⊆ Y_b`, `T_f ⊆ Y_f` and cover-base hypotheses with one pair of constants `(K_c, C_χ)`.
Here `𝔹_{k+1}` and `𝔹_k` are level sets (`IsLevel`), `𝔹_{k+1}(Y) = localB (k + 1) … Y` and
`𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))`, and the parameters are those of Lemma AE: `σ w =
extParams 𝔹_{k+1} X₁ w` for `w` supported on a family `𝒞` of cubes disjoint from `X₁`, and its
transport `τ w` (`σ w` at the cubes of `𝔹_{k+1}(Y)` with base in the top layer, `0` at the others).

**Depth.**  Let `R` be a set of sites containing the cubes of `𝒞`, the cubes meeting `X₁` and the
data sites of the term generator `𝔹_k(X)` (the read region of the term), and suppose the margin
`d_∞(R, y) ≤ 3 M₁ L^{k+1} ⇒ y ∈ Ω_{k+1}(𝔹_{k+1}(Y))` (the `𝒞_{k+1}`-cube of `y` lies in `Y`).
Then all component hypotheses hold with `T_b = T_f = R` and `Y_b = Y_f` the sites within
`M₁ L^{k+1}` of `R`: every cube with a non-zero factor has its thickened cube `□̂_z` inside `R`
(`level_hatBox_subset_of_active`), so the dichotomy and row hypotheses hold on the side of the
ambient pairs, and the local side follows from the IndexMatch lemmas of
`LocalPairLevelInner.lean`.

* `supDist_le_of_sameCell`, `supDist_le_of_bump_ne_zero`, `supDist_le_of_mem_blk`: distances;
* `isLevel_top_mem_Ω`, `isLevel_top_cubeAligned`, `isLevel_top_supSep`, `isLevel_top_precedes`:
  a level set of the top level;
* `level_coverBase_mixed`, `localB_replacement_coverBases`: the four cover bases with the constants
  `(mixedKc d L, Cchi d L)` (deliverable (2));
* `level_hatBox_subset_of_active`, `localB_top_of_margin`, the depth lemmas
  `localB_depth_*` (deliverable (1)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation

/-! ### Distances -/

section Dist

variable {d n : ℕ} [NeZero n]

/-- Two sites in one cell of side `a > 0` are at sup-distance at most `a`. -/
theorem supDist_le_of_sameCell {a : ℕ} (ha : 0 < a) {x y : Torus d n} (h : SameCell a x y) :
    supDist x y ≤ a := by
  refine supDist_le_of_lift (fun μ => ((x μ).val : ℤ)) (fun μ => ((y μ).val : ℤ))
    (fun μ => by simp) (fun μ => by simp) fun μ => ?_
  have h1 := Nat.div_add_mod (x μ).val a
  have h2 := Nat.div_add_mod (y μ).val a
  have h3 := Nat.mod_lt (x μ).val ha
  have h4 := Nat.mod_lt (y μ).val ha
  rw [h μ] at h1
  omega

end Dist

section Bump

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- **The support of a block bump**: `b_{m, y₀}(x) ≠ 0` puts `x` within sup-distance `2 L^m` of the
base `y₀`. -/
theorem supDist_le_of_bump_ne_zero {m : ℕ} {y0 x : Torus d (N₀ * L ^ k)}
    (h : bump m y0 x ≠ 0) : supDist x y0 ≤ 2 * L ^ m := by
  have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hper : ∀ μ, ∃ p : ℤ, |(((x μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m +
      p * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m)| < 3 / 2 := fun μ =>
    exists_of_perN_ne_zero (Finset.prod_ne_zero_iff.1 h μ (mem_univ μ))
  choose p hp using hper
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ m :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  refine supDist_le_of_lift (fun μ => ((x μ).val : ℤ) + p μ * ((N₀ * L ^ k : ℕ) : ℤ))
    (fun μ => ((y0 μ).val : ℤ)) (fun μ => ?_) (fun μ => by simp) fun μ => ?_
  · show ((((x μ).val : ℤ) + p μ * ((N₀ * L ^ k : ℕ) : ℤ) : ℤ) : ZMod (N₀ * L ^ k)) = x μ
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
      ZMod.natCast_zmod_val]
  · have h1 := hp μ
    have e : (((x μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m +
        p μ * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) =
        (((x μ).val : ℝ) - bumpCentre m y0 μ + p μ * ((N₀ * L ^ k : ℕ) : ℝ)) / (L : ℝ) ^ m := by
      field_simp
    rw [e, abs_div, abs_of_pos hlam, div_lt_iff₀ hlam, abs_lt] at h1
    unfold bumpCentre at h1
    show (((x μ).val : ℤ) + p μ * ((N₀ * L ^ k : ℕ) : ℤ) - ((y0 μ).val : ℤ)).natAbs ≤ 2 * L ^ m
    have e2 : ((((x μ).val : ℤ) + p μ * ((N₀ * L ^ k : ℕ) : ℤ) - ((y0 μ).val : ℤ)).natAbs : ℝ) =
        |((x μ).val : ℝ) + p μ * ((N₀ * L ^ k : ℕ) : ℝ) - (y0 μ).val| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    have h3 : ((((x μ).val : ℤ) + p μ * ((N₀ * L ^ k : ℕ) : ℤ) - ((y0 μ).val : ℤ)).natAbs : ℝ) ≤
        ((2 * L ^ m : ℕ) : ℝ) := by
      rw [e2, abs_le]
      push_cast at h1 ⊢
      constructor <;> linarith [h1.1, h1.2]
    exact_mod_cast h3

/-- **The sites of a block are close**: a site of the block `B_j(x)`, `j ≤ K`, is within
sup-distance `L^j` of `x`. -/
theorem supDist_le_of_mem_blk {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {j : ℕ} (hj : j ≤ k)
    {x y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.blk j x) : supDist x y ≤ L ^ j :=
  supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
    (sameCell_of_jBlock_eq hj (GeneratingSet.mem_blk.1 hy)).symm

end Bump

/-! ### Level sets of the top level -/

section Level

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ}

/-- A level set of the top level `K` has `Ω_j` the whole torus for `1 ≤ j ≤ K`. -/
theorem isLevel_top_mem_Ω (h : IsLevel G K) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (x : Torus d (N₀ * L ^ K)) : x ∈ G.Ω j :=
  G.Ω_antitone hj1 hj (by omega) ((G.mem_layer).1 (h.mem_layer x)).1

/-- Every generating set precedes a level set of the top level. -/
theorem isLevel_top_precedes (h : IsLevel G K) {ϱ' : ℝ} (H : GeneratingSet d L N₀ K ϱ') :
    Precedes H G :=
  fun _ hi hiK x _ => isLevel_top_mem_Ω h hi hiK x

end Level

section LevelCube

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- A level set of the top level is cube aligned (`m₁ ≥ 2`). -/
theorem isLevel_top_cubeAligned (h : IsLevel G K) (hm₁ : 2 ≤ m₁) : CubeAligned G m₁ where
  two_le := hm₁
  dvd := dvd_mul_left _ _
  union _ hj1 hjK x x' _ := iff_of_true (isLevel_top_mem_Ω h hj1 hjK x) (isLevel_top_mem_Ω h hj1 hjK x')

/-- A level set of the top level is sup-separated (no site lies outside `Ω_j`, `j < K`). -/
theorem isLevel_top_supSep (h : IsLevel G K) : SupSep G m₁ :=
  fun _ hj1 hjK x hx => absurd (isLevel_top_mem_Ω h hj1 hjK.le x) hx

/-- **The cover base of a level set of the top level, with the mixed constants**: for every operator
generating set `H` on the same torus, `Dec2.CoverBase (coverOf 𝔹) H a ν (mixedKc d L) (Cchi d L)`
(`p6_coverGeom_of_pair`, `Dec2.coverBase_mixed`), under `N₁ > 5`, `m₁ ≥ 2`, `M₁ ≥ 4 L²` and the
operator conditions of `H`. -/
theorem level_coverBase_mixed (h : IsLevel G K) {ϱH : ℝ}
    (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱH) (hN : 5 < N₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (ha : IsAdmissibleWeights K a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱH - 1)) :
    Dec2.CoverBase (coverOf G) H a ν (Dec2.mixedKc d L) (Cchi d L) :=
  Dec2.coverBase_mixed hN G (p6_coverGeom_of_pair (isLevel_top_cubeAligned h hm₁) (isLevel_top_supSep h)
    (isLevel_top_precedes h H) hM
    hd hL hν hνL ha hag) hνL (fun _ hq => hq)

end LevelCube

/-! ### Read sites near a site -/

section Reads

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The sites `resSites G x` read by the residual at `x` (the site, its block and its nearest
neighbours) are within sup-distance `L^K` of `x`. -/
theorem supDist_le_of_mem_resSites {x y : Torus d (N₀ * L ^ K)} (hy : y ∈ resSites G x) :
    supDist x y ≤ L ^ K := by
  classical
  have hLK : 1 ≤ L ^ K := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold resSites at hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · rw [supDist_self]; exact Nat.zero_le _
  rcases Finset.mem_union.1 hy with hy | hy
  · rcases Finset.mem_union.1 hy with hy | hy
    · exact (supDist_le_of_mem_blk (layerIndex_le_of_Ω_empty G G.top x) hy).trans
        (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L))
          (layerIndex_le_of_Ω_empty G G.top x))
    · obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 hy
      exact (supDist_add_single_le x μ).trans hLK
  · obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 hy
    exact (supDist_sub_single_le x μ).trans hLK

/-- The sites `approxDep G x` whose data enter the approximate field at `x` (the site and the
bases of the blocks active at `x`) are within sup-distance `2 L^K` of `x`. -/
theorem supDist_le_of_mem_approxDep {x z : Torus d (N₀ * L ^ K)} (hz : z ∈ approxDep G x) :
    supDist x z ≤ 2 * L ^ K := by
  classical
  unfold approxDep at hz
  rcases Finset.mem_insert.1 hz with rfl | hz
  · rw [supDist_self]; exact Nat.zero_le _
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨hqi, hne⟩ := (mem_active G).1 hq
  have hqK : q.1 ≤ K := ((mem_blockIdx G).1 hqi).1.2
  exact (supDist_le_of_bump_ne_zero hne).trans (Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hqK))

end Reads

/-! ### Depth inside the local generator -/

section Depth

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The thickened cube of an active ambient cube lies in the read region.**  Let `𝔹_{k+1}` be a
level set, `w` a vector of parameters supported on a family `𝒞` of cubes disjoint from `X₁`, and
`R` a set of sites containing every cube of `𝒞` and every cube meeting `X₁`.  If the factor
`s_z = ∏_{P ∈ 𝒬(z)} s_P` of `s = extParams 𝔹_{k+1} X₁ w` does not vanish, every site of `□̂_z` lies in
`R`: its own cube is in `𝒬(z)`, so its parameter does not vanish, so it is a cube of `𝒞` or meets
`X₁`. -/
theorem level_hatBox_subset_of_active (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hne : (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) : y ∈ R := by
  classical
  have hP : ((k + 1, ownBase (k + 1 + m₁) y) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈ cubeIdx Gp :=
    own_mem_cubeIdx (isLevel_top_cubeAligned hG' hm₁) (by omega) le_rfl (hG'.mem_layer y)
  have hsc : SameCell (L ^ (k + 1 + m₁)) y (ownBase (k + 1 + m₁) y) := ownBase_sameCell y
  have hQ : ((k + 1, ownBase (k + 1 + m₁) y) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈
      (coverOf Gp).Qset q :=
    (DecCover.mem_Qset _).2 ⟨hP, y, hsc, hy⟩
  have hne' : Dec2.extS (coverOf Gp) (extParams Gp X₁ w) (k + 1, ownBase (k + 1 + m₁) y) ≠ 0 :=
    fun h0 => hne (Finset.prod_eq_zero hQ h0)
  have hyP : y ∈ Pset m₁ ((k + 1, ownBase (k + 1 + m₁) y) : ℕ × CTorus d L N₁ m₁ (k + 1)) := hsc
  have hP' : ((k + 1, ownBase (k + 1 + m₁) y) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈
      (coverOf Gp).cubeIdx := hP
  unfold Dec2.extS at hne'
  rw [dite_eq_left hP'] at hne'
  unfold extParams at hne'
  split_ifs at hne' with hdis
  · by_cases hC : (⟨⟨_, hP⟩, hdis⟩ : ParIdx Gp X₁) ∈ C
    · exact hRC _ hC y hyP
    · exact absurd (hw _ hC) hne'
  · exact hRX _ hP hdis y hyP

/-- The interaction cube `□_z` of an active ambient cube lies in the read region
(`□_z ⊆ □̂_z`). -/
theorem level_intBox_subset_of_active (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hne : (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q) : x ∈ R := by
  refine level_hatBox_subset_of_active hG' hm₁ hRC hRX hw hne ((mem_intBox.1 hx).mono ?_)
  unfold hatRad
  have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
  linarith

/-- The base of an active ambient cube lies in the read region. -/
theorem level_base_mem_of_active (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hne : (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0) : q.2 ∈ R := by
  refine level_hatBox_subset_of_active hG' hm₁ hRC hRX hw hne (inBox_centre q.1 q.2 ?_)
  unfold hatRad
  have hB : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
  linarith

end Depth

/-! ### The transport `τ` of the parameters -/

section Tau

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The transport `τ` vanishes off the top layer**: `τ s` (the parameter `s_P` at the cubes of
`𝔹_{k+1}(Y)` with base in `Ω_{k+1}(𝔹_{k+1}(Y))`, `0` at the others) is `0` at a cube of the cover of
`𝔹_{k+1}(Y)` whose base is not in the top layer. -/
theorem localB_tau_off_top (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) (s : Dec2.DecParams (coverOf Gp)) :
    ∀ P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      P.2 ∉ (localB (k + 1) hk Y hsep).Ω (k + 1) →
        Dec2.extS (coverOf (localB (k + 1) hk Y hsep))
          (fun P => if P.1.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) then
            Dec2.extS (coverOf Gp) s P.1 else 0) P = 0 := by
  intro P hP hPt
  unfold Dec2.extS
  rw [dite_eq_left hP]
  exact ite_eq_right hPt

/-- **The transport `τ` agrees with `s` on the top layer** (`𝔹_{k+1}` a level set): at a pair
`P` with base in `Ω_{k+1}(𝔹_{k+1}(Y))` the extended parameters of `τ s` (cover of `𝔹_{k+1}(Y)`) and
of `s` (cover of `𝔹_{k+1}`) coincide; the pair is a cube of both covers or of neither. -/
theorem localB_tau_top (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    (s : Dec2.DecParams (coverOf Gp)) :
    ∀ P : ℕ × CTorus d L N₁ m₁ (k + 1), P.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) →
      Dec2.extS (coverOf (localB (k + 1) hk Y hsep))
          (fun P => if P.1.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) then
            Dec2.extS (coverOf Gp) s P.1 else 0) P =
        Dec2.extS (coverOf Gp) s P := by
  intro P hP
  by_cases hc : P ∈ (coverOf (localB (k + 1) hk Y hsep)).cubeIdx
  · unfold Dec2.extS
    rw [dite_eq_left hc]
    exact ite_eq_left hP
  · have hc' : P ∉ (coverOf Gp).cubeIdx := fun h =>
      hc ((level_localB_mem_cubeIdx_iff hG' hk Y hsep ((mem_localB_Ω_top P.2).1 hP)).1 h)
    unfold Dec2.extS
    rw [dite_eq_right hc, dite_eq_right hc']

/-- **The transport `τ` keeps the polydisc**: if `|s_P| < r` for all cubes and `1 < r`, then
`|(τ s)_P| < r`. -/
theorem localB_tau_norm_lt (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {s : Dec2.DecParams (coverOf Gp)} {r : ℝ}
    (hs : ∀ P, ‖s P‖ < r) (hr : 1 < r) :
    ∀ P : ↥(coverOf (localB (k + 1) hk Y hsep)).cubeIdx,
      ‖(fun P : ↥(coverOf (localB (k + 1) hk Y hsep)).cubeIdx =>
        if P.1.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) then
          Dec2.extS (coverOf Gp) s P.1 else 0) P‖ < r := by
  intro P
  simp only
  split_ifs
  · unfold Dec2.extS
    split_ifs
    · exact hs _
    · simpa using hr
  · simpa using (zero_lt_one.trans hr)

end Tau

/-! ### Layers at the top layer of the local generator -/

section TopLayers

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl ϱl' ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- At a site of the top layer `Ω_{k+1}(𝔹_{k+1}(Y))`, the level set `𝔹_{k+1}` and `𝔹_{k+1}(Y)` have
the same layers. -/
theorem level_localB_layer_iff_of_top (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) :
    ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Gp.layer n ↔ x ∈ (localB (k + 1) hk Y hsep).layer n) :=
  fun _ hn hnK => level_localB_layer_iff hG' hk Y hsep ((mem_localB_Ω_top x).1 hx) hn hnK

/-- `Ω_k(𝔹_{k+1}(Y))` lies in `Ω₁(𝔹_k(Y))`, `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))` (`k ≥ 1`). -/
theorem localB_drop_Ω_one_of_mem (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (hk' : k ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    (hsep' : ϱl' ≤ minSep L (L ^ m₁)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ (localB (k + 1) hk Y hsep).Ω k) :
    x ∈ (localB k hk' (↑((localB (k + 1) hk Y hsep).Ω k) : Set (CTorus d L N₁ m₁ (k + 1)))
      hsep').Ω 1 := by
  have h := localB_drop_Ω hk hk' Y hsep hsep' (le_refl k)
  refine (localB k hk' (↑((localB (k + 1) hk Y hsep).Ω k) : Set (CTorus d L N₁ m₁ (k + 1)))
      hsep').Ω_antitone le_rfl hk1 (by omega) ?_
  rw [h]; exact hx

/-- At a site of the top layer `Ω_{k+1}(𝔹_{k+1}(Y))`, a level set `𝔹_k` and the local fluctuation
generator `𝔹_k(Y)` have the same layers (`k ≥ 1`). -/
theorem localB_drop_layer_iff_of_top (hG : IsLevel Hm k) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (hk' : k ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    (hsep' : ϱl' ≤ minSep L (L ^ m₁)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) :
    ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Hm.layer n ↔
      x ∈ (localB k hk' (↑((localB (k + 1) hk Y hsep).Ω k) : Set (CTorus d L N₁ m₁ (k + 1)))
        hsep').layer n) := by
  intro n hn hnK
  have hxk : x ∈ (localB k hk' (↑((localB (k + 1) hk Y hsep).Ω k) :
      Set (CTorus d L N₁ m₁ (k + 1))) hsep').Ω k := by
    rw [localB_drop_Ω hk hk' Y hsep hsep' (le_refl k)]
    exact (localB (k + 1) hk Y hsep).Ω_antitone hk1 (Nat.le_succ k) (by omega) hx
  exact layer_iff_of_level_of_top hG (localB_drop_top hk hk' Y hsep hsep') hxk hn hnK

end TopLayers

/-! ### Depth from a margin -/

section Margin

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl ϱH ϱH' ϱ₁ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

omit [NeZero N₁] [NeZero L] in
/-- The top cube side `M₁ L^n` is at least `2 L^n` when `M₁ = L^{m₁} ≥ 2`. -/
theorem two_mul_pow_le_pow_add (hM2 : 2 ≤ L ^ m₁) (n : ℕ) : 2 * L ^ n ≤ L ^ (n + m₁) := by
  rw [pow_add]
  calc 2 * L ^ n = L ^ n * 2 := by ring
    _ ≤ L ^ n * L ^ m₁ := Nat.mul_le_mul_left _ hM2

/-- **The sites near `Y_b` are in the top layer.**  Under the margin `d_∞(R, y) ≤ 2 M₁ L^{k+1} ⇒
y ∈ Ω_{k+1}(𝔹_{k+1}(Y))`, a site within `M₁ L^{k+1}` of a site of `Y_b` (itself within
`M₁ L^{k+1}` of `R`) lies in the top layer. -/
theorem localB_top_of_near (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hYR : ∀ y ∈ Yb, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁))
    {y z : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ Yb) (hz : supDist y z ≤ L ^ (k + 1 + m₁)) :
    z ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := by
  obtain ⟨x, hx, hxy⟩ := hYR y hy
  exact hmar x hx z ((supDist_triangle x y z).trans (by omega))

/-- The sites of `Y_b` are in the top layer. -/
theorem localB_top_of_mem (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hYR : ∀ y ∈ Yb, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁))
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ Yb) : y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) :=
  localB_top_of_near hk Y hsep hmar hYR hy (by rw [supDist_self]; exact Nat.zero_le _)

/-- **Depth, dichotomy.**  Every interaction cube of an active ambient cube lies in the read region
`R` (for any operator generating set `H`). -/
theorem localB_depth_dich (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH) {w : ParIdx Gp X₁ → ℂ}
    (hw : w ∈ supportedOn C) :
    ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0 →
        SubI H (intBox q) R ∨ DisjI H (intBox q) R :=
  fun _ _ hne => Or.inl fun _ hx =>
    level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx

/-- **Depth, rows.**  A site of any set `Y_c` in the interaction cube of an active ambient cube
lies in the read region `R`. -/
theorem localB_depth_row (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (Yc : Finset (CTorus d L N₁ m₁ (k + 1))) {w : ParIdx Gp X₁ → ℂ}
    (hw : w ∈ supportedOn C) :
    ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0 →
        ∀ x ∈ Yc, x ∈ intBox q → x ∈ R :=
  fun _ _ hne _ _ hx => level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx

/-- **Depth, the inner cubes.**  For an active ambient cube with interaction cube in `R`: the
layers of `H`, `H'` agree on the stencil of `□_z` (given that they agree on the top layer), its base
is in the top layer, the bases of the cubes (of either cover) whose bump does not vanish on `□_z`
are in the top layer, and so are those of the cubes meeting `□̂_z`.  These are the hypotheses
`hdeep` of `level_localB_inner_cross`. -/
theorem localB_depth_deep (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hst : ∀ y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1), ∀ n, 1 ≤ n → n ≤ k + 1 →
      (y ∈ H.layer n ↔ y ∈ H'.layer n))
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C) :
    ∀ q ∈ Dec2.innerCentres (coverOf Gp) H R,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0 →
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
        q.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) ∧
        (∀ x ∈ intBox q, ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
          (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
            cubeBump m₁ q'.1 q'.2 x ≠ 0 → q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) ∧
        (∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1),
          (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx (localB (k + 1) hk Y hsep)) →
            (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
              q'.2 ∈ (localB (k + 1) hk Y hsep).Ω (k + 1)) := by
  intro q _ hne
  have hM1 : 1 ≤ L ^ (k + 1 + m₁) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  refine ⟨fun x hx y hy => hst y ?_, ?_, fun x hx q' hq' hb => ?_, ?_⟩
  · have hxR := level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx
    refine hmar x hxR y ?_
    rcases hy with rfl | ⟨μ, rfl | rfl⟩
    · rw [supDist_self]; exact Nat.zero_le _
    · exact (supDist_add_single_le x μ).trans (by omega)
    · exact (supDist_sub_single_le x μ).trans (by omega)
  · exact hmar _ (level_base_mem_of_active hG' hm₁ hRC hRX hw hne) _
      (by rw [supDist_self]; exact Nat.zero_le _)
  · have hxR := level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx
    have hj : q'.1 ≤ k + 1 := by
      rcases hq' with h | h
      · exact ((mem_cubeIdx _).1 h).1.2
      · exact ((mem_cubeIdx _).1 h).1.2
    have hB : (0 : ℝ) ≤ 3 / 2 * (L : ℝ) ^ (q'.1 + m₁) := by positivity
    have hd := supDist_le_of_inBox hB (inBox_of_cubeBump_ne_zero hb)
    have hLj : (L : ℝ) ^ (q'.1 + m₁) ≤ (L : ℝ) ^ (k + 1 + m₁) :=
      pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) (by omega)
    have hd' : (supDist x q'.2 : ℝ) ≤ ((2 * L ^ (k + 1 + m₁) : ℕ) : ℝ) := by
      push_cast; linarith
    exact hmar x hxR q'.2 (by exact_mod_cast hd')
  · exact level_localB_hat_of_box hk Y hsep fun y hy =>
      hmar y (level_hatBox_subset_of_active hG' hm₁ hRC hRX hw hne hy) y
        (by rw [supDist_self]; exact Nat.zero_le _)

/-- **Depth, the residual rows of the background.**  For `x ∈ R` the sites read by the residual at
`x` are in `Ω₁(𝔹_{k+1})` and in `Y_b` (the `M₁ L^{k+1}`-neighbourhood of `R`). -/
theorem localB_depth_res_bg (hG' : IsLevel Gp (k + 1)) {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRY : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1 + m₁) → y ∈ Yb) :
    ∀ x ∈ R, x ∈ Gp.Ω 1 → ∀ y ∈ resSites Gp x, y ∈ Gp.Ω 1 ∧ y ∈ Yb :=
  fun x hx _ y hy => ⟨(hG' y).1, hRY x hx y ((supDist_le_of_mem_resSites hy).trans
    (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)))⟩

/-- **Depth, the residual rows of the fluctuation.**  For `x ∈ R` the sites read by the residual of
`H` at `x` are in `Y_f` (the `M₁ L^{k+1}`-neighbourhood of `R`), where the layers of `H` and `H'`
agree. -/
theorem localB_depth_res_fl (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hRY : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1 + m₁) → y ∈ Yb)
    (hYR : ∀ y ∈ Yb, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁))
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hst : ∀ y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1), ∀ n, 1 ≤ n → n ≤ k + 1 →
      (y ∈ H.layer n ↔ y ∈ H'.layer n)) :
    ∀ x ∈ R, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧ (y ∈ H.Ω 1 → y ∈ Yb) ∧
        y ∈ Yb := by
  intro x hx _ y hy
  have hyY : y ∈ Yb := hRY x hx y ((supDist_le_of_mem_resSites hy).trans
    (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)))
  exact ⟨hst y (localB_top_of_mem hk Y hsep hmar hYR hyY), fun _ => hyY, hyY⟩

/-- **Depth, the active blocks of the approximate field.**  At a site of `Y_b`, the bases of the
blocks whose bump does not vanish are in the top layer, where the layers of `𝔹_{k+1}` and
`𝔹_{k+1}(Y)` agree (`M₁ ≥ 2`). -/
theorem localB_depth_act (hG' : IsLevel Gp (k + 1)) (hM2 : 2 ≤ L ^ m₁) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hYR : ∀ y ∈ Yb, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁)) :
    ∀ y ∈ Yb, y ∈ Gp.Ω 1 → ∀ q : ℕ × CTorus d L N₁ m₁ (k + 1), 1 ≤ q.1 →
      q.1 ≤ k + 1 → bump q.1 q.2 y ≠ 0 →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (q.2 ∈ Gp.layer n ↔ q.2 ∈ (localB (k + 1) hk Y hsep).layer n) := by
  intro y hy _ q _ hqK hb
  have h1 := supDist_le_of_bump_ne_zero hb
  have h2 : 2 * L ^ q.1 ≤ 2 * L ^ (k + 1) :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hqK)
  have h3 := two_mul_pow_le_pow_add hM2 (k + 1)
  exact level_localB_layer_iff_of_top hG' hk Y hsep
    (localB_top_of_near hk Y hsep hmar hYR hy (by omega))

/-- **Depth, the data of the approximate field.**  At a site of `Y_b`, the sites whose data enter
the approximate field of `𝔹_{k+1}` are in the top layer (`M₁ ≥ 2`). -/
theorem localB_depth_approxDep (hM2 : 2 ≤ L ^ m₁) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱl ≤ minSep L (L ^ m₁))
    {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hYR : ∀ y ∈ Yb, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁)) :
    ∀ y ∈ Yb, ∀ z ∈ approxDep Gp y, z ∈ (localB (k + 1) hk Y hsep).Ω (k + 1) := by
  intro y hy z hz
  have h1 := supDist_le_of_mem_approxDep hz
  have h3 := two_mul_pow_le_pow_add hM2 (k + 1)
  exact localB_top_of_near hk Y hsep hmar hYR hy (by omega)

/-- **Depth, the composition.**  At a data site `x ∈ R` of the term generator `𝔹_k(X)`: the layers
of `H`, `H'` agree at `x`, and the sites read by `composeField` at `x` (the site, its block of
`𝔹_k(X)` and its block of `H`) are in `Y_b`. -/
theorem localB_depth_compose (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1))
    (hRY : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1 + m₁) → y ∈ Yb)
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH}
    {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱH'}
    (hst : ∀ y ∈ (localB (k + 1) hk Y hsep).Ω (k + 1), ∀ n, 1 ≤ n → n ≤ k + 1 →
      (y ∈ H.layer n ↔ y ∈ H'.layer n))
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁} (hRk : ∀ x ∈ dataSites Gk, x ∈ R) :
    ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ H.layer n ↔ x ∈ H'.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ H.blk (H.layerIndex x) x) → y ∈ Yb := by
  intro x hx
  have hxR := hRk x hx
  have hLM : ∀ j, j ≤ k + 1 → L ^ j ≤ L ^ (k + 1 + m₁) := fun j hj =>
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  refine ⟨hst x (hmar x hxR x (by rw [supDist_self]; exact Nat.zero_le _)), fun y hy => ?_⟩
  refine hRY x hxR y ?_
  rcases hy with rfl | hy | hy
  · rw [supDist_self]; exact Nat.zero_le _
  · exact (supDist_le_of_mem_blk (layerIndex_le_of_Ω_empty Gk Gk.top x) hy).trans
      (hLM _ (layerIndex_le_of_Ω_empty Gk Gk.top x))
  · exact (supDist_le_of_mem_blk (layerIndex_le_of_Ω_empty H H.top x) hy).trans
      (hLM _ (layerIndex_le_of_Ω_empty H H.top x))

end Margin

/-! ### One pair of constants for the four cover bases -/

section Constants

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **One pair `(K_c, C_χ)` for the ambient and the local cover bases** (deliverable (2)).  Let
`𝔹_{k+1}` be a level set (index `ϱ`) and `H⁻` any operator generating set (index `ϱ_m`).  With the
mixed-wall cut-operator constant `K_c = mixedKc d L` and `C_χ = Cchi d L`, all four pairs of the
replacement have `Dec2.CoverBase`: the ambient background pair `(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, the local
background pair `(coverOf 𝔹_{k+1}(Y), 𝔹_{k+1}(Y))`, the ambient fluctuation pair
`(coverOf 𝔹_{k+1}, H⁻)` and the local fluctuation pair `(coverOf 𝔹_{k+1}(Y), 𝔹_k(Y))`,
`𝔹_{k+1}(Y) = localB (k + 1) … Y`, `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))` at the index `5 L M₁`.
Premises: `N₁ > 5`, `m₁ ≥ 2`, `M₁ = L^{m₁} ≥ 4 L²`, the standing hypotheses `BgHyp` of the weights
and the mass, and the Agmon condition `2 d log L ≤ γ_A/16 (ϱ' - 1)` at each of the three indices
`ϱ' = ϱ, ϱ_m, 5 L M₁`.  (`Dec2.DecSpecs d L (mixedKc d L) (Cchi d L) c BG` holds for some `c, BG`:
`p6_decSpecs_exists`.) -/
theorem localB_replacement_coverBases (hG' : IsLevel Gp (k + 1))
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (HB : BgHyp d L (k + 1) ϱ a ν)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) :
    Dec2.CoverBase (coverOf Gp) Gp a ν (Dec2.mixedKc d L) (Cchi d L) ∧
    Dec2.CoverBase (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) a ν (Dec2.mixedKc d L) (Cchi d L) ∧
    Dec2.CoverBase (coverOf Gp) Hm a ν (Dec2.mixedKc d L) (Cchi d L) ∧
    Dec2.CoverBase (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (localB k (Nat.le_succ k)
        (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
      a ν (Dec2.mixedKc d L) (Cchi d L) :=
  ⟨level_coverBase_mixed hG' Gp hN hm₁ hM HB.hd HB.hL HB.mass HB.massLe HB.weights hag,
    localB_coverBase hk Y _ hN hm₁ hM HB.hd HB.hL HB.mass HB.massLe HB.weights hagl,
    level_coverBase_mixed hG' Hm hN hm₁ hM HB.hd HB.hL HB.mass HB.massLe HB.weights hagm,
    (localB_drop_pair hk Y hN hm₁ hM HB.hd HB.hL HB.mass HB.massLe HB.weights
      hagl).2.2.1.toCoverBase⟩

end Constants

end Balaban.Localization
