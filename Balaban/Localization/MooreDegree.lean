/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LedgerCounter
public import Balaban.Localization.LedgerPacking
public import Balaban.Localization.MooreDegreeGrid
public import Balaban.Localization.P6PairOp
public import Balaban.Localization.P6PairHalo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Degree of the Moore graph of a cube-aligned cover (VMOD-24 Lemma 3.1)

Source: `notes/phase1/VMOD-24.md` §3, (3.1)-(3.2).  `G` is a cube-aligned generating set with
separation constant `ϱ`, `cubeIdx G` its index set, `Pset m₁ P` the parameter patch of `P`.

* `cubeIdx_moore_layer_gap` (T1): if the patches of `P, Q ∈ cubeIdx G` Moore-touch then their
  layers differ by at most one, provided `d ≤ ϱ L²`; `cubeIdx_moore_layer_gap_p6` is the case
  of `p6FsharpC` (`ϱ = 5 L M₁`) under `d < 5 L³ M₁`.
* `card_gridBases_le` (in `MooreDegreeGrid`, T2): the count in one coordinate.
* `cubeIdx_moore_degree` (T3): every index has at most `3 (L + 2)^d`, hence at most
  `3 (L + 4)^d`, other indices whose patch Moore-touches its patch.
* `mooreGraph` (T4): the graph on `cubeIdx G`, with `degree ≤ 3 (L + 4)^d`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Fluctuation Balaban.Multiscale Finset

section Basic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- `Near 1 1 x y` says that `y - x` has all coordinates the residue of an integer of absolute
value at most one. -/
theorem near_one_iff {n : ℕ} {x y : Torus d n} :
    Near 1 1 x y ↔ ∃ q : Fin d → ℤ, (∀ μ, |q μ| ≤ 1) ∧ ∀ μ, y μ = x μ + (q μ : ZMod n) := by
  unfold Near
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, fun μ => by simpa using hq μ, fun μ => by simp⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨q, fun μ => by simpa using hq μ, funext fun μ => by simp [h μ]⟩

/-- Sites at `Near 1 1` are at torus `ℓ¹` distance at most `d`. -/
theorem torusDist_le_of_near {x y : CTorus d L N₁ m₁ K} (h : Near 1 1 x y) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y ≤ d := by
  obtain ⟨q, hq, hy⟩ := near_one_iff.1 h
  unfold Green.torusDist
  calc ∑ μ, ((Green.cycRep (x μ - y μ)).natAbs : ℝ) ≤ ∑ _μ : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        have e : x μ - y μ = -(q μ : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by rw [hy μ]; ring
        rw [e, Green.natAbs_cycRep_neg]
        refine (Nat.cast_le.2 (Green.natAbs_cycRep_le_of_cast _ (q μ) rfl)).trans ?_
        have := abs_le.1 (hq μ)
        have h1 : (q μ).natAbs ≤ 1 := by omega
        exact_mod_cast h1
    _ = d := by simp

omit [NeZero N₁] [NeZero L] in
/-- Moore-touching is symmetric. -/
theorem MooreTouch.symm {S S' : Set (CTorus d L N₁ m₁ K)} (h : MooreTouch S S') :
    MooreTouch S' S := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  obtain ⟨q, hq, h⟩ := near_one_iff.1 h
  refine ⟨y, hy, x, hx, near_one_iff.2 ⟨fun μ => -q μ, fun μ => by simpa using hq μ, fun μ => ?_⟩⟩
  rw [h μ]; push_cast; ring

end Basic

section Gap

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- Sites of layers `i` and `j ≥ i + 2` are at torus distance `> ϱ L ^ (i + 1)`. -/
theorem layer_far (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j)
    (hjK : j ≤ K) {x y : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer i) (hy : y ∈ G.layer j) :
    ϱ * (L : ℝ) ^ (i + 1) < Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y := by
  rw [GeneratingSet.mem_layer] at hx hy
  exact G.separation (i + 1) (by omega) (by omega) x hx.2 y
    (G.Ω_antitone (by omega) hij (by omega) hy.1)

/-- **Layer gap, general form.**  Two sites of layers `i` and `j ≥ i + 2` of a generating set
are not at distance `≤ d` if `d ≤ ϱ L ^ 2` (here `i ≥ 1`). -/
theorem layer_not_near (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjK : j ≤ K) {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ G.layer i) (hy : y ∈ G.layer j) :
    ¬ Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y ≤ d := by
  intro hle
  have h := layer_far G hi hij hjK hx hy
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne (n := L))
  have hϱ0 : 0 ≤ ϱ := by
    by_contra hneg
    have : ϱ * (L : ℝ) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) (by positivity)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have : ϱ * (L : ℝ) ^ 2 ≤ ϱ * (L : ℝ) ^ (i + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) hϱ0
  linarith

/-- A site of the patch of an index lies in the layer of the index. -/
theorem mem_layer_of_mem_Pset {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : CubeAligned G m₁)
    {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ cubeIdx G) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ Pset m₁ P) : x ∈ G.layer P.1 := by
  obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_cubeIdx G).1 hP
  exact (hG.mem_layer_iff h1 hK hx).2 hl

/-- **T1 (VMOD-24 Lemma 3.1, layer gap).**  If the patches of two indices of a cube-aligned cover
Moore-touch, their layers differ by at most one; the premise is `d ≤ ϱ L ^ 2`. -/
theorem cubeIdx_moore_layer_gap {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hG : CubeAligned G m₁) (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) {P Q : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx G) (hQ : Q ∈ cubeIdx G) (h : MooreTouch (Pset m₁ P) (Pset m₁ Q)) :
    P.1 ≤ Q.1 + 1 ∧ Q.1 ≤ P.1 + 1 := by
  obtain ⟨x, hx, y, hy, hn⟩ := h
  have hdist := torusDist_le_of_near hn
  have hxl := mem_layer_of_mem_Pset hG hP hx
  have hyl := mem_layer_of_mem_Pset hG hQ hy
  obtain ⟨⟨hP1, hPK⟩, -, -⟩ := (mem_cubeIdx G).1 hP
  obtain ⟨⟨hQ1, hQK⟩, -, -⟩ := (mem_cubeIdx G).1 hQ
  constructor
  · by_contra hlt
    refine layer_not_near G hϱ hQ1 (by omega) hPK hyl hxl ?_
    rwa [Green.torusDist_comm_gen]
  · by_contra hlt
    exact layer_not_near G hϱ hP1 (by omega) hQK hxl hyl hdist

end Gap

section Degree

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁] [NeZero L] in
/-- A residue in the same cell of side `p` as an aligned base `a` is `a + i`, `i < p`. -/
theorem exists_add_of_div_eq {n : ℕ} [NeZero n] {p : ℕ} (hp : 0 < p) {x a : ZMod n}
    (hxa : x.val / p = a.val / p) (ha : a.val % p = 0) : ∃ i < p, x = a + (i : ZMod n) := by
  refine ⟨x.val % p, Nat.mod_lt _ hp, ?_⟩
  have h1 := Nat.div_add_mod x.val p
  have h2 := Nat.div_add_mod a.val p
  have h3 : x.val = a.val + x.val % p := by rw [ha, hxa] at *; omega
  calc x = ((x.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val x).symm
    _ = ((a.val + x.val % p : ℕ) : ZMod n) := congrArg Nat.cast h3
    _ = a + ((x.val % p : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]

/-- In each coordinate, the base of a neighbour patch is a grid base near the interval of the
patch of `P`. -/
theorem moore_coord {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {P Q : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx G) (hQ : Q ∈ cubeIdx G) (h : MooreTouch (Pset m₁ P) (Pset m₁ Q))
    (μ : Fin d) :
    NearGridBase (L ^ (P.1 + m₁)) (L ^ (Q.1 + m₁)) (P.2 μ) (Q.2 μ) := by
  obtain ⟨x, hx, y, hy, hn⟩ := h
  obtain ⟨q, hq, hyx⟩ := near_one_iff.1 hn
  obtain ⟨-, -, hPb⟩ := (mem_cubeIdx G).1 hP
  obtain ⟨-, -, hQb⟩ := (mem_cubeIdx G).1 hQ
  obtain ⟨i, hi, hxi⟩ := exists_add_of_div_eq (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne (n := L))))
    (hx μ) (hPb μ)
  obtain ⟨j, hj, hyj⟩ := exists_add_of_div_eq (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne (n := L))))
    (hy μ) (hQb μ)
  refine ⟨Nat.dvd_of_mod_eq_zero (hQb μ), j, i, hj, hi, -q μ, by simpa using hq μ, ?_⟩
  have := hyx μ
  rw [hyj, hxi] at this
  push_cast
  linear_combination -this

open Classical in
/-- The indices of layer `j` whose patch Moore-touches the patch of `P` number at most
`(L + 2)^d`, if `P.1 ≤ j + 1`. -/
theorem card_moore_layer_le {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ cubeIdx G) {j : ℕ} (hj : P.1 ≤ j + 1) :
    ((cubeIdx G).filter fun Q => Q.1 = j ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)).card
      ≤ (L + 2) ^ d := by
  by_cases hjK : j ≤ K
  swap
  · have : ((cubeIdx G).filter fun Q => Q.1 = j ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun Q hQ => ?_
      have := ((mem_cubeIdx G).1 hQ).1.2
      omega
    rw [this]; simp
  set B : Fin d → Finset (ZMod ((N₁ * L ^ m₁) * L ^ K)) := fun μ =>
    (Finset.univ).filter (NearGridBase (L ^ (P.1 + m₁)) (L ^ (j + m₁)) (P.2 μ)) with hB
  have hqpos : 0 < L ^ (j + m₁) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne (n := L)))
  have hqn : L ^ (j + m₁) ∣ (N₁ * L ^ m₁) * L ^ K := by
    have : L ^ (j + m₁) ∣ L ^ m₁ * L ^ K := by
      rw [← pow_add]; exact pow_dvd_pow L (by omega)
    exact Dvd.dvd.trans this (by rw [mul_assoc]; exact Dvd.intro_left _ rfl)
  have hBc : ∀ μ, (B μ).card ≤ L + 2 := by
    intro μ
    refine (card_gridBases_le _ _ hqpos hqn _).trans ?_
    have : L ^ (P.1 + m₁) / L ^ (j + m₁) ≤ L := by
      refine Nat.div_le_of_le_mul ?_
      calc L ^ (P.1 + m₁) ≤ L ^ (j + m₁ + 1) :=
            Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne (n := L))) (by omega)
        _ = L ^ (j + m₁) * L := pow_succ _ _
    omega
  calc _ ≤ (Fintype.piFinset B).card := by
        refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
        · intro Q hQ
          obtain ⟨hQi, hj', hm⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hQ)
          refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun μ => ?_)
          have := moore_coord hP hQi hm μ
          rw [hj'] at this
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
        · intro Q hQ Q' hQ' hsnd
          have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hQ)).2.1
          have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hQ')).2.1
          exact Prod.ext (h1.trans h2.symm) hsnd
    _ = ∏ μ, (B μ).card := Fintype.card_piFinset B
    _ ≤ ∏ _μ : Fin d, (L + 2) := Finset.prod_le_prod (fun μ _ => hBc μ)
    _ = (L + 2) ^ d := by simp

open Classical in
/-- **T3 (VMOD-24 Lemma 3.1, degree), sharp form.**  Every index has at most `3 (L + 2)^d` other
indices whose patch Moore-touches its patch, if `d ≤ ϱ L ^ 2`. -/
theorem cubeIdx_moore_degree_le_L_add_two {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hG : CubeAligned G m₁) (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx G) :
    ((cubeIdx G).filter fun Q => Q ≠ P ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)).card
      ≤ 3 * (L + 2) ^ d := by
  have hP1 := ((mem_cubeIdx G).1 hP).1.1
  have hsub : ((cubeIdx G).filter fun Q => Q ≠ P ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)) ⊆
      (Finset.Icc (P.1 - 1) (P.1 + 1)).biUnion fun j =>
        (cubeIdx G).filter fun Q => Q.1 = j ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q) := by
    intro Q hQ
    obtain ⟨hQi, -, hm⟩ := Finset.mem_filter.1 hQ
    have hgap := cubeIdx_moore_layer_gap hG hϱ hP hQi hm
    exact Finset.mem_biUnion.2 ⟨Q.1, Finset.mem_Icc.2 ⟨by omega, by omega⟩,
      Finset.mem_filter.2 ⟨hQi, rfl, hm⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ j ∈ Finset.Icc (P.1 - 1) (P.1 + 1),
        ((cubeIdx G).filter fun Q => Q.1 = j ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)).card
      ≤ ∑ _j ∈ Finset.Icc (P.1 - 1) (P.1 + 1), (L + 2) ^ d :=
        Finset.sum_le_sum fun j hj => card_moore_layer_le hP (by
          have := (Finset.mem_Icc.1 hj).1
          omega)
    _ = 3 * (L + 2) ^ d := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        congr 1
        omega

open Classical in
/-- **T3 (VMOD-24 Lemma 3.1, degree).**  Every index of the cube index set of a cube-aligned
generating set has at most `3 (L + 4)^d` other indices whose patch Moore-touches its patch,
independently of `K`, the torus size and the history; the premise is `d ≤ ϱ L ^ 2`. -/
theorem cubeIdx_moore_degree {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hG : CubeAligned G m₁) (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx G) :
    ((cubeIdx G).filter fun Q => Q ≠ P ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)).card
      ≤ 3 * (L + 4) ^ d :=
  (cubeIdx_moore_degree_le_L_add_two hG hϱ hP).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) d))

/-- **T4.**  The Moore graph of the index set of a cover: the vertices are the indices, two
distinct indices are adjacent when their patches Moore-touch. -/
def mooreGraph (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    SimpleGraph {P // P ∈ cubeIdx G} where
  Adj P Q := P ≠ Q ∧ MooreTouch (Pset m₁ P.1) (Pset m₁ Q.1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- **T4.**  The degree of the Moore graph is at most `3 (L + 4)^d` (indeed `3 (L + 2)^d`). -/
theorem mooreGraph_degree_le {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hG : CubeAligned G m₁) (hϱ : (d : ℝ) ≤ ϱ * (L : ℝ) ^ 2) (P : {P // P ∈ cubeIdx G}) :
    (mooreGraph G).degree P ≤ 3 * (L + 4) ^ d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine le_trans ?_ (cubeIdx_moore_degree hG hϱ P.2)
  refine Finset.card_le_card_of_injOn Subtype.val ?_ (fun _ _ _ _ h => Subtype.ext h)
  intro Q hQ
  have hQ0 := (SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 hQ)
  obtain ⟨hne, hm⟩ : P ≠ Q ∧ MooreTouch (Pset m₁ P.1) (Pset m₁ Q.1) := hQ0
  exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Q.2, fun h => hne (Subtype.ext h.symm), hm⟩)

end Degree

section P6

open Balaban.LargeField

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

omit [NeZero L] [NeZero M1] in
/-- The separation constant `5 L M₁` of `p6FsharpC` satisfies `d ≤ ϱ L²` when `d < 5 L³ M₁`. -/
theorem p6_moore_premise (hd : d < 5 * L ^ 3 * M1) :
    (d : ℝ) ≤ minSep L M1 * (L : ℝ) ^ 2 := by
  unfold minSep
  have : (d : ℝ) < 5 * (L : ℝ) ^ 3 * M1 := by exact_mod_cast hd
  nlinarith

/-- **T1 for the common cover `p6FsharpC` of the P6 pair**: under `d < 5 L³ M₁` Moore-touching
patches have layers differing by at most one. -/
theorem cubeIdx_moore_layer_gap_p6 (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    {P Q : ℕ × CTorus d L (c * n1) m₁ (k + 1)}
    (hP : P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1))
    (hQ : Q ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1))
    (h : MooreTouch (Pset m₁ P) (Pset m₁ Q)) : P.1 ≤ Q.1 + 1 ∧ Q.1 ≤ P.1 + 1 :=
  cubeIdx_moore_layer_gap
    (GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ hc Z hM1 hm₁))
    (p6_moore_premise hd) hP hQ h

open Classical in
/-- **T3 for `p6FsharpC`**: under `d < 5 L³ M₁`, every index has at most `3 (L + 4)^d` Moore
neighbours. -/
theorem cubeIdx_moore_degree_p6 (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    {P : ℕ × CTorus d L (c * n1) m₁ (k + 1)}
    (hP : P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)) :
    ((cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)).filter
        fun Q => Q ≠ P ∧ MooreTouch (Pset m₁ P) (Pset m₁ Q)).card ≤ 3 * (L + 4) ^ d :=
  cubeIdx_moore_degree
    (GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ hc Z hM1 hm₁))
    (p6_moore_premise hd) hP

end P6

end Balaban.Localization
