/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Bump
public import Balaban.Background.BlockGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The normalized quotient (LEMMA53-astra.md, §3, Lemma 5.3b; §6 item 6)

`blockIdx G` indexes the blocks of all layers by pairs `(m, y0)` (`y0` the base site of a layer
`m` block); `denom G x = ∑ bump` and `weight G q x = bump / denom`.  For `x` in layer `n`:

* `denom_ge`, `denom_le`: `2^{-d} ≤ D(x) ≤ 3 · 3^d · 4^d`;
* `active_layer_bounds`: a block with a bump nonzero at `x` has layer `m` with `|m - n| ≤ 1`, and
  `n - 1 ≤ m` if the bump is nonzero at a neighbour of `x`;
* `card_active_le`: at most `3 · 3^d` blocks are active at `x`;
* `weight_diff1`, `weight_diff2`: first and centred second differences of the weights along `±e_μ`
  are at most `H₁ / ℓ(x)` and `H₂ / ℓ(x)²` for `ℓ(x) = L ^ n`, `n ≥ 3` hmm (for `n ≥ 2`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Index

variable (G : GeneratingSet d L N₀ k ϱ)

open Classical in
/-- Index set of the blocks: pairs `(m, y0)`, `1 ≤ m ≤ k`, `y0` the base site of a layer-`m`
block. -/
noncomputable def blockIdx : Finset (ℕ × Torus d (N₀ * L ^ k)) :=
  ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (Torus d (N₀ * L ^ k)))).filter
    (fun q => q.2 ∈ G.layer q.1 ∧ IsBase q.1 q.2)

theorem mem_blockIdx {q : ℕ × Torus d (N₀ * L ^ k)} :
    q ∈ blockIdx G ↔ (1 ≤ q.1 ∧ q.1 ≤ k) ∧ q.2 ∈ G.layer q.1 ∧ IsBase q.1 q.2 := by
  classical
  simp [blockIdx]

/-- The denominator `D(x) = ∑_B b_B(x)`. -/
noncomputable def denom (x : Torus d (N₀ * L ^ k)) : ℝ :=
  ∑ q ∈ blockIdx G, bump q.1 q.2 x

/-- The weight `h_B(x) = b_B(x) / D(x)`. -/
noncomputable def weight (q : ℕ × Torus d (N₀ * L ^ k)) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  bump q.1 q.2 x / denom G x

open Classical in
/-- The blocks whose bump is nonzero at `x`. -/
noncomputable def active (x : Torus d (N₀ * L ^ k)) : Finset (ℕ × Torus d (N₀ * L ^ k)) :=
  (blockIdx G).filter fun q => bump q.1 q.2 x ≠ 0

theorem mem_active {x : Torus d (N₀ * L ^ k)} {q : ℕ × Torus d (N₀ * L ^ k)} :
    q ∈ active G x ↔ q ∈ blockIdx G ∧ bump q.1 q.2 x ≠ 0 := by
  classical
  simp [active]

theorem bump_nonneg_of_mem {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G)
    (x : Torus d (N₀ * L ^ k)) : 0 ≤ bump q.1 q.2 x :=
  bump_nonneg ((mem_blockIdx G).1 hq).1.2 _ _

theorem bump_eq_zero_of_not_active {x : Torus d (N₀ * L ^ k)} {q : ℕ × Torus d (N₀ * L ^ k)}
    (hq : q ∈ blockIdx G) (h : q ∉ active G x) : bump q.1 q.2 x = 0 := by
  by_contra hne
  exact h ((mem_active G).2 ⟨hq, hne⟩)

theorem denom_nonneg (x : Torus d (N₀ * L ^ k)) : 0 ≤ denom G x :=
  sum_nonneg fun _ hq => bump_nonneg_of_mem G hq x

/-- The own block of `x` (the block containing `x`, with base the corner of its cell). -/
def ownBase (n : ℕ) (x : Torus d (N₀ * L ^ k)) : Torus d (N₀ * L ^ k) :=
  fun μ => (((x μ).val / L ^ n * L ^ n : ℕ) : ZMod (N₀ * L ^ k))

theorem ownBase_val {n : ℕ} (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    (ownBase n x μ).val = (x μ).val / L ^ n * L ^ n := by
  unfold ownBase
  apply ZMod.val_natCast_of_lt
  calc (x μ).val / L ^ n * L ^ n ≤ (x μ).val := Nat.div_mul_le_self _ _
    _ < N₀ * L ^ k := ZMod.val_lt _

theorem ownBase_isBase {n : ℕ} (x : Torus d (N₀ * L ^ k)) :
    IsBase n (ownBase n x) := fun μ => by
  rw [ownBase_val]; exact Nat.mul_mod_left _ _

theorem ownBase_jBlock {n : ℕ} (x : Torus d (N₀ * L ^ k)) :
    jBlock d L N₀ k n (ownBase n x) = jBlock d L N₀ k n x := by
  funext μ
  unfold jBlock
  rw [Balaban.blockMap_apply, Balaban.blockMap_apply]
  unfold Balaban.blockCoord
  have hlam : 0 < L ^ n := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n
  rw [ownBase_val, Nat.mul_div_cancel _ hlam]

theorem own_mem_blockIdx {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) : (n, ownBase n x) ∈ blockIdx G := by
  rw [mem_blockIdx]
  refine ⟨⟨hn1, hnk⟩, ?_, ownBase_isBase x⟩
  exact (G.mem_layer_iff hn1 hnk (ownBase_jBlock x)).2 hx

/-- `D(x) ≥ 2^{-d}`. -/
theorem denom_ge {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) : (1 / 2 : ℝ) ^ d ≤ denom G x := by
  have hmem := own_mem_blockIdx G hn1 hnk hx
  calc (1 / 2 : ℝ) ^ d ≤ bump n (ownBase n x) x :=
        bump_ge_of_jBlock_eq hnk (ownBase_isBase x) (ownBase_jBlock x).symm
    _ ≤ denom G x := by
        have := Finset.single_le_sum (f := fun q : ℕ × Torus d (N₀ * L ^ k) => bump q.1 q.2 x)
          (fun q hq => bump_nonneg_of_mem G hq x) hmem
        exact this


/-- A block with a bump nonzero at `x'` has a point `z` of the block within `L ^ m` (in each lifted
coordinate) of a lift of `x'`. -/
theorem active_lift {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G)
    {x' : Torus d (N₀ * L ^ k)} (h : bump q.1 q.2 x' ≠ 0) :
    ∃ t u : Fin d → ℤ, (∀ μ, ((t μ : ℤ) : ZMod (N₀ * L ^ k)) = x' μ) ∧
      (intTorus u : Torus d (N₀ * L ^ k)) ∈ G.layer q.1 ∧
      jBlock d L N₀ k q.1 (intTorus u) = jBlock d L N₀ k q.1 q.2 ∧
      ∀ μ, (t μ - u μ).natAbs ≤ L ^ q.1 := by
  obtain ⟨⟨hm1, hmk⟩, hl, hb⟩ := (mem_blockIdx G).1 hq
  obtain ⟨t, u, ht, hj, hd⟩ := exists_lift_near hmk hb h
  exact ⟨t, u, ht, (G.mem_layer_iff hm1 hmk hj).2 hl, hj, hd⟩

theorem active_dist {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G)
    {x' : Torus d (N₀ * L ^ k)} (h : bump q.1 q.2 x' ≠ 0) :
    ∃ z ∈ G.layer q.1, Green.torusDist d (N₀ * L ^ k) x' z ≤ d * (L : ℝ) ^ q.1 := by
  obtain ⟨t, u, ht, hz, -, hd⟩ := active_lift G hq h
  refine ⟨intTorus u, hz, (torusDist_le_of_lift t u ht (fun _ => rfl)).trans ?_⟩
  calc ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ ∑ _μ : Fin d, (L : ℝ) ^ q.1 :=
        Finset.sum_le_sum fun μ _ => by exact_mod_cast hd μ
    _ = d * (L : ℝ) ^ q.1 := by simp

/-- **Lemma 5.3a(1),(3)**: a block active at `x'`, with `x'` within distance one of a site `x` of
layer `n`, has layer `m` with `|m - n| ≤ 1`. -/
theorem active_layer_bounds (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n)
    (hxx' : Green.torusDist d (N₀ * L ^ k) x x' ≤ 1) {q : ℕ × Torus d (N₀ * L ^ k)}
    (hq : q ∈ active G x') : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  obtain ⟨hqi, hne⟩ := (mem_active G).1 hq
  obtain ⟨⟨hm1, hmk⟩, -, -⟩ := (mem_blockIdx G).1 hqi
  obtain ⟨z, hz, hdz⟩ := active_dist G hqi hne
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hL'
  have htri := Green.torusDist_triangle_gen x x' z
  refine layer_bounds_of_dist G hϱ hm1 hmk hn1 hnk hx hz (htri.trans ?_) hL
  nlinarith

open Classical in
theorem card_active_le (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n)
    (hxx' : Green.torusDist d (N₀ * L ^ k) x x' ≤ 1) : (active G x').card ≤ 3 * 3 ^ d := by
  set M : Finset ℕ := (Finset.Icc (n - 1) (n + 1)).filter (fun m => 1 ≤ m ∧ m ≤ k) with hM
  have hMc : M.card ≤ 3 := by
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]; omega
  have hsub : active G x' ⊆ M.biUnion (fun m =>
      ((Finset.univ : Finset (Torus d (N₀ * L ^ k))).filter
        (fun y0 => IsBase m y0 ∧ bump m y0 x' ≠ 0)).image (fun y0 => (m, y0))) := by
    intro q hq
    obtain ⟨hqi, hne⟩ := (mem_active G).1 hq
    obtain ⟨⟨hm1, hmk⟩, -, hb⟩ := (mem_blockIdx G).1 hqi
    have hl := active_layer_bounds G hϱ hd hL hn1 hnk hx hxx' hq
    rw [Finset.mem_biUnion]
    refine ⟨q.1, ?_, ?_⟩
    · rw [hM, Finset.mem_filter, Finset.mem_Icc]; omega
    · rw [Finset.mem_image]
      exact ⟨q.2, by simp [hb, hne], rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ m ∈ M, (((Finset.univ : Finset (Torus d (N₀ * L ^ k))).filter
          (fun y0 => IsBase m y0 ∧ bump m y0 x' ≠ 0)).image (fun y0 => (m, y0))).card
      ≤ ∑ _m ∈ M, 3 ^ d := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine card_image_le.trans ?_
        exact card_active_bases_le (by rw [hM, Finset.mem_filter] at hm; exact hm.2.2) x'
    _ = M.card * 3 ^ d := by simp
    _ ≤ 3 * 3 ^ d := Nat.mul_le_mul_right _ hMc


omit [NeZero N₀] [NeZero L] in
theorem torusDist_self_le (x : Torus d (N₀ * L ^ k)) :
    Green.torusDist d (N₀ * L ^ k) x x ≤ 1 := by
  unfold Green.torusDist
  simp [Green.natAbs_cycRep_zero]

omit [NeZero N₀] [NeZero L] in
theorem adj_add (x : Torus d (N₀ * L ^ k)) (μ : Fin d) : Adj x (x + Pi.single μ 1) :=
  ⟨μ, Or.inl rfl⟩

omit [NeZero N₀] [NeZero L] in
theorem adj_sub (x : Torus d (N₀ * L ^ k)) (μ : Fin d) : Adj x (x - Pi.single μ 1) :=
  ⟨μ, Or.inr (by simp)⟩

theorem denom_le (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn1 : 1 ≤ n)
    (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) :
    denom G x ≤ 3 * 3 ^ d * 4 ^ d := by
  have hsub : active G x ⊆ blockIdx G := fun q hq => ((mem_active G).1 hq).1
  have : denom G x = ∑ q ∈ active G x, bump q.1 q.2 x := by
    unfold denom
    symm
    refine Finset.sum_subset hsub fun q hq hqa => ?_
    exact bump_eq_zero_of_not_active G hq hqa
  rw [this]
  calc ∑ q ∈ active G x, bump q.1 q.2 x ≤ ∑ _q ∈ active G x, (4 : ℝ) ^ d :=
        Finset.sum_le_sum fun q hq =>
          bump_le ((mem_blockIdx G).1 ((mem_active G).1 hq).1).1.2 _ _
    _ = (active G x).card * 4 ^ d := by simp
    _ ≤ (3 * 3 ^ d : ℕ) * (4 : ℝ) ^ d := by
        have := card_active_le G hϱ hd hL hn1 hnk hx (torusDist_self_le x)
        have h2 : ((active G x).card : ℝ) ≤ ((3 * 3 ^ d : ℕ) : ℝ) := by exact_mod_cast this
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 3 * 3 ^ d * 4 ^ d := by push_cast; ring

theorem denom_pos {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) : 0 < denom G x :=
  lt_of_lt_of_le (by positivity) (denom_ge G hn1 hnk hx)

theorem weight_nonneg {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G) :
    0 ≤ weight G q x :=
  div_nonneg (bump_nonneg_of_mem G hq x) (denom_pos G hn1 hnk hx).le

theorem weight_le_one {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G) :
    weight G q x ≤ 1 := by
  unfold weight
  rw [div_le_one (denom_pos G hn1 hnk hx)]
  have := Finset.single_le_sum (f := fun q : ℕ × Torus d (N₀ * L ^ k) => bump q.1 q.2 x)
    (fun q hq => bump_nonneg_of_mem G hq x) hq
  exact this

theorem sum_weight {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) : ∑ q ∈ blockIdx G, weight G q x = 1 := by
  unfold weight
  rw [← Finset.sum_div]
  exact div_self (denom_pos G hn1 hnk hx).ne'

theorem weight_eq_zero {x : Torus d (N₀ * L ^ k)} {q : ℕ × Torus d (N₀ * L ^ k)}
    (hq : q ∈ blockIdx G) (h : q ∉ active G x) : weight G q x = 0 := by
  unfold weight; rw [bump_eq_zero_of_not_active G hq h, zero_div]

/-- The blocks active at `x` or at one of `x ± e_μ`. -/
noncomputable def supp (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    Finset (ℕ × Torus d (N₀ * L ^ k)) :=
  active G x ∪ active G (x + Pi.single μ 1) ∪ active G (x - Pi.single μ 1)

theorem supp_subset (x : Torus d (N₀ * L ^ k)) (μ : Fin d) : supp G x μ ⊆ blockIdx G := by
  intro q hq
  simp only [supp, Finset.mem_union] at hq
  rcases hq with (h | h) | h <;> exact ((mem_active G).1 h).1

theorem not_mem_supp {x : Torus d (N₀ * L ^ k)} {μ : Fin d} {q : ℕ × Torus d (N₀ * L ^ k)}
    (hq : q ∈ blockIdx G) (h : q ∉ supp G x μ) :
    bump q.1 q.2 x = 0 ∧ bump q.1 q.2 (x + Pi.single μ 1) = 0 ∧
      bump q.1 q.2 (x - Pi.single μ 1) = 0 := by
  simp only [supp, Finset.mem_union, not_or] at h
  exact ⟨bump_eq_zero_of_not_active G hq h.1.1, bump_eq_zero_of_not_active G hq h.1.2,
    bump_eq_zero_of_not_active G hq h.2⟩

theorem card_supp_le (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn1 : 1 ≤ n)
    (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d) :
    (supp G x μ).card ≤ 9 * 3 ^ d := by
  have h1 := card_active_le G hϱ hd hL hn1 hnk hx (torusDist_self_le x)
  have h2 := card_active_le G hϱ hd hL hn1 hnk hx (adj_add x μ).torusDist_le
  have h3 := card_active_le G hϱ hd hL hn1 hnk hx (adj_sub x μ).torusDist_le
  unfold supp
  calc _ ≤ (active G x ∪ active G (x + Pi.single μ 1)).card + (active G (x - Pi.single μ 1)).card :=
        card_union_le _ _
    _ ≤ (active G x).card + (active G (x + Pi.single μ 1)).card +
        (active G (x - Pi.single μ 1)).card := by
        have := card_union_le (active G x) (active G (x + Pi.single μ 1)); omega
    _ ≤ 9 * 3 ^ d := by omega

theorem supp_layer_bounds (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ supp G x μ) : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  simp only [supp, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · exact active_layer_bounds G hϱ hd hL hn1 hnk hx (torusDist_self_le x) h
  · exact active_layer_bounds G hϱ hd hL hn1 hnk hx (adj_add x μ).torusDist_le h
  · exact active_layer_bounds G hϱ hd hL hn1 hnk hx (adj_sub x μ).torusDist_le h


/-! ### Difference bounds -/

/-- Constants of the first and second differences of the bump (`bump_diff1`, `bump_diff2`). -/
noncomputable def wb1 (d : ℕ) : ℝ := 150 * 4 ^ d
noncomputable def wb2 (d : ℕ) : ℝ := 20 * 4 ^ d
/-- Constants for the denominator `D`: `9 * 3^d` active blocks. -/
noncomputable def wU (d L : ℕ) : ℝ := 9 * 3 ^ d * wb1 d * L
noncomputable def wV (d L : ℕ) : ℝ := 9 * 3 ^ d * wb2 d * (L : ℝ) ^ 2
/-- Constants `H₁`, `H₂` of the weight differences, `(4)` of the note. -/
noncomputable def wH1 (d L : ℕ) : ℝ := (wb1 d * L + wU d L) / (1 / 2 : ℝ) ^ d
noncomputable def wH2 (d L : ℕ) : ℝ :=
  (wb2 d * (L : ℝ) ^ 2 + wV d L + 2 * wH1 d L * wU d L) / (1 / 2 : ℝ) ^ d

theorem wb1_nonneg (d : ℕ) : 0 ≤ wb1 d := by unfold wb1; positivity
theorem wb2_nonneg (d : ℕ) : 0 ≤ wb2 d := by unfold wb2; positivity
theorem wU_nonneg (d L : ℕ) : 0 ≤ wU d L := by unfold wU; have := wb1_nonneg d; positivity
theorem wV_nonneg (d L : ℕ) : 0 ≤ wV d L := by unfold wV; have := wb2_nonneg d; positivity
theorem wH1_nonneg (d L : ℕ) : 0 ≤ wH1 d L := by
  unfold wH1; have := wb1_nonneg d; have := wU_nonneg d L; positivity
theorem wH2_nonneg (d L : ℕ) : 0 ≤ wH2 d L := by
  unfold wH2; have := wb2_nonneg d; have := wV_nonneg d L; have := wU_nonneg d L
  have := wH1_nonneg d L; positivity

omit [NeZero L] in
theorem one_le_pow_L (hL : 1 ≤ L) (m : ℕ) : (1 : ℝ) ≤ (L : ℝ) ^ m :=
  one_le_pow₀ (by exact_mod_cast hL)

omit [NeZero L] in
/-- For a block of the support, the scale is at least `ℓ / L`. -/
theorem scale_ge {m n : ℕ} (hmn : n ≤ m + 1) (hL : 1 ≤ L) :
    (L : ℝ) ^ n ≤ L * (L : ℝ) ^ m := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  calc (L : ℝ) ^ n ≤ (L : ℝ) ^ (m + 1) := pow_le_pow_right₀ hL' hmn
    _ = L * (L : ℝ) ^ m := by ring

theorem bump_diff_supp (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ supp G x μ) :
    |bump q.1 q.2 (x + Pi.single μ 1) - bump q.1 q.2 x| ≤ wb1 d * L / (L : ℝ) ^ n ∧
    |bump q.1 q.2 (x - Pi.single μ 1) - bump q.1 q.2 x| ≤ wb1 d * L / (L : ℝ) ^ n ∧
    |bump q.1 q.2 (x + Pi.single μ 1) + bump q.1 q.2 (x - Pi.single μ 1) - 2 * bump q.1 q.2 x| ≤
      wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ n) ^ 2 := by
  have hbl := supp_layer_bounds G hϱ hd (by omega) hn1 hnk hx μ hq
  obtain ⟨⟨hm1, hmk⟩, -, -⟩ := (mem_blockIdx G).1 (supp_subset G x μ hq)
  have hlam : 2 ≤ L ^ q.1 := by
    calc 2 ≤ L := hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ q.1 := Nat.pow_le_pow_right (by omega) hm1
  obtain ⟨d1, d1'⟩ := bump_diff1 hmk hlam q.2 x μ
  have d2 := bump_diff2 hmk hlam q.2 x μ
  have hs := scale_ge hbl.1 (by omega : 1 ≤ L)
  have hLm : (0 : ℝ) < (L : ℝ) ^ q.1 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have key1 : 150 * (4 : ℝ) ^ d / (L : ℝ) ^ q.1 ≤ wb1 d * L / (L : ℝ) ^ n := by
    unfold wb1
    rw [div_le_div_iff₀ hLm hLn]
    have : (0 : ℝ) ≤ 150 * 4 ^ d := by positivity
    nlinarith
  have key2 : 20 * (4 : ℝ) ^ d / ((L : ℝ) ^ q.1) ^ 2 ≤ wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ n) ^ 2 := by
    unfold wb2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ 20 * 4 ^ d := by positivity
    have h3 : ((L : ℝ) ^ n) ^ 2 ≤ ((L : ℝ) * (L : ℝ) ^ q.1) ^ 2 :=
      pow_le_pow_left₀ hLn.le hs 2
    nlinarith
  exact ⟨d1.trans key1, d1'.trans key1, d2.trans key2⟩


theorem sum_abs_le_supp {x : Torus d (N₀ * L ^ k)} {μ : Fin d}
    {f : ℕ × Torus d (N₀ * L ^ k) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ q ∈ blockIdx G, q ∉ supp G x μ → f q = 0) (h1 : ∀ q ∈ supp G x μ, |f q| ≤ c)
    (hcard : (supp G x μ).card ≤ 9 * 3 ^ d) :
    |∑ q ∈ blockIdx G, f q| ≤ 9 * 3 ^ d * c := by
  rw [← Finset.sum_subset (supp_subset G x μ) h0]
  calc |∑ q ∈ supp G x μ, f q| ≤ ∑ q ∈ supp G x μ, |f q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ supp G x μ, c := Finset.sum_le_sum h1
    _ = (supp G x μ).card * c := by simp
    _ ≤ (9 * 3 ^ d : ℕ) * c := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
    _ = 9 * 3 ^ d * c := by push_cast; ring

theorem denom_diff (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d) :
    |denom G (x + Pi.single μ 1) - denom G x| ≤ wU d L / (L : ℝ) ^ n ∧
    |denom G (x - Pi.single μ 1) - denom G x| ≤ wU d L / (L : ℝ) ^ n ∧
    |denom G (x + Pi.single μ 1) + denom G (x - Pi.single μ 1) - 2 * denom G x| ≤
      wV d L / ((L : ℝ) ^ n) ^ 2 := by
  have hcard := card_supp_le G hϱ hd (by omega) hn1 hnk hx μ
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hb1 := wb1_nonneg d
  have hb2 := wb2_nonneg d
  have hsupp := fun q (hq : q ∈ supp G x μ) => bump_diff_supp G hϱ hd hL hn1 hnk hx μ hq
  refine ⟨?_, ?_, ?_⟩
  · have := sum_abs_le_supp G (x := x) (μ := μ)
      (f := fun q => bump q.1 q.2 (x + Pi.single μ 1) - bump q.1 q.2 x)
      (c := wb1 d * L / (L : ℝ) ^ n) (by positivity)
      (fun q hq hqs => by
        obtain ⟨h1, h2, h3⟩ := not_mem_supp G hq hqs; simp [h1, h2])
      (fun q hq => (hsupp q hq).1) hcard
    unfold denom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wU; ring
  · have := sum_abs_le_supp G (x := x) (μ := μ)
      (f := fun q => bump q.1 q.2 (x - Pi.single μ 1) - bump q.1 q.2 x)
      (c := wb1 d * L / (L : ℝ) ^ n) (by positivity)
      (fun q hq hqs => by
        obtain ⟨h1, h2, h3⟩ := not_mem_supp G hq hqs; simp [h1, h3])
      (fun q hq => (hsupp q hq).2.1) hcard
    unfold denom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wU; ring
  · have := sum_abs_le_supp G (x := x) (μ := μ)
      (f := fun q => bump q.1 q.2 (x + Pi.single μ 1) + bump q.1 q.2 (x - Pi.single μ 1)
        - 2 * bump q.1 q.2 x)
      (c := wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ n) ^ 2) (by positivity)
      (fun q hq hqs => by
        obtain ⟨h1, h2, h3⟩ := not_mem_supp G hq hqs; simp [h1, h2, h3])
      (fun q hq => (hsupp q hq).2.2) hcard
    unfold denom
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wV; ring

end Index

section Alg

theorem weight_step {b' b D' D q0 B U : ℝ} (hq0 : 0 < q0) (hD' : q0 ≤ D') (hD : q0 ≤ D)
    (hb : 0 ≤ b) (hbD : b ≤ D) (hdb : |b' - b| ≤ B) (hdD : |D' - D| ≤ U) :
    |b' / D' - b / D| ≤ (B + U) / q0 := by
  have hD'0 : 0 < D' := lt_of_lt_of_le hq0 hD'
  have hD0 : 0 < D := lt_of_lt_of_le hq0 hD
  have e : b' / D' - b / D = (b' - b) / D' - (b / D) * (D' - D) / D' := by
    field_simp; ring
  have w1 : 0 ≤ b / D := div_nonneg hb hD0.le
  have w2 : b / D ≤ 1 := (div_le_one hD0).2 hbD
  have t1 : |(b' - b) / D'| ≤ B / q0 := by
    rw [abs_div, abs_of_pos hD'0]
    calc |b' - b| / D' ≤ |b' - b| / q0 :=
          div_le_div_of_nonneg_left (abs_nonneg _) hq0 hD'
      _ ≤ B / q0 := div_le_div_of_nonneg_right hdb hq0.le
  have t2 : |(b / D) * (D' - D) / D'| ≤ U / q0 := by
    rw [abs_div, abs_of_pos hD'0, abs_mul, abs_of_nonneg w1]
    calc b / D * |D' - D| / D' ≤ |D' - D| / D' := by
          exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) w2) hD'0.le
      _ ≤ |D' - D| / q0 := div_le_div_of_nonneg_left (abs_nonneg _) hq0 hD'
      _ ≤ U / q0 := div_le_div_of_nonneg_right hdD hq0.le
  rw [e]
  calc _ ≤ |(b' - b) / D'| + |(b / D) * (D' - D) / D'| := abs_sub _ _
    _ ≤ B / q0 + U / q0 := add_le_add t1 t2
    _ = (B + U) / q0 := by ring

theorem weight_second_alg {wp wm w0 Dp Dm D0 q0 B2 V U H : ℝ} (hq0 : 0 < q0) (hD0 : q0 ≤ D0)
    (hw0 : 0 ≤ w0) (hw1 : w0 ≤ 1)
    (hB : |wp * Dp + wm * Dm - 2 * (w0 * D0)| ≤ B2) (hV : |Dp + Dm - 2 * D0| ≤ V)
    (hp : |wp - w0| ≤ H) (hm : |wm - w0| ≤ H) (hdp : |Dp - D0| ≤ U) (hdm : |Dm - D0| ≤ U) :
    |wp + wm - 2 * w0| ≤ (B2 + V + 2 * H * U) / q0 := by
  have hD0pos : 0 < D0 := lt_of_lt_of_le hq0 hD0
  have e : D0 * (wp + wm - 2 * w0) = (wp * Dp + wm * Dm - 2 * (w0 * D0)) - w0 * (Dp + Dm - 2 * D0)
      - (wp - w0) * (Dp - D0) - (wm - w0) * (Dm - D0) := by ring
  have h1 : |D0 * (wp + wm - 2 * w0)| ≤ B2 + V + 2 * H * U := by
    rw [e]
    have a1 : |w0 * (Dp + Dm - 2 * D0)| ≤ V := by
      rw [abs_mul, abs_of_nonneg hw0]
      calc w0 * |Dp + Dm - 2 * D0| ≤ 1 * V := mul_le_mul hw1 hV (abs_nonneg _) zero_le_one
        _ = V := one_mul V
    have a2 : |(wp - w0) * (Dp - D0)| ≤ H * U := by
      rw [abs_mul]; exact mul_le_mul hp hdp (abs_nonneg _) ((abs_nonneg _).trans hp)
    have a3 : |(wm - w0) * (Dm - D0)| ≤ H * U := by
      rw [abs_mul]; exact mul_le_mul hm hdm (abs_nonneg _) ((abs_nonneg _).trans hm)
    have t1 := abs_sub (wp * Dp + wm * Dm - 2 * (w0 * D0)) (w0 * (Dp + Dm - 2 * D0))
    have t2 := abs_sub (wp * Dp + wm * Dm - 2 * (w0 * D0) - w0 * (Dp + Dm - 2 * D0))
      ((wp - w0) * (Dp - D0))
    have t3 := abs_sub (wp * Dp + wm * Dm - 2 * (w0 * D0) - w0 * (Dp + Dm - 2 * D0)
      - (wp - w0) * (Dp - D0)) ((wm - w0) * (Dm - D0))
    linarith
  rw [abs_mul, abs_of_pos hD0pos] at h1
  rw [le_div_iff₀ hq0]
  nlinarith [abs_nonneg (wp + wm - 2 * w0)]

end Alg

section WeightDiff

variable (G : GeneratingSet d L N₀ k ϱ)

theorem exists_layer_adj (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn2 : 2 ≤ n) (hnk : n ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n)
    (h : Adj x x') : ∃ n', 1 ≤ n' ∧ n' ≤ k ∧ x' ∈ G.layer n' := by
  have h1 := adj_mem_pred G hϱ hd hL hn2 hnk (G.mem_layer.1 hx).1 h
  have h2 : x' ∈ G.Ω 1 := G.Ω_antitone le_rfl (by omega) (by omega) h1
  obtain ⟨j, hj1, hjk, hl⟩ := G.exists_layer h2
  exact ⟨j, hj1, hjk, hl⟩

theorem weight_diff (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ}
    (hn2 : 2 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G) :
    |weight G q (x + Pi.single μ 1) - weight G q x| ≤ wH1 d L / (L : ℝ) ^ n ∧
    |weight G q (x - Pi.single μ 1) - weight G q x| ≤ wH1 d L / (L : ℝ) ^ n ∧
    |weight G q (x + Pi.single μ 1) + weight G q (x - Pi.single μ 1) - 2 * weight G q x| ≤
      wH2 d L / ((L : ℝ) ^ n) ^ 2 := by
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hn1 : 1 ≤ n := by omega
  have hH1 := wH1_nonneg d L
  have hH2 := wH2_nonneg d L
  by_cases hs : q ∈ supp G x μ
  · obtain ⟨n₁, h11, h1k, hx₁⟩ := exists_layer_adj G hϱ hd (by omega) hn2 hnk hx (adj_add x μ)
    obtain ⟨n₂, h21, h2k, hx₂⟩ := exists_layer_adj G hϱ hd (by omega) hn2 hnk hx (adj_sub x μ)
    have hq0 : (0 : ℝ) < (1 / 2 : ℝ) ^ d := by positivity
    have hDp := denom_ge G h11 h1k hx₁
    have hDm := denom_ge G h21 h2k hx₂
    have hD0 := denom_ge G hn1 hnk hx
    obtain ⟨Dd1, Dd1', Dd2⟩ := denom_diff G hϱ hd hL hn1 hnk hx μ
    obtain ⟨Bd1, Bd1', Bd2⟩ := bump_diff_supp G hϱ hd hL hn1 hnk hx μ hs
    have hb0 := bump_nonneg_of_mem G hq x
    have hbD : bump q.1 q.2 x ≤ denom G x := by
      have := Finset.single_le_sum (f := fun q : ℕ × Torus d (N₀ * L ^ k) => bump q.1 q.2 x)
        (fun q hq => bump_nonneg_of_mem G hq x) hq
      exact this
    have f1 : |weight G q (x + Pi.single μ 1) - weight G q x| ≤ wH1 d L / (L : ℝ) ^ n := by
      have := weight_step hq0 hDp hD0 hb0 hbD Bd1 Dd1
      refine this.trans (le_of_eq ?_)
      unfold wH1; field_simp
    have f2 : |weight G q (x - Pi.single μ 1) - weight G q x| ≤ wH1 d L / (L : ℝ) ^ n := by
      have := weight_step hq0 hDm hD0 hb0 hbD Bd1' Dd1'
      refine this.trans (le_of_eq ?_)
      unfold wH1; field_simp
    refine ⟨f1, f2, ?_⟩
    have hDp0 : denom G (x + Pi.single μ 1) ≠ 0 := (lt_of_lt_of_le hq0 hDp).ne'
    have hDm0 : denom G (x - Pi.single μ 1) ≠ 0 := (lt_of_lt_of_le hq0 hDm).ne'
    have hD00 : denom G x ≠ 0 := (lt_of_lt_of_le hq0 hD0).ne'
    have e1 : weight G q (x + Pi.single μ 1) * denom G (x + Pi.single μ 1) =
        bump q.1 q.2 (x + Pi.single μ 1) := by unfold weight; field_simp
    have e2 : weight G q (x - Pi.single μ 1) * denom G (x - Pi.single μ 1) =
        bump q.1 q.2 (x - Pi.single μ 1) := by unfold weight; field_simp
    have e3 : weight G q x * denom G x = bump q.1 q.2 x := by unfold weight; field_simp
    have := weight_second_alg (wp := weight G q (x + Pi.single μ 1))
      (wm := weight G q (x - Pi.single μ 1)) (w0 := weight G q x)
      (Dp := denom G (x + Pi.single μ 1)) (Dm := denom G (x - Pi.single μ 1))
      (D0 := denom G x) (q0 := (1 / 2 : ℝ) ^ d)
      (B2 := wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ n) ^ 2) (V := wV d L / ((L : ℝ) ^ n) ^ 2)
      (U := wU d L / (L : ℝ) ^ n) (H := wH1 d L / (L : ℝ) ^ n) hq0 hD0
      (weight_nonneg G hn1 hnk hx hq) (weight_le_one G hn1 hnk hx hq)
      (by rw [e1, e2, e3]; exact Bd2) Dd2 f1 f2 Dd1 Dd1'
    refine this.trans (le_of_eq ?_)
    unfold wH2; field_simp
  · obtain ⟨h1, h2, h3⟩ := not_mem_supp G hq hs
    have z0 : weight G q x = 0 := by unfold weight; rw [h1, zero_div]
    have z1 : weight G q (x + Pi.single μ 1) = 0 := by unfold weight; rw [h2, zero_div]
    have z2 : weight G q (x - Pi.single μ 1) = 0 := by unfold weight; rw [h3, zero_div]
    rw [z0, z1, z2]
    simp only [sub_zero, abs_zero, add_zero, mul_zero]
    refine ⟨by positivity, by positivity, by positivity⟩

end WeightDiff

end Balaban.Background
