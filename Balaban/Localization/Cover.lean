/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeBump
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cover and the partition of unity (LOCALIZATION.md §1.2)

Let `G` be a generating set on the torus `(N₁ L ^ m₁) L ^ K`.  The *centres* are the cubes
`(j, y0)`, `1 ≤ j ≤ K`, `y0 ∈ Λ_j` the base of a cube of side `M₁ ℓ_j = L ^ (j + m₁)`
(`cubeIdx`).  The quotient `χ_z = h̃_z / D` of the cube bumps (`cubeBump`) by their sum
(`coverDenom`) is the partition of unity (Cov1) of `Ω₁`; `D(x) ≥ 4⁻ᵈ` at every neighbour of every
site of `Ω₁` (also at the wall), so there is no wall term.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

/-- The torus carrying a cube-aligned generating set with `N₀ = N₁ L ^ m₁`. -/
abbrev CTorus (d L N₁ m₁ K : ℕ) : Type := Torus d ((N₁ * L ^ m₁) * L ^ K)

/-! ### Layers of nearby sites -/

section Layers

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (m₁ : ℕ)

/-- Separation, contrapositive form at the cube scale: a site within `4 d L ^ (n + m₁)` of `Ω_n`
lies in `Ω_{n-1}`, if `ϱ ≥ 4 d L ^ (m₁ + 1)`. -/
theorem mem_pred_cube (G : GeneratingSet d L N₀ k ϱ) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    {n : ℕ} (hn1 : 2 ≤ n) (hnk : n ≤ k) {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω n)
    (h : Green.torusDist d (N₀ * L ^ k) x y ≤ 4 * d * (L : ℝ) ^ (n + m₁)) : y ∈ G.Ω (n - 1) := by
  by_contra hy
  have hn : n - 1 + 1 = n := by omega
  have hsep := G.separation (n - 1) (by omega) (by omega) y hy x (by rw [hn]; exact hx)
  rw [Green.torusDist_comm_gen] at hsep
  have hLn : (L : ℝ) ^ (n + m₁) = (L : ℝ) ^ (n - 1) * L * (L : ℝ) ^ m₁ := by
    rw [show n + m₁ = (n - 1) + 1 + m₁ by omega, pow_add, pow_succ]
  have hp : (0 : ℝ) ≤ (L : ℝ) ^ (n - 1) := by positivity
  have : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) * (L : ℝ) ^ (n - 1) ≤ ϱ * (L : ℝ) ^ (n - 1) :=
    mul_le_mul_of_nonneg_right hϱ hp
  rw [hLn] at h
  nlinarith

/-- Layers of nearby sites differ by at most one: a site of layer `n` within `4 d L ^ (m + m₁)` of
a site of layer `m` has `|m - n| ≤ 1`. -/
theorem layer_bounds_cube (G : GeneratingSet d L N₀ k ϱ) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    {m n : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {x z : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (hz : z ∈ G.layer m)
    (h : Green.torusDist d (N₀ * L ^ k) x z ≤ 4 * d * (L : ℝ) ^ (m + m₁)) (hL : 1 ≤ L) :
    n ≤ m + 1 ∧ m ≤ n + 1 := by
  rw [GeneratingSet.mem_layer] at hx hz
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  constructor
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have := mem_pred_cube m₁ G hϱ (by omega) hnk hx.1
      (h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL' (by omega)) (by positivity)))
    exact hz.2 (G.Ω_antitone (by omega) (by omega) (by omega) this)
  · by_contra hlt
    replace hlt := not_le.1 hlt
    rw [Green.torusDist_comm_gen] at h
    have := mem_pred_cube m₁ G hϱ (by omega) hmk hz.1 h
    exact hx.2 (G.Ω_antitone (by omega) (by omega) (by omega) this)

end Layers


/-! ### The index set of centres and the denominator -/

section Index

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)

open Classical in
/-- The centres `Z`: pairs `(j, y0)`, `1 ≤ j ≤ K`, with `y0 ∈ Λ_j` the base of a cube of side
`L ^ (j + m₁)`; the cube is `{x | SameCell (L ^ (j + m₁)) x y0}` and lies in `Λ_j`. -/
noncomputable def cubeIdx : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  ((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ K))).filter
    (fun q => q.2 ∈ G.layer q.1 ∧ CubeBase m₁ q.1 q.2)

theorem mem_cubeIdx {q : ℕ × CTorus d L N₁ m₁ K} :
    q ∈ cubeIdx G ↔ (1 ≤ q.1 ∧ q.1 ≤ K) ∧ q.2 ∈ G.layer q.1 ∧ CubeBase m₁ q.1 q.2 := by
  classical
  simp [cubeIdx]

/-- The denominator `D(x) = ∑_z h̃_z(x)`. -/
noncomputable def coverDenom (x : CTorus d L N₁ m₁ K) : ℝ :=
  ∑ q ∈ cubeIdx G, cubeBump m₁ q.1 q.2 x

/-- The partition of unity `χ_z = h̃_z / D`. -/
noncomputable def chi (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) : ℝ :=
  cubeBump m₁ q.1 q.2 x / coverDenom G x

open Classical in
/-- The centres whose bump is nonzero at `x`. -/
noncomputable def cubeActive (x : CTorus d L N₁ m₁ K) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun q => cubeBump m₁ q.1 q.2 x ≠ 0

theorem mem_cubeActive {x : CTorus d L N₁ m₁ K} {q : ℕ × CTorus d L N₁ m₁ K} :
    q ∈ cubeActive G x ↔ q ∈ cubeIdx G ∧ cubeBump m₁ q.1 q.2 x ≠ 0 := by
  classical
  simp [cubeActive]

theorem cubeBump_nonneg_of_mem {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    (x : CTorus d L N₁ m₁ K) : 0 ≤ cubeBump m₁ q.1 q.2 x :=
  cubeBump_nonneg ((mem_cubeIdx G).1 hq).1.2 _ _

theorem cubeBump_eq_zero_of_not_active {x : CTorus d L N₁ m₁ K} {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (h : q ∉ cubeActive G x) : cubeBump m₁ q.1 q.2 x = 0 := by
  by_contra hne
  exact h ((mem_cubeActive G).2 ⟨hq, hne⟩)

theorem coverDenom_nonneg (x : CTorus d L N₁ m₁ K) : 0 ≤ coverDenom G x :=
  sum_nonneg fun _ hq => cubeBump_nonneg_of_mem G hq x

variable {G}

/-- The own cube of a site of layer `n` is a centre. -/
theorem own_mem_cubeIdx (hG : CubeAligned G m₁) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) : (n, ownBase (n + m₁) x) ∈ cubeIdx G := by
  rw [mem_cubeIdx]
  exact ⟨⟨hn1, hnK⟩, (hG.mem_layer_iff hn1 hnK (ownBase_sameCell x)).1 hx, ownBase_cubeBase x⟩

/-- **Lower bound of the denominator.**  At `x`, `x + e_μ`, `x - e_μ` for `x` of layer `n`,
`D ≥ 4⁻ᵈ` (also if the neighbour lies outside `Ω₁`). -/
theorem coverDenom_ge (hG : CubeAligned G m₁) (hL : 2 ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    (hz : z = x ∨ z = x + Pi.single μ 1 ∨ z = x - Pi.single μ 1) :
    (1 / 4 : ℝ) ^ d ≤ coverDenom G z := by
  have hmem := own_mem_cubeIdx hG hn1 hnK hx
  have hlam : 2 ≤ L ^ (n + m₁) :=
    calc 2 ≤ L := hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (n + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
  calc (1 / 4 : ℝ) ^ d ≤ cubeBump m₁ n (ownBase (n + m₁) x) z :=
        cubeBump_ge_quarter_nbr hnK hlam (ownBase_cubeBase x) (ownBase_sameCell x) μ hz
    _ ≤ coverDenom G z := by
        have := Finset.single_le_sum
          (f := fun q : ℕ × CTorus d L N₁ m₁ K => cubeBump m₁ q.1 q.2 z)
          (fun q hq => cubeBump_nonneg_of_mem G hq z) hmem
        exact this

theorem coverDenom_pos (hG : CubeAligned G m₁) (hL : 2 ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) : 0 < coverDenom G x :=
  lt_of_lt_of_le (by positivity) (coverDenom_ge hG hL hn1 hnK hx μ (Or.inl rfl))


/-! ### Active centres -/

variable (G) in
/-- A centre active at `x'` has a point of its cube within `d L ^ (j + m₁)` of `x'`. -/
theorem cube_active_dist (hG : CubeAligned G m₁) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {x' : CTorus d L N₁ m₁ K} (h : cubeBump m₁ q.1 q.2 x' ≠ 0) :
    ∃ z ∈ G.layer q.1, Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x' z ≤ d * (L : ℝ) ^ (q.1 + m₁) := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨t, u, ht, hsc, hd'⟩ := cube_active_lift hmK hb h
  refine ⟨intTorus u, (hG.mem_layer_iff hm1 hmK hsc).2 hl,
    (torusDist_le_of_lift t u ht (fun _ => rfl)).trans ?_⟩
  calc ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ ∑ _μ : Fin d, (L : ℝ) ^ (q.1 + m₁) :=
        Finset.sum_le_sum fun μ _ => by exact_mod_cast hd' μ
    _ = d * (L : ℝ) ^ (q.1 + m₁) := by simp

/-- A centre active at a point `x'` within distance one of a site `x` of layer `n` has layer `m`
with `|m - n| ≤ 1`. -/
theorem cubeActive_layer_bounds (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x x' : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (hxx' : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x x' ≤ 1)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeActive G x') : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  obtain ⟨hqi, hne⟩ := (mem_cubeActive G).1 hq
  obtain ⟨⟨hm1, hmK⟩, -, -⟩ := (mem_cubeIdx G).1 hqi
  obtain ⟨z, hz, hdz⟩ := cube_active_dist G hG hqi hne
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hL'
  have htri := Green.torusDist_triangle_gen x x' z
  refine layer_bounds_cube m₁ G hϱ hm1 hmK hn1 hnK hx hz (htri.trans ?_) hL
  nlinarith

open Classical in
theorem card_cubeActive_le (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x x' : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (hxx' : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x x' ≤ 1) :
    (cubeActive G x').card ≤ 3 * 3 ^ d := by
  set M : Finset ℕ := (Finset.Icc (n - 1) (n + 1)).filter (fun m => 1 ≤ m ∧ m ≤ K) with hM
  have hMc : M.card ≤ 3 := by
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]; omega
  have hsub : cubeActive G x' ⊆ M.biUnion (fun m =>
      ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun y0 => CubeBase m₁ m y0 ∧ cubeBump m₁ m y0 x' ≠ 0)).image (fun y0 => (m, y0))) := by
    intro q hq
    obtain ⟨hqi, hne⟩ := (mem_cubeActive G).1 hq
    obtain ⟨⟨hm1, hmK⟩, -, hb⟩ := (mem_cubeIdx G).1 hqi
    have hl := cubeActive_layer_bounds hG hϱ hd hL hn1 hnK hx hxx' hq
    rw [Finset.mem_biUnion]
    refine ⟨q.1, ?_, ?_⟩
    · rw [hM, Finset.mem_filter, Finset.mem_Icc]; omega
    · rw [Finset.mem_image]
      exact ⟨q.2, by simp [hb, hne], rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ m ∈ M, (((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
          (fun y0 => CubeBase m₁ m y0 ∧ cubeBump m₁ m y0 x' ≠ 0)).image (fun y0 => (m, y0))).card
      ≤ ∑ _m ∈ M, 3 ^ d := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine card_image_le.trans ?_
        exact card_cube_bases_le (by rw [hM, Finset.mem_filter] at hm; exact hm.2.2) x'
    _ = M.card * 3 ^ d := by simp
    _ ≤ 3 * 3 ^ d := Nat.mul_le_mul_right _ hMc

theorem coverDenom_le (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn1 : 1 ≤ n)
    (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) :
    coverDenom G x ≤ 3 * 3 ^ d * 4 ^ d := by
  have hsub : cubeActive G x ⊆ cubeIdx G := fun q hq => ((mem_cubeActive G).1 hq).1
  have : coverDenom G x = ∑ q ∈ cubeActive G x, cubeBump m₁ q.1 q.2 x := by
    unfold coverDenom
    symm
    refine Finset.sum_subset hsub fun q hq hqa => ?_
    exact cubeBump_eq_zero_of_not_active G hq hqa
  rw [this]
  calc ∑ q ∈ cubeActive G x, cubeBump m₁ q.1 q.2 x ≤ ∑ _q ∈ cubeActive G x, (4 : ℝ) ^ d :=
        Finset.sum_le_sum fun q hq =>
          cubeBump_le ((mem_cubeIdx G).1 ((mem_cubeActive G).1 hq).1).1.2 _ _
    _ = (cubeActive G x).card * 4 ^ d := by simp
    _ ≤ (3 * 3 ^ d : ℕ) * (4 : ℝ) ^ d := by
        have := card_cubeActive_le hG hϱ hd hL hn1 hnK hx (torusDist_self_le x)
        have h2 : ((cubeActive G x).card : ℝ) ≤ ((3 * 3 ^ d : ℕ) : ℝ) := by exact_mod_cast this
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 3 * 3 ^ d * 4 ^ d := by push_cast; ring

theorem chi_nonneg (hG : CubeAligned G m₁) (hL : 2 ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : 0 ≤ chi G q x :=
  div_nonneg (cubeBump_nonneg_of_mem G hq x) (coverDenom_pos hG hL hn1 hnK hx μ).le

theorem chi_le_one (hG : CubeAligned G m₁) (hL : 2 ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : chi G q x ≤ 1 := by
  unfold chi
  rw [div_le_one (coverDenom_pos hG hL hn1 hnK hx μ)]
  have := Finset.single_le_sum
    (f := fun q : ℕ × CTorus d L N₁ m₁ K => cubeBump m₁ q.1 q.2 x)
    (fun q hq => cubeBump_nonneg_of_mem G hq x) hq
  exact this

/-- **(Cov1)** `∑_z χ_z = 1` on `Ω₁`. -/
theorem sum_chi (hG : CubeAligned G m₁) (hL : 2 ≤ L) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) :
    ∑ q ∈ cubeIdx G, chi G q x = 1 := by
  unfold chi
  rw [← Finset.sum_div]
  exact div_self (coverDenom_pos hG hL hn1 hnK hx μ).ne'

theorem chi_eq_zero {x : CTorus d L N₁ m₁ K} {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (h : q ∉ cubeActive G x) : chi G q x = 0 := by
  unfold chi; rw [cubeBump_eq_zero_of_not_active G hq h, zero_div]


/-! ### Difference bounds (Cov3) -/

/-- The centres active at `x` or at one of `x ± e_μ`. -/
noncomputable def cubeSupp (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (x : CTorus d L N₁ m₁ K)
    (μ : Fin d) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  cubeActive G x ∪ cubeActive G (x + Pi.single μ 1) ∪ cubeActive G (x - Pi.single μ 1)

theorem cubeSupp_subset (x : CTorus d L N₁ m₁ K) (μ : Fin d) : cubeSupp G x μ ⊆ cubeIdx G := by
  intro q hq
  simp only [cubeSupp, Finset.mem_union] at hq
  rcases hq with (h | h) | h <;> exact ((mem_cubeActive G).1 h).1

theorem not_mem_cubeSupp {x : CTorus d L N₁ m₁ K} {μ : Fin d} {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (h : q ∉ cubeSupp G x μ) :
    cubeBump m₁ q.1 q.2 x = 0 ∧ cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) = 0 ∧
      cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) = 0 := by
  simp only [cubeSupp, Finset.mem_union, not_or] at h
  exact ⟨cubeBump_eq_zero_of_not_active G hq h.1.1, cubeBump_eq_zero_of_not_active G hq h.1.2,
    cubeBump_eq_zero_of_not_active G hq h.2⟩

theorem card_cubeSupp_le (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn1 : 1 ≤ n)
    (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) :
    (cubeSupp G x μ).card ≤ 9 * 3 ^ d := by
  have h1 := card_cubeActive_le hG hϱ hd hL hn1 hnK hx (torusDist_self_le x)
  have h2 := card_cubeActive_le hG hϱ hd hL hn1 hnK hx (adj_add x μ).torusDist_le
  have h3 := card_cubeActive_le hG hϱ hd hL hn1 hnK hx (adj_sub x μ).torusDist_le
  unfold cubeSupp
  calc _ ≤ (cubeActive G x ∪ cubeActive G (x + Pi.single μ 1)).card +
        (cubeActive G (x - Pi.single μ 1)).card := card_union_le _ _
    _ ≤ (cubeActive G x).card + (cubeActive G (x + Pi.single μ 1)).card +
        (cubeActive G (x - Pi.single μ 1)).card := by
        have := card_union_le (cubeActive G x) (cubeActive G (x + Pi.single μ 1)); omega
    _ ≤ 9 * 3 ^ d := by omega

theorem cubeSupp_layer_bounds (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeSupp G x μ) : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  simp only [cubeSupp, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · exact cubeActive_layer_bounds hG hϱ hd hL hn1 hnK hx (torusDist_self_le x) h
  · exact cubeActive_layer_bounds hG hϱ hd hL hn1 hnK hx (adj_add x μ).torusDist_le h
  · exact cubeActive_layer_bounds hG hϱ hd hL hn1 hnK hx (adj_sub x μ).torusDist_le h

theorem cubeBump_diff_supp (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeSupp G x μ) :
    |cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) - cubeBump m₁ q.1 q.2 x| ≤
        wb1 d * L / (L : ℝ) ^ (n + m₁) ∧
    |cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) - cubeBump m₁ q.1 q.2 x| ≤
        wb1 d * L / (L : ℝ) ^ (n + m₁) ∧
    |cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) + cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) -
        2 * cubeBump m₁ q.1 q.2 x| ≤ wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
  have hbl := cubeSupp_layer_bounds hG hϱ hd (by omega) hn1 hnK hx μ hq
  obtain ⟨⟨hm1, hmK⟩, -, -⟩ := (mem_cubeIdx G).1 (cubeSupp_subset x μ hq)
  have hlam : 2 ≤ L ^ (q.1 + m₁) :=
    calc 2 ≤ L := hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (q.1 + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨d1, d1', d2⟩ := cubeBump_diff hmK hlam q.2 x μ
  have hs := scale_ge (m := q.1 + m₁) (n := n + m₁) (by omega) (by omega : 1 ≤ L)
  have hLm : (0 : ℝ) < (L : ℝ) ^ (q.1 + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hLn : (0 : ℝ) < (L : ℝ) ^ (n + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have key1 : 150 * (4 : ℝ) ^ d / (L : ℝ) ^ (q.1 + m₁) ≤ wb1 d * L / (L : ℝ) ^ (n + m₁) := by
    unfold wb1
    rw [div_le_div_iff₀ hLm hLn]
    have : (0 : ℝ) ≤ 150 * 4 ^ d := by positivity
    nlinarith
  have key2 : 20 * (4 : ℝ) ^ d / ((L : ℝ) ^ (q.1 + m₁)) ^ 2 ≤
      wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
    unfold wb2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ 20 * 4 ^ d := by positivity
    have h3 : ((L : ℝ) ^ (n + m₁)) ^ 2 ≤ ((L : ℝ) * (L : ℝ) ^ (q.1 + m₁)) ^ 2 :=
      pow_le_pow_left₀ hLn.le hs 2
    nlinarith
  exact ⟨d1.trans key1, d1'.trans key1, d2.trans key2⟩

theorem sum_abs_le_cubeSupp {x : CTorus d L N₁ m₁ K} {μ : Fin d}
    {f : ℕ × CTorus d L N₁ m₁ K → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ q ∈ cubeIdx G, q ∉ cubeSupp G x μ → f q = 0) (h1 : ∀ q ∈ cubeSupp G x μ, |f q| ≤ c)
    (hcard : (cubeSupp G x μ).card ≤ 9 * 3 ^ d) :
    |∑ q ∈ cubeIdx G, f q| ≤ 9 * 3 ^ d * c := by
  rw [← Finset.sum_subset (cubeSupp_subset x μ) h0]
  calc |∑ q ∈ cubeSupp G x μ, f q| ≤ ∑ q ∈ cubeSupp G x μ, |f q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ cubeSupp G x μ, c := Finset.sum_le_sum h1
    _ = (cubeSupp G x μ).card * c := by simp
    _ ≤ (9 * 3 ^ d : ℕ) * c := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
    _ = 9 * 3 ^ d * c := by push_cast; ring

theorem coverDenom_diff (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) :
    |coverDenom G (x + Pi.single μ 1) - coverDenom G x| ≤ wU d L / (L : ℝ) ^ (n + m₁) ∧
    |coverDenom G (x - Pi.single μ 1) - coverDenom G x| ≤ wU d L / (L : ℝ) ^ (n + m₁) ∧
    |coverDenom G (x + Pi.single μ 1) + coverDenom G (x - Pi.single μ 1) - 2 * coverDenom G x| ≤
      wV d L / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
  have hcard := card_cubeSupp_le hG hϱ hd (by omega) hn1 hnK hx μ
  have hLn : (0 : ℝ) < (L : ℝ) ^ (n + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hb1 := wb1_nonneg d
  have hb2 := wb2_nonneg d
  have hsupp := fun q (hq : q ∈ cubeSupp G x μ) => cubeBump_diff_supp hG hϱ hd hL hn1 hnK hx μ hq
  refine ⟨?_, ?_, ?_⟩
  · have := sum_abs_le_cubeSupp (G := G) (x := x) (μ := μ)
      (f := fun q => cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) - cubeBump m₁ q.1 q.2 x)
      (c := wb1 d * L / (L : ℝ) ^ (n + m₁)) (by positivity)
      (fun q hq hqs => by
        obtain ⟨h1, h2, h3⟩ := not_mem_cubeSupp hq hqs; simp [h1, h2])
      (fun q hq => (hsupp q hq).1) hcard
    unfold coverDenom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wU; ring
  · have := sum_abs_le_cubeSupp (G := G) (x := x) (μ := μ)
      (f := fun q => cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) - cubeBump m₁ q.1 q.2 x)
      (c := wb1 d * L / (L : ℝ) ^ (n + m₁)) (by positivity)
      (fun q hq hqs => by
        obtain ⟨h1, h2, h3⟩ := not_mem_cubeSupp hq hqs; simp [h1, h3])
      (fun q hq => (hsupp q hq).2.1) hcard
    unfold coverDenom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wU; ring
  · have := sum_abs_le_cubeSupp (G := G) (x := x) (μ := μ)
      (f := fun q => cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) +
        cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) - 2 * cubeBump m₁ q.1 q.2 x)
      (c := wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ (n + m₁)) ^ 2) (by positivity)
      (fun q hq hqs => by
        obtain ⟨h1, h2, h3⟩ := not_mem_cubeSupp hq hqs; simp [h1, h2, h3])
      (fun q hq => (hsupp q hq).2.2) hcard
    unfold coverDenom
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wV; ring

/-- Constants of the first and second differences of `χ_z` (denominator bound `4⁻ᵈ`). -/
noncomputable def cH1 (d L : ℕ) : ℝ := (wb1 d * L + wU d L) / (1 / 4 : ℝ) ^ d
noncomputable def cH2 (d L : ℕ) : ℝ :=
  (wb2 d * (L : ℝ) ^ 2 + wV d L + 2 * cH1 d L * wU d L) / (1 / 4 : ℝ) ^ d

theorem cH1_nonneg (d L : ℕ) : 0 ≤ cH1 d L := by
  unfold cH1; have := wb1_nonneg d; have := wU_nonneg d L; positivity

theorem cH2_nonneg (d L : ℕ) : 0 ≤ cH2 d L := by
  unfold cH2; have := wb2_nonneg d; have := wV_nonneg d L; have := wU_nonneg d L
  have := cH1_nonneg d L; positivity

/-- **(Cov3)** First and second differences of `χ_z` along `±e_μ` at a site `x` of layer `n`
(including `n = 1`, whose neighbours may lie outside `Ω₁`): they are at most
`C_χ / (M₁ ℓ(x))` and `C_χ / (M₁ ℓ(x))²`, `ℓ(x) = L ^ n`, `M₁ = L ^ m₁`. -/
theorem chi_diff (hG : CubeAligned G m₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    |chi G q (x + Pi.single μ 1) - chi G q x| ≤ cH1 d L / (L : ℝ) ^ (n + m₁) ∧
    |chi G q (x - Pi.single μ 1) - chi G q x| ≤ cH1 d L / (L : ℝ) ^ (n + m₁) ∧
    |chi G q (x + Pi.single μ 1) + chi G q (x - Pi.single μ 1) - 2 * chi G q x| ≤
      cH2 d L / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
  have hLn : (0 : ℝ) < (L : ℝ) ^ (n + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hH1 := cH1_nonneg d L
  have hH2 := cH2_nonneg d L
  by_cases hs : q ∈ cubeSupp G x μ
  · have hq0 : (0 : ℝ) < (1 / 4 : ℝ) ^ d := by positivity
    have hDp := coverDenom_ge hG hL hn1 hnK hx μ (Or.inr (Or.inl rfl))
    have hDm := coverDenom_ge hG hL hn1 hnK hx μ (Or.inr (Or.inr rfl))
    have hD0 := coverDenom_ge hG hL hn1 hnK hx μ (Or.inl rfl)
    obtain ⟨Dd1, Dd1', Dd2⟩ := coverDenom_diff hG hϱ hd hL hn1 hnK hx μ
    obtain ⟨Bd1, Bd1', Bd2⟩ := cubeBump_diff_supp hG hϱ hd hL hn1 hnK hx μ hs
    have hb0 := cubeBump_nonneg_of_mem G hq x
    have hbD : cubeBump m₁ q.1 q.2 x ≤ coverDenom G x := by
      have := Finset.single_le_sum
        (f := fun q : ℕ × CTorus d L N₁ m₁ K => cubeBump m₁ q.1 q.2 x)
        (fun q hq => cubeBump_nonneg_of_mem G hq x) hq
      exact this
    have f1 : |chi G q (x + Pi.single μ 1) - chi G q x| ≤ cH1 d L / (L : ℝ) ^ (n + m₁) := by
      have := weight_step hq0 hDp hD0 hb0 hbD Bd1 Dd1
      refine this.trans (le_of_eq ?_)
      unfold cH1; field_simp
    have f2 : |chi G q (x - Pi.single μ 1) - chi G q x| ≤ cH1 d L / (L : ℝ) ^ (n + m₁) := by
      have := weight_step hq0 hDm hD0 hb0 hbD Bd1' Dd1'
      refine this.trans (le_of_eq ?_)
      unfold cH1; field_simp
    refine ⟨f1, f2, ?_⟩
    have hDp0 : coverDenom G (x + Pi.single μ 1) ≠ 0 := (lt_of_lt_of_le hq0 hDp).ne'
    have hDm0 : coverDenom G (x - Pi.single μ 1) ≠ 0 := (lt_of_lt_of_le hq0 hDm).ne'
    have hD00 : coverDenom G x ≠ 0 := (lt_of_lt_of_le hq0 hD0).ne'
    have e1 : chi G q (x + Pi.single μ 1) * coverDenom G (x + Pi.single μ 1) =
        cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) := by unfold chi; field_simp
    have e2 : chi G q (x - Pi.single μ 1) * coverDenom G (x - Pi.single μ 1) =
        cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) := by unfold chi; field_simp
    have e3 : chi G q x * coverDenom G x = cubeBump m₁ q.1 q.2 x := by unfold chi; field_simp
    have := weight_second_alg (wp := chi G q (x + Pi.single μ 1))
      (wm := chi G q (x - Pi.single μ 1)) (w0 := chi G q x)
      (Dp := coverDenom G (x + Pi.single μ 1)) (Dm := coverDenom G (x - Pi.single μ 1))
      (D0 := coverDenom G x) (q0 := (1 / 4 : ℝ) ^ d)
      (B2 := wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ (n + m₁)) ^ 2)
      (V := wV d L / ((L : ℝ) ^ (n + m₁)) ^ 2)
      (U := wU d L / (L : ℝ) ^ (n + m₁)) (H := cH1 d L / (L : ℝ) ^ (n + m₁)) hq0 hD0
      (chi_nonneg hG hL hn1 hnK hx μ hq) (chi_le_one hG hL hn1 hnK hx μ hq)
      (by rw [e1, e2, e3]; exact Bd2) Dd2 f1 f2 Dd1 Dd1'
    refine this.trans (le_of_eq ?_)
    unfold cH2; field_simp
  · obtain ⟨h1, h2, h3⟩ := not_mem_cubeSupp hq hs
    have z0 : chi G q x = 0 := by unfold chi; rw [h1, zero_div]
    have z1 : chi G q (x + Pi.single μ 1) = 0 := by unfold chi; rw [h2, zero_div]
    have z2 : chi G q (x - Pi.single μ 1) = 0 := by unfold chi; rw [h3, zero_div]
    rw [z0, z1, z2]
    simp only [sub_zero, abs_zero, add_zero, mul_zero]
    refine ⟨by positivity, by positivity, by positivity⟩


/-! ### The cubes `C_z`, `□_z` as periodic boxes -/

section Boxes

omit [NeZero N₁] [NeZero L] in
/-- The box of half-width `R` (in the `ℓ^∞` sense, periodically) around the centre of the cube of
layer `j` and base `y0`: the centre has coordinates `y0 + (L ^ (j + m₁) - 1) / 2`. -/
def InBox (m₁ j : ℕ) (y0 : CTorus d L N₁ m₁ K) (R : ℝ) (x : CTorus d L N₁ m₁ K) : Prop :=
  ∀ μ, ∃ p : ℤ, |((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
    (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < R

omit [NeZero N₁] [NeZero L] in
theorem InBox.mono {j : ℕ} {y0 x : CTorus d L N₁ m₁ K} {R R' : ℝ} (h : InBox m₁ j y0 R x)
    (hR : R ≤ R') : InBox m₁ j y0 R' x := fun μ => by
  obtain ⟨p, hp⟩ := h μ
  exact ⟨p, lt_of_lt_of_le hp hR⟩

omit [NeZero N₁] in
/-- **(Cov2), support.**  The support of the bump (hence of `χ_z`) is contained in the open cube
`C_z` of side `3 M₁ ℓ_j` centred at the centre of the cube. -/
theorem inBox_of_cubeBump_ne_zero {j : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (h : cubeBump m₁ j y0 x ≠ 0) : InBox m₁ j y0 (3 / 2 * (L : ℝ) ^ (j + m₁)) x := by
  intro μ
  unfold cubeBump bump at h
  have hμ := Finset.prod_ne_zero_iff.1 h μ (Finset.mem_univ μ)
  unfold perFac at hμ
  obtain ⟨p, hp⟩ := exists_of_perN_ne_zero hμ
  have hl0 : (0 : ℝ) < (L : ℝ) ^ (j + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hS : (((N₁ * L ^ (K + m₁) : ℕ)) : ℝ) = (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) := by
    rw [cubeSide_eq]
  refine ⟨p, ?_⟩
  have e : (((tor m₁ x μ).val : ℝ) - bumpCentre (j + m₁) (tor m₁ y0) μ) / (L : ℝ) ^ (j + m₁) +
      p * (((N₁ * L ^ (K + m₁) : ℕ) : ℝ) / (L : ℝ) ^ (j + m₁)) =
      (((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
        (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)) / (L : ℝ) ^ (j + m₁) := by
    unfold bumpCentre
    rw [tor_val, tor_val, hS]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hl0, div_lt_iff₀ hl0] at hp
  exact hp

/-- Moving a point by an integer vector of size `B` enlarges the box by `B`. -/
theorem InBox.add_int {j : ℕ} {y0 x : CTorus d L N₁ m₁ K} {R : ℝ} (h : InBox m₁ j y0 R x)
    (w : Fin d → ℤ) {B : ℝ} (hw : ∀ μ, |(w μ : ℝ)| ≤ B) :
    InBox m₁ j y0 (R + B) (x + (intTorus w : CTorus d L N₁ m₁ K)) := by
  intro μ
  obtain ⟨p, hp⟩ := h μ
  have hz : ((((x + (intTorus w : CTorus d L N₁ m₁ K)) μ).val : ℕ) :
      ZMod ((N₁ * L ^ m₁) * L ^ K)) = (((x μ).val + w μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
    rw [ZMod.natCast_zmod_val]
    push_cast
    simp [intTorus_apply]
  have hdvd : (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) ∣
      ((((x + (intTorus w : CTorus d L N₁ m₁ K)) μ).val : ℕ) : ℤ) - ((x μ).val + w μ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hz ⊢
    rw [hz]; ring
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨p - q, ?_⟩
  have hq' : ((((x + (intTorus w : CTorus d L N₁ m₁ K)) μ).val : ℕ) : ℝ) =
      (x μ).val + w μ + (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) * q := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hq
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_add, Int.cast_mul] at this
    linarith
  have hw' := abs_le.1 (hw μ)
  rw [hq', Int.cast_sub]
  rw [abs_lt] at hp ⊢
  constructor <;> nlinarith [hp.1, hp.2]

/-- **(Cov4)** For `M₁ ≥ 4 L²` the interaction cube `□_z` (half-width `5/2 M₁ ℓ_j`) contains the
`ℓ^∞`-neighbourhood of size `2 L² ℓ_j + 1` of `C_z` (half-width `3/2 M₁ ℓ_j`). -/
theorem inBox_cov4 (hM : 4 * L ^ 2 ≤ L ^ m₁) {j : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (h : InBox m₁ j y0 (3 / 2 * (L : ℝ) ^ (j + m₁)) x) (w : Fin d → ℤ)
    (hw : ∀ μ, |(w μ : ℝ)| ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ j + 1) :
    InBox m₁ j y0 (5 / 2 * (L : ℝ) ^ (j + m₁)) (x + (intTorus w : CTorus d L N₁ m₁ K)) := by
  refine (h.add_int w hw).mono ?_
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ j),
    one_le_pow₀ (n := 2) hL1]

/-- The torus distance from a point of a box to the base of its cube. -/
theorem torusDist_le_of_inBox {j : ℕ} {y0 x : CTorus d L N₁ m₁ K} {R : ℝ}
    (h : InBox m₁ j y0 R x) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y0 ≤ d * (R + (L : ℝ) ^ (j + m₁) / 2) := by
  classical
  choose p hp using h
  set t : Fin d → ℤ := fun μ => ((x μ).val : ℤ) + p μ * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) with ht
  set u : Fin d → ℤ := fun μ => ((y0 μ).val : ℤ) with hu
  have hS0 : ((((N₁ * L ^ m₁) * L ^ K : ℕ) : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = 0 := by
    rw [Int.cast_natCast]; exact ZMod.natCast_self _
  have htx : ∀ μ, ((t μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = x μ := by
    intro μ
    simp only [ht, Int.cast_add, Int.cast_mul, hS0, mul_zero, add_zero, Int.cast_natCast,
      ZMod.natCast_zmod_val]
  have huy : ∀ μ, ((u μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = y0 μ := by
    intro μ
    simp [hu]
  refine (torusDist_le_of_lift t u htx huy).trans ?_
  have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  calc ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ ∑ _μ : Fin d, (R + (L : ℝ) ^ (j + m₁) / 2) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        have h1 := abs_lt.1 (hp μ)
        have e : ((t μ - u μ).natAbs : ℝ) = |((t μ : ℝ) - u μ)| := by
          rw [Nat.cast_natAbs]; push_cast; rfl
        have hT : ((t μ : ℤ) : ℝ) = ((x μ).val : ℝ) +
            p μ * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) := by simp [ht]
        have hU : ((u μ : ℤ) : ℝ) = ((y0 μ).val : ℝ) := by simp [hu]
        rw [e, abs_le, hT, hU]
        constructor <;> nlinarith [h1.1, h1.2]
    _ = d * (R + (L : ℝ) ^ (j + m₁) / 2) := by simp; ring

open Classical in
/-- Counting the cubes of one layer whose box contains `v`. -/
theorem card_cube_bases_inBox {j : ℕ} (hj : j ≤ K) (v : Fin d → ℝ) {s : ℝ} (N : ℕ)
    (hs : 2 * s ≤ N) :
    ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter (fun y0 => CubeBase m₁ j y0 ∧ ∀ μ,
      ∃ p : ℤ, |v μ + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
        (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < s * (L : ℝ) ^ (j + m₁))).card ≤
      N ^ d := by
  have hl0 : (0 : ℝ) < (L : ℝ) ^ (j + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hS : (((N₁ * L ^ (K + m₁) : ℕ)) : ℝ) = (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) := by
    rw [cubeSide_eq]
  set T : Finset (Torus d (N₁ * L ^ (K + m₁))) := (Finset.univ.filter
      (fun y0 => IsBase (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (j + m₁) y0 ∧ ∀ μ, ∃ p : ℤ,
        |(v μ - bumpCentre (j + m₁) y0 μ) / (L : ℝ) ^ (j + m₁) +
          p * (((N₁ * L ^ (K + m₁) : ℕ) : ℝ) / (L : ℝ) ^ (j + m₁))| < s)) with hT
  calc _ ≤ T.card := Finset.card_le_card_of_injOn (tor m₁) (fun y0 hy => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
        rw [hT, Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, isBase_tor.2 hy.1, fun μ => ?_⟩
        obtain ⟨p, hp⟩ := hy.2 μ
        refine ⟨p, ?_⟩
        have e : (v μ - bumpCentre (j + m₁) (tor m₁ y0) μ) / (L : ℝ) ^ (j + m₁) +
            p * (((N₁ * L ^ (K + m₁) : ℕ) : ℝ) / (L : ℝ) ^ (j + m₁)) =
            (v μ + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
              (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)) / (L : ℝ) ^ (j + m₁) := by
          unfold bumpCentre
          rw [tor_val, hS]
          field_simp
          ring
        rw [e, abs_div, abs_of_pos hl0, div_lt_iff₀ hl0]
        exact hp) (tor_injective.injOn)
    _ ≤ N ^ d := card_bases_window (by omega) v N hs

open Classical in
/-- **Multiplicity of the boxes.**  A site of layer `n` lies in at most `3 N ^ d` of the boxes of
half-width `s M₁ ℓ_j` (`2 s ≤ N`, `s ≤ 7/2`) of the centres: `s = 3/2`, `N = 3` gives the bound
`c_d = 3 ^ (d + 1)` of (Cov2) for the cubes `C_z`; `s = 5/2`, `N = 5` gives the bound
`c_d' = 3 · 5 ^ d` for the interaction cubes `□_z`. -/
theorem card_inBox_le
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) {s : ℝ}
    (hs7 : s ≤ 7 / 2) (N : ℕ) (hs : 2 * s ≤ N) :
    ((cubeIdx G).filter (fun q => InBox m₁ q.1 q.2 (s * (L : ℝ) ^ (q.1 + m₁)) x)).card ≤
      3 * N ^ d := by
  set M : Finset ℕ := (Finset.Icc (n - 1) (n + 1)).filter (fun m => 1 ≤ m ∧ m ≤ K) with hM
  have hMc : M.card ≤ 3 := by
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]; omega
  have hsub : ((cubeIdx G).filter (fun q => InBox m₁ q.1 q.2 (s * (L : ℝ) ^ (q.1 + m₁)) x)) ⊆
      M.biUnion (fun m => ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun y0 => CubeBase m₁ m y0 ∧ ∀ μ, ∃ p : ℤ, |((x μ).val : ℝ) +
          p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
          (((y0 μ).val : ℝ) + ((L : ℝ) ^ (m + m₁) - 1) / 2)| < s * (L : ℝ) ^ (m + m₁))).image
            (fun y0 => (m, y0))) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqi, hbox⟩ := hq
    obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hqi
    have hdist := torusDist_le_of_inBox hbox
    have hd1 : (0 : ℝ) ≤ d := by positivity
    have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) :=
      one_le_pow₀ (by exact_mod_cast hL)
    have hbound := layer_bounds_cube m₁ G hϱ hm1 hmK hn1 hnK hx hl
      (hdist.trans (by
        have := mul_nonneg (mul_nonneg hd1 (le_trans zero_le_one hl1))
          (by linarith : (0 : ℝ) ≤ 4 - (s + 1 / 2))
        nlinarith)) hL
    rw [Finset.mem_biUnion]
    refine ⟨q.1, ?_, ?_⟩
    · rw [hM, Finset.mem_filter, Finset.mem_Icc]; omega
    · rw [Finset.mem_image]
      exact ⟨q.2, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hb, hbox⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ m ∈ M, (((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun y0 => CubeBase m₁ m y0 ∧ ∀ μ, ∃ p : ℤ, |((x μ).val : ℝ) +
          p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
          (((y0 μ).val : ℝ) + ((L : ℝ) ^ (m + m₁) - 1) / 2)| < s * (L : ℝ) ^ (m + m₁))).image
            (fun y0 => (m, y0))).card
      ≤ ∑ _m ∈ M, N ^ d := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine card_image_le.trans ?_
        exact card_cube_bases_inBox (by rw [hM, Finset.mem_filter] at hm; exact hm.2.2)
          (fun μ => ((x μ).val : ℝ)) N hs
    _ = M.card * N ^ d := by simp
    _ ≤ 3 * N ^ d := Nat.mul_le_mul_right _ hMc

/-! ### The parameter cubes `𝒬(z)` and the counts -/

/-- The half-width of the thickened interaction cube `□̂_z`: `5/2 M₁ ℓ_j + ρ_*`,
`ρ_* = 3 L² ℓ_j`. -/
noncomputable def hatRad (L m₁ j : ℕ) : ℝ := 5 / 2 * (L : ℝ) ^ (j + m₁) + 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ j

open Classical in
/-- `𝒬(z)`: the centres (cubes of the cover) meeting the thickened interaction cube `□̂_z`. -/
noncomputable def Qset (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter (fun q' => ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
    InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y)

theorem mem_Qset {q q' : ℕ × CTorus d L N₁ m₁ K} :
    q' ∈ Qset G q ↔ q' ∈ cubeIdx G ∧ ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
      InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y := by
  classical
  simp [Qset]

/-- A cube meeting the thickened interaction cube of `q` has layer within one of that of `q`. -/
theorem Qset_layer (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q q' : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (hq' : q' ∈ Qset G q) : q.1 ≤ q'.1 + 1 ∧ q'.1 ≤ q.1 + 1 := by
  obtain ⟨hqi', y, hy, hbox⟩ := (mem_Qset).1 hq'
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨⟨hm1', hmK'⟩, hl', hb'⟩ := (mem_cubeIdx G).1 hqi'
  have hyl : y ∈ G.layer q'.1 := (hG.mem_layer_iff hm1' hmK' hy).2 hl'
  have hdist := torusDist_le_of_inBox hbox
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 :=
    one_le_pow₀ (by exact_mod_cast hL)
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hlam : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ q.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  have key : hatRad L m₁ q.1 + (L : ℝ) ^ (q.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (q.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ q.1)
    rw [hlam] at *
    nlinarith
  have := layer_bounds_cube m₁ G hϱ hm1 hmK hm1' hmK' hyl hl
    (hdist.trans (by nlinarith [mul_le_mul_of_nonneg_left key hd1])) hL
  omega

open Classical in
/-- **The count `N₀`.**  At most `3 (8 L) ^ d` cubes of the cover meet the thickened interaction
cube of a centre. -/
theorem card_Qset_le (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    (Qset G q).card ≤ 3 * (8 * L) ^ d := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  set M : Finset ℕ := (Finset.Icc (q.1 - 1) (q.1 + 1)).filter (fun m => 1 ≤ m ∧ m ≤ K) with hMdef
  have hMc : M.card ≤ 3 := by
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]; omega
  set v : Fin d → ℝ := fun μ => ((q.2 μ).val : ℝ) + ((L : ℝ) ^ (q.1 + m₁) - 1) / 2 with hv
  have hsub : Qset G q ⊆ M.biUnion (fun m => ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun y0 => CubeBase m₁ m y0 ∧ ∀ μ, ∃ p : ℤ, |v μ +
          p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
          (((y0 μ).val : ℝ) + ((L : ℝ) ^ (m + m₁) - 1) / 2)| < (4 * L) * (L : ℝ) ^ (m + m₁))).image
            (fun y0 => (m, y0))) := by
    intro q' hq'
    have hlay := Qset_layer hG hϱ hM hL hq hq'
    obtain ⟨hqi', y, hy, hbox⟩ := (mem_Qset).1 hq'
    obtain ⟨⟨hm1', hmK'⟩, hl', hb'⟩ := (mem_cubeIdx G).1 hqi'
    rw [Finset.mem_biUnion]
    refine ⟨q'.1, ?_, ?_⟩
    · rw [hMdef, Finset.mem_filter, Finset.mem_Icc]; omega
    · rw [Finset.mem_image]
      refine ⟨q'.2, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hb', fun μ => ?_⟩
      obtain ⟨p, hp⟩ := hbox μ
      refine ⟨-p, ?_⟩
      set lam' : ℕ := L ^ (q'.1 + m₁) with hlam'
      have hlpos : 0 < lam' := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
      have hbq : (q'.2 μ).val = lam' * ((y μ).val / lam') := by
        rw [hy μ]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb' μ))).symm
      have e1 := Nat.div_mul_le_self (y μ).val lam'
      have e2 := Nat.lt_div_mul_add (a := (y μ).val) hlpos
      have n1 : (q'.2 μ).val ≤ (y μ).val := by
        rw [hbq]; linarith [mul_comm lam' ((y μ).val / lam')]
      have n2 : (y μ).val + 1 ≤ (q'.2 μ).val + lam' := by
        rw [hbq]; linarith [mul_comm lam' ((y μ).val / lam')]
      have r1 : ((q'.2 μ).val : ℝ) ≤ (y μ).val := by exact_mod_cast n1
      have r2 : ((y μ).val : ℝ) + 1 ≤ (q'.2 μ).val + (L : ℝ) ^ (q'.1 + m₁) := by
        have : (((y μ).val + 1 : ℕ) : ℝ) ≤ (((q'.2 μ).val + lam' : ℕ) : ℝ) := by exact_mod_cast n2
        simpa [hlam'] using this
      have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
      have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
      have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hLr
      have hlam : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ q.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
      have hlr : (L : ℝ) ^ (q.1 + m₁) ≤ L * (L : ℝ) ^ (q'.1 + m₁) :=
        scale_ge (m := q'.1 + m₁) (n := q.1 + m₁) (by omega) hL
      have hρ := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ q.1)
      have hl'1 : (1 : ℝ) ≤ (L : ℝ) ^ (q'.1 + m₁) := one_le_pow₀ hLr
      have hRh : hatRad L m₁ q.1 ≤ 13 / 4 * ((L : ℝ) * (L : ℝ) ^ (q'.1 + m₁)) := by
        unfold hatRad
        rw [hlam] at hlr
        rw [hlam]
        nlinarith
      rw [abs_lt] at hp ⊢
      simp only [hv]
      push_cast at hp ⊢
      have hlL : (L : ℝ) ^ (q'.1 + m₁) ≤ L * (L : ℝ) ^ (q'.1 + m₁) := by nlinarith
      constructor <;> nlinarith [hp.1, hp.2]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ m ∈ M, (((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun y0 => CubeBase m₁ m y0 ∧ ∀ μ, ∃ p : ℤ, |v μ +
          p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
          (((y0 μ).val : ℝ) + ((L : ℝ) ^ (m + m₁) - 1) / 2)| < (4 * L) * (L : ℝ) ^ (m + m₁))).image
            (fun y0 => (m, y0))).card
      ≤ ∑ _m ∈ M, (8 * L) ^ d := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine card_image_le.trans ?_
        exact card_cube_bases_inBox (by rw [hMdef, Finset.mem_filter] at hm; exact hm.2.2) v
          (8 * L) (by push_cast; linarith)
    _ = M.card * (8 * L) ^ d := by simp
    _ ≤ 3 * (8 * L) ^ d := Nat.mul_le_mul_right _ hMc

/-- A site of a cell of side `a` differs from another site of the cell by an integer vector of
coordinates smaller than `a` in absolute value. -/
theorem exists_int_of_sameCell {a : ℕ} (ha : 0 < a) {x y : CTorus d L N₁ m₁ K}
    (h : SameCell a x y) :
    ∃ w : Fin d → ℤ, x = y + (intTorus w : CTorus d L N₁ m₁ K) ∧
      ∀ μ, |(w μ : ℝ)| < a := by
  refine ⟨fun μ => ((x μ).val : ℤ) - (y μ).val, ?_, fun μ => ?_⟩
  · funext μ
    simp [intTorus_apply]
  · have hx := Nat.div_add_mod (x μ).val a
    have hy := Nat.div_add_mod (y μ).val a
    have hmx := Nat.mod_lt (x μ).val ha
    have hmy := Nat.mod_lt (y μ).val ha
    rw [← h μ] at hy
    have e : ((x μ).val : ℝ) - (y μ).val = ((x μ).val % a : ℕ) - ((y μ).val % a : ℕ) := by
      have hx' : (((a * ((x μ).val / a) + (x μ).val % a : ℕ)) : ℝ) = (x μ).val := by
        exact_mod_cast hx
      have hy' : (((a * ((x μ).val / a) + (y μ).val % a : ℕ)) : ℝ) = (y μ).val := by
        exact_mod_cast hy
      push_cast at hx' hy'
      linarith
    have r1 : (((x μ).val % a : ℕ) : ℝ) < a := by exact_mod_cast hmx
    have r2 : (((y μ).val % a : ℕ) : ℝ) < a := by exact_mod_cast hmy
    have r3 : (0 : ℝ) ≤ (((x μ).val % a : ℕ) : ℝ) := Nat.cast_nonneg _
    have r4 : (0 : ℝ) ≤ (((y μ).val % a : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    rw [abs_lt]
    constructor <;> linarith

/-- **Locality of the cut.**  If `y` lies in `C_z` and `x` is a neighbour of `y` or lies in the
`n`-block of `y` (`x` of layer `n`), then `x` lies in the interaction cube `□_z`.  Consequently
`χ_z` and the cut commutator `K_z` at `x` only see data inside `□_z`. -/
theorem inSq_of_near (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K) {x y : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (hy : InBox m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁)) y)
    (hnear : (∃ μ, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) ∨ SameCell (L ^ n) x y) :
    InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) x := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hLr
  have key : ∀ w : Fin d → ℤ, x = y + (intTorus w : CTorus d L N₁ m₁ K) →
      (∀ μ, |(w μ : ℝ)| ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 + 1) →
      InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) x := by
    intro w hw hbd
    rw [hw]
    exact inBox_cov4 hM hy w hbd
  have hbig : (1 : ℝ) ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hLr
    nlinarith
  rcases hnear with ⟨μ, hμ | hμ⟩ | hcell
  · refine key (Pi.single μ (-1)) ?_ (fun ν => ?_)
    · funext ν
      by_cases h : ν = μ <;> simp [hμ, intTorus_apply, h]
    · by_cases h : ν = μ
      · subst h; simp; linarith
      · simp [h]; linarith
  · refine key (Pi.single μ 1) ?_ (fun ν => ?_)
    · funext ν
      by_cases h : ν = μ <;> simp [hμ, intTorus_apply, h]
    · by_cases h : ν = μ
      · subst h; simp; linarith
      · simp [h]; linarith
  · have hlpos : 0 < L ^ n := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n
    have hxy : y ∈ G.layer n := (G.mem_layer_iff hn1 hnK (jBlock_eq_of_sameCell hcell)).1 hx
    have hdist := torusDist_le_of_inBox hy
    have hd1 : (0 : ℝ) ≤ d := by positivity
    have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hLr
    have hbound := layer_bounds_cube m₁ G hϱ hm1 hmK hn1 hnK hxy hl
      (hdist.trans (by
        have := mul_nonneg (mul_nonneg hd1 (le_trans zero_le_one hl1))
          (by linarith : (0 : ℝ) ≤ 4 - (3 / 2 + 1 / 2))
        nlinarith)) hL
    obtain ⟨w, hw, hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine key w hw (fun ν => ?_)
    have h1 := hwb ν
    have h2 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (q.1 + 1) := pow_le_pow_right₀ hLr (by omega)
    have h3 : (((L ^ n : ℕ)) : ℝ) = (L : ℝ) ^ n := by push_cast; rfl
    rw [h3] at h1
    have h4 : (L : ℝ) ^ (q.1 + 1) = L * (L : ℝ) ^ q.1 := by ring
    have h5 : (L : ℝ) * (L : ℝ) ^ q.1 ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by nlinarith
    linarith

/-- **(Cov2)** `supp χ_z ⊂ C_z`. -/
theorem inBox_of_chi_ne_zero {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K}
    (h : chi G q x ≠ 0) : InBox m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁)) x := by
  apply inBox_of_cubeBump_ne_zero
  intro h0
  apply h
  unfold chi
  rw [h0, zero_div]

open Classical in
/-- **(Cov2), multiplicity.**  A site of layer `n` lies in the support of at most
`c_d = 3 ^ (d + 1)` of the functions `χ_z` (hence in at most `c_d` of the cubes `C_z`). -/
theorem card_chi_ne_zero_le
    (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) :
    ((cubeIdx G).filter (fun q => chi G q x ≠ 0)).card ≤ 3 ^ (d + 1) := by
  have := card_inBox_le hϱ hL hn1 hnK hx (s := 3 / 2) (by norm_num) 3 (by norm_num)
  refine le_trans (Finset.card_le_card ?_) (this.trans (le_of_eq (by ring)))
  intro q hq
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, inBox_of_chi_ne_zero hq.2⟩

/-- The constant `N₀(d, L)` bounding `|𝒬(z)|`. -/
def N0 (d L : ℕ) : ℕ := 3 * (8 * L) ^ d

/-- The decoupling factor `s_z = ∏_{P ∈ 𝒬(z)} s_P`, for a vector `s` indexed by the centres (the
factors of cubes that are not parameter cubes are `1`; `s_z = 1` if the product is empty). -/
noncomputable def sProd (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ K) : ℂ := ∏ P ∈ Qset G q, s P

/-- `|s_z| ≤ e^{N₀ κ₁}` if every `|s_P| ≤ e^{κ₁}`. -/
theorem norm_sProd_le (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) : ‖sProd G s q‖ ≤ Real.exp (N0 d L * κ) := by
  unfold sProd
  rw [norm_prod]
  calc ∏ P ∈ Qset G q, ‖s P‖ ≤ ∏ _P ∈ Qset G q, Real.exp κ :=
        Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => hs P
    _ = Real.exp κ ^ (Qset G q).card := Finset.prod_const _
    _ = Real.exp ((Qset G q).card * κ) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (N0 d L * κ) := by
        apply Real.exp_le_exp.2
        have := card_Qset_le hG hϱ hM hL hq
        have h2 : ((Qset G q).card : ℝ) ≤ (N0 d L : ℝ) := by
          unfold N0; exact_mod_cast this
        exact mul_le_mul_of_nonneg_right h2 hκ

end Boxes

end Index

end Balaban.Localization
