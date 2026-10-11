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

end Index

end Balaban.Localization
