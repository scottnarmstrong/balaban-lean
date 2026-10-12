/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Self
public import Balaban.Background.Composition
public import Balaban.LargeField.Region.Generating
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cover of a sup-separated generating set (VMOD-11 §1.2, rows 3)

The landed cover geometry (`Cover.lean`, `BoxGeometry.lean`) takes the `ℓ¹`-separation
`ϱ ≥ 4 d L M₁`.  The common auxiliary set `F♯` of the P6 mixed pair only has the separation
`5 L M₁` (and, for the minimal sets, in the sup metric on the cube indices).  Here the cover
estimates are proved from the **sup-separation** `SupSep`: for `1 ≤ j < K`, `x ∉ Ω_j`, `y ∈ Ω_{j+1}`,
`4 L^(j+1+m₁) < supDist x y`.  All constants (`cH1`, `cH2`, `Cchi`, `3 * 5^d`, `N0`) are the ones
of the landed development.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-! ### Sup-distance preliminaries -/

theorem supDist_le_of_lift {m : ℕ} [NeZero m] {x z : Torus d m} (t u : Fin d → ℤ)
    (ht : ∀ μ, ((t μ : ℤ) : ZMod m) = x μ) (hu : ∀ μ, ((u μ : ℤ) : ZMod m) = z μ) {B : ℕ}
    (hB : ∀ μ, (t μ - u μ).natAbs ≤ B) : supDist x z ≤ B := by
  refine supDist_le_iff.mpr fun μ => ?_
  rw [cycNorm_le_iff]
  refine ⟨t μ - u μ, ?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact_mod_cast hB μ
  · push_cast; rw [ht, hu]

theorem supDist_self_le_one {m : ℕ} [NeZero m] (x : Torus d m) : supDist x x ≤ 1 := by
  rw [supDist_self]; exact Nat.zero_le _

theorem supDist_add_single_le {m : ℕ} [NeZero m] (x : Torus d m) (μ : Fin d) :
    supDist x (x + Pi.single μ 1) ≤ 1 := by
  refine supDist_le_iff.mpr fun ν => ?_
  rw [cycNorm_le_iff]
  refine ⟨if ν = μ then -1 else 0, ?_, ?_⟩
  · split_ifs <;> simp
  · by_cases h : ν = μ
    · subst h; simp
    · simp [h]

theorem supDist_sub_single_le {m : ℕ} [NeZero m] (x : Torus d m) (μ : Fin d) :
    supDist x (x - Pi.single μ 1) ≤ 1 := by
  refine supDist_le_iff.mpr fun ν => ?_
  rw [cycNorm_le_iff]
  refine ⟨if ν = μ then 1 else 0, ?_, ?_⟩
  · split_ifs <;> simp
  · by_cases h : ν = μ
    · subst h; simp
    · simp [h]

/-! ### The sup-separation -/

/-- **Sup-separation** of a generating set at the cube scale: for `1 ≤ j < K`, a site outside
`Ω_j` is at sup-distance `> 4 L^(j+1+m₁) = 4 L M₁ ℓ_j` from every site of `Ω_{j+1}`.  (The minimal
generating sets of P3 have `5 L M₁ ℓ_j`.) -/
def SupSep {N₀ : ℕ} [NeZero N₀] (G : GeneratingSet d L N₀ K ϱ) (m₁ : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < K → ∀ x, x ∉ G.Ω j → ∀ y ∈ G.Ω (j + 1),
    4 * (L : ℝ) ^ (j + 1 + m₁) < (supDist x y : ℝ)

/-- `SupSep` is satisfiable: a generating set with all domains empty. -/
theorem supSep_exists {N₀ : ℕ} [NeZero N₀] (K m₁ : ℕ) (ϱ : ℝ) :
    ∃ G : GeneratingSet d L N₀ K ϱ, SupSep G m₁ :=
  ⟨{ Ω := fun _ => ∅
     top := rfl
     subset := fun _ _ _ => subset_rfl
     blockUnion := fun _ _ _ _ _ _ => by simp
     separation := fun _ _ _ _ _ y hy => absurd hy (Finset.notMem_empty y) },
   fun _ _ _ _ _ y hy => absurd hy (Finset.notMem_empty y)⟩

section Core

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

theorem mem_pred_cube_sup (hSS : SupSep G m₁) {n : ℕ} (hn1 : 2 ≤ n) (hnK : n ≤ K)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω n)
    (h : (supDist x y : ℝ) ≤ 4 * (L : ℝ) ^ (n + m₁)) : y ∈ G.Ω (n - 1) := by
  by_contra hy
  have hn : n - 1 + 1 = n := by omega
  have hsep := hSS (n - 1) (by omega) (by omega) y hy x (by rw [hn]; exact hx)
  rw [supDist_comm] at hsep
  have e : (L : ℝ) ^ (n - 1 + 1 + m₁) = (L : ℝ) ^ (n + m₁) := by rw [hn]
  rw [e] at hsep
  linarith

/-- Layers of nearby sites differ by at most one (sup-metric form). -/
theorem layer_bounds_cube_sup (hSS : SupSep G m₁)
    {m n : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ K) (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (hz : z ∈ G.layer m)
    (h : (supDist x z : ℝ) ≤ 4 * (L : ℝ) ^ (m + m₁)) (hL : 1 ≤ L) :
    n ≤ m + 1 ∧ m ≤ n + 1 := by
  rw [GeneratingSet.mem_layer] at hx hz
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  constructor
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have := mem_pred_cube_sup hSS (by omega) hnK hx.1
      (h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL' (by omega)) (by positivity)))
    exact hz.2 (G.Ω_antitone (by omega) (by omega) (by omega) this)
  · by_contra hlt
    replace hlt := not_le.1 hlt
    rw [supDist_comm] at h
    have := mem_pred_cube_sup hSS (by omega) hmK hz.1 h
    exact hx.2 (G.Ω_antitone (by omega) (by omega) (by omega) this)

/-- A centre active at `x'` has a point of its cube within sup-distance `L ^ (j + m₁)` of `x'`. -/
theorem cube_active_dist_sup (hG : CubeAligned G m₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) {x' : CTorus d L N₁ m₁ K} (h : cubeBump m₁ q.1 q.2 x' ≠ 0) :
    ∃ z ∈ G.layer q.1, (supDist x' z : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨t, u, ht, hsc, hd'⟩ := cube_active_lift hmK hb h
  refine ⟨intTorus u, (hG.mem_layer_iff hm1 hmK hsc).2 hl, ?_⟩
  have := supDist_le_of_lift t u ht (fun _ => rfl) hd'
  exact_mod_cast this

/-- A centre active at a point `x'` within distance one of a site `x` of layer `n` has layer `m`
with `|m - n| ≤ 1`. -/
theorem cubeActive_layer_bounds_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x x' : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (hxx' : supDist x x' ≤ 1)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeActive G x') : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  obtain ⟨hqi, hne⟩ := (mem_cubeActive G).1 hq
  obtain ⟨⟨hm1, hmK⟩, -, -⟩ := (mem_cubeIdx G).1 hqi
  obtain ⟨z, hz, hdz⟩ := cube_active_dist_sup hG hqi hne
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hL'
  have htri : (supDist x z : ℝ) ≤ supDist x x' + supDist x' z := by
    exact_mod_cast supDist_triangle x x' z
  have hxx'r : (supDist x x' : ℝ) ≤ 1 := by exact_mod_cast hxx'
  refine layer_bounds_cube_sup hSS hm1 hmK hn1 hnK hx hz (htri.trans ?_) hL
  linarith

open Classical in
theorem card_cubeActive_le_sup (hG : CubeAligned G m₁)
    (hSS : SupSep G m₁) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x x' : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (hxx' : supDist x x' ≤ 1) :
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
    have hl := cubeActive_layer_bounds_sup hG hSS hL hn1 hnK hx hxx' hq
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

theorem card_cubeSupp_le_sup (hG : CubeAligned G m₁)
    (hSS : SupSep G m₁) (hL : 1 ≤ L) {n : ℕ} (hn1 : 1 ≤ n)
    (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) :
    (cubeSupp G x μ).card ≤ 9 * 3 ^ d := by
  have h1 := card_cubeActive_le_sup hG hSS hL hn1 hnK hx (supDist_self_le_one x)
  have h2 := card_cubeActive_le_sup hG hSS hL hn1 hnK hx (supDist_add_single_le x μ)
  have h3 := card_cubeActive_le_sup hG hSS hL hn1 hnK hx (supDist_sub_single_le x μ)
  unfold cubeSupp
  calc _ ≤ (cubeActive G x ∪ cubeActive G (x + Pi.single μ 1)).card +
        (cubeActive G (x - Pi.single μ 1)).card := card_union_le _ _
    _ ≤ (cubeActive G x).card + (cubeActive G (x + Pi.single μ 1)).card +
        (cubeActive G (x - Pi.single μ 1)).card := by
        have := card_union_le (cubeActive G x) (cubeActive G (x + Pi.single μ 1)); omega
    _ ≤ 9 * 3 ^ d := by omega

theorem cubeSupp_layer_bounds_sup (hG : CubeAligned G m₁)
    (hSS : SupSep G m₁) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeSupp G x μ) : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  simp only [cubeSupp, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · exact cubeActive_layer_bounds_sup hG hSS hL hn1 hnK hx (supDist_self_le_one x) h
  · exact cubeActive_layer_bounds_sup hG hSS hL hn1 hnK hx (supDist_add_single_le x μ) h
  · exact cubeActive_layer_bounds_sup hG hSS hL hn1 hnK hx (supDist_sub_single_le x μ) h

theorem cubeBump_diff_supp_sup (hG : CubeAligned G m₁)
    (hSS : SupSep G m₁) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeSupp G x μ) :
    |cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) - cubeBump m₁ q.1 q.2 x| ≤
        wb1 d * L / (L : ℝ) ^ (n + m₁) ∧
    |cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) - cubeBump m₁ q.1 q.2 x| ≤
        wb1 d * L / (L : ℝ) ^ (n + m₁) ∧
    |cubeBump m₁ q.1 q.2 (x + Pi.single μ 1) + cubeBump m₁ q.1 q.2 (x - Pi.single μ 1) -
        2 * cubeBump m₁ q.1 q.2 x| ≤ wb2 d * (L : ℝ) ^ 2 / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
  have hbl := cubeSupp_layer_bounds_sup hG hSS (by omega) hn1 hnK hx μ hq
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

theorem coverDenom_diff_sup (hG : CubeAligned G m₁)
    (hSS : SupSep G m₁) (hL : 2 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (μ : Fin d) :
    |coverDenom G (x + Pi.single μ 1) - coverDenom G x| ≤ wU d L / (L : ℝ) ^ (n + m₁) ∧
    |coverDenom G (x - Pi.single μ 1) - coverDenom G x| ≤ wU d L / (L : ℝ) ^ (n + m₁) ∧
    |coverDenom G (x + Pi.single μ 1) + coverDenom G (x - Pi.single μ 1) - 2 * coverDenom G x| ≤
      wV d L / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
  have hcard := card_cubeSupp_le_sup hG hSS (by omega) hn1 hnK hx μ
  have hLn : (0 : ℝ) < (L : ℝ) ^ (n + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hb1 := wb1_nonneg d
  have hb2 := wb2_nonneg d
  have hsupp := fun q (hq : q ∈ cubeSupp G x μ) => cubeBump_diff_supp_sup hG hSS hL hn1 hnK hx μ hq
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

/-- **(Cov3)** First and second differences of `χ_z` along `±e_μ` at a site `x` of layer `n`
(including `n = 1`, whose neighbours may lie outside `Ω₁`): they are at most
`C_χ / (M₁ ℓ(x))` and `C_χ / (M₁ ℓ(x))²`, `ℓ(x) = L ^ n`, `M₁ = L ^ m₁`. -/
theorem chi_diff_sup (hG : CubeAligned G m₁)
    (hSS : SupSep G m₁) (hL : 2 ≤ L) {n : ℕ}
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
    obtain ⟨Dd1, Dd1', Dd2⟩ := coverDenom_diff_sup hG hSS hL hn1 hnK hx μ
    obtain ⟨Bd1, Bd1', Bd2⟩ := cubeBump_diff_supp_sup hG hSS hL hn1 hnK hx μ hs
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

/-! ### Boxes: sup-distance to the base, multiplicity and the thickened box -/

/-- The sup-distance from a point of a box (of nonnegative half-width `R`) to the base of its
cube. -/
theorem supDist_le_of_inBox {j : ℕ} {y0 x : CTorus d L N₁ m₁ K} {R : ℝ} (hR : 0 ≤ R)
    (h : InBox m₁ j y0 R x) :
    (supDist x y0 : ℝ) ≤ R + (L : ℝ) ^ (j + m₁) / 2 := by
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
  have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hμ : ∀ μ, ((t μ - u μ).natAbs : ℝ) ≤ R + (L : ℝ) ^ (j + m₁) / 2 := by
    intro μ
    have h1 := abs_lt.1 (hp μ)
    have e : ((t μ - u μ).natAbs : ℝ) = |((t μ : ℝ) - u μ)| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    have hT : ((t μ : ℤ) : ℝ) = ((x μ).val : ℝ) +
        p μ * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) := by simp [ht]
    have hU : ((u μ : ℤ) : ℝ) = ((y0 μ).val : ℝ) := by simp [hu]
    rw [e, abs_le, hT, hU]
    constructor <;> nlinarith [h1.1, h1.2]
  have hR' : 0 ≤ R + (L : ℝ) ^ (j + m₁) / 2 := by linarith
  have hB : ∀ μ, (t μ - u μ).natAbs ≤ ⌊R + (L : ℝ) ^ (j + m₁) / 2⌋₊ := fun μ =>
    Nat.le_floor (hμ μ)
  have h2 : supDist x y0 ≤ ⌊R + (L : ℝ) ^ (j + m₁) / 2⌋₊ := supDist_le_of_lift t u htx huy hB
  exact (by exact_mod_cast h2 : (supDist x y0 : ℝ) ≤ (⌊R + (L : ℝ) ^ (j + m₁) / 2⌋₊ : ℝ)).trans
    (Nat.floor_le hR')

open Classical in
/-- **Multiplicity of the boxes.**  A site of layer `n` lies in at most `3 N ^ d` of the boxes of
half-width `s M₁ ℓ_j` (`2 s ≤ N`, `s ≤ 7/2`) of the centres: `s = 3/2`, `N = 3` gives the bound
`c_d = 3 ^ (d + 1)` of (Cov2) for the cubes `C_z`; `s = 5/2`, `N = 5` gives the bound
`c_d' = 3 · 5 ^ d` for the interaction cubes `□_z`. -/
theorem card_inBox_le_sup
    (hSS : SupSep G m₁) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnK : n ≤ K) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) {s : ℝ} (hs0 : 0 ≤ s)
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
    have hdist := supDist_le_of_inBox (by positivity) hbox
    have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) :=
      one_le_pow₀ (by exact_mod_cast hL)
    have hbound := layer_bounds_cube_sup hSS hm1 hmK hn1 hnK hx hl
      (hdist.trans (by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - (s + 1 / 2))
          (le_trans zero_le_one hl1)
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

/-- A cube meeting the thickened interaction cube of `q` has layer within one of that of `q`. -/
theorem Qset_layer_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q q' : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (hq' : q' ∈ Qset G q) : q.1 ≤ q'.1 + 1 ∧ q'.1 ≤ q.1 + 1 := by
  obtain ⟨hqi', y, hy, hbox⟩ := (mem_Qset).1 hq'
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨⟨hm1', hmK'⟩, hl', hb'⟩ := (mem_cubeIdx G).1 hqi'
  have hyl : y ∈ G.layer q'.1 := (hG.mem_layer_iff hm1' hmK' hy).2 hl'
  have hdist := supDist_le_of_inBox (by unfold hatRad; positivity) hbox
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 :=
    one_le_pow₀ (by exact_mod_cast hL)
  have hlam : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ q.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  have key : hatRad L m₁ q.1 + (L : ℝ) ^ (q.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (q.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ q.1)
    rw [hlam] at *
    nlinarith
  have := layer_bounds_cube_sup hSS hm1 hmK hm1' hmK' hyl hl
    (hdist.trans key) hL
  omega

open Classical in
/-- **The count `N₀`.**  At most `3 (8 L) ^ d` cubes of the cover meet the thickened interaction
cube of a centre. -/
theorem card_Qset_le_sup (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
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
    have hlay := Qset_layer_sup hG hSS hM hL hq hq'
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

/-! ### Layers in boxes and block alignment -/

/-- The points of `□_z` lie in layers `≤ j + 1` (sup-separation form). -/
theorem layer_le_of_mem_box_sup (hSS : SupSep G m₁) (hL : 1 ≤ L)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (hb : x ∈ intBox q) : n ≤ q.1 + 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx G).1 hq
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hdist := supDist_le_of_inBox (by positivity) ((mem_intBox).1 hb)
  have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hLr
  have := layer_bounds_cube_sup hSS hm1 hmK hn1 hnK hx hl (hdist.trans (by nlinarith)) hL
  exact this.1

/-- **`p6_cover_scale_near`** (VMOD-11 §1.2, cover-layer comparison): for a pair `H ≺ F` with `F`
sup-separated, a site of `Ω₁(H)` lying in the interaction cube `□_q` of a centre `q` of the cover
of `F` has `n_H(x) ≤ n_F(x) ≤ q.1 + 1`. -/
theorem p6_cover_scale_near {ϱ' : ℝ} {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hSS : SupSep F m₁) (hHF : Precedes H F)
    (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hb : x ∈ intBox q) :
    H.layerIndex x ≤ F.layerIndex x ∧ F.layerIndex x ≤ q.1 + 1 := by
  refine ⟨hHF.layerIndex_le hx, ?_⟩
  obtain ⟨hn1, hnK, hxl⟩ := F.layerIndex_spec (hHF.mem_Ω1 hx)
  exact layer_le_of_mem_box_sup hSS hL hq hn1 hnK hxl hb

/-- **Block alignment of the cover cubes for the operator `H`**: `□_q` is a union of `H`-blocks
(`H ≺ F`, `F` sup-separated and cube aligned). -/
theorem p6_blockAligned {ϱ' : ℝ} {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hF : CubeAligned F m₁) (hSS : SupSep F m₁)
    (hHF : Precedes H F) (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F) :
    BlockAligned H (intBox q) := by
  intro j hj1 hjK x x' hx hbl
  by_cases hj : j ≤ q.1 + m₁
  · have hcell : SameCell (L ^ j) x' x := sameCell_of_jBlock_eq hjK hbl
    exact (box_sameCell hq ((hcell.symm).mono (pow_dvd_pow L hj))).symm.symm
  · have hx' : x' ∈ H.layer j := (H.mem_layer_iff hj1 hjK hbl.symm).1 hx
    have hm1 : 1 ≤ m₁ := by have := hF.two_le; omega
    have key : ∀ y : CTorus d L N₁ m₁ K, y ∈ H.layer j → y ∈ intBox q → False := by
      intro y hy hyb
      have hyΩ : y ∈ H.Ω 1 := H.layer_subset hj1 hjK hy
      have := (p6_cover_scale_near hSS hHF hL hq hyΩ hyb).1
      rw [H.layerIndex_eq hj1 hjK hy] at this
      have := (p6_cover_scale_near hSS hHF hL hq hyΩ hyb).2
      have h3 := hHF.layerIndex_le hyΩ
      rw [H.layerIndex_eq hj1 hjK hy] at h3
      omega
    constructor
    · intro h; exact (key x hx h).elim
    · intro h; exact (key x' hx' h).elim

/-! ### The interior of the cover -/

/-- The interior property of `Inner`, from a layer bound `n ≤ q.1 + 1`. -/
theorem inner_of_near_gen (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K}
    {n : ℕ} {x y : CTorus d L N₁ m₁ K} (hnb : SameCell (L ^ n) x y → n ≤ q.1 + 1)
    (hy : InBox m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁)) y)
    (hnear : (∃ μ, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) ∨ SameCell (L ^ n) x y) :
    Inner q x := by
  intro w hw
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hLr
  have key : ∀ w' : Fin d → ℤ, x = y + (intTorus w' : CTorus d L N₁ m₁ K) →
      (∀ μ, |(w' μ : ℝ)| ≤ L * (L : ℝ) ^ q.1) →
      x + (intTorus w : CTorus d L N₁ m₁ K) ∈ intBox q := by
    intro w' hw' hbd
    rw [mem_intBox, hw', add_assoc, intTorus_add_aux]
    refine inBox_cov4 hM hy (w' + w) (fun μ => ?_)
    simp only [Pi.add_apply, Int.cast_add]
    have h1 := hbd μ
    have h2 := hw μ
    have h3 : (L : ℝ) * (L : ℝ) ^ q.1 ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 - 1 := by
      have : (1 : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ q.1 := by nlinarith
      nlinarith
    calc |(w' μ : ℝ) + w μ| ≤ |(w' μ : ℝ)| + |(w μ : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hbig : (1 : ℝ) ≤ L * (L : ℝ) ^ q.1 := by nlinarith
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
    obtain ⟨w', hw', hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine key w' hw' (fun ν => ?_)
    have h1 := hwb ν
    have h2 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (q.1 + 1) := pow_le_pow_right₀ hLr (hnb hcell)
    have h3 : (((L ^ n : ℕ)) : ℝ) = (L : ℝ) ^ n := by push_cast; rfl
    rw [h3] at h1
    have h4 : (L : ℝ) ^ (q.1 + 1) = L * (L : ℝ) ^ q.1 := by ring
    linarith

/-- **`inner_near` for the pair** (`CoverGeom.inner_near`): if `chi_q y ≠ 0` and `x ∈ Ω₁(H)` is a
neighbour of `y` or in the `H`-block of `y` (at scale `n_H(x)`), then `x` is an interior point of
`□_q`. -/
theorem p6_inner_near {ϱ' : ℝ} {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hSS : SupSep F m₁)
    (hHF : Precedes H F) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F) {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    {y : CTorus d L N₁ m₁ K} (hy : chi F q y ≠ 0)
    (hnear : (∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) ∨
      SameCell (L ^ H.layerIndex x) x y) : Inner q x := by
  have hyb := inBox_of_chi_ne_zero hy
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx F).1 hq
  refine inner_of_near_gen hM hL (n := H.layerIndex x) (fun hcell => ?_) hyb hnear
  obtain ⟨hn1, hnK, hxl⟩ := H.layerIndex_spec hx
  set n := H.layerIndex x with hn
  have hxF := hHF.mem_Ω1 hx
  have hle := hHF.layerIndex_le hx
  obtain ⟨hp1, hpK, hxp⟩ := F.layerIndex_spec hxF
  have hxn : x ∈ F.Ω n :=
    F.Ω_antitone hn1 hle (by omega) (F.mem_layer.1 hxp).1
  have hyn : y ∈ F.Ω n := (F.blockUnion n hn1 hnK x y (jBlock_eq_of_sameCell hcell)).1 hxn
  have hy1 : y ∈ F.Ω 1 := F.Ω_antitone le_rfl hn1 (by omega) hyn
  obtain ⟨hq1, hqK, hyl⟩ := F.layerIndex_spec hy1
  have hnle : n ≤ F.layerIndex y := (mem_Ω_iff_le_layerIndex F hy1 hn1 hnK).1 hyn
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hLr
  have hdist := supDist_le_of_inBox (by positivity) hyb
  have hb := layer_bounds_cube_sup hSS hm1 hmK hq1 hqK hyl hl (hdist.trans (by nlinarith)) hL
  omega

/-! ### Partition of unity, smoothness and counts -/

/-- `0 ≤ χ_q ≤ 1` at the stencil points of a site of `Ω₁(H)`. -/
theorem p6_chi_unit {ϱ' : ℝ} {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hF : CubeAligned F m₁) (hHF : Precedes H F)
    (hd : 0 < d) (hL : 2 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F)
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    (hz : z = x ∨ ∃ μ : Fin d, z = x + Pi.single μ 1 ∨ z = x - Pi.single μ 1) :
    0 ≤ chi F q z ∧ chi F q z ≤ 1 := by
  obtain ⟨hn1, hnK, hxl⟩ := F.layerIndex_spec (hHF.mem_Ω1 hx)
  rcases hz with rfl | ⟨μ, hμ⟩
  · exact chi_nbr_mem_unit hF hL hn1 hnK hxl (⟨0, hd⟩ : Fin d) (Or.inl rfl) hq
  · exact chi_nbr_mem_unit hF hL hn1 hnK hxl μ (Or.inr hμ) hq

/-- `∑_q χ_q = 1` on `Ω₁(H)`. -/
theorem p6_sum_chi {ϱ' : ℝ} {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hF : CubeAligned F m₁) (hHF : Precedes H F)
    (hd : 0 < d) (hL : 2 ≤ L) {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) :
    ∑ q ∈ cubeIdx F, chi F q x = 1 := by
  obtain ⟨hn1, hnK, hxl⟩ := F.layerIndex_spec (hHF.mem_Ω1 hx)
  exact sum_chi hF hL hn1 hnK hxl ⟨0, hd⟩

/-- **`p6_cover_chi_diff`** (VMOD-11 §1.2 (4)): the first and second differences of `χ_q` at a
site of `Ω₁(H)` are bounded by `H`-scaled constants: `ℓ_H(x)·|∂χ_q|, ℓ_H(x)²·|Δχ_q| ≤ C_χ / M₁`
with `C_χ = Cchi d L` (the constant of the landed development; the proof is the quotient proof of
`chi_diff`, with the sup-separation, at the `F`-layer `n_F ≥ n_H`). -/
theorem p6_cover_chi_diff {ϱ' : ℝ} {F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} (hF : CubeAligned F m₁) (hSS : SupSep F m₁)
    (hHF : Precedes H F) (hd : 1 ≤ d) (hL : 2 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx F) :
    IsSmoothField H (Cchi d L / (L : ℝ) ^ m₁) (fun x => chiField F q x) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hLr
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by linarith
  have hCc := Cchi_nonneg d L
  have hH1 := cH1_nonneg d L
  have hH2 := cH2_nonneg d L
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hH1C : cH1 d L ≤ Cchi d L := by
    unfold Cchi; nlinarith [mul_nonneg hd0 hH2]
  have hdH2C : d * cH2 d L ≤ Cchi d L := by
    unfold Cchi; linarith
  have hgrad : ∀ (nH nF : ℕ) (δ' : ℝ), nH ≤ nF → |δ'| ≤ cH1 d L / (L : ℝ) ^ (nF + m₁) →
      |δ'| ≤ Cchi d L / (L : ℝ) ^ m₁ / (L : ℝ) ^ nH := by
    intro nH nF δ' hle h
    refine h.trans ?_
    have hpow : (L : ℝ) ^ (nH + m₁) ≤ (L : ℝ) ^ (nF + m₁) :=
      pow_le_pow_right₀ hLr (by omega)
    have hpos : (0 : ℝ) < (L : ℝ) ^ (nH + m₁) := by positivity
    calc cH1 d L / (L : ℝ) ^ (nF + m₁) ≤ cH1 d L / (L : ℝ) ^ (nH + m₁) :=
          div_le_div_of_nonneg_left hH1 hpos hpow
      _ = cH1 d L / (L : ℝ) ^ m₁ / (L : ℝ) ^ nH := by
          rw [pow_add, div_div, mul_comm]
      _ ≤ Cchi d L / (L : ℝ) ^ m₁ / (L : ℝ) ^ nH := by gcongr
  constructor
  · intro x hx μ
    obtain ⟨hn1, hnK, hxl⟩ := F.layerIndex_spec (hHF.mem_Ω1 hx)
    obtain ⟨hh1, hhK, hhl⟩ := H.layerIndex_spec hx
    have hsp := H.spacing_eq hh1 hhK hhl
    have hle := hHF.layerIndex_le hx
    obtain ⟨d1, d1', -⟩ := chi_diff_sup hF hSS hL hn1 hnK hxl μ hq
    have e1 : chiField F q (x + Pi.single μ 1) - chiField F q x =
        fun _ => ((chi F q (x + Pi.single μ 1) - chi F q x : ℝ) : ℂ) := by
      funext i; simp [chiField]
    have e2 : chiField F q (x - Pi.single μ 1) - chiField F q x =
        fun _ => ((chi F q (x - Pi.single μ 1) - chi F q x : ℝ) : ℂ) := by
      funext i; simp [chiField]
    rw [hsp]
    constructor
    · rw [e1, vn_const_one]; exact hgrad _ _ _ hle d1
    · rw [e2, vn_const_one]; exact hgrad _ _ _ hle d1'
  · intro x hx
    obtain ⟨hn1, hnK, hxl⟩ := F.layerIndex_spec (hHF.mem_Ω1 hx)
    obtain ⟨hh1, hhK, hhl⟩ := H.layerIndex_spec hx
    have hsp := H.spacing_eq hh1 hhK hhl
    have hle := hHF.layerIndex_le hx
    set nH := H.layerIndex x with hnH
    set nF := F.layerIndex x with hnF
    have hvec : (fun i : Fin 1 => ∑ μ : Fin d, (chiField F q (x + Pi.single μ 1) i +
        chiField F q (x - Pi.single μ 1) i - 2 * chiField F q x i)) =
        fun _ => ((∑ μ : Fin d, (chi F q (x + Pi.single μ 1) + chi F q (x - Pi.single μ 1) -
          2 * chi F q x) : ℝ) : ℂ) := by
      funext i; simp [chiField]
    rw [hvec, vn_const_one, hsp]
    have hLn : (0 : ℝ) < (L : ℝ) ^ nH := by positivity
    have hpow : (L : ℝ) ^ (nH + m₁) ≤ (L : ℝ) ^ (nF + m₁) :=
      pow_le_pow_right₀ hLr (by omega)
    have hpos : (0 : ℝ) < ((L : ℝ) ^ (nH + m₁)) ^ 2 := by positivity
    have hpow2 : ((L : ℝ) ^ (nH + m₁)) ^ 2 ≤ ((L : ℝ) ^ (nF + m₁)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpow 2
    calc |∑ μ : Fin d, (chi F q (x + Pi.single μ 1) + chi F q (x - Pi.single μ 1) -
          2 * chi F q x)|
        ≤ ∑ μ : Fin d, |chi F q (x + Pi.single μ 1) + chi F q (x - Pi.single μ 1) -
          2 * chi F q x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _μ : Fin d, cH2 d L / ((L : ℝ) ^ (nF + m₁)) ^ 2 :=
          Finset.sum_le_sum fun μ _ => (chi_diff_sup hF hSS hL hn1 hnK hxl μ hq).2.2
      _ ≤ ∑ _μ : Fin d, cH2 d L / ((L : ℝ) ^ (nH + m₁)) ^ 2 :=
          Finset.sum_le_sum fun μ _ => div_le_div_of_nonneg_left hH2 hpos hpow2
      _ = d * (cH2 d L / ((L : ℝ) ^ (nH + m₁)) ^ 2) := by simp
      _ ≤ Cchi d L / (L : ℝ) ^ m₁ / ((L : ℝ) ^ nH) ^ 2 := by
          have e : d * (cH2 d L / ((L : ℝ) ^ (nH + m₁)) ^ 2) =
              (d * cH2 d L) / (L : ℝ) ^ m₁ / ((L : ℝ) ^ nH) ^ 2 / (L : ℝ) ^ m₁ := by
            rw [pow_add]; field_simp
          rw [e]
          have h1 : (d * cH2 d L) / (L : ℝ) ^ m₁ / ((L : ℝ) ^ nH) ^ 2 / (L : ℝ) ^ m₁ ≤
              (d * cH2 d L) / (L : ℝ) ^ m₁ / ((L : ℝ) ^ nH) ^ 2 := by
            apply div_le_self (by positivity) hM1
          refine h1.trans ?_
          gcongr

/-- **`p6_card_box`** (VMOD-11 §1.2 (6)): at most `3 · 5^d` interaction boxes of the cover of `F`
contain a site of `Ω₁(F)` (in particular of `Ω₁(H)`, `H ≺ F`). -/
theorem p6_card_box (hSS : SupSep G m₁) (hL : 1 ≤ L) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) :
    ((cubeIdx G).filter fun q => x ∈ intBox q).card ≤ 3 * 5 ^ d := by
  classical
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
  have hcard := card_inBox_le_sup hSS hL hn1 hnK hxl (s := 5 / 2) (by norm_num) (by norm_num) 5
    (by norm_num)
  have hf : (cubeIdx G).filter (fun q => x ∈ intBox q) =
      (cubeIdx G).filter (fun q => InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) x) :=
    Finset.filter_congr fun q _ => mem_intBox
  exact hf ▸ hcard

/-- **`p6_card_qset`** (VMOD-11 §1.2 (7)): `|𝒬(q)| ≤ N₀(d, L) = 3 (8 L)^d`. -/
theorem p6_card_qset (hG : CubeAligned G m₁) (hSS : SupSep G m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    (Qset G q).card ≤ N0 d L :=
  card_Qset_le_sup hG hSS hM hL hq

end Core

end Balaban.Localization
