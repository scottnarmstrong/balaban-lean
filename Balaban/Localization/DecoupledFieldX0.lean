/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledFieldClose
public import Balaban.Localization.DecoupledFieldLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem I-4a (d) on `X₀` (LOCALIZATION.md §3.2)

The closeness of the solutions at `s` and at `s ≡ 1` decays like `e^{-γ_w d(x, 𝒲)}` in the scaled
path metric (`i4a_close`).  Here the scaled distance from `X₀` to the set `𝒲` of the interaction
cubes that meet a parameter cube is bounded below, from the geometric hypothesis that the
physical `r₀ M₁ ℓ(x)`-neighbourhood of `x ∈ X₀` lies in `X₁`.

* `pathDist_ge_torusDist`: the scaled path distance dominates the truncated physical distance
  divided by `L ℓ(x)` (a `1/ℓ(b)`-Lipschitz function, the separation `(S)` bounds the spacing);
* `scaled_dist_X0`: for `x ∈ X₀` and `w ∈ 𝒲`, `d(x, w) ≥ ((r₀ - 4 d L³) / L) M₁`;
* `i4a_close_X0`: the closeness bounds of `i4a_close` on `X₀` with the factor
  `e^{-γ_w r₁ M₁}`, `r₁ = (r₀ - 4 d L³)/L`.

With the metric of the proof (steps cost `1/ℓ` and layers differ by one between nearby cubes) the
constant is `r₁ = (r₀ - 4dL³)/L` and not `r₀ - 6` as in the paper's count of cubes.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Lower

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Sites within physical distance `ϱ ℓ^+` of a site of layer `n` have spacing at most `L ℓ(x)`. -/
theorem spacing_le_of_torusDist (G : GeneratingSet d L N₀ k ϱ) {n : ℕ} (hn1 : 1 ≤ n)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) {p : Torus d (N₀ * L ^ k)}
    (hp : p ∈ G.Ω 1) (hd : Green.torusDist d (N₀ * L ^ k) x p ≤ ϱ * (L : ℝ) ^ (n + 1)) :
    G.spacing p ≤ (L : ℝ) ^ (n + 1) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  obtain ⟨hj1, hjk, hpl⟩ := G.layerIndex_spec hp
  have hle : G.layerIndex p ≤ n + 1 := by
    by_contra hcon
    push Not at hcon
    have hpΩ : p ∈ G.Ω (n + 2) := G.Ω_antitone (by omega) (by omega) (by omega)
      (G.mem_layer.1 hpl).1
    have hxn : x ∉ G.Ω (n + 1) := (G.mem_layer.1 hx).2
    have := G.separation (n + 1) (by omega) (by omega) x hxn p hpΩ
    linarith
  exact pow_le_pow_right₀ hL1 hle

/-- **The path metric dominates the truncated physical distance** divided by `L ℓ(x)`. -/
theorem pathDist_ge_torusDist (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {n : ℕ} (hn1 : 1 ≤ n)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (p : Torus d (N₀ * L ^ k)) :
    ENNReal.ofReal (min (Green.torusDist d (N₀ * L ^ k) x p) (ϱ * (L : ℝ) ^ (n + 1) - 1) /
      (L : ℝ) ^ (n + 1)) ≤ G.pathDist x p := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set c : ℝ := (L : ℝ) ^ (n + 1) with hc
  have hc1 : 1 ≤ c := one_le_pow₀ hL1
  have hc0 : 0 < c := by linarith
  set R : ℝ := ϱ * c - 1 with hR
  have hR0 : 0 ≤ R := by nlinarith
  set F : Torus d (N₀ * L ^ k) → ℝ := fun p => min (Green.torusDist d (N₀ * L ^ k) x p) R / c
    with hF
  have hFx : F x = 0 := by
    show min (Green.torusDist d (N₀ * L ^ k) x x) R / c = 0
    rw [Balaban.Multiscale.torusDist_self', min_eq_left hR0, zero_div]
  have hlip : ∀ a b, a ∈ G.Ω 1 → b ∈ G.Ω 1 → Adj a b → |F a - F b| ≤ G.bondCost a b := by
    intro a b ha hb hadj
    have hab := hadj.torusDist_le
    have t1 := Green.torusDist_triangle_gen (d := d) (m := N₀ * L ^ k) x a b
    have t2 := Green.torusDist_triangle_gen (d := d) (m := N₀ * L ^ k) x b a
    have t3 : Green.torusDist d (N₀ * L ^ k) b a = Green.torusDist d (N₀ * L ^ k) a b :=
      Green.torusDist_comm_gen _ _
    set ta := Green.torusDist d (N₀ * L ^ k) x a with hta
    set tb := Green.torusDist d (N₀ * L ^ k) x b with htb
    have hdiff : |min ta R - min tb R| ≤ 1 := by
      have h1 := abs_min_sub_min_le_max ta R tb R
      have h2 : |ta - tb| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      simp only [sub_self, abs_zero] at h1
      exact h1.trans (max_le h2 zero_le_one)
    have hnn := G.bondCost_nonneg a b
    by_cases hboth : R ≤ ta ∧ R ≤ tb
    · show |min ta R / c - min tb R / c| ≤ _
      rw [min_eq_right hboth.1, min_eq_right hboth.2, sub_self, abs_zero]
      exact hnn
    · have hsmall : ta < R ∨ tb < R := by
        by_contra h
        push Not at h
        exact hboth ⟨h.1, h.2⟩
      have hda : ta ≤ ϱ * c := by
        rcases hsmall with h | h
        · linarith
        · have : ta ≤ tb + 1 := by linarith
          linarith
      have hdb : tb ≤ ϱ * c := by
        rcases hsmall with h | h
        · have : tb ≤ ta + 1 := by linarith
          linarith
        · linarith
      have hsa := spacing_le_of_torusDist G hn1 hx ha hda
      have hsb := spacing_le_of_torusDist G hn1 hx hb hdb
      have hmax : max (G.spacing a) (G.spacing b) ≤ c := max_le hsa hsb
      have hmpos : 0 < max (G.spacing a) (G.spacing b) :=
        lt_of_lt_of_le (spacing_pos G) (le_max_left _ _)
      have hbc : 1 / c ≤ G.bondCost a b := by
        unfold GeneratingSet.bondCost
        exact one_div_le_one_div_of_le hmpos hmax
      calc |F a - F b| = |min ta R - min tb R| / c := by
            show |min ta R / c - min tb R / c| = _
            rw [← sub_div, abs_div, abs_of_pos hc0]
        _ ≤ 1 / c := div_le_div_of_nonneg_right hdiff hc0.le
        _ ≤ _ := hbc
  have := G.ofReal_sub_le_pathDist F hlip x p
  rw [hFx, sub_zero] at this
  exact this

end Lower

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- Two sites of one cell of side `a` are at physical distance `≤ d a`. -/
theorem torusDist_sameCell_le {a : ℕ} {x y : CTorus d L N₁ m₁ K} (ha : 0 < a)
    (h : SameCell a x y) : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y ≤ d * a := by
  have key : ∀ μ, (((x μ).val : ℤ) - ((y μ).val : ℤ)).natAbs ≤ a := by
    intro μ
    have h1 := h μ
    have e1 := Nat.div_add_mod (x μ).val a
    have e2 := Nat.div_add_mod (y μ).val a
    have l1 := Nat.mod_lt (x μ).val ha
    have l2 := Nat.mod_lt (y μ).val ha
    rw [h1] at e1
    omega
  refine (torusDist_le_of_lift (fun μ => ((x μ).val : ℤ)) (fun μ => ((y μ).val : ℤ))
    (fun μ => by simp) (fun μ => by simp)).trans ?_
  calc ∑ μ, ((((x μ).val : ℤ) - ((y μ).val : ℤ)).natAbs : ℝ) ≤ ∑ _μ : Fin d, (a : ℝ) :=
        Finset.sum_le_sum fun μ _ => by exact_mod_cast key μ
    _ = d * a := by simp

/-- The sites of the thickened interaction cube are within `4 d M₁ ℓ_j` of the centre. -/
theorem torusDist_hatBox_le (S : DGSetting G a ν) {z : ℕ × CTorus d L N₁ m₁ K}
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ hatBox z) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y z.2 ≤ 4 * d * (L : ℝ) ^ (z.1 + m₁) := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast S.hM
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ (by linarith)
  have hlam : (L : ℝ) ^ (z.1 + m₁) = (L : ℝ) ^ z.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) := by positivity
  have key : hatRad L m₁ z.1 + (L : ℝ) ^ (z.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (z.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ z.1)
    rw [hlam] at *
    nlinarith
  have hbox : InBox m₁ z.1 z.2 (hatRad L m₁ z.1) y := by
    unfold hatBox at hy
    exact mem_boxSet.1 hy
  have hdist := torusDist_le_of_inBox hbox
  refine hdist.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left key hd1]

/-- **The layer of a site of `□_z` is at least `j - 1`.** -/
theorem layer_ge_of_mem_box (S : DGSetting G a ν) {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ cubeIdx G) {w : CTorus d L N₁ m₁ K} (hw : w ∈ intBox z) (hwΩ : w ∈ G.Ω 1) :
    z.1 ≤ G.layerIndex w + 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hz
  obtain ⟨hn1, hnK, hwl⟩ := G.layerIndex_spec hwΩ
  by_cases h2 : z.1 ≤ 1
  · omega
  · have hz2 : 2 ≤ z.1 := by omega
    have hdist := torusDist_hatBox_le S (box_subset_hatBox z hw)
    have hz2Ω : z.2 ∈ G.Ω z.1 := (G.mem_layer.1 hl).1
    have := mem_pred_cube m₁ G S.cover_sep hz2 hmK hz2Ω (by
      rw [Green.torusDist_comm_gen]; exact hdist)
    by_contra hcon
    push Not at hcon
    have hsub : w ∈ G.Ω (G.layerIndex w + 1) :=
      G.Ω_antitone (by omega) (by omega) (by omega) this
    exact (G.mem_layer.1 hwl).2 hsub

/-- **Distance from a site of `□_z` to a site of a cube `P ∈ 𝒬(z)`.** -/
theorem torusDist_box_cube_le (S : DGSetting G a ν) {z P : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ cubeIdx G) (hP : P ∈ Qset G z) {w : CTorus d L N₁ m₁ K} (hw : w ∈ intBox z)
    {y' : CTorus d L N₁ m₁ K} (hy' : y' ∈ cubeP P) :
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) w y' ≤ 4 * d * L * (L : ℝ) ^ (z.1 + m₁) := by
  obtain ⟨hPi, y, hy, hbox⟩ := mem_Qset.1 hP
  have hlay := Qset_layer S.aligned S.cover_sep S.hM (by have := S.hL; omega) hz hP
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := S.hL; omega : 1 ≤ L)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hyhat : y ∈ hatBox z := by unfold hatBox; exact mem_boxSet.2 hbox
  have d1 := torusDist_hatBox_le S (box_subset_hatBox z hw)
  have d2 := torusDist_hatBox_le S hyhat
  have hyy : SameCell (L ^ (P.1 + m₁)) y' y := by
    have h1 := mem_cubeP.1 hy'
    exact h1.trans hy.symm
  have d3 := torusDist_sameCell_le (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hyy
  have hBP : (L : ℝ) ^ (P.1 + m₁) ≤ L * (L : ℝ) ^ (z.1 + m₁) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hL1 (by omega)
  have t1 := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) w z.2 y'
  have t2 := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) z.2 y y'
  have c1 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) z.2 y =
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y z.2 := Green.torusDist_comm_gen _ _
  have c2 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y y' =
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y' y := Green.torusDist_comm_gen _ _
  have e3 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y' y ≤ d * (L : ℝ) ^ (P.1 + m₁) := by
    have : ((L ^ (P.1 + m₁) : ℕ) : ℝ) = (L : ℝ) ^ (P.1 + m₁) := by push_cast; rfl
    rw [← this]; exact d3
  have hB0 : (0 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) := by positivity
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  nlinarith [mul_le_mul_of_nonneg_left hBP hd0, mul_nonneg hd0 hB0,
    mul_nonneg (mul_nonneg hd0 hB0) (by linarith : (0 : ℝ) ≤ 4 * (L : ℝ) - 11)]

end Geometry

section Main

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- `𝒲`: the interaction cubes of the centres `z` whose parameter set `𝒬(z)` contains a
parameter cube (a cube of the cover not contained in `X₁`). -/
noncomputable def Wpar (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Finset (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  ((cubeIdx G).filter fun z => ∃ P ∈ Qset G z, P ∈ parCubes G X₁).biUnion intBox

theorem mem_Wpar {X₁ : Finset (CTorus d L N₁ m₁ K)} {w : CTorus d L N₁ m₁ K} :
    w ∈ Wpar G X₁ ↔ ∃ z ∈ cubeIdx G, (∃ P ∈ Qset G z, P ∈ parCubes G X₁) ∧ w ∈ intBox z := by
  classical
  unfold Wpar
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨hz, hP⟩, hw⟩; exact ⟨z, hz, hP, hw⟩
  · rintro ⟨z, hz, hP, hw⟩; exact ⟨z, ⟨hz, hP⟩, hw⟩

/-- If the parameters are `1` off the parameter cubes, the cubes with `s_z ≠ 1` lie in `𝒲`. -/
theorem hW_of_par {X₁ : Finset (CTorus d L N₁ m₁ K)} {s : DecParams G}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx G), P ∉ parCubes G X₁ → s ⟨P, hP⟩ = 1) :
    ∀ z ∈ cubeIdx G, sProd G (extS G s) z ≠ 1 → intBox z ⊆ Wpar G X₁ := by
  classical
  intro z hz hne w hw
  rw [mem_Wpar]
  refine ⟨z, hz, ?_, hw⟩
  by_contra hcon
  push Not at hcon
  apply hne
  unfold sProd
  refine Finset.prod_eq_one fun P hP => ?_
  have hPi : P ∈ cubeIdx G := (mem_Qset.1 hP).1
  unfold extS
  simp only [hPi, ↓reduceDIte]
  exact hs1 P hPi (hcon P hP)

/-- **The scaled distance from `X₀` to `𝒲`.**  If the physical `r₀ M₁ ℓ(x)`-neighbourhood of every
site `x ∈ X₀ ∩ Ω₁` lies in `X₁`, then `d(x, w) ≥ ((r₀ - 4 d L³)/L) M₁` for every `w ∈ 𝒲`. -/
theorem scaled_dist_X0 (S : DGSetting G a ν) {r₀ : ℝ} {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ G.Ω 1)
    {w : CTorus d L N₁ m₁ K} (hw : w ∈ Wpar G X₁) :
    ENNReal.ofReal ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L) ≤ G.pathDist x w := by
  classical
  by_cases hwΩ : w ∉ G.Ω 1
  · have : G.pathDist x w = ⊤ := by
      refine eq_top_iff.2 (le_iInf₂ fun c hc => ?_)
      exact absurd hc.right_mem hwΩ
    rw [this]; exact le_top
  push Not at hwΩ
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
  set n := G.layerIndex x with hn
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := S.hL; omega : 1 ≤ L)
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hρ : 1 ≤ ϱ := S.one_lt_rho.le
  have hℓ1 : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1
  have hsp : G.spacing x = (L : ℝ) ^ n := rfl
  -- the data of `w`
  obtain ⟨z, hz, ⟨P, hPQ, hPpar⟩, hwz⟩ := mem_Wpar.1 hw
  have hPsub : ¬ cubeP P ⊆ X₁ := (Finset.mem_filter.1 hPpar).2
  obtain ⟨y', hy'P, hy'X⟩ := Finset.not_subset.1 hPsub
  -- the layer of `w`
  obtain ⟨hm1, hmK, hwl⟩ := G.layerIndex_spec hwΩ
  set nw := G.layerIndex w with hnw
  set T : ℝ := (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L with hTdef
  have hLpos : (0 : ℝ) < L := by linarith
  have hTpos : 0 < T := by
    by_contra h
    push Not at h
    rw [ENNReal.ofReal_of_nonpos h] at hcon
    exact absurd hcon (not_lt.2 bot_le)
  have hr0 : 4 * d * (L : ℝ) ^ 3 < r₀ := by
    by_contra h
    push Not at h
    have : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (by positivity)) hLpos.le
    linarith
  have hT : T ≤ ϱ - 1 := by
    have h1 : T ≤ r₀ * (L : ℝ) ^ m₁ / L := by
      rw [hTdef]
      refine div_le_div_of_nonneg_right ?_ hLpos.le
      have : 0 ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ := by positivity
      nlinarith
    have h2 : r₀ * (L : ℝ) ^ m₁ / L ≤ r₀ * (L : ℝ) ^ m₁ := by
      have h0 : 0 ≤ r₀ * (L : ℝ) ^ m₁ := by
        have : 0 < r₀ := lt_of_le_of_lt (by positivity) hr0
        positivity
      exact div_le_self h0 hL1
    linarith
  have hnw1 : nw ≤ n + 1 := by
    by_contra hh
    push Not at hh
    have h1 := G.pathDist_separation_le hρ hn1 hmK hxl (G.mem_layer.1 hwl).1
    have h2 : ϱ - 1 ≤ (ϱ - 1) * (((nw - n - 1 : ℕ)) : ℝ) := by
      have : (1 : ℝ) ≤ ((nw - n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ nw - n - 1)
      nlinarith
    have h3 : ENNReal.ofReal (ϱ - 1) ≤ G.pathDist x w := h1.trans' (ENNReal.ofReal_le_ofReal h2)
    exact absurd (hcon.trans_le (ENNReal.ofReal_le_ofReal hT)) (not_lt.2 h3)
  have hzn : z.1 ≤ n + 2 := by
    have := layer_ge_of_mem_box S hz hwz hwΩ
    omega
  -- the physical distances
  have hB := torusDist_box_cube_le S hz hPQ hwz hy'P
  have hz1 : (L : ℝ) ^ (z.1 + m₁) ≤ (L : ℝ) ^ n * (L : ℝ) ^ 2 * (L : ℝ) ^ m₁ := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hxy : r₀ * (L : ℝ) ^ m₁ * G.spacing x ≤ Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y' := by
    by_contra h
    push Not at h
    exact hy'X (hN x hx hxΩ y' h)
  have tri := Green.torusDist_triangle_gen (d := d) (m := (N₁ * L ^ m₁) * L ^ K) x w y'
  set tw := Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x w with htw
  have hℓ0 : 0 < (L : ℝ) ^ n := by linarith
  have hQ : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n ≤ tw := by
    have h1 : 4 * d * L * (L : ℝ) ^ (z.1 + m₁) ≤ 4 * d * L * ((L : ℝ) ^ n * (L : ℝ) ^ 2 * (L : ℝ) ^ m₁) :=
      mul_le_mul_of_nonneg_left hz1 (by positivity)
    rw [hsp] at hxy
    nlinarith
  have hR : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n ≤ ϱ * (L : ℝ) ^ (n + 1) - 1 := by
    have h1 : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n ≤ r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ n := by
      have : 0 ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ * (L : ℝ) ^ n := by positivity
      nlinarith
    have h2 : r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ n ≤ (ϱ - 1) * (L : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hr hℓ0.le
    have h3 : (ϱ - 1) * (L : ℝ) ^ n ≤ ϱ * (L : ℝ) ^ (n + 1) - 1 := by
      rw [show (L : ℝ) ^ (n + 1) = (L : ℝ) ^ n * L from pow_succ _ _]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ϱ) (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ n),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ ϱ) hℓ0.le) (by linarith : (0 : ℝ) ≤ L - 1)]
    linarith
  have hA := pathDist_ge_torusDist G hρ hn1 hxl w
  have hmin : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n ≤
      min tw (ϱ * (L : ℝ) ^ (n + 1) - 1) := le_min hQ hR
  have hdiv : T ≤ min tw (ϱ * (L : ℝ) ^ (n + 1) - 1) / (L : ℝ) ^ (n + 1) := by
    have hsucc : (L : ℝ) ^ (n + 1) = (L : ℝ) ^ n * L := pow_succ _ _
    rw [le_div_iff₀ (by positivity), hTdef, hsucc]
    have : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L * ((L : ℝ) ^ n * L) =
        (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ * (L : ℝ) ^ n := by
      field_simp
    rw [this]; exact hmin
  exact absurd hcon (not_lt.2 ((ENNReal.ofReal_le_ofReal hdiv).trans hA))

/-- The scaled distance from `x ∈ X₀` to `𝒲`. -/
theorem siteSetDist_X0 (S : DGSetting G a ν) {r₀ : ℝ} {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)}
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ G.Ω 1) :
    ENNReal.ofReal ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L) ≤
      siteSetDist G (Wpar G X₁) x := by
  unfold siteSetDist
  exact le_iInf₂ fun w hw => scaled_dist_X0 S hN hr hx hxΩ hw

theorem closeConst_nonneg {BG κ δ₁ : ℝ} (hBG : 0 ≤ BG) (hδ₁ : 0 ≤ δ₁) (hd : 0 < d) {N : ℕ} :
    0 ≤ closeConst d L N BG κ δ₁ := by
  have hB1 := famConst_ge_one (L := L) hBG κ hd
  have h1 := cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L BG κ) (by linarith)
  have h2 := Balaban.Background.cF_pos d L
  unfold closeConst; positivity

/-- **Theorem I-4a (d) on `X₀`.**  Under the hypotheses of `i4a_close`, with the parameters equal
to `1` off the parameter cubes (the cubes of the cover not contained in `X₁`) and the physical
`r₀ M₁ ℓ(x)`-neighbourhood of every site `x ∈ X₀ ∩ Ω₁` contained in `X₁`, the solutions at `s` and
at `s ≡ 1` differ on `X₀ ∩ Ω₁` by at most `closeConst · e^{-γ_w r₁ M₁}` (twice that for the
fields), `r₁ = (r₀ - 4 d L³)/L`. -/
theorem i4a_close_X0 {c BG : ℝ} (hF : FamSpec d L c BG) (hD : Dg2Spec d L c BG)
    (hCl : CloseSpec d L c BG) (h1 : OneSpec d L c) (S : DGSetting G a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)} {r₀ : ℝ}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx G), P ∉ parCubes G X₁ →
      s ⟨P, hP⟩ = 1)
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    {N : ℕ} {ιU : Bool} {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaClose d L N BG κ) (hδ₁ : δ₁ ≤ deltaClose d L N BG κ)
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed G a ν (fun _ => 1) ιU α₀ φ₀ (pertSource G a δΨ f₁) δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ X₀ →
      G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖ ≤ closeConst d L N BG κ δ₁ *
        Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) ∧
    (∀ y ∈ X₀, y ∈ G.Ω 1 → ∀ i : Fin N,
      ‖svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') y i‖ ≤
        2 * closeConst d L N BG κ δ₁ *
          Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) ∧
    (∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ (μ : Fin d) (i : Fin N), G.spacing x *
      ‖svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') (x + Pi.single μ 1) i -
        svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') x i‖ ≤
        2 * closeConst d L N BG κ δ₁ *
          Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) ∧
    (∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ i : Fin N, G.spacing x ^ 2 * ‖∑ μ : Fin d,
      (2 * svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') x i -
      svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') (x + Pi.single μ 1) i -
      svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') (x - Pi.single μ 1) i)‖ ≤
        2 * closeConst d L N BG κ δ₁ *
          Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hBG : 0 ≤ BG := hF.2.1
  have hδ₁0 : 0 ≤ δ₁ := H.δ₁_nn
  have hcc := closeConst_nonneg (d := d) (L := L) (κ := κ) (N := N) hBG hδ₁0 hd0
  have hγ0 : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hL1 : (0 : ℝ) < L := by exact_mod_cast (by have := S.hL; omega : 0 < L)
  have hT0 : 0 ≤ (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L := by
    have : 0 ≤ r₀ - 4 * d * (L : ℝ) ^ 3 := by linarith
    positivity
  have hclose := i4a_close hF hD hCl h1 S hκ hM hs (W := Wpar G X₁) (hW_of_par hs1) H hδ₀ hδ₁
    hfix hsm hfix' hsm'
  have hdec : ∀ x ∈ X₀, x ∈ G.Ω 1 → decay (gammaW d) (siteSetDist G (Wpar G X₁) x) ≤
      Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
    intro x hx hxΩ
    have h := decay_anti_dist hγ0 (siteSetDist_X0 S hN hr hx hxΩ)
    rw [decay_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hT0] at h
    exact h
  obtain ⟨c1, c2, c3, c4⟩ := hclose
  refine ⟨fun x hx => ?_, fun y hy hyΩ i => ?_, fun x hx hxΩ μ i => ?_, fun x hx hxΩ i => ?_⟩
  · refine (c1 x).trans ?_
    exact mul_le_mul_of_nonneg_left (hdec x hx x.2) hcc
  · refine (c2 y i).trans ?_
    exact mul_le_mul_of_nonneg_left (hdec y hy hyΩ) (by positivity)
  · refine (c3 x hxΩ μ i).trans ?_
    exact mul_le_mul_of_nonneg_left (hdec x hx hxΩ) (by positivity)
  · refine (c4 x hxΩ i).trans ?_
    exact mul_le_mul_of_nonneg_left (hdec x hx hxΩ) (by positivity)

end Main

end Balaban.Localization
