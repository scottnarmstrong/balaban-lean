/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledX
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# (DG7): weighted `L²` bounds for the cube Green's functions of the x-variant

In the weighted `L²` form of (DG1)--(DG6) the norms are, for a weight `w = e^{ε r}` with `r` an Agmon
weight and `0 ≤ ε ≤ ε_x = c_x / (16 d L)`,

* `agmonSource G ε r f = ‖ℓ w f‖²` for sources,
* `cwsq G (agmonField G ε r u) = ‖ℓ⁻¹ w u‖²` and `gradOn G ε r Λ u = ‖w ∂u‖²_Λ` for solutions.

This file contains the overlap bookkeeping of the cover and the bounds for one cube:

* `card_overlap_le`, `sq_norm_sum_overlap`, `agmonSource_sum_le`, `sum_agmonSource_cD_le`:
  at most `3 · 5^d` interaction cubes contain a point;
* `cube_energy` (NC2 in the weighted form): the energy inequality for `G^{(z)}_x(A) c_z g`;
* `gradOn_le_cutEnergy`: the weighted gradient at interior points is bounded by the retained
  energy (interior points have no removed bond).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ}

/-! ### Overlap of the interaction cubes -/

section Overlap

theorem card_overlap_le (S : XSetting G a aT ν) (y : G.Ω 1) :
    ((cubeIdx G).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q)).card ≤
      3 * 5 ^ d := by
  classical
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec y.2
  have hcard := card_inBox_le (G := G) S.dg.cover_sep (by have := S.dg.hL; omega) hn1 hnK hxl
    (s := 5 / 2) (by norm_num) 5 (by norm_num)
  have hf : (cubeIdx G).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q) =
      (cubeIdx G).filter (fun q => InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁))
        (y : CTorus d L N₁ m₁ (k + 1))) :=
    Finset.filter_congr fun q _ => mem_intBox
  rw [hf]
  exact_mod_cast hcard

theorem sq_norm_sum_overlap (S : XSetting G a aT ν) {F : ℕ × CTorus d L N₁ m₁ (k + 1) → G.Ω 1 → ℂ}
    (hF : ∀ q ∈ cubeIdx G, ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y = 0)
    (y : G.Ω 1) :
    ‖∑ q ∈ cubeIdx G, F q y‖ ^ 2 ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ cubeIdx G, ‖F q y‖ ^ 2 := by
  classical
  set Q := (cubeIdx G).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q) with hQ
  have hsum : ∑ q ∈ cubeIdx G, F q y = ∑ q ∈ Q, F q y := by
    symm
    refine Finset.sum_filter_of_ne fun q hq hne => ?_
    by_contra hnb
    exact hne (hF q hq y hnb)
  rw [hsum]
  have h1 : ‖∑ q ∈ Q, F q y‖ ≤ ∑ q ∈ Q, ‖F q y‖ := norm_sum_le _ _
  have h2 : (∑ q ∈ Q, ‖F q y‖) ^ 2 ≤ (Q.card : ℝ) * ∑ q ∈ Q, ‖F q y‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (Q.card : ℝ) ≤ 3 * 5 ^ d := by exact_mod_cast card_overlap_le S y
  have h4 : ∑ q ∈ Q, ‖F q y‖ ^ 2 ≤ ∑ q ∈ cubeIdx G, ‖F q y‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have h5 : 0 ≤ ∑ q ∈ Q, ‖F q y‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ q ∈ Q, F q y‖ ^ 2 ≤ (∑ q ∈ Q, ‖F q y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Q.card : ℝ) * ∑ q ∈ Q, ‖F q y‖ ^ 2 := h2
    _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ Q, ‖F q y‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h5
    _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ cubeIdx G, ‖F q y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

theorem agmonSource_sum_le (S : XSetting G a aT ν)
    {F : ℕ × CTorus d L N₁ m₁ (k + 1) → G.Ω 1 → ℂ}
    (hF : ∀ q ∈ cubeIdx G, ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y = 0)
    (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) :
    agmonSource G ε r (fun y => ∑ q ∈ cubeIdx G, F q y) ≤
      (3 * 5 ^ d : ℝ) * ∑ q ∈ cubeIdx G, agmonSource G ε r (F q) := by
  simp only [agmonSource_eq]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := sq_norm_sum_overlap S hF y
  have h0 : 0 ≤ G.spacing (y : CTorus d L N₁ m₁ (k + 1)) ^ 2 *
      Real.exp (ε * r y) ^ 2 := by positivity
  calc G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖∑ q ∈ cubeIdx G, F q y‖ ^ 2
      ≤ G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 *
        ((3 * 5 ^ d : ℝ) * ∑ q ∈ cubeIdx G, ‖F q y‖ ^ 2) := mul_le_mul_of_nonneg_left h h0
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring

theorem agmonSource_cD_le (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (ε : ℝ)
    (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (g : G.Ω 1 → ℂ) :
    agmonSource G ε r (cD G q *ᵥ g) ≤ agmonSource G ε r g := by
  simp only [agmonSource_eq]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [cD_mulVec]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity

theorem sum_agmonSource_cD_le (S : XSetting G a aT ν) (ε : ℝ)
    (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (g : G.Ω 1 → ℂ) :
    ∑ q ∈ cubeIdx G, agmonSource G ε r (cD G q *ᵥ g) ≤
      (3 * 5 ^ d : ℝ) * agmonSource G ε r g := by
  classical
  simp only [agmonSource_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have e : ∀ q, G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖(cD G q *ᵥ g) y‖ ^ 2 =
      if (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q then
        G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖g y‖ ^ 2 else 0 := by
    intro q
    rw [cD_mulVec]
    split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h3 : (((cubeIdx G).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q)).card : ℝ)
      ≤ 3 * 5 ^ d := by exact_mod_cast card_overlap_le S y
  have h0 : 0 ≤ G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖g y‖ ^ 2 := by positivity
  calc _ ≤ (3 * 5 ^ d : ℝ) * (G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 * ‖g y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h3 h0
    _ = _ := by ring

end Overlap

/-! ### The energy inequality for one cube -/

section CubeEnergy

theorem cube_energy (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 → ℂ) :
    (1 / 2) * cutEnergy (cubeCut G (intBox q))
        (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g)) +
      (1 / 32) * cwsq G (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g)) ≤
      8 * agmonSource G ε r (cD G q *ᵥ g) :=
  x_agmon_energy_cut G (cubeCut_aligned G (box_blockAligned S.dg.aligned S.dg.cover_sep
    (by have := S.dg.hL; omega) hq)) (by have := S.dg.hd; omega) S.dg.hL S.hk S.dg.mass S.ha
    S.haT1 S.haT2 hx α (AdmPot.le_eighth S.dg hα) hr hε0 hε1 (cubeHx_cubeGx S hα hx hq g)

theorem cube_cwsq_le (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 → ℂ) :
    cwsq G (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g)) ≤
      256 * agmonSource G ε r (cD G q *ᵥ g) := by
  have h := cube_energy S hα hx hq hr hε0 hε1 g
  have hE := cutEnergy_nonneg (cubeCut G (intBox q))
    (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g))
  linarith

theorem cube_cutEnergy_le (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 → ℂ) :
    cutEnergy (cubeCut G (intBox q)) (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g)) ≤
      16 * agmonSource G ε r (cD G q *ᵥ g) := by
  have h := cube_energy S hα hx hq hr hε0 hε1 g
  have hW := cwsq_nonneg G (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g))
  linarith

end CubeEnergy


/-! ### The weighted gradient at interior points -/

section Grad

/-- `‖w ∂u‖²_Λ`: the two-sided weighted gradient of the zero extension, charged at the points of
`Λ ∩ Ω₁`. -/
noncomputable def gradOn {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (ε : ℝ)
    (r : CTorus d L N₁ m₁ K → ℝ) (Λ : Finset (CTorus d L N₁ m₁ K)) (u : G.Ω 1 → ℂ) : ℝ :=
  ∑ y ∈ G.Ω 1, if y ∈ Λ then Real.exp (ε * r y) ^ 2 * ∑ μ : Fin d,
    (‖zeroExt (G.Ω 1) u (y + Pi.single μ 1) - zeroExt (G.Ω 1) u y‖ ^ 2 +
      ‖zeroExt (G.Ω 1) u (y - Pi.single μ 1) - zeroExt (G.Ω 1) u y‖ ^ 2) else 0

theorem gradOn_nonneg {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (ε : ℝ)
    (r : CTorus d L N₁ m₁ K → ℝ) (Λ : Finset (CTorus d L N₁ m₁ K)) (u : G.Ω 1 → ℂ) :
    0 ≤ gradOn G ε r Λ u :=
  Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun μ _ => by positivity)
    · exact le_rfl

theorem sum_shift_cutEnergy_back {K : ℕ}
    (cut : Finset (CTorus d L N₁ m₁ K × Fin d)) (v : CTorus d L N₁ m₁ K → ℂ) :
    ∑ y : CTorus d L N₁ m₁ K, ∑ μ : Fin d, (if (y - Pi.single μ 1, μ) ∈ cut then 0 else
      ‖v (y - Pi.single μ 1) - v y‖ ^ 2) = cutEnergy cut v := by
  classical
  have key : ∀ μ : Fin d, ∑ y : CTorus d L N₁ m₁ K, (if (y - Pi.single μ 1, μ) ∈ cut then 0 else
      ‖v (y - Pi.single μ 1) - v y‖ ^ 2) =
      ∑ y : CTorus d L N₁ m₁ K, (if (y, μ) ∈ cut then 0 else
        ‖v (y + Pi.single μ 1) - v y‖ ^ 2) := by
    intro μ
    have := sum_shift (Pi.single μ 1) (fun y : CTorus d L N₁ m₁ K =>
      if (y - Pi.single μ 1, μ) ∈ cut then (0 : ℝ) else ‖v (y - Pi.single μ 1) - v y‖ ^ 2)
    rw [← this]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [add_sub_cancel_right]
    split_ifs
    · rfl
    · rw [norm_sub_rev]
  unfold cutEnergy
  calc _ = ∑ μ : Fin d, ∑ y : CTorus d L N₁ m₁ K, (if (y - Pi.single μ 1, μ) ∈ cut then 0 else
        ‖v (y - Pi.single μ 1) - v y‖ ^ 2) := Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ y : CTorus d L N₁ m₁ K, (if (y, μ) ∈ cut then 0 else
        ‖v (y + Pi.single μ 1) - v y‖ ^ 2) := Finset.sum_congr rfl fun μ _ => key μ
    _ = _ := Finset.sum_comm

/-- **Interior gradient bound.** If no bond is removed at the points of `Λ`, the weighted gradient
charged on `Λ` is bounded by the retained energy of `v = w ũ` and its weighted `L²` norm. -/
theorem gradOn_le {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    {cut : Finset (CTorus d L N₁ m₁ K × Fin d)} {Λ : Finset (CTorus d L N₁ m₁ K)}
    (hΛ : ∀ y ∈ Λ, NoCutAt cut y) {r : CTorus d L N₁ m₁ K → ℝ} (hr : IsAgmonWeight G r)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) :
    gradOn G ε r Λ u ≤ 4 * cutEnergy cut (agmonField G ε r u) +
      16 * ε ^ 2 * (d * cwsq G (agmonField G ε r u)) := by
  classical
  set v := agmonField G ε r u with hv
  set B : CTorus d L N₁ m₁ K → ℝ := fun y => ∑ μ : Fin d,
      ((2 * (if (y, μ) ∈ cut then 0 else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) +
        8 * ε ^ 2 * (invSqSpacing G (y + Pi.single μ 1) * ‖v (y + Pi.single μ 1)‖ ^ 2)) +
       (2 * (if (y - Pi.single μ 1, μ) ∈ cut then 0 else ‖v (y - Pi.single μ 1) - v y‖ ^ 2) +
        8 * ε ^ 2 * (invSqSpacing G (y - Pi.single μ 1) * ‖v (y - Pi.single μ 1)‖ ^ 2))) with hB
  have hB0 : ∀ y, 0 ≤ B y := fun y => Finset.sum_nonneg fun μ _ => by
    have h1 := invSqSpacing_nonneg G (y + Pi.single μ 1)
    have h2 := invSqSpacing_nonneg G (y - Pi.single μ 1)
    have h3 : 0 ≤ (if (y, μ) ∈ cut then (0 : ℝ) else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) := by
      split_ifs <;> positivity
    have h4 : 0 ≤ (if (y - Pi.single μ 1, μ) ∈ cut then (0 : ℝ) else
        ‖v (y - Pi.single μ 1) - v y‖ ^ 2) := by
      split_ifs <;> positivity
    positivity
  have hpt : ∀ y ∈ G.Ω 1, (if y ∈ Λ then Real.exp (ε * r y) ^ 2 * ∑ μ : Fin d,
      (‖zeroExt (G.Ω 1) u (y + Pi.single μ 1) - zeroExt (G.Ω 1) u y‖ ^ 2 +
        ‖zeroExt (G.Ω 1) u (y - Pi.single μ 1) - zeroExt (G.Ω 1) u y‖ ^ 2) else 0) ≤ B y := by
    intro y hy
    by_cases hyΛ : y ∈ Λ
    · simp only [hyΛ, ↓reduceIte]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun μ _ => ?_
      have h1 := agmon_bond_pointwise G hr hε0 hε1 u hy (b := y + Pi.single μ 1)
        ⟨μ, Or.inl rfl⟩
      have h2 := agmon_bond_pointwise G hr hε0 hε1 u hy (b := y - Pi.single μ 1)
        ⟨μ, Or.inr (by simp)⟩
      have hc := hΛ y hyΛ μ
      simp only [hc.1, hc.2, ↓reduceIte]
      rw [mul_add]
      exact add_le_add h1 h2
    · simp only [hyΛ, ↓reduceIte]
      exact hB0 y
  have hsum : gradOn G ε r Λ u ≤ ∑ y, B y := by
    calc gradOn G ε r Λ u ≤ ∑ y ∈ G.Ω 1, B y := Finset.sum_le_sum fun y hy => hpt y hy
      _ ≤ ∑ y, B y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun y _ _ => hB0 y
  have hBsum : ∑ y, B y = 4 * cutEnergy cut v + 16 * ε ^ 2 * (d * cwsq G v) := by
    have e1 : ∑ y : CTorus d L N₁ m₁ K, ∑ μ : Fin d,
        (if (y, μ) ∈ cut then 0 else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) = cutEnergy cut v := rfl
    have e2 := sum_shift_cutEnergy_back cut v
    have e3 := sum_shift_cwsq G v
    have e4 := sum_shift_cwsq_back G v
    simp only [hB, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [e1, e2, e3, e4]
    ring
  rw [hBsum] at hsum
  exact hsum

end Grad


/-! ### Scalar fields as vector fields with one component -/

section Scalar

theorem vn_fin_one (z : ℂ) : vn (fun _ : Fin 1 => z) = ‖z‖ := by
  have h := vn_sq (fun _ : Fin 1 => z)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  exact (sq_eq_sq₀ (vn_nonneg _) (norm_nonneg _)).1 h

theorem svec_scalar_eq {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (u : G.Ω 1 → ℂ)
    (y : CTorus d L N₁ m₁ K) :
    svec G (fun p : G.Ω 1 × Fin 1 => u p.1) y = fun _ => zeroExt (G.Ω 1) u y := by
  funext i; rfl

theorem vecGradOn_scalar {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (ε : ℝ)
    (r : CTorus d L N₁ m₁ K → ℝ) (Λ : Finset (CTorus d L N₁ m₁ K)) (u : G.Ω 1 → ℂ) :
    vecGradOn G ε r Λ (fun p : G.Ω 1 × Fin 1 => u p.1) = gradOn G ε r Λ u := by
  unfold vecGradOn gradOn
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    have e1 : svec G (fun p : G.Ω 1 × Fin 1 => u p.1) (y + Pi.single μ 1) -
        svec G (fun p : G.Ω 1 × Fin 1 => u p.1) y =
        fun _ => zeroExt (G.Ω 1) u (y + Pi.single μ 1) - zeroExt (G.Ω 1) u y := by
      funext i; rfl
    have e2 : svec G (fun p : G.Ω 1 × Fin 1 => u p.1) (y - Pi.single μ 1) -
        svec G (fun p : G.Ω 1 × Fin 1 => u p.1) y =
        fun _ => zeroExt (G.Ω 1) u (y - Pi.single μ 1) - zeroExt (G.Ω 1) u y := by
      funext i; rfl
    rw [e1, e2, vn_fin_one, vn_fin_one]
  · rfl

theorem vecM_scalar {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (ε : ℝ)
    (r : CTorus d L N₁ m₁ K → ℝ) (u : G.Ω 1 → ℂ) :
    vecM G ε r (fun p : G.Ω 1 × Fin 1 => u p.1) = cwsq G (agmonField G ε r u) := by
  unfold vecM wsq cwsq
  refine Finset.sum_congr rfl fun y _ => ?_
  beta_reduce
  rw [norm_agmonField, svec_scalar_eq, vn_fin_one]

end Scalar

/-! ### The commutator on a cube solution -/

section KzBound

omit [NeZero L] in
theorem xAgmonRate_le_agmonRate (hd : 0 < d) (hL : 1 ≤ L) : xAgmonRate d L ≤ agmonRate d := by
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hc := xPoincareConst_pos hd
  unfold xAgmonRate agmonRate
  calc xPoincareConst d / (16 * d * L) ≤ xPoincareConst d / (16 * d) := by
        apply div_le_div_of_nonneg_left hc.le (by positivity)
        nlinarith
    _ ≤ poincareConst d / (16 * d) :=
        div_le_div_of_nonneg_right (xPoincareConst_le_poincareConst d) (by positivity)

theorem Kzx_agmonSource_le (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 → ℂ) :
    agmonSource G ε r (Kzx G a aT x ν q *ᵥ (cubeGx G a aT x ν α q *ᵥ g)) ≤
      324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2 *
        agmonSource G ε r (cD G q *ᵥ g) := by
  classical
  have hd : 0 < d := by have := S.dg.hd; omega
  have hL1 : 1 ≤ L := by have := S.dg.hL; omega
  have hε2 : ε ≤ agmonRate d := hε1.trans (xAgmonRate_le_agmonRate hd hL1)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  have hsmooth := chiField_isSmooth S.dg.aligned S.dg.cover_sep (by omega : 1 ≤ d)
    (by have := S.dg.hL; omega : 2 ≤ L) hq
  have hδ : 0 ≤ Cchi d L / (L : ℝ) ^ m₁ := div_nonneg (Cchi_nonneg d L) hM0.le
  set u := cubeGx G a aT x ν α q *ᵥ g with hu
  set Λ : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (fun y => Inner q y) with hΛ
  have hKe : Kzx G a aT x ν q *ᵥ u = commK (xDirichletOperator G a aT x ν 0)
      (restrictField G (chiField G q)) *ᵥ (fun p : G.Ω 1 × Fin 1 => u p.1) := by
    funext y; exact Kzx_mulVec_eq_commK a aT x ν 0 q u y
  have hΛ0 : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∉ Λ →
      (commK (xDirichletOperator G a aT x ν 0) (restrictField G (chiField G q)) *ᵥ
        (fun p : G.Ω 1 × Fin 1 => u p.1)) y = 0 := by
    intro y hy
    rw [← hKe]
    by_contra hne
    exact hy (by simp [hΛ, inner_of_Kzx_ne_zero S hq u y hne])
  have hcomm := agmonSource_commKx_le G hd S.hk S.ha S.haT1 hx (ν := ν) 0 hsmooth hδ hr hε0 hε2
    (fun p : G.Ω 1 × Fin 1 => u p.1) Λ hΛ0
  rw [vecGradOn_scalar, vecM_scalar] at hcomm
  rw [hKe]
  have hgrad := gradOn_le G (cut := cubeCut G (intBox q)) (Λ := Λ)
    (fun y hy => (by simpa [hΛ] using hy : Inner q y).noCut) hr hε0
    (by linarith [agmonRate_le hd]) u
  have hE := cube_cutEnergy_le S hα hx hq hr hε0 hε1 g
  have hW := cube_cwsq_le S hα hx hq hr hε0 hε1 g
  have hS0 := agmonSource_nonneg G ε r (cD G q *ᵥ g)
  have hε3 : ε ^ 2 * d ≤ 1 / 1024 := by
    have h1 := rate_mul_le hd hε2
    have h2 : ε ≤ 1 / 32 := hε2.trans (agmonRate_le hd)
    nlinarith [mul_nonneg hε0 hε0]
  have hgr : gradOn G ε r Λ u + cwsq G (agmonField G ε r u) ≤
      324 * agmonSource G ε r (cD G q *ᵥ g) := by
    have : 16 * ε ^ 2 * (d * cwsq G (agmonField G ε r u)) ≤
        16 * (1 / 1024) * cwsq G (agmonField G ε r u) := by
      have hw0 := cwsq_nonneg G (agmonField G ε r u)
      nlinarith [mul_nonneg hw0 (by linarith : (0 : ℝ) ≤ 1 / 1024 - ε ^ 2 * d)]
    nlinarith
  have hC0 := commXConst_nonneg d L
  calc _ ≤ commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2 *
        (gradOn G ε r Λ u + cwsq G (agmonField G ε r u)) := hcomm
    _ ≤ commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2 *
        (324 * agmonSource G ε r (cD G q *ᵥ g)) :=
        mul_le_mul_of_nonneg_left hgr (by positivity)
    _ = _ := by ring

end KzBound


/-! ### (DG1) -/

section DG1

/-- The constant `c_*(d, L)` of (DG1): `M₁ ≥ c_* e^{N₀ κ₁}`. -/
noncomputable def cstarX (d L : ℕ) : ℝ :=
  72 * (3 * 5 ^ d) * (commXConst d L + 1) * (Cchi d L + 1)

theorem cstarX_pos (d L : ℕ) : 0 < cstarX d L := by
  have := commXConst_nonneg d L
  have := Cchi_nonneg d L
  unfold cstarX; positivity

omit [NeZero L] in
theorem dg1_numeric {n C Cχ E M : ℝ} (hn : 1 ≤ n) (hC : 0 ≤ C) (hCχ : 0 ≤ Cχ) (hE : 1 ≤ E)
    (hM : 72 * n * (C + 1) * (Cχ + 1) * E ≤ M) :
    n * (E ^ 2 * (324 * C * (Cχ / M) ^ 2)) * n ≤ 1 / 16 := by
  have hM0 : 0 < 72 * n * (C + 1) * (Cχ + 1) * E := by positivity
  have h1 : Cχ / M ≤ Cχ / (72 * n * (C + 1) * (Cχ + 1) * E) :=
    div_le_div_of_nonneg_left hCχ hM0 hM
  have h2 : (Cχ / M) ^ 2 ≤ (Cχ / (72 * n * (C + 1) * (Cχ + 1) * E)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hCχ (hM0.le.trans hM)) h1 2
  have e : n * (E ^ 2 * (324 * C * (Cχ / (72 * n * (C + 1) * (Cχ + 1) * E)) ^ 2)) * n =
      (1 / 16) * (C / (C + 1) ^ 2 * (Cχ ^ 2 / (Cχ + 1) ^ 2)) := by
    have hn0 : n ≠ 0 := by positivity
    have hE0 : E ≠ 0 := by positivity
    have hC0 : (C + 1) ≠ 0 := by positivity
    have hX0 : (Cχ + 1) ≠ 0 := by positivity
    field_simp
    ring
  have h3 : C / (C + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h4 : Cχ ^ 2 / (Cχ + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h5 : 0 ≤ C / (C + 1) ^ 2 := by positivity
  have h6 : 0 ≤ Cχ ^ 2 / (Cχ + 1) ^ 2 := by positivity
  calc n * (E ^ 2 * (324 * C * (Cχ / M) ^ 2)) * n
      ≤ n * (E ^ 2 * (324 * C * (Cχ / (72 * n * (C + 1) * (Cχ + 1) * E)) ^ 2)) * n := by
        gcongr
    _ = (1 / 16) * (C / (C + 1) ^ 2 * (Cχ ^ 2 / (Cχ + 1) ^ 2)) := e
    _ ≤ 1 / 16 := by nlinarith [mul_le_mul h3 h4 h6 zero_le_one]

theorem Kcalx_mulVec (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (f : G.Ω 1 → ℂ) :
    Kcalx G a aT x ν α s *ᵥ f = fun y => ∑ q ∈ cubeIdx G, sProd G s q *
      (Kzx G a aT x ν q *ᵥ (cubeGx G a aT x ν α q *ᵥ f)) y := by
  funext y
  unfold Kcalx
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, ← Matrix.mulVec_mulVec]

theorem Gstarx_mulVec (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (f : G.Ω 1 → ℂ) :
    Gstarx G a aT x ν α s *ᵥ f = fun y => ∑ q ∈ cubeIdx G, sProd G s q *
      (chiD G q *ᵥ (cubeGx G a aT x ν α q *ᵥ f)) y := by
  funext y
  unfold Gstarx
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, ← Matrix.mulVec_mulVec]

/-- **(DG1), weighted `L²` form.** For `M₁ ≥ c_* e^{N₀ κ₁}`, `|s_P| ≤ e^{κ₁}`, `|A| ≤ γ₁`, every
weight `w = e^{ε r}` with `0 ≤ ε ≤ ε_x`, uniformly in `x ≥ 0`:
`‖ℓ w 𝒦_{x,s}(A) f‖ ≤ ¼ ‖ℓ w f‖`. -/
theorem dg1x (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : G.Ω 1 → ℂ) :
    agmonSource G ε r (Kcalx G a aT x ν α s *ᵥ f) ≤ (1 / 16) * agmonSource G ε r f := by
  classical
  set F : ℕ × CTorus d L N₁ m₁ (k + 1) → G.Ω 1 → ℂ := fun q y =>
    sProd G s q * (Kzx G a aT x ν q *ᵥ (cubeGx G a aT x ν α q *ᵥ f)) y with hF
  have hFs : ∀ q ∈ cubeIdx G, ∀ y : G.Ω 1,
      (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y = 0 := by
    intro q hq y hy
    simp only [hF]
    have : (Kzx G a aT x ν q *ᵥ (cubeGx G a aT x ν α q *ᵥ f)) y = 0 := by
      by_contra hne
      exact hy (inner_of_Kzx_ne_zero S hq _ y hne).self
    rw [this, mul_zero]
  have hL1 : 1 ≤ L := by have := S.dg.hL; omega
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  rw [Kcalx_mulVec]
  have h1 := agmonSource_sum_le S hFs ε r
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by positivity)
  have hterm : ∀ q ∈ cubeIdx G, agmonSource G ε r (F q) ≤ Real.exp (N0 d L * κ) ^ 2 *
      (324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2 *
        agmonSource G ε r (cD G q *ᵥ f)) := by
    intro q hq
    have hsp : ‖sProd G s q‖ ≤ Real.exp (N0 d L * κ) :=
      norm_sProd_le S.dg.aligned S.dg.cover_sep S.dg.hM hL1 hq hκ hs
    have h2 := agmonSource_mul_le G ε r (fun _ => sProd G s q)
      (Kzx G a aT x ν q *ᵥ (cubeGx G a aT x ν α q *ᵥ f)) (c := Real.exp (N0 d L * κ))
      (fun _ => hsp)
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left (Kzx_agmonSource_le S hα hx hq hr hε0 hε1 f) (by positivity)
  have h3 := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h3
  have h4 := sum_agmonSource_cD_le S ε r f
  have hC0 := commXConst_nonneg d L
  have hnum := dg1_numeric (n := 3 * 5 ^ d) (C := commXConst d L) (Cχ := Cchi d L)
    (E := Real.exp (N0 d L * κ)) (M := (L : ℝ) ^ m₁)
    (by have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num); linarith) hC0 (Cchi_nonneg d L) hE1
    (by unfold cstarX at hMκ; linarith)
  have hS0 := agmonSource_nonneg G ε r f
  calc _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ cubeIdx G, agmonSource G ε r (F q) := h1
    _ ≤ (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        (324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2 *
          ∑ q ∈ cubeIdx G, agmonSource G ε r (cD G q *ᵥ f))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        (324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2 *
          ((3 * 5 ^ d : ℝ) * agmonSource G ε r f))) := by
        gcongr
    _ = ((3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        (324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2)) * (3 * 5 ^ d : ℝ)) *
          agmonSource G ε r f := by ring
    _ ≤ (1 / 16) * agmonSource G ε r f := by
        refine mul_le_mul_of_nonneg_right ?_ hS0
        have e : (324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2) =
            (324 * commXConst d L * (Cchi d L / (L : ℝ) ^ m₁) ^ 2) := rfl
        linarith [hnum]

end DG1

end Balaban.Localization
