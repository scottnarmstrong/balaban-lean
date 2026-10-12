/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeActionRealStar
public import Balaban.Fluctuation.CubeActionShift
public import Balaban.Fluctuation.CubeActionBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Step 3 in the star convention (FLUCTUATION.md §4.2, Step 3)

The bounds of `CubeActionShift.lean` / `CubeActionBound.lean` for `cubeActionStar`, where every
bond touching `Q` is counted with weight `½ starWeight`, so that the cube actions of a partition
of `X` add up to the localized action of `X` (`sum_cubeDiffStar_eq`).  The sum of the bond weights
is `d |Q|`, so the constants are those of the base-charged convention; the neighbourhood `R`
must also contain the left neighbours `x - e_μ` of `Q`.

* `cubeActionStar_shift_bound`, `cubeDiffStar_bound_of_far`, `cubeDiffStar_step3`,
  `cubeDiffStar_step3_quadratic`: `|β F_□| ≤ C_F' β |Q| r² e^{-γ_w Dist}`;
* `cubeDiffStar_analytic`: holomorphy of `F_□`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Finset

section Bound

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

omit [NeZero N₀] [NeZero L] in
open Classical in
theorem norm_starWeight (Q : Finset (Torus d (N₀ * L ^ k))) (x : Torus d (N₀ * L ^ k))
    (μ : Fin d) :
    ‖starWeight Q x μ‖ = ((if x ∈ Q then 1 else 0) + (if x + Pi.single μ 1 ∈ Q then 1 else 0)) / 2 := by
  unfold starWeight
  by_cases h1 : x ∈ Q <;> by_cases h2 : x + Pi.single μ 1 ∈ Q <;> simp [h1, h2]

omit [NeZero N₀] [NeZero L] in
open Classical in
theorem starWeight_ne_zero {Q : Finset (Torus d (N₀ * L ^ k))} {x : Torus d (N₀ * L ^ k)}
    {μ : Fin d} (h : starWeight Q x μ ≠ 0) : x ∈ Q ∨ x + Pi.single μ 1 ∈ Q := by
  by_contra hc
  rw [not_or] at hc
  exact h (by unfold starWeight; simp [hc.1, hc.2])

open Classical in
theorem sum_norm_starWeight (Q : Finset (Torus d (N₀ * L ^ k))) :
    ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, ‖starWeight Q x μ‖ = d * Q.card := by
  simp only [norm_starWeight]
  rw [Finset.sum_comm]
  have : ∀ μ : Fin d, ∑ x : Torus d (N₀ * L ^ k),
      (((if x ∈ Q then (1 : ℝ) else 0) + (if x + Pi.single μ 1 ∈ Q then 1 else 0)) / 2) = Q.card := by
    intro μ
    have h1 : ∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then (1 : ℝ) else 0) = Q.card := by
      simp
    have h2 : ∑ x : Torus d (N₀ * L ^ k), (if x + Pi.single μ 1 ∈ Q then (1 : ℝ) else 0) =
        Q.card := by
      rw [← h1]
      exact Fintype.sum_equiv (Equiv.addRight (Pi.single μ 1)) _ _ (fun x => rfl)
    simp only [← Finset.sum_div, Finset.sum_add_distrib, h1, h2]
    ring
  simp only [this]
  simp

open Classical in
theorem cubeBondStar_shift_bound (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) {E T : ℝ}
    (hE : 0 ≤ E) (hT : 0 ≤ T)
    (HG : ∀ x, ∀ μ : Fin d, (x ∈ Q ∨ x + Pi.single μ 1 ∈ Q) →
      (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ≤ E)
    (TG : ∀ x, ∀ μ : Fin d, (x ∈ Q ∨ x + Pi.single μ 1 ∈ Q) →
      (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖svec G τ (x + Pi.single μ 1) i - svec G τ x i‖ ≤ T) :
    ‖∑ x : Torus d (N₀ * L ^ k), cubeBondStar G Q Ψ (φ + τ) x -
      ∑ x : Torus d (N₀ * L ^ k), cubeBondStar G Q Ψ φ x‖ ≤
      Q.card * (d * (N * (2 * E * T + T ^ 2))) := by
  have hP0 : 0 ≤ (N : ℝ) * (2 * E * T + T ^ 2) := by positivity
  set P : ℝ := N * (2 * E * T + T ^ 2) with hP
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x : Torus d (N₀ * L ^ k), ‖cubeBondStar G Q Ψ (φ + τ) x - cubeBondStar G Q Ψ φ x‖ ≤
      ∑ μ : Fin d, ‖starWeight Q x μ‖ * P := by
    intro x
    unfold cubeBondStar
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
    by_cases hμ : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hμ, ↓reduceIte]
      by_cases hw : starWeight Q x μ = 0
      · simp [hw]
      · have hQ := starWeight_ne_zero hw
        rw [← mul_sub, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hsum : ∑ i, (barField G Ψ (φ + τ) (x + Pi.single μ 1) i - barField G Ψ (φ + τ) x i) *
              (barField G Ψ (φ + τ) (x + Pi.single μ 1) i - barField G Ψ (φ + τ) x i) -
            ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
              (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) =
            ∑ i, (((barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) +
              (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) *
              ((barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) +
              (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) -
              (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
              (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [barField_add, barField_add]; ring_nf
        rw [hsum]
        exact sum_sq_shift_le _ _ (fun i => HG x μ hQ hμ i) (fun i => TG x μ hQ hμ i) hE hT
    · simp only [hμ, ↓reduceIte, sub_self, norm_zero]
      exact mul_nonneg (norm_nonneg (starWeight Q x μ)) hP0
  refine (Finset.sum_le_sum fun x _ => hterm x).trans ?_
  have := sum_norm_starWeight Q
  calc ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, ‖starWeight Q x μ‖ * P
      = (∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, ‖starWeight Q x μ‖) * P := by
        simp only [← Finset.sum_mul]
    _ ≤ Q.card * (d * P) := by rw [this]; apply le_of_eq; ring

open Classical in
/-- **The first-order expansion bound for the star cube action.**  Same as `cubeAction_shift_bound`
with the first-variation and change bounds required on all bonds touching `Q`. -/
theorem cubeActionStar_shift_bound (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) {W E T : ℝ}
    (hW : ∀ x : G.Ω 1, ‖((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ)‖ ≤ W)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hW0 : 0 ≤ W) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (HB : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i,
      ‖Ψ x i - blockAvg G φ x i‖ ≤ E)
    (HG : ∀ x, ∀ μ : Fin d, (x ∈ Q ∨ x + Pi.single μ 1 ∈ Q) →
      (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ≤ E)
    (HF : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ν * ‖φ (x, i) - h x i‖ ≤ E)
    (TB : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ‖blockAvg G τ x i‖ ≤ T)
    (TG : ∀ x, ∀ μ : Fin d, (x ∈ Q ∨ x + Pi.single μ 1 ∈ Q) →
      (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) → ∀ i,
      ‖svec G τ (x + Pi.single μ 1) i - svec G τ x i‖ ≤ T)
    (TF : ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ k)) ∈ Q → ∀ i, ‖τ (x, i)‖ ≤ T) :
    ‖cubeActionStar G a ν Q Ψ h (φ + τ) - cubeActionStar G a ν Q Ψ h φ‖ ≤
      (1 / 2) * (Q.card * ((W + d + 1) * (N * (2 * E * T + T ^ 2)))) := by
  have h1 := cubeBlock_shift_bound (a := a) Q Ψ φ τ hW hW0 hE hT HB TB
  have h2 := cubeBondStar_shift_bound Q Ψ φ τ hE hT HG TG
  have h3 := cubeMass_shift_bound Q h φ τ hν0 hν1 hE hT HF TF
  have hdiff : cubeActionStar G a ν Q Ψ h (φ + τ) - cubeActionStar G a ν Q Ψ h φ =
      (1 / 2) * (∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ (φ + τ) x else 0) -
        ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ φ x else 0)) +
      (1 / 2) * (∑ x : Torus d (N₀ * L ^ k), cubeBondStar G Q Ψ (φ + τ) x -
        ∑ x : Torus d (N₀ * L ^ k), cubeBondStar G Q Ψ φ x) +
      (1 / 2) * ((ν : ℂ) * (∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h (φ + τ) x else 0) -
        ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h φ x else 0))) := by
    unfold cubeActionStar; ring
  rw [hdiff]
  refine (norm_add₃_le).trans ?_
  have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  simp only [norm_mul (1 / 2 : ℂ), e]
  nlinarith [h1, h2, h3]

end Bound
section Far

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- **Step 3 in the star convention: the bound on `F_□` from the far-decay of the data change.**
As `cubeDiff_bound_of_far`, with the neighbourhood `R` also containing the left neighbours
`x - e_μ` of the sites of the cube (the star bonds with one end in `Q`). -/
theorem cubeDiffStar_bound_of_far (hw : IsAdmissibleWeights K a) (hν0 : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (D : BgData G N) {r : ℝ} (hr : 0 ≤ r)
    (Q R : Finset (CTorus d L N₁ m₁ K)) (hQR : Q ⊆ R)
    (hQR1 : ∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R)
    (hQR2 : ∀ x : CTorus d L N₁ m₁ K, ∀ μ : Fin d, x + Pi.single μ 1 ∈ Q → x ∈ R)
    (hQblk : ∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R)
    (hreg : RegIneq G a ν D r R R)
    {Ws : Finset (CTorus d L N₁ m₁ K)} {γ Bnd Dist : ℝ} (hγ : 0 ≤ γ) (hB : 0 ≤ Bnd)
    (hdist : ∀ y ∈ R, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G Ws y)
    {τ : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ} (hfar : FarBounds G Ws γ Bnd τ δα) :
    ‖cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D + τ) -
        cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D)‖ ≤
      (1 / 2) * (Q.card * ((2 + d + 1) * (N * (2 * r * (Bnd * Real.exp (-(γ * Dist))) +
        (Bnd * Real.exp (-(γ * Dist))) ^ 2)))) := by
  set φ := bgFieldC G a ν (bgC0 d L N) D with hφ
  set T := Bnd * Real.exp (-(γ * Dist)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hℓ : (1 : ℝ) ≤ (L : ℝ) ^ K := by
    exact one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hdec : ∀ y ∈ R, y ∈ G.Ω 1 → decay γ (siteSetDist G Ws y) ≤ Real.exp (-(γ * Dist)) :=
    fun y hy hyΩ => decay_le_exp_dist hγ (hdist y hy hyΩ)
  have hBd : ∀ y ∈ R, y ∈ G.Ω 1 → Bnd * decay γ (siteSetDist G Ws y) ≤ T :=
    fun y hy hyΩ => mul_le_mul_of_nonneg_left (hdec y hy hyΩ) hB
  have TF : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Q → ∀ i, ‖τ (x, i)‖ ≤ T :=
    fun x hx i => (hfar.val x i).trans (hBd x (hQR hx) x.2)
  have hends : ∀ x : CTorus d L N₁ m₁ K, ∀ μ : Fin d, (x ∈ Q ∨ x + Pi.single μ 1 ∈ Q) →
      x ∈ R ∧ x + Pi.single μ 1 ∈ R := by
    intro x μ hq
    rcases hq with hx | hy
    · exact ⟨hQR hx, hQR1 x hx μ⟩
    · exact ⟨hQR2 x μ hy, hQR hy⟩
  refine cubeActionStar_shift_bound Q D.Ψ D.h φ τ (blockWeight_le hw) hν0
    ((le_mul_of_one_le_right hν0 (one_le_pow₀ hℓ)).trans hν1) (by norm_num) hr hT0 ?_ ?_ ?_ ?_ ?_ TF
  · -- HB
    intro x hx i
    have h1 := hreg.1 x (hQR hx)
    exact (norm_le_vn (fun i => D.Ψ x i - blockAvg G φ x i) i).trans h1.le
  · -- HG
    intro x μ hq hact i
    obtain ⟨hxR, hyR⟩ := hends x μ hq
    obtain ⟨-, hgrad, -⟩ := hreg
    rcases hact with hxΩ | hyΩ
    · have h1 := ((hgrad ⟨x, hxΩ⟩ hxR).1 μ).1
      have h2 := norm_le_vn (barVec G D φ (x + Pi.single μ 1) - barVec G D φ x) i
      have h3 : ‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ ≤
          vn (barVec G D φ (x + Pi.single μ 1) - barVec G D φ x) := h2
      nlinarith [vn_nonneg (barVec G D φ (x + Pi.single μ 1) - barVec G D φ x)]
    · have h1 := ((hgrad ⟨x + Pi.single μ 1, hyΩ⟩ hyR).1 μ).2
      have h2 := norm_le_vn (barVec G D φ (x + Pi.single μ 1 - Pi.single μ 1) -
        barVec G D φ (x + Pi.single μ 1)) i
      rw [add_sub_cancel_right] at h2 h1
      have h3 : ‖barField G D.Ψ φ x i - barField G D.Ψ φ (x + Pi.single μ 1) i‖ ≤
          vn (barVec G D φ x - barVec G D φ (x + Pi.single μ 1)) := h2
      rw [norm_sub_rev] at h3
      simp only at h1
      nlinarith [vn_nonneg (barVec G D φ x - barVec G D φ (x + Pi.single μ 1))]
  · -- HF
    intro x hx i
    rcases hν0.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hr
    · set νd := ν * ((L : ℝ) ^ K) ^ 2 with hνd
      have hνd0 : 0 < νd := by positivity
      have hνdle : ν ≤ νd := le_mul_of_one_le_right hν0 (one_le_pow₀ hℓ)
      have hsq : νd ≤ Real.sqrt νd := by
        rw [Real.le_sqrt' hνd0]
        nlinarith
      have hfc := (hreg.2.2 hνd0 x (hQR hx)).1
      have h1 := norm_le_vn (fun i => φ (x, i) - D.h x i) i
      have hs0 : 0 < Real.sqrt νd := Real.sqrt_pos.2 hνd0
      calc ν * ‖φ (x, i) - D.h x i‖ ≤ ν * (r / Real.sqrt νd) :=
            mul_le_mul_of_nonneg_left (h1.trans hfc.le) hν0
        _ ≤ Real.sqrt νd * (r / Real.sqrt νd) :=
            mul_le_mul_of_nonneg_right (hνdle.trans hsq) (by positivity)
        _ = r := by field_simp
  · -- TB
    intro x hx i
    exact blockAvg_norm_le τ x.2 (fun y hy hyΩ j => by
      refine (hfar.val ⟨y, hyΩ⟩ j).trans (hBd y (hQblk x hx x.2 y hy) hyΩ)) i
  · -- TG
    intro x μ hq hact i
    obtain ⟨hxR, hyR⟩ := hends x μ hq
    rcases hact with hxΩ | hyΩ
    · have h1 := hfar.fwd x hxΩ μ i
      have hsp := G.spacing_ge_one x
      have hn := norm_nonneg (svec G τ (x + Pi.single μ 1) i - svec G τ x i)
      nlinarith [hBd x hxR hxΩ]
    · have h1 := hfar.bwd (x + Pi.single μ 1) hyΩ μ i
      rw [add_sub_cancel_right] at h1
      have hsp := G.spacing_ge_one (x + Pi.single μ 1)
      have hn := norm_nonneg (svec G τ x i - svec G τ (x + Pi.single μ 1) i)
      rw [norm_sub_rev] at h1 hn
      nlinarith [hBd _ hyR hyΩ]

open Classical in
/-- **Theorem 4.2, Step 3 (undecoupled): the bound on the cube action difference.**
There are `K_w, δ_w > 0` (depending on `(d, L, N)`) such that the following holds.  Let `D`, `Du`
be data in the complex domain, with `Du = D + δΨ` (same `h`), `δΨ` supported in `W` and bounded by
`δ₁` on the data sites, as in `lemma41_domain_uncond`.  Let `Q ⊆ R` be a cube and its
neighbourhood (the bonds based at `Q` and the blocks of the sites of `Q` lie in `R`), let the data
`D` satisfy the regularity inequalities on `R` with radius `r` (the membership of the data in
`Δ^c`, Definition II.3.5 (a)), and let `R ∩ Ω₁` be at distance at least `Dist` from the shadow
of `W`.  Then with `φ = bgFieldC D`, `φ' = bgFieldC Du` and `T = K_w C_F δ₁ e^{-γ_w Dist}`,
`|A_Q(D; φ') - A_Q(D; φ)| ≤ ½ |Q| (d + 3) N (2 r T + T²)`. -/
theorem cubeDiffStar_step3 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → Dec2.OpSetting G a ν →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K)),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        ∀ (Q R : Finset (CTorus d L N₁ m₁ K)) {r Dist : ℝ}, 0 ≤ r → 0 ≤ Dist → Q ⊆ R →
        (∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R) →
        (∀ x : CTorus d L N₁ m₁ K, ∀ μ : Fin d, x + Pi.single μ 1 ∈ Q → x ∈ R) →
        (∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R) →
        RegIneq G a ν D r R R →
        (∀ y ∈ R, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G (shadow G W) y) →
        ‖cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D)‖ ≤
          (1 / 2) * (Q.card * ((2 + d + 1) * (N * (2 * r *
            (Kw * (cF d L * δ₁) * Real.exp (-(gammaW d * Dist))) +
            (Kw * (cF d L * δ₁) * Real.exp (-(gammaW d * Dist))) ^ 2)))) := by
  obtain ⟨Kw, δw, hK, hδ, hfar⟩ := lemma41_domain_uncond (d := d) (L := L) (N := N) hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν H hOp D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu
    hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ Q R r Dist hr hDist hQR hQR1 hQR2 hQblk hreg hdist
  have hF := hfar H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu hK1 hKw W hsupp hΨ hh
    hδ₁0 hδ₁s hδ₁w hdΨ
  have hB : 0 ≤ Kw * (cF d L * δ₁) := mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hδ₁0)
  have hγ : 0 ≤ gammaW d := by
    unfold gammaW
    have := agmonRate_pos (d := d) (by omega)
    positivity
  have h1 := cubeDiffStar_bound_of_far hOp.weights hOp.mass hOp.massLe D hr Q R hQR hQR1 hQR2 hQblk hreg
    (Ws := shadow G W) (γ := gammaW d) (Bnd := Kw * (cF d L * δ₁)) (Dist := Dist) hγ hB hdist hF
  have e : bgFieldC G a ν (bgC0 d L N) Du = bgFieldC G a ν (bgC0 d L N) D +
      (bgFieldC G a ν (bgC0 d L N) Du - bgFieldC G a ν (bgC0 d L N) D) := by abel
  rw [e]
  exact h1


open Classical in
/-- **Theorem 4.2, Step 3, in the form of the statement:** if moreover `δ₁ ≤ C_δ r` (Step 1: the
data change is bounded by a constant multiple of the H7 radius `r`), then
`|β F_□| ≤ C_F' β |Q| r² e^{-γ_w Dist}` with `C_F'` depending only on `(d, L, N, C_δ)`. -/
theorem cubeDiffStar_step3_quadratic (hd : 3 ≤ d) (hL : 3 ≤ L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF δw : ℝ, 0 < CF ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → Dec2.OpSetting G a ν →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (W : Finset (CTorus d L N₁ m₁ K)),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        ∀ (Q R : Finset (CTorus d L N₁ m₁ K)) {r Dist : ℝ}, 0 ≤ r → 0 ≤ Dist → δ₁ ≤ Cδ * r →
        Q ⊆ R → (∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R) →
        (∀ x : CTorus d L N₁ m₁ K, ∀ μ : Fin d, x + Pi.single μ 1 ∈ Q → x ∈ R) →
        (∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R) →
        RegIneq G a ν D r R R →
        (∀ y ∈ R, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G (shadow G W) y) →
        ∀ β : ℝ, 0 ≤ β →
        ‖(β : ℂ) * (cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D))‖ ≤
          CF * β * Q.card * r ^ 2 * Real.exp (-(gammaW d * Dist)) := by
  obtain ⟨Kw, δw, hK, hδ, hstep⟩ := cubeDiffStar_step3 (N := N) hd hL
  set c : ℝ := Kw * (cF d L * Cδ) with hc
  have hc0 : 0 ≤ c := mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hCδ)
  refine ⟨(1 / 2) * ((2 + d + 1) * (N * (2 * c + c ^ 2))) + 1, δw, by positivity, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν H hOp D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu
    hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ Q R r Dist hr hDist hδr hQR hQR1 hQR2 hQblk hreg
    hdist β hβ
  have h1 := hstep H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu hK1 hKw W hsupp hΨ hh
    hδ₁0 hδ₁s hδ₁w hdΨ Q R hr hDist hQR hQR1 hQR2 hQblk hreg hdist
  have hγ : 0 ≤ gammaW d := by
    unfold gammaW
    have := agmonRate_pos (d := d) (by omega)
    positivity
  set e := Real.exp (-(gammaW d * Dist)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set T := Kw * (cF d L * δ₁) * e with hT
  have hT0 : 0 ≤ T := mul_nonneg (mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hδ₁0)) he0
  have hTb : T ≤ c * r * e := by
    rw [hT, hc]
    have : Kw * (cF d L * δ₁) ≤ Kw * (cF d L * Cδ) * r := by
      calc Kw * (cF d L * δ₁) ≤ Kw * (cF d L * (Cδ * r)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδr (cF_pos d L).le) hK.le
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right this he0
  have h2 := step3_arith hr hT0 he0 he1 hTb
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
  have hQ0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  calc β * ‖cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionStar G a ν Q D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D)‖
      ≤ β * ((1 / 2) * (Q.card * ((2 + d + 1) * (N * (2 * r * T + T ^ 2))))) :=
        mul_le_mul_of_nonneg_left h1 hβ
    _ ≤ β * ((1 / 2) * (Q.card * ((2 + d + 1) * (N * ((2 * c + c ^ 2) * r ^ 2 * e))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hβ
        gcongr
    _ ≤ _ := by
        have hpos : 0 ≤ β * Q.card * r ^ 2 * e := by positivity
        nlinarith [mul_nonneg hpos (by positivity : (0 : ℝ) ≤ (1 / 2) * ((2 + d + 1) * (N * (2 * c + c ^ 2))))]


end Far

section Analytic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Holomorphy of the cube action difference.**  Let `s` be an open set of parameters `p` of a
complex normed space (the complex data), `Dact p` the data of the action and `Dold p`, `Dnew p`
the data of the two backgrounds, depending analytically on `p ∈ s` and lying in the complex domain
`𝒟` of Theorem 5.2.  Then
`p ↦ A_Q(Dact p; φ(Dnew p)) - A_Q(Dact p; φ(Dold p))`, `φ = bgFieldC`, is holomorphic on `s`. -/
theorem cubeDiffStar_analytic (H : BgHyp d L k ϱ a ν) (Q : Finset (Torus d (N₀ * L ^ k)))
    {s : Set E} (hs : IsOpen s) (Dact Dold Dnew : E → BgData G N)
    (hact : AnalyticOnNhd ℂ (fun p => ((Dact p).Ψ, (Dact p).h)) s)
    (hold : AnalyticOnNhd ℂ (fun p => ((Dold p).Ψ, (Dold p).h)) s)
    (hnew : AnalyticOnNhd ℂ (fun p => ((Dnew p).Ψ, (Dnew p).h)) s)
    (hdold : ∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dold p))
    (hdnew : ∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dnew p)) :
    AnalyticOnNhd ℂ (fun p => cubeActionStar G a ν Q (Dact p).Ψ (Dact p).h (bgFieldC G a ν (bgC0 d L N) (Dnew p)) -
      cubeActionStar G a ν Q (Dact p).Ψ (Dact p).h (bgFieldC G a ν (bgC0 d L N) (Dold p))) s := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  have hΦ : ∀ (Dd : E → BgData G N),
      AnalyticOnNhd ℂ (fun p => ((Dd p).Ψ, (Dd p).h)) s →
      (∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dd p)) →
      AnalyticOnNhd ℂ (fun p => bgFieldC G a ν (bgC0 d L N) (Dd p)) s := by
    intro Dd hD hdd
    have h1 : AnalyticOnNhd ℂ (fun p => (F ((Dd p).Ψ, (Dd p).h)).1) s := fun p hp =>
      analyticAt_fst.comp (AnalyticAt.comp (hF _ ⟨Dd p, hdd p hp, rfl⟩) (hD p hp))
    refine h1.congr hs fun p hp => ?_
    show (F ((Dd p).Ψ, (Dd p).h)).1 = bgFieldC G a ν (bgC0 d L N) (Dd p)
    rw [hFe (Dd p) (hdd p hp)]
  have hA : ∀ (Dd : E → BgData G N),
      AnalyticOnNhd ℂ (fun p => ((Dd p).Ψ, (Dd p).h)) s →
      ∀ p ∈ s, AnalyticAt ℂ (fun q => (Dd q).Ψ) p ∧ AnalyticAt ℂ (fun q => (Dd q).h) p := by
    intro Dd hD p hp
    exact ⟨analyticAt_fst.comp (hD p hp), analyticAt_snd.comp (hD p hp)⟩
  intro p hp
  obtain ⟨h1, h2⟩ := hA Dact hact p hp
  exact (cubeActionStar_analyticAt Q h1 h2 (hΦ Dnew hnew hdnew p hp)).sub
    (cubeActionStar_analyticAt Q h1 h2 (hΦ Dold hold hdold p hp))

end Analytic

end Balaban.Fluctuation
