/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Cutoff functions on the lattice `ℤ^d` (Lemma Loc)

* `latticeBall x₀ r`: the finite set of lattice points `z` with `‖z - x₀‖ ≤ r` (`ℓ^∞` ball).
* `exists_profile`: a one-dimensional `C²` profile `H` with `H = 1` on `[-1, 1]`, `H = 0` outside
  `(-7/4, 7/4)`, `0 ≤ H ≤ 1`, with bounded first and second derivatives.
* `latticeCutoff H ρ x₀`: the product cutoff `χ(z) = ∏_μ H((z_μ - x₀_μ)/ρ)`, with the first and
  second difference bounds `|χ(z ± e_μ) - χ(z)| ≤ M₁/ρ` and
  `|χ(z + e_μ) + χ(z - e_μ) - 2χ(z)| ≤ M₂/ρ²`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open Function

variable {d : ℕ}

/-! ### Lattice balls -/

/-- The `ℓ^∞` ball of radius `r` about `x₀` in `ℤ^d`, as a finite set. -/
def latticeBall (x₀ : Fin d → ℤ) (r : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (x₀ i - ⌊r⌋) (x₀ i + ⌊r⌋)

theorem mem_latticeBall {x₀ z : Fin d → ℤ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ latticeBall x₀ r ↔ ‖z - x₀‖ ≤ r := by
  rw [latticeBall, Fintype.mem_piFinset, pi_norm_le_iff_of_nonneg hr]
  refine forall_congr' fun i => ?_
  rw [Finset.mem_Icc, Pi.sub_apply, Int.norm_eq_abs, Int.cast_sub, abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    have a1 : ((z i - x₀ i : ℤ) : ℝ) ≤ r := Int.le_floor.1 (by omega)
    have a2 : ((x₀ i - z i : ℤ) : ℝ) ≤ r := Int.le_floor.1 (by omega)
    push_cast at a1 a2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have a1 : z i - x₀ i ≤ ⌊r⌋ := Int.le_floor.2 (by push_cast; linarith)
    have a2 : x₀ i - z i ≤ ⌊r⌋ := Int.le_floor.2 (by push_cast; linarith)
    constructor <;> omega

theorem card_latticeBall_le (x₀ : Fin d → ℤ) {r : ℝ} (hr : 0 ≤ r) :
    ((latticeBall x₀ r).card : ℝ) ≤ (2 * r + 1) ^ d := by
  rw [latticeBall, Fintype.card_piFinset]
  have hc : ∀ i : Fin d, (Finset.Icc (x₀ i - ⌊r⌋) (x₀ i + ⌊r⌋)).card = (2 * ⌊r⌋ + 1).toNat := by
    intro i
    rw [Int.card_Icc]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  have h0 : (0 : ℤ) ≤ ⌊r⌋ := Int.floor_nonneg.2 hr
  have h1 : (((2 * ⌊r⌋ + 1).toNat : ℕ) : ℝ) ≤ 2 * r + 1 := by
    have : (((2 * ⌊r⌋ + 1).toNat : ℕ) : ℤ) = 2 * ⌊r⌋ + 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((2 * ⌊r⌋ + 1).toNat : ℕ) : ℝ) = 2 * (⌊r⌋ : ℝ) + 1 := by
      exact_mod_cast this
    rw [h2]
    linarith [Int.floor_le r]
  exact pow_le_pow_left₀ (by positivity) h1 d

/-! ### The one-dimensional profile -/

/-- A one-dimensional cutoff profile with bounded first and second derivatives. -/
structure CutoffProfile where
  /-- the profile -/
  H : ℝ → ℝ
  /-- bound on `|H'|` -/
  M₁ : ℝ
  /-- bound on `|H''|` -/
  M₂ : ℝ
  M₁_nonneg : 0 ≤ M₁
  M₂_nonneg : 0 ≤ M₂
  differentiable : Differentiable ℝ H
  differentiable_deriv : Differentiable ℝ (deriv H)
  nonneg_le_one : ∀ t, 0 ≤ H t ∧ H t ≤ 1
  eq_one : ∀ t, |t| ≤ 1 → H t = 1
  eq_zero : ∀ t, 7 / 4 ≤ |t| → H t = 0
  deriv_le : ∀ t, |deriv H t| ≤ M₁
  deriv_deriv_le : ∀ t, |deriv (deriv H) t| ≤ M₂

theorem nonempty_cutoffProfile : Nonempty CutoffProfile := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 7 / 4, one_pos, by norm_num⟩
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) := f.contDiff
  have hcs : HasCompactSupport (f : ℝ → ℝ) := f.hasCompactSupport
  have hd1 : Continuous (deriv (f : ℝ → ℝ)) := hsm.continuous_deriv (by simp)
  have hcs1 : HasCompactSupport (deriv (f : ℝ → ℝ)) := hcs.deriv
  have hsm1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (f : ℝ → ℝ)) := (contDiff_infty_iff_deriv.1 hsm).2
  have hd2 : Continuous (deriv (deriv (f : ℝ → ℝ))) := hsm1.continuous_deriv (by simp)
  have hcs2 : HasCompactSupport (deriv (deriv (f : ℝ → ℝ))) := hcs1.deriv
  obtain ⟨M1, hM1⟩ := hd1.bounded_above_of_compact_support hcs1
  obtain ⟨M2, hM2⟩ := hd2.bounded_above_of_compact_support hcs2
  refine ⟨⟨f, max M1 0, max M2 0, le_max_right _ _, le_max_right _ _,
    hsm.differentiable (by simp), hsm1.differentiable (by simp),
    fun t => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    exact f.one_of_mem_closedBall (by simpa [Real.dist_eq] using ht)
  · intro t ht
    exact f.zero_of_le_dist (by simpa [Real.dist_eq] using ht)
  · intro t
    have := hM1 t
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · intro t
    have := hM2 t
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- A fixed cutoff profile. -/
def cutoffProfile : CutoffProfile := Classical.choice nonempty_cutoffProfile

theorem profile_diff1 {H : ℝ → ℝ} {M : ℝ} (hH : Differentiable ℝ H)
    (hM : ∀ t, |deriv H t| ≤ M) (s h : ℝ) : |H (s + h) - H s| ≤ M * |h| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := H) (s := Set.univ)
    (x := s) (y := s + h) (C := M) (fun x _ => hH x) (fun x _ => by simpa using hM x)
    convex_univ trivial trivial
  simpa using this

theorem profile_diff2 {H : ℝ → ℝ} {M2 : ℝ} (hH : Differentiable ℝ H)
    (hH' : Differentiable ℝ (deriv H)) (hM2 : ∀ t, |deriv (deriv H) t| ≤ M2) (s h : ℝ) :
    |H (s + h) + H (s - h) - 2 * H s| ≤ M2 * h ^ 2 := by
  have hk : ∀ t, HasDerivAt (fun t => H (t + h) - H t) (deriv H (t + h) - deriv H t) t := by
    intro t
    have h1 : HasDerivAt (fun t => H (t + h)) (deriv H (t + h)) t :=
      (hH (t + h)).hasDerivAt.comp_add_const t h
    exact h1.sub (hH t).hasDerivAt
  have hb : ∀ t, |deriv H (t + h) - deriv H t| ≤ M2 * |h| := fun t =>
    profile_diff1 hH' hM2 t h
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun t => H (t + h) - H t)
    (s := Set.univ) (x := s - h) (y := s) (C := M2 * |h|) (fun x _ => (hk x).differentiableAt)
    (fun x _ => by rw [(hk x).deriv]; simpa using hb x) convex_univ trivial trivial
  simp only [Real.norm_eq_abs, sub_add_cancel] at this
  have e : H (s + h) + H (s - h) - 2 * H s = (H (s + h) - H s) - (H s - H (s - h)) := by ring
  rw [e]
  have e2 : |(H (s + h) - H s) - (H s - H (s - h))| ≤ M2 * |h| * |s - (s - h)| := by
    simpa [sub_sub_cancel] using this
  have e3 : |s - (s - h)| = |h| := by rw [sub_sub_cancel]
  rw [e3] at e2
  calc _ ≤ M2 * |h| * |h| := e2
    _ = M2 * h ^ 2 := by rw [mul_assoc, ← sq_abs h]; ring


/-! ### The product cutoff -/

/-- The product cutoff `χ(z) = ∏_μ H((z_μ - x₀_μ)/ρ)`. -/
def latticeCutoff (ρ : ℝ) (x₀ z : Fin d → ℤ) : ℝ :=
  ∏ μ, cutoffProfile.H (((z μ - x₀ μ : ℤ) : ℝ) / ρ)

theorem latticeCutoff_nonneg (ρ : ℝ) (x₀ z : Fin d → ℤ) : 0 ≤ latticeCutoff ρ x₀ z :=
  Finset.prod_nonneg fun _ _ => (cutoffProfile.nonneg_le_one _).1

theorem latticeCutoff_le_one (ρ : ℝ) (x₀ z : Fin d → ℤ) : latticeCutoff ρ x₀ z ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => (cutoffProfile.nonneg_le_one _).1)
    fun _ _ => (cutoffProfile.nonneg_le_one _).2

theorem latticeCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {x₀ z : Fin d → ℤ} (h : ‖z - x₀‖ ≤ ρ) :
    latticeCutoff ρ x₀ z = 1 := by
  refine Finset.prod_eq_one fun μ _ => cutoffProfile.eq_one _ ?_
  rw [abs_div, abs_of_pos hρ, div_le_one hρ]
  have := norm_le_pi_norm (z - x₀) μ
  rw [Pi.sub_apply, Int.norm_eq_abs] at this
  exact this.trans h

theorem latticeCutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {x₀ z : Fin d → ℤ}
    (h : 7 * ρ / 4 ≤ ‖z - x₀‖) : latticeCutoff ρ x₀ z = 0 := by
  by_contra hne
  have hall : ∀ μ, cutoffProfile.H (((z μ - x₀ μ : ℤ) : ℝ) / ρ) ≠ 0 := fun μ =>
    Finset.prod_ne_zero_iff.1 hne μ (Finset.mem_univ μ)
  have hlt : ‖z - x₀‖ < 7 * ρ / 4 := by
    refine (pi_norm_lt_iff (by positivity)).2 fun μ => ?_
    have h1 : |((z μ - x₀ μ : ℤ) : ℝ) / ρ| < 7 / 4 := by
      by_contra hc
      exact hall μ (cutoffProfile.eq_zero _ (not_lt.1 hc))
    rw [abs_div, abs_of_pos hρ, div_lt_iff₀ hρ] at h1
    rw [Pi.sub_apply, Int.norm_eq_abs, Int.cast_sub]
    push_cast at h1
    linarith
  linarith

theorem latticeCutoff_shift (ρ : ℝ) (x₀ z : Fin d → ℤ) (μ : Fin d) (σ : ℤ) :
    latticeCutoff ρ x₀ (z + Pi.single μ σ) =
      cutoffProfile.H ((((z μ - x₀ μ : ℤ) : ℝ) + σ) / ρ) *
        ∏ ν ∈ Finset.univ.erase μ, cutoffProfile.H (((z ν - x₀ ν : ℤ) : ℝ) / ρ) := by
  unfold latticeCutoff
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
  congr 1
  · congr 1
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    ring_nf
  · refine Finset.prod_congr rfl fun ν hν => ?_
    rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hν), add_zero]

theorem latticeCutoff_eq_mul (ρ : ℝ) (x₀ z : Fin d → ℤ) (μ : Fin d) :
    latticeCutoff ρ x₀ z =
      cutoffProfile.H (((z μ - x₀ μ : ℤ) : ℝ) / ρ) *
        ∏ ν ∈ Finset.univ.erase μ, cutoffProfile.H (((z ν - x₀ ν : ℤ) : ℝ) / ρ) := by
  unfold latticeCutoff
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]

theorem prod_erase_mem (ρ : ℝ) (x₀ z : Fin d → ℤ) (μ : Fin d) :
    0 ≤ ∏ ν ∈ Finset.univ.erase μ, cutoffProfile.H (((z ν - x₀ ν : ℤ) : ℝ) / ρ) ∧
    ∏ ν ∈ Finset.univ.erase μ, cutoffProfile.H (((z ν - x₀ ν : ℤ) : ℝ) / ρ) ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (cutoffProfile.nonneg_le_one _).1,
    Finset.prod_le_one₀ (fun _ _ => (cutoffProfile.nonneg_le_one _).1)
      fun _ _ => (cutoffProfile.nonneg_le_one _).2⟩

/-- First difference of the cutoff: `|χ(z + σ e_μ) - χ(z)| ≤ M₁ |σ| / ρ`. -/
theorem latticeCutoff_diff1_le {ρ : ℝ} (hρ : 0 < ρ) (x₀ z : Fin d → ℤ) (μ : Fin d) (σ : ℤ) :
    |latticeCutoff ρ x₀ (z + Pi.single μ σ) - latticeCutoff ρ x₀ z| ≤
      cutoffProfile.M₁ * |(σ : ℝ)| / ρ := by
  rw [latticeCutoff_shift, latticeCutoff_eq_mul ρ x₀ z μ, ← sub_mul, abs_mul]
  obtain ⟨hp0, hp1⟩ := prod_erase_mem ρ x₀ z μ
  have h1 := profile_diff1 cutoffProfile.differentiable cutoffProfile.deriv_le
    (((z μ - x₀ μ : ℤ) : ℝ) / ρ) ((σ : ℝ) / ρ)
  have e : (((z μ - x₀ μ : ℤ) : ℝ) + σ) / ρ = ((z μ - x₀ μ : ℤ) : ℝ) / ρ + (σ : ℝ) / ρ := by
    ring
  rw [e, abs_of_nonneg hp0]
  calc _ ≤ cutoffProfile.M₁ * |(σ : ℝ) / ρ| * 1 :=
        mul_le_mul h1 hp1 hp0 (by have := cutoffProfile.M₁_nonneg; positivity)
    _ = _ := by rw [abs_div, abs_of_pos hρ]; ring

theorem latticeCutoff_diff1_add_le {ρ : ℝ} (hρ : 0 < ρ) (x₀ z : Fin d → ℤ) (μ : Fin d) :
    |latticeCutoff ρ x₀ (z + Pi.single μ 1) - latticeCutoff ρ x₀ z| ≤ cutoffProfile.M₁ / ρ := by
  simpa using latticeCutoff_diff1_le hρ x₀ z μ 1

theorem latticeCutoff_diff1_sub_le {ρ : ℝ} (hρ : 0 < ρ) (x₀ z : Fin d → ℤ) (μ : Fin d) :
    |latticeCutoff ρ x₀ (z - Pi.single μ 1) - latticeCutoff ρ x₀ z| ≤ cutoffProfile.M₁ / ρ := by
  have e1 : z - Pi.single μ (1 : ℤ) = z + Pi.single μ (-1 : ℤ) := by
    rw [sub_eq_add_neg, Pi.single_neg]
  rw [e1]
  simpa using latticeCutoff_diff1_le hρ x₀ z μ (-1)

/-- Second difference of the cutoff: `|χ(z + e_μ) + χ(z - e_μ) - 2χ(z)| ≤ M₂/ρ²`. -/
theorem latticeCutoff_diff2_le {ρ : ℝ} (hρ : 0 < ρ) (x₀ z : Fin d → ℤ) (μ : Fin d) :
    |latticeCutoff ρ x₀ (z + Pi.single μ 1) + latticeCutoff ρ x₀ (z - Pi.single μ 1) -
        2 * latticeCutoff ρ x₀ z| ≤ cutoffProfile.M₂ / ρ ^ 2 := by
  have e1 : z - Pi.single μ (1 : ℤ) = z + Pi.single μ (-1 : ℤ) := by
    rw [sub_eq_add_neg, Pi.single_neg]
  rw [e1, latticeCutoff_shift, latticeCutoff_shift, latticeCutoff_eq_mul ρ x₀ z μ]
  obtain ⟨hp0, hp1⟩ := prod_erase_mem ρ x₀ z μ
  have h2 := profile_diff2 cutoffProfile.differentiable cutoffProfile.differentiable_deriv
    cutoffProfile.deriv_deriv_le (((z μ - x₀ μ : ℤ) : ℝ) / ρ) (1 / ρ)
  have ea : (((z μ - x₀ μ : ℤ) : ℝ) + ((1 : ℤ) : ℝ)) / ρ = ((z μ - x₀ μ : ℤ) : ℝ) / ρ + 1 / ρ := by
    push_cast; ring
  have eb : (((z μ - x₀ μ : ℤ) : ℝ) + ((-1 : ℤ) : ℝ)) / ρ = ((z μ - x₀ μ : ℤ) : ℝ) / ρ - 1 / ρ := by
    push_cast; ring
  rw [ea, eb]
  set P := ∏ ν ∈ Finset.univ.erase μ, cutoffProfile.H (((z ν - x₀ ν : ℤ) : ℝ) / ρ)
  set a := ((z μ - x₀ μ : ℤ) : ℝ) / ρ
  have e : cutoffProfile.H (a + 1 / ρ) * P + cutoffProfile.H (a - 1 / ρ) * P -
      2 * (cutoffProfile.H a * P) =
      (cutoffProfile.H (a + 1 / ρ) + cutoffProfile.H (a - 1 / ρ) - 2 * cutoffProfile.H a) * P := by
    ring
  rw [e, abs_mul, abs_of_nonneg hp0]
  calc _ ≤ cutoffProfile.M₂ * (1 / ρ) ^ 2 * 1 :=
        mul_le_mul h2 hp1 hp0 (by have := cutoffProfile.M₂_nonneg; positivity)
    _ = _ := by field_simp

end Balaban.LatticeGreen
