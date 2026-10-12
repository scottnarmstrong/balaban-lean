/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldSource
public import Balaban.Multiscale.PointwiseP
public import Balaban.Multiscale.PointwiseCase2d
public import Balaban.Multiscale.PointwiseCase2c

/-!
# Lemma P for the cut operator of a cube (VMOD-9 §3, Lemma 3.1)

For `U_D(x) = |u(x)| + ℓ(x) ∑_{(x,μ) ∉ D} |u(x+e_μ) - u(x)|` of the solution of the cut equation with
the physical wall retained:

`U_D(x) ≤ K₁ e^{-γ t} L^{2j'} M_f + ϑ M`

whenever `0 ≤ t ≤ d_H(x, y')` and `U_D ≤ M` on the `H`-path ball of radius `2d + 1` around `x`.
The constant `K₁ = cutK1 d L` is the explicit expression (1.3) of VMOD-9 in the constants of the
landed finite-lattice estimates `lemma_loc_a`, `lemma_loc_b`, `green_sum_le`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.LatticeGreen Balaban.Reflection Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The constant `C_a(d)` of the landed `lemma_loc_a` (chosen). -/
noncomputable def locCa (d : ℕ) : ℝ :=
  if h : 3 ≤ d then Classical.choose (lemma_loc_a h) else 0

/-- The constant `C_b(d)` of the landed `lemma_loc_b` (chosen). -/
noncomputable def locCb (d : ℕ) : ℝ :=
  if h : 3 ≤ d then Classical.choose (lemma_loc_b h) else 0

/-- The constant `c_G(d)` of the landed `green_sum_le` (chosen). -/
noncomputable def locCG (d : ℕ) : ℝ :=
  if h : 3 ≤ d then Classical.choose (green_sum_le h) else 0

theorem locCa_spec (hd : 3 ≤ d) : 0 ≤ locCa d ∧ ∀ (ρ : ℝ), 8 ≤ ρ → ∀ (x₀ x : Fin d → ℤ),
    ‖x - x₀‖ ≤ ρ / 2 → ∀ (u g : (Fin d → ℤ) → ℂ),
      (∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) →
        ‖u x‖ ≤ locCa d * ρ ^ (-(d : ℝ) / 2) *
            Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) +
          ∑ z ∈ latticeBall x₀ (2 * ρ), latticeGreen d (x - z) * ‖g z‖ := by
  unfold locCa
  simp only [hd, ↓reduceDIte]
  exact Classical.choose_spec (lemma_loc_a hd)

theorem locCb_spec (hd : 3 ≤ d) : 0 ≤ locCb d ∧ ∀ (ρ : ℝ), 8 ≤ ρ → ∀ (x₀ x : Fin d → ℤ),
    ‖x - x₀‖ ≤ ρ / 2 → ∀ (ν : Fin d) (u g : (Fin d → ℤ) → ℂ),
      (∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) →
        ‖u (x + Pi.single ν 1) - u x‖ ≤
          locCb d * ρ ^ (-1 - (d : ℝ) / 2) * Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) +
          ∑ z ∈ latticeBall x₀ (2 * ρ),
            |latticeGreen d (x - z + Pi.single ν 1) - latticeGreen d (x - z)| * ‖g z‖ := by
  unfold locCb
  simp only [hd, ↓reduceDIte]
  exact Classical.choose_spec (lemma_loc_b hd)

theorem locCG_spec (hd : 3 ≤ d) : 0 ≤ locCG d ∧ ∀ (R : ℝ), 0 ≤ R → ∀ (A : Finset (Fin d → ℤ)),
    A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      (∑ z ∈ A, latticeGreen d (0 - z) ≤ locCG d * (R + 1) ^ 2) ∧
      (∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| ≤
        locCG d * (R + 1)) := by
  unfold locCG
  simp only [hd, ↓reduceDIte]
  exact Classical.choose_spec (green_sum_le hd)

/-- `D₀ = 2d + 1`, `ϑ = ¼ e^{-γ D₀}` is `thetaStar d`; the radius constant
`c₀ = min {1/4, ϑ / (c_G (3+1)(9+3L) + 1)}`. -/
noncomputable def cutC0 (d L : ℕ) : ℝ :=
  min (1 / 4 : ℝ) (thetaStar d / (locCG d * ((3 + 1) * (9 + 3 * L)) + 1))

/-- `J₀ = 8 d L / c₀`. -/
noncomputable def cutJ0 (d L : ℕ) : ℝ := 8 * d * L / cutC0 d L

/-- `A₀ = √8 / c_p + d √(10 / c_p)`. -/
noncomputable def cutA0 (d : ℕ) : ℝ :=
  Real.sqrt 8 / poincareConst d + d * Real.sqrt (10 / poincareConst d)

/-- `C₂ = 2 e^{ε₀ (1 + 2d)} L² b² / (c_p √((c₀/d)^d))`. -/
noncomputable def cutC2 (d L : ℕ) : ℝ :=
  2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
    Real.sqrt ((cutC0 d L / d) ^ d)

/-- **The constant `K₁` of VMOD-9 (1.3)**:
`max {A₀ b √(J₀^d), 2^{d/2} (C_a + d² L C_b / c₀) C₂ + c_G (9 + 3 d L) e^{γ D₀}}`. -/
noncomputable def cutK1 (d L : ℕ) : ℝ :=
  max (cutA0 d * bd d L * Real.sqrt (cutJ0 d L ^ d))
    (Real.sqrt (2 ^ d) * ((locCa d + d * (d * L / cutC0 d L) * locCb d) * cutC2 d L) +
      locCG d * (9 + 3 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)))

omit [NeZero L] in
theorem cutC0_pos (hd : 3 ≤ d) : 0 < cutC0 d L := by
  have := (locCG_spec hd).1
  unfold cutC0
  refine lt_min (by norm_num) (div_pos (thetaStar_pos d) (by positivity))

omit [NeZero L] in
theorem cutC0_le : cutC0 d L ≤ 1 / 4 := min_le_left _ _

theorem cutK1_nonneg (hd : 3 ≤ d) : 0 ≤ cutK1 d L := by
  have h1 := cutC0_pos (L := L) hd
  have hCa := (locCa_spec hd).1
  have hCb := (locCb_spec hd).1
  have hcG := (locCG_spec hd).1
  have hc := poincareConst_pos (by omega : 0 < d)
  refine le_max_of_le_left ?_
  unfold cutA0
  have := one_le_bd (d := d) (L := L)
  have hJ : 0 ≤ cutJ0 d L := by unfold cutJ0; positivity
  positivity

omit [NeZero N₀] [NeZero L] in
/-- The arithmetic of the radius `ρ = c₀ L^{j₀} / d ≥ 8`. -/
theorem case2_radius_arith {d' c0 Lj : ℝ} (hd : 1 ≤ d') (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4)
    (hLj : 0 < Lj) (hρ : 8 ≤ c0 * Lj / d') :
    d' * (2 * (c0 * Lj / d')) ≤ Lj ∧ d' * (2 * (c0 * Lj / d') + 1) ≤ Lj ∧ d' ≤ Lj ∧
      c0 * Lj / d' ≤ c0 * Lj := by
  have hd0 : 0 < d' := by linarith
  have h1 : d' * (c0 * Lj / d') = c0 * Lj := by field_simp
  have h2 : 8 * d' ≤ c0 * Lj := by
    rw [le_div_iff₀ hd0] at hρ; linarith
  have h3 : c0 * Lj ≤ Lj / 4 := by nlinarith
  refine ⟨?_, ?_, ?_, div_le_self (by positivity) hd⟩ <;> nlinarith

omit [NeZero N₀] [NeZero L] in
/-- Combination of the Loc bounds, the source sums and the potential term. -/
theorem case2_combine {d : ℕ} {Ca Cb cG c0 ρ Tval Mf m Lc L TT Fsrc Pot Gs u0 : ℝ}
    {Δ Ds : Fin d → ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hc0 : 0 < c0) (hL : 0 < L)
    (hd : (1 : ℝ) ≤ d) (hLc : 0 < Lc)
    (hUa : u0 ≤ Ca * Tval + (Mf * Gs + m * (cG * (2 * ρ + 1) ^ 2)))
    (hUb : ∀ ν, Δ ν ≤ Cb * ρ⁻¹ * Tval + (Mf * Ds ν + m * (cG * (2 * ρ + 1))))
    (hsr : Lc * L * ρ⁻¹ = d * L / c0)
    (hTb : Tval ≤ TT)
    (hftot : Mf * Gs + Lc * L * ∑ ν : Fin d, (Mf * Ds ν) ≤ Fsrc)
    (hpot : m * (cG * (2 * ρ + 1) ^ 2) + (Lc * L) * d * (m * (cG * (2 * ρ + 1))) ≤ Pot) :
    u0 + Lc * L * ∑ ν : Fin d, Δ ν ≤ (Ca + d * (d * L / c0) * Cb) * TT + Fsrc + Pot := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hsumΔ : ∑ ν : Fin d, Δ ν ≤ d * (Cb * ρ⁻¹ * Tval) + ∑ ν : Fin d, (Mf * Ds ν) +
      d * (m * (cG * (2 * ρ + 1))) := by
    calc _ ≤ ∑ ν : Fin d, (Cb * ρ⁻¹ * Tval + (Mf * Ds ν + m * (cG * (2 * ρ + 1)))) :=
          Finset.sum_le_sum fun ν _ => hUb ν
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp
          ring
  have hU2 := mul_le_mul_of_nonneg_left hsumΔ (mul_pos hLc hL).le
  have hX1 : 0 ≤ Ca + d * (d * L / c0) * Cb := by positivity
  have hT' := mul_le_mul_of_nonneg_left hTb hX1
  have key : (Ca * Tval + (Mf * Gs + m * (cG * (2 * ρ + 1) ^ 2))) +
      (Lc * L) * (d * (Cb * ρ⁻¹ * Tval) + ∑ ν : Fin d, (Mf * Ds ν) +
        d * (m * (cG * (2 * ρ + 1)))) =
      (Ca + d * (d * L / c0) * Cb) * Tval +
      (Mf * Gs + (Lc * L) * ∑ ν : Fin d, (Mf * Ds ν)) +
      (m * (cG * (2 * ρ + 1) ^ 2) + (Lc * L) * d * (m * (cG * (2 * ρ + 1)))) := by
    linear_combination (d * Cb * Tval) * hsr
  linarith only [key, hU2, hUa, hT', hftot, hpot]

/-- **Lemma P, evaluation scale `ρ ≥ 8`** (VMOD-9 (3.5)--(3.8)): the folded Loc estimate. -/
theorem cubeFold_case2_bound {Ca Cb cG c0 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hcG : 0 ≤ cG)
    (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4) {G : GeneratingSet d L N₀ k ϱ} (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α *ᵥ u = f)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c))
    {j₀ j' : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hy' : y' ∈ G.layer j')
    (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (hρ : 8 ≤ c0 * (L : ℝ) ^ j₀ / d) {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x y') {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ G.Ω 1, G.pathDist z x ≤ ENNReal.ofReal (2 * d + 1) →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) (zeroExt (G.Ω 1) u) z ≤ M)
    (hLoc : ∀ (p0 : Torus d (2 * S)),
      foldMap (N₀ * L ^ k) S (2 * S) c p0 = x →
      ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 0)‖ ≤ Ca * (c0 * (L : ℝ) ^ j₀ / d) ^ (-(d : ℝ) / 2) *
          Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
            ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)‖ ^ 2) +
        ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          latticeGreen d (0 - z) *
            ‖negLap (fun w => zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)) z‖)
    (hLocb : ∀ (p0 : Torus d (2 * S)),
      foldMap (N₀ * L ^ k) S (2 * S) c p0 = x → ∀ μ : Fin d,
      ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (Pi.single μ 1)) -
          zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 0)‖ ≤
        Cb * (c0 * (L : ℝ) ^ j₀ / d) ^ (-1 - (d : ℝ) / 2) *
          Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
            ‖zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)‖ ^ 2) +
        ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          |latticeGreen d (0 - z + Pi.single μ 1) - latticeGreen d (0 - z)| *
            ‖negLap (fun w => zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)) z‖)
    (hG : ∀ R : ℝ, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      (∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (R + 1) ^ 2) ∧
      (∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| ≤
        cG * (R + 1))) :
    cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) (zeroExt (G.Ω 1) u) x ≤
      (((Ca + d * (d * L / c0) * Cb) * (Real.sqrt (2 ^ d) *
          (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 *
            bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d))) +
        cG * (9 + 3 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1))) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf)) +
      cG * ((3 + 1) * (9 + 3 * L)) * c0 * M := by
  have hd0 : 0 < d := by omega
  have hc := poincareConst_pos hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hj2 : 2 ≤ j₀ + 1 := by omega
  obtain ⟨p0, hp0, hlow⟩ := exists_lowerHalf (c := c) hxΛ
  have hS : L ^ (j₀ + 1) ≤ S :=
    side_ge_of_blockAligned G hd0 hΛ (by omega) hjk hx hxΛ
  obtain ⟨hRd, hRd1, hdL, hρle⟩ := case2_radius_arith hd1 hc0 hc04 hLc hρ
  set ρ := c0 * (L : ℝ) ^ j₀ / d with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hRS : 2 * ρ < S := by
    have h2 : (L : ℝ) ^ (j₀ + 1) ≤ S := by exact_mod_cast hS
    have h3 : (L : ℝ) ^ j₀ < (L : ℝ) ^ (j₀ + 1) := by
      rw [pow_succ]
      have : (3 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    have h4 : 2 * ρ ≤ (L : ℝ) ^ j₀ :=
      (le_mul_of_one_le_left (by positivity) hd1).trans hRd
    linarith
  set ball := latticeBall (0 : Fin d → ℤ) (2 * ρ) with hball
  set ut := zeroExt (G.Ω 1) u with hut
  set ft := zeroExt (G.Ω 1) f with hft
  set P := cubeFoldPt N₀ L k S c p0 with hP
  have hzb : ∀ z ∈ ball, (d : ℝ) * (‖z‖ + 1) ≤ (L : ℝ) ^ (j₀ + 1 - 1) := by
    intro z hz
    have := (mem_latticeBall (by positivity)).1 hz
    rw [sub_zero] at this
    simp only [Nat.add_sub_cancel]
    exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)).trans hRd1
  set m := (3 + 1) * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M with hm
  have hm0 : 0 ≤ m := by positivity
  have hg : ∀ z ∈ ball, ‖negLap (fun w => ut (P w)) z‖ ≤ ‖ft (P z)‖ + m := by
    intro z hz
    have := cubeFold_local_poisson_bound G hϱ hν hν1 ha S c hSℓ hu (j := j₀ + 1) hj2 hjk hx p0 hp0
      (hzb z hz) hM0 hα hM
    simpa only [Nat.add_sub_cancel] using this
  have hcut : CutAligned G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) := cubeCut_aligned G hΛ
  have hT := cubeFold_ball_l2 hcut hd hL hϱ hsep hν ha α hα hu hj01 hjk hj'1 hj'k hx hy' hsupp S c
    p0 hp0 hSℓ hS hc0 hc04 hρ hMf0 hMf ht0 ht
  set Tval := ρ ^ (-(d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖ut (P w)‖ ^ 2) with hTval
  obtain ⟨A, hzero, hftot⟩ := cubeFold_source_green_sum hd hL hϱ hsep hcG hG hj01 hjk hj'1 hj'k hx
    hy' hsupp S c p0 hp0 hSℓ (R := 2 * ρ) (by positivity) hRd hRS hMf0 hMf ht
  obtain ⟨hGB, hGBν⟩ := hG (2 * ρ) (by positivity) ball le_rfl
  have hSa : ∑ z ∈ ball, latticeGreen d (0 - z) * ‖negLap (fun w => ut (P w)) z‖ ≤
      Mf * ∑ z ∈ A, latticeGreen d (0 - z) + m * (cG * (2 * ρ + 1) ^ 2) := by
    calc _ ≤ ∑ z ∈ ball, latticeGreen d (0 - z) * (‖ft (P z)‖ + m) :=
          Finset.sum_le_sum fun z hz =>
            mul_le_mul_of_nonneg_left (hg z hz) (latticeGreen_nonneg _)
      _ = ∑ z ∈ ball, latticeGreen d (0 - z) * ‖ft (P z)‖ +
          m * ∑ z ∈ ball, latticeGreen d (0 - z) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ _ := add_le_add (hzero _ fun z => latticeGreen_nonneg _)
            (mul_le_mul_of_nonneg_left hGB hm0)
  have hSb : ∀ ν : Fin d, ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) -
        latticeGreen d (0 - z)| * ‖negLap (fun w => ut (P w)) z‖ ≤
      Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| +
        m * (cG * (2 * ρ + 1)) := by
    intro ν
    calc _ ≤ ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| *
          (‖ft (P z)‖ + m) :=
          Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hg z hz) (abs_nonneg _)
      _ = ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| *
            ‖ft (P z)‖ + m * ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) -
              latticeGreen d (0 - z)| := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ _ := add_le_add (hzero (fun z => |latticeGreen d (0 - z + Pi.single ν 1) -
            latticeGreen d (0 - z)|) (fun z => abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hGBν ν) hm0)
  have hUa : ‖ut (P 0)‖ ≤ Ca * Tval + (Mf * ∑ z ∈ A, latticeGreen d (0 - z) +
      m * (cG * (2 * ρ + 1) ^ 2)) := by
    have e : Ca * ρ ^ (-(d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖ut (P w)‖ ^ 2) =
        Ca * Tval := by rw [hTval]; ring
    linarith only [hLoc p0 hp0, hSa, e]
  have hUb : ∀ ν : Fin d, ‖ut (P (Pi.single ν 1)) - ut (P 0)‖ ≤ Cb * ρ⁻¹ * Tval +
      (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| +
        m * (cG * (2 * ρ + 1))) := by
    intro ν
    have e : Cb * ρ ^ (-1 - (d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖ut (P w)‖ ^ 2) =
        Cb * ρ⁻¹ * Tval := by
      rw [hTval, rpow_neg_one_sub_half hρ0 d]; ring
    linarith only [hLocb p0 hp0 ν, hSb ν, e]
  have hsr : (L : ℝ) ^ j₀ * L * ρ⁻¹ = d * L / c0 := by
    rw [hρdef]; field_simp
  have hpot := pot_arith (cG := cG) (c0 := c0) (L := (L : ℝ)) (d := (d : ℝ)) (M := M)
    (Lc := (L : ℝ) ^ j₀) (κ := 3 + 1) hcG hc0 (by linarith) hL1 hd1 hLc hM0 (by linarith)
    (by linarith)
  have hftot' : Mf * ∑ z ∈ A, latticeGreen d (0 - z) + ((L : ℝ) ^ j₀ * L) *
      ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
        latticeGreen d (0 - z)|) ≤
      cG * (9 + 3 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) := by
    rw [← pow_succ]; exact hftot
  have hfin := case2_combine (Ca := Ca) (Cb := Cb) (cG := cG) (c0 := c0) (ρ := ρ) (Tval := Tval)
    (Mf := Mf) (m := m) (Lc := (L : ℝ) ^ j₀) (L := (L : ℝ))
    (TT := Real.sqrt (2 ^ d) * (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) *
        (L : ℝ) ^ 2 * bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf)))
    (Fsrc := cG * (9 + 3 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf))
    (Pot := cG * ((3 + 1) * (9 + 3 * L)) * c0 * M)
    (Gs := ∑ z ∈ A, latticeGreen d (0 - z)) (u0 := ‖ut (P 0)‖)
    (Δ := fun ν => ‖ut (P (Pi.single ν 1)) - ut (P 0)‖)
    (Ds := fun ν => ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)|)
    hCa hCb hc0 hL0 hd1 hLc hUa hUb hsr hT hftot' hpot
  have hU : cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) ut x =
      ‖ut (P 0)‖ + (L : ℝ) ^ (j₀ + 1) * ∑ ν : Fin d, ‖ut (P (Pi.single ν 1)) - ut (P 0)‖ :=
    cubeFold_local_cutU_eq G hϱ S c hSℓ hj2 hjk hx
      (by simpa only [Nat.add_sub_cancel] using hdL) p0 hp0 hlow ut
  rw [hU, pow_succ]
  refine hfin.trans (le_of_eq ?_)
  ring

end Balaban.Localization
