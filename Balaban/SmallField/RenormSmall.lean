/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormCtx

/-!
# The contribution of a polymer with small `d_j(X)` (Steps 2–5 of §2.3)

`Ctx.small_case`: for `X ∈ 𝒫` such that `(C₁ + κ₁)(1 + d_j(X)) σ ε ≤ ρ/2`,
`𝓔(0,X;ψ,b) - 𝓔(0,X;ψ(0),b) - A_X - L_X` is bounded by the explicit sum `smallBnd`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The constant `C₁ = 160 N + 1` bounding the constant part of the displacement. -/
def cC1 (N : ℕ) : ℝ := 160 * N + 1

/-- The constant `κ₁ = 40 N A` bounding the differences in the rotated frame. -/
def cK1 (N : ℕ) (A : ℝ) : ℝ := N * 40 * A

/-- The size `D` of the differences of a polymer with `t = 1 + d_j(X)`. -/
def sD (N : ℕ) (A σ ε t : ℝ) : ℝ := cK1 N A * t * (σ * ε)

/-- The size `Z₀` of the constant part. -/
def sZ0 (N : ℕ) (σ ε : ℝ) : ℝ := cC1 N * (σ ^ 2 * ε)

/-- The bound `F` for the longitudinal differences. -/
def sF (N : ℕ) (A σ ε t : ℝ) : ℝ := 2 * (σ ^ 2 * ε) + N * sD N A σ ε t ^ 2

/-- The bound `Eₑ` for the linearization error of the longitudinal differences. -/
def sEe (N : ℕ) (A σ ε t : ℝ) : ℝ := sF N A σ ε t * (σ ^ 2 * ε) + sF N A σ ε t ^ 2

/-- The bound `E_b` for the transverse second-order expansion. -/
def sEb (N : ℕ) (A σ ε K₂ t : ℝ) : ℝ :=
  2 * N * (2 * (A * t) * (N * 40 * (σ * ε))) * (N * 40 * (6 * (A * t) ^ 2 * K₂)) +
    N * (N * 40 * (6 * (A * t) ^ 2 * K₂)) ^ 2

/-- The explicit bound of the local estimate. -/
noncomputable def smallBnd (N : ℕ) (A M ρ ν σ ε K₂ t P : ℝ) : ℝ :=
  2 * M * ((sZ0 N σ ε + sD N A σ ε t) / ρ) ^ 3 + 2 * M * (sZ0 N σ ε / ρ) ^ 3 +
    4 * M * sZ0 N σ ε * sD N A σ ε t / ρ ^ 2 + P * (M / ρ) * sEe N A σ ε t +
    2 * P ^ 2 * M * sF N A σ ε t ^ 2 / ρ ^ 2 + ν / 2 * P * (4 * M / ρ ^ 2) * (N * sD N A σ ε t ^ 2) +
    P ^ 2 * (M / ρ ^ 2) * sEb N A σ ε K₂ t

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem Ctx.termOK (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) : TermOK i₀ ν ρ X (T.term X) :=
  ⟨c.ρpos, c.hyp.analytic X hX, fun c' hc' R' hR' hbd hmem => c.hyp.rot_inv X hX c' hc' R' hR' hbd hmem⟩

theorem Ctx.hM (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
  fun y hy => c.hyp.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)

/-- Rotation invariance for the configuration of a polymer. -/
theorem Ctx.term_rot (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) {ψ' : Site d → Spin N} {b' : Spin N}
    (hball : rotCfgL R X (pack X ψ' b') ∈ ball (refPt i₀ ν X) ρ) :
    T.term X (pack X ψ' b') = T.term X (rotCfgL R X (pack X ψ' b')) := by
  have hmem : pack X ψ' b' ∈ Tube i₀ ν ρ X := ⟨R, c.frame.orth, c.frame.bd, hball⟩
  exact (c.hyp.rot_inv X hX _ hmem R c.frame.orth c.frame.bd
    (ball_subset_tube i₀ ν ρ X hball)).symm

theorem Ctx.small_case (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) (hs : (cC1 N + cK1 N A) * (1 + T.dist X) * σ * ε ≤ ρ / 2) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      smallBnd N A (E₀ * Real.exp (-κ * T.dist X)) ρ ν σ ε K₂ (1 + T.dist X) X.card := by
  have hok := c.termOK hX
  have hM := c.hM hX
  have hne : i₁ ≠ i₀ := c.hyp.ne.symm
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hσ := c.σpos
  have hε := c.εpos
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := c.Ann; positivity
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  have hτ0 : 0 ≤ σ ^ 2 * ε := by positivity
  have hD0 : 0 ≤ sD N A σ ε t := by unfold sD; positivity
  have hZ0n : 0 ≤ sZ0 N σ ε := by unfold sZ0; positivity
  have hDφ : ∀ x ∈ X, ‖rotDiff R ψ x‖ ≤ sD N A σ ε t := by
    intro x hx
    refine (c.rotDiff_le x).trans ?_
    unfold sD cK1
    have := c.l1_le hX hx
    have h2 : 0 ≤ σ * ε := by positivity
    calc (N : ℝ) * 40 * ((l1 x : ℝ) * (σ * ε)) ≤ N * 40 * (A * t * (σ * ε)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h2) (by positivity)
          simpa [ht] using this
      _ = _ := by ring
  have hpk : ‖pack X (rotDiff R ψ) 0‖ ≤ sD N A σ ε t := norm_pack_le X _ hD0 hDφ
  have hzc : ‖zcfg X i₀ ν ψ b R‖ ≤ sZ0 N σ ε := by unfold sZ0 cC1; exact c.zc_le X
  have hz : ‖zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0‖ ≤ sZ0 N σ ε + sD N A σ ε t :=
    (norm_add_le _ _).trans (add_le_add hzc hpk)
  have hZ : sZ0 N σ ε + sD N A σ ε t ≤ ρ / 2 := by
    refine le_trans ?_ hs
    unfold sZ0 sD
    have h1 : σ ^ 2 * ε ≤ t * σ * ε := by
      have : σ ≤ 1 := c.σle
      nlinarith [mul_pos hσ hε]
    nlinarith [mul_pos hσ hε, mul_nonneg hC1 (sub_nonneg.mpr h1)]
  have hZ0 : sZ0 N σ ε ≤ ρ / 2 := by linarith
  -- the rotated configuration
  have hball1 : rotCfgL R X (pack X ψ b) ∈ ball (refPt i₀ ν X) ρ := by
    rw [rotCfgL_pack, pack_rot_eq, mem_ball, dist_eq_norm, add_sub_cancel_left]
    have := c.ρpos; linarith
  have hball2 : rotCfgL R X (pack X (fun _ => ψ 0) b) ∈ ball (refPt i₀ ν X) ρ := by
    rw [rotCfgL_pack, pack_const_rot_eq, mem_ball, dist_eq_norm, add_sub_cancel_left]
    have := c.ρpos; linarith
  rw [c.term_rot hX hball1, c.term_rot hX hball2, rotCfgL_pack, rotCfgL_pack, pack_rot_eq,
    pack_const_rot_eq]
  -- the longitudinal and transverse bounds
  have hlong : ∀ x ∈ X, ‖rotDiff R ψ x (i₀)‖ ≤ sF N A σ ε t ∧
      ‖rotDiff R ψ x i₀ - (dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) / 2 +
        dotT i₀ (rotDiff R ψ x) (rotDiff R ψ x) / 2‖ ≤ sEe N A σ ε t := by
    intro x hx
    have hθ : ‖dotT i₀ (rotDiff R ψ x) (rotDiff R ψ x)‖ ≤ N * sD N A σ ε t ^ 2 :=
      (norm_dotT_self_le i₀ _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hDφ x hx) 2) hN)
    have hφ : ‖rotDiff R ψ x i₀‖ ≤ 1 / 2 := by
      refine (norm_le_pi_norm _ i₀).trans ((hDφ x hx).trans ?_)
      have := c.ρle; linarith
    have := long_bounds (u := u) (φ0 := rotDiff R ψ x i₀)
      (θ := dotT i₀ (rotDiff R ψ x) (rotDiff R ψ x))
      (g := dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)) c.frame.u_close c.τle (c.ga_le x) hθ hφ
      (c.frame.long_identity x)
    exact this
  have hEb : ∀ x ∈ X, ∀ x' ∈ X, ‖dotT i₀ (rotDiff R ψ x - rotDiff R ψ x')
      (rotDiff R ψ x - rotDiff R ψ x') - wquad (gradTensor i₀ R ψ) x x'‖ ≤
      sEb N A σ ε K₂ t := by
    intro x hx x' hx'
    have hR : ∀ i k, ‖R i k‖ ≤ 40 := fun i k => by
      have := c.frame.bd i k; simpa [rotBound] using this
    have := dotT_diff_bound hR c.dat.adj c.dat.sec x x' (L := A * t) (by simpa [ht] using c.l1_le hX hx)
      (by simpa [ht] using c.l1_le hX hx') (by have := c.Ann; positivity) i₀ (by positivity)
      c.dat.K2_nonneg
    exact this
  have key := hok.local_bound hne hM c.ν0 (rotDiff R ψ)
    (fun y => dot (ψ y) (ψ y) - dot (ψ 0) (ψ 0)) (gradTensor i₀ R ψ) (zcfg X i₀ ν ψ b R)
    (Z := sZ0 N σ ε + sD N A σ ε t) (Z0 := sZ0 N σ ε) (D := sD N A σ ε t)
    (F := sF N A σ ε t) (Ee := sEe N A σ ε t) (Eb := sEb N A σ ε K₂ t) hD0
    (by unfold sF; positivity) hz hZ hzc hZ0 hDφ (fun x hx => (hlong x hx).1)
    (fun x hx => (hlong x hx).2) hEb
  exact key

end Balaban.SmallField
