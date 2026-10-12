/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormEstimates

/-!
# The context of the local analysis and the rotated configuration of a polymer

`Ctx` bundles the premises, the data, a frame (`u`, `R`) and the numerical conditions.  The
lemmas express the configuration `pack X ψ b` of a polymer in the rotated frame as the reference
point plus the small displacement `zc + pack X φ 0` (constant part and differences), with the
norm bounds used by the local estimate.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The context of the local analysis. -/
structure Ctx (T : TermFamily d N) (i₀ i₁ : Fin N) (ν ρ E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) (ψ : Site d → Spin N) (b : Spin N)
    (σ ε K₂ : ℝ) (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ) : Prop where
  hyp : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom
  dat : DataHyp Dom ν σ ε K₂ ψ b
  frame : Frame i₀ σ ε ψ u R
  σpos : 0 < σ
  σle : σ ≤ 1
  εpos : 0 < ε
  ρpos : 0 < ρ
  ρle : ρ ≤ 1
  ν0 : 0 ≤ ν
  νσ : ν ≤ σ ^ 2
  E0nn : 0 ≤ E₀
  Ann : 0 ≤ A
  τle : σ ^ 2 * ε ≤ 1 / 4

section Ctx

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem l1_cast (x : Site d) : (l1 x : ℝ) = ((∑ μ, |x μ| : ℤ) : ℝ) := by
  unfold l1
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem Ctx.l1_le (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) {x : Site d} (hx : x ∈ X) : (l1 x : ℝ) ≤ A * (1 + T.dist X) := by
  rw [l1_cast]; exact c.hyp.diam X hX x hx

theorem Ctx.rotDiff_le (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (x : Site d) :
    ‖rotDiff R ψ x‖ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := by
  have h := norm_mulVec_le (R := R) (B := 40) (by norm_num) (fun i k => by
    have := c.frame.bd i k; simpa [rotBound] using this) (ψ x - ψ 0)
  have h2 := norm_sub_le_l1 (ψ := ψ) (δ := σ * ε) c.dat.adj 0 x
  simp only [zero_add] at h2
  unfold rotDiff
  calc ‖R.mulVec (ψ x - ψ 0)‖ ≤ N * 40 * ‖ψ x - ψ 0‖ := h
    _ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem Ctx.ga_le (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (x : Site d) :
    ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ 2 * (σ ^ 2 * ε) := by
  have h1 := c.dat.sq x
  have h2 := c.dat.sq 0
  calc ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖
      = ‖(dot (ψ x) (ψ x) - 1) - (dot (ψ 0) (ψ 0) - 1)‖ := by ring_nf
    _ ≤ ‖dot (ψ x) (ψ x) - 1‖ + ‖dot (ψ 0) (ψ 0) - 1‖ := norm_sub_le _ _
    _ ≤ 2 * (σ ^ 2 * ε) := by linarith

/-- The constant part of the displacement in the rotated frame. -/
def zcfg (X : Finset (Site d)) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N) (b : Spin N)
    (R : Matrix (Fin N) (Fin N) ℂ) : Cfg d N X :=
  pack X (fun _ => R.mulVec (ψ 0) - Pi.single i₀ 1) (R.mulVec b - (ν : ℂ) • Pi.single i₀ 1)

theorem pack_rot_eq (X : Finset (Site d)) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N) (b : Spin N)
    (R : Matrix (Fin N) (Fin N) ℂ) :
    pack X (fun x => R.mulVec (ψ x)) (R.mulVec b) =
      refPt i₀ ν X + (zcfg X i₀ ν ψ b R + pack X (rotDiff R ψ) 0) := by
  ext (⟨x, j⟩ | j)
  · simp [pack, zcfg, refPt, rotDiff, Matrix.mulVec_sub]
  · simp [pack, zcfg, refPt]

theorem pack_const_rot_eq (X : Finset (Site d)) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N)
    (b : Spin N) (R : Matrix (Fin N) (Fin N) ℂ) :
    pack X (fun _ => R.mulVec (ψ 0)) (R.mulVec b) = refPt i₀ ν X + zcfg X i₀ ν ψ b R := by
  ext (⟨x, j⟩ | j)
  · simp [pack, zcfg, refPt]
  · simp [pack, zcfg, refPt]

theorem Ctx.u_norm (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) : 3 / 4 ≤ ‖u‖ := by
  have h := c.frame.u_close
  have := norm_sub_norm_le (1 : ℂ) u
  rw [norm_sub_rev] at this
  simp at this
  have := c.τle
  linarith

theorem Ctx.zc_le (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (X : Finset (Site d)) :
    ‖zcfg X i₀ ν ψ b R‖ ≤ (160 * N + 1) * (σ ^ 2 * ε) := by
  have hτ0 : 0 ≤ σ ^ 2 * ε := by have := c.εpos; positivity
  have hu := c.u_norm
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  rintro (⟨x, j⟩ | j)
  · -- constant part: `(u - 1) e_{i₀}`
    have key : R.mulVec (ψ 0) - (Pi.single i₀ 1 : Spin N) = (u - 1) • (Pi.single i₀ 1 : Spin N) := by
      rw [c.frame.rot0, sub_smul, one_smul]
    simp only [zcfg, pack, Sum.elim_inl, key, Pi.smul_apply, smul_eq_mul]
    have h1 : ‖(u - 1) * (Pi.single i₀ 1 : Spin N) j‖ ≤ ‖u - 1‖ := by
      rw [norm_mul]
      have : ‖(Pi.single i₀ 1 : Spin N) j‖ ≤ 1 := by
        by_cases h : j = i₀ <;> simp [h]
      nlinarith [norm_nonneg (u - 1), norm_nonneg ((Pi.single i₀ 1 : Spin N) j)]
    have := c.frame.u_close
    nlinarith [this, h1]
  · -- the field part
    have hw : R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 =
        R.mulVec (b - ((ν : ℂ) / u) • ψ 0) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, c.frame.rot0, smul_smul]
      congr 1
      rw [div_mul_cancel₀ _ hu0]
    simp only [zcfg, pack, Sum.elim_inr]
    rw [hw]
    have hb := norm_mulVec_le (R := R) (B := 40) (by norm_num) (fun i k => by
      have := c.frame.bd i k; simpa [rotBound] using this) (b - ((ν : ℂ) / u) • ψ 0)
    have h1 : ‖b - ((ν : ℂ) / u) • ψ 0‖ ≤ 4 * (σ ^ 2 * ε) := by
      have e : b - ((ν : ℂ) / u) • ψ 0 = (b - (ν : ℂ) • ψ 0) + ((ν : ℂ) • ψ 0 - ((ν : ℂ) / u) • ψ 0) := by
        abel
      rw [e]
      have t1 := c.dat.b_close
      have t2 : ‖(ν : ℂ) • ψ 0 - ((ν : ℂ) / u) • ψ 0‖ ≤ 3 * (σ ^ 2 * ε) := by
        have : (ν : ℂ) • ψ 0 - ((ν : ℂ) / u) • ψ 0 = ((ν : ℂ) * (1 - 1 / u)) • ψ 0 := by
          rw [mul_sub, sub_smul, mul_one, mul_one_div]
        rw [this, norm_smul, norm_mul]
        have h3 : ‖(ν : ℂ)‖ = ν := by simp [abs_of_nonneg c.ν0]
        have h4 : ‖(1 : ℂ) - 1 / u‖ ≤ 4 / 3 * (σ ^ 2 * ε) := by
          have : (1 : ℂ) - 1 / u = (u - 1) / u := by field_simp
          rw [this, norm_div, div_le_iff₀ (by linarith)]
          have := c.frame.u_close
          nlinarith [norm_nonneg (u - 1)]
        have h5 : ν ≤ 1 := c.νσ.trans (by nlinarith [c.σpos, c.σle])
        rw [h3]
        calc ν * ‖(1 : ℂ) - 1 / u‖ * ‖ψ 0‖ ≤ 1 * (4 / 3 * (σ ^ 2 * ε)) * 2 := by
              refine mul_le_mul (mul_le_mul h5 h4 (norm_nonneg _) zero_le_one) c.dat.bdd0
                (norm_nonneg _) (by positivity)
          _ ≤ 3 * (σ ^ 2 * ε) := by nlinarith
      linarith [(norm_add_le _ _).trans (add_le_add t1 t2)]
    have : (N : ℝ) * 40 * ‖b - ((ν : ℂ) / u) • ψ 0‖ ≤ (160 * N + 1) * (σ ^ 2 * ε) := by
      calc (N : ℝ) * 40 * ‖b - ((ν : ℂ) / u) • ψ 0‖ ≤ N * 40 * (4 * (σ ^ 2 * ε)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ _ := by nlinarith
    exact (norm_le_pi_norm _ j).trans (hb.trans this)

end Ctx

end Balaban.SmallField
