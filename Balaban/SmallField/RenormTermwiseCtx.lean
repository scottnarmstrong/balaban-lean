/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseDefs
public import Balaban.SmallField.RenormMain

/-!
# Lemma 3.2: the termwise context

`CtxTw` is the landed `Ctx` with `PremisesTerm` in place of `Premises`: the premises without the
renormalization conditions (H.5) on the sum.  The landed per-term estimates (`Ctx.small_case`,
`Ctx.tail_case`, `Ctx.A_le`, `Ctx.Lq_le`, `Ctx.potential_term`, `Ctx.dlt_bound`) never use (H.5);
they are restated here under the new names with the same proofs (the landed lemmas are stated for
the bundle `Premises`, which includes (H.5)).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The context of the local analysis. -/
structure CtxTw (T : TermFamily d N) (i₀ i₁ : Fin N) (ν ρ E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) (ψ : Site d → Spin N) (b : Spin N)
    (σ ε K₂ : ℝ) (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ) : Prop where
  hyp : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom
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


section CtxTw

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem CtxTw.l1_le (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) {x : Site d} (hx : x ∈ X) : (l1 x : ℝ) ≤ A * (1 + T.dist X) := by
  rw [l1_cast]; exact c.hyp.diam X hX x hx

theorem CtxTw.rotDiff_le (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (x : Site d) :
    ‖rotDiff R ψ x‖ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := by
  have h := norm_mulVec_le (R := R) (B := 40) (by norm_num) (fun i k => by
    have := c.frame.bd i k; simpa [rotBound] using this) (ψ x - ψ 0)
  have h2 := norm_sub_le_l1 (ψ := ψ) (δ := σ * ε) c.dat.adj 0 x
  simp only [zero_add] at h2
  unfold rotDiff
  calc ‖R.mulVec (ψ x - ψ 0)‖ ≤ N * 40 * ‖ψ x - ψ 0‖ := h
    _ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem CtxTw.ga_le (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (x : Site d) :
    ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ 2 * (σ ^ 2 * ε) := by
  have h1 := c.dat.sq x
  have h2 := c.dat.sq 0
  calc ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖
      = ‖(dot (ψ x) (ψ x) - 1) - (dot (ψ 0) (ψ 0) - 1)‖ := by ring_nf
    _ ≤ ‖dot (ψ x) (ψ x) - 1‖ + ‖dot (ψ 0) (ψ 0) - 1‖ := norm_sub_le _ _
    _ ≤ 2 * (σ ^ 2 * ε) := by linarith

theorem CtxTw.u_norm (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) : 3 / 4 ≤ ‖u‖ := by
  have h := c.frame.u_close
  have := norm_sub_norm_le (1 : ℂ) u
  rw [norm_sub_rev] at this
  simp at this
  have := c.τle
  linarith

theorem CtxTw.zc_le (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) (X : Finset (Site d)) :
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

theorem CtxTw.termOK (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) : TermOK i₀ ν ρ X (T.term X) :=
  ⟨c.ρpos, c.hyp.analytic X hX, fun c' hc' R' hR' hbd hmem => c.hyp.rot_inv X hX c' hc' R' hR' hbd hmem⟩

theorem CtxTw.hM (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
  fun y hy => c.hyp.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)

/-- Rotation invariance for the configuration of a polymer. -/
theorem CtxTw.term_rot (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) {ψ' : Site d → Spin N} {b' : Spin N}
    (hball : rotCfgL R X (pack X ψ' b') ∈ ball (refPt i₀ ν X) ρ) :
    T.term X (pack X ψ' b') = T.term X (rotCfgL R X (pack X ψ' b')) := by
  have hmem : pack X ψ' b' ∈ Tube i₀ ν ρ X := ⟨R, c.frame.orth, c.frame.bd, hball⟩
  exact (c.hyp.rot_inv X hX _ hmem R c.frame.orth c.frame.bd
    (ball_subset_tube i₀ ν ρ X hball)).symm

theorem CtxTw.small_case (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
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

/-- Bound for the first-order term `A_X`. -/
theorem CtxTw.A_le (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖(1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
      (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      X.card * (E₀ * Real.exp (-κ * T.dist X) / ρ * (σ ^ 2 * ε)) := by
  have hok := c.termOK hX
  have hM := c.hM hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hρ := c.ρpos
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcρ : 0 ≤ M / ρ := by positivity
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      (Fintype.card ↥X : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε))) := by
    refine norm_sum_le_card _ fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hok.norm_tensA_le hM x) (c.ga_le x.1) (norm_nonneg _) hcρ
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2, hcard] at *
  calc 1 / 2 * ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖
      ≤ 1 / 2 * ((X.card : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε)))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

/-- Bound for the quadratic term `L_X`. -/
theorem CtxTw.Lq_le (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖(1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X) / ρ ^ 2) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) := by
  have hok := c.termOK hX
  have hM := c.hM hX
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hρ := c.ρpos
  have hσ := c.σpos
  have hε := c.εpos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcρ2 : 0 ≤ 4 * M / ρ ^ 2 := by positivity
  have hGm : ∀ μ μ', ‖gradTensor i₀ R ψ μ μ'‖ ≤ N * (N * 40 * (σ * ε)) ^ 2 := by
    intro μ μ'
    have hφ : ∀ ν', ‖rotDiff R ψ (eU ν')‖ ≤ N * 40 * (σ * ε) := fun ν' => by
      have := c.rotDiff_le (eU ν')
      rwa [l1_eU, Nat.cast_one, one_mul] at this
    refine (norm_dotT_le i₀ _ _).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hφ μ) (hφ μ') (norm_nonneg _) (by positivity)) hN
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤ (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * M / ρ ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)))) := by
    refine norm_sum_le_card _ fun x => ?_
    refine norm_sum_le_card _ fun x' => ?_
    rw [norm_mul]
    refine mul_le_mul (hok.norm_D2_basis_le hM _ _) ?_ (norm_nonneg _) (by positivity)
    refine (norm_wquad_le _ hGm x.1 x'.1).trans ?_
    have hl : (l1 (x.1 - x'.1) : ℝ) ≤ 2 * (A * t) := by
      have := l1_sub_le x.1 x'.1
      have h3 : (l1 (x.1 - x'.1) : ℝ) ≤ l1 x.1 + l1 x'.1 := by exact_mod_cast this
      have h4 := c.l1_le hX x.2
      have h5 := c.l1_le hX x'.2
      simp only [ht] at *
      linarith
    have hl0 : (0 : ℝ) ≤ l1 (x.1 - x'.1) := Nat.cast_nonneg _
    have : 0 ≤ (N : ℝ) * (N * 40 * (σ * ε)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 hl 2) this
  have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [h2, hcard] at *
  calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        wquad (gradTensor i₀ R ψ) x.1 x'.1‖
      ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) *
        (4 * M / ρ ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2))))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := by ring

theorem CtxTw.tail_case (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
        - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x *
            (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
        + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
            wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤
      tailBnd N A (E₀ * Real.exp (-κ * T.dist X)) ρ σ ε (1 + T.dist X) X.card := by
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  set t : ℝ := 1 + T.dist X with ht
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hρ := c.ρpos
  have a1 : ‖T.term X (pack X ψ b)‖ ≤ M := c.hyp.bdd_dom X hX (ψ, b) c.dat.mem
  have a2 : ‖T.term X (pack X (fun _ => ψ 0) b)‖ ≤ M :=
    c.hyp.bdd_dom X hX ((fun _ => ψ 0), b) c.dat.mem_const
  have a3 := c.A_le hX
  have a4 := c.Lq_le hX
  have tri : ∀ a b c e : ℂ, ‖a - b - c + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ := by
    intro a b c e
    have h1 := norm_add_le (a - b - c) e
    have h2 := norm_sub_le (a - b) c
    have h3 := norm_sub_le a b
    linarith
  refine (tri _ _ _ _).trans ?_
  unfold tailBnd
  have e : (X.card : ℝ) * (M / ρ * (σ ^ 2 * ε)) + (X.card : ℝ) ^ 2 * (M / ρ ^ 2) *
      ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)) =
      M * ((X.card : ℝ) * (σ ^ 2 * ε / ρ) + 6400 * N ^ 3 * A ^ 2 * (X.card : ℝ) ^ 2 * t ^ 2 *
        (σ * ε / ρ) ^ 2) := by
    field_simp
    ring
  linarith [a1, a2, a3, a4, e]

theorem CtxTw.card_pos (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {X : Finset (Site d)}
    (hX : X ∈ T.polys) : 1 ≤ X.card :=
  Finset.card_pos.mpr ⟨0, c.hyp.zero_mem X hX⟩

/-- The expansion of the term at the constant configuration around the reference point. -/
theorem CtxTw.potential_term (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (hZ0 : sZ0 N σ ε ≤ ρ / 2) :
    ‖T.term X (pack X (fun _ => ψ 0) b) - T.term X (refPt i₀ ν X) -
        ((∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
          ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
            fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1))‖ ≤
      2 * (E₀ * Real.exp (-κ * T.dist X)) * (sZ0 N σ ε / ρ) ^ 2 := by
  have hok := c.termOK hX
  have hM := c.hM hX
  have hzc : ‖zcfg X i₀ ν ψ b R‖ ≤ sZ0 N σ ε := by unfold sZ0 cC1; exact c.zc_le X
  have hball : rotCfgL R X (pack X (fun _ => ψ 0) b) ∈ ball (refPt i₀ ν X) ρ := by
    rw [rotCfgL_pack, pack_const_rot_eq, mem_ball, dist_eq_norm, add_sub_cancel_left]
    have := c.ρpos; linarith
  rw [c.term_rot hX hball, rotCfgL_pack, pack_const_rot_eq]
  have h := taylor_first c.ρpos hok.analytic_ball hM (z := zcfg X i₀ ν ψ b R) (hzc.trans hZ0)
  have hlin : fderiv ℂ (T.term X) (refPt i₀ ν X) (zcfg X i₀ ν ψ b R) =
      (∑ x : ↥X, tensA i₀ ν X (T.term X) x) * ((R.mulVec (ψ 0) - Pi.single i₀ 1 : Spin N) i₀) +
        ((R.mulVec b - (ν : ℂ) • Pi.single i₀ 1 : Spin N) i₀) *
          fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1) := by
    unfold zcfg
    rw [hok.lin_pack_b, Finset.sum_mul]
  rw [hlin] at h
  refine h.trans ?_
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  have : (‖zcfg X i₀ ν ψ b R‖ / ρ) ^ 2 ≤ (sZ0 N σ ε / ρ) ^ 2 :=
    pow_le_pow_left₀ (by positivity [c.ρpos]) (div_le_div_of_nonneg_right hzc c.ρpos.le) 2
  nlinarith

/-- The per-term bound of the landed `Ctx.dlt_bound` before the polynomial weights are absorbed:
`‖Dlt X‖ ≤ (C_s + C_t) · E₀ e^{-κ d_j(X)} |X|² (1 + d_j(X))⁶ · σ^{3-α₁} (ε/ρ)²`. -/
theorem CtxTw.dlt_bound_raw (c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R)
    {Λ Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBnd N A M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cC1 N + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hεΛ : ε ≤ Λ * ρ) (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      (Cs + Ct) * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  have hρ := c.ρpos
  have hεpos := c.εpos
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  set r : ℝ := ε / ρ with hr
  have hr0 : 0 < r := by positivity
  have hrε : ε = r * ρ := by rw [hr]; field_simp
  have hrΛ : r ≤ Λ := by rw [hr, div_le_iff₀ hρ]; linarith
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hT0 : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos c.σpos _).le
  have hfin : ∀ C : ℝ, 0 ≤ C → C ≤ Cs + Ct → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * r ^ 2) →
      ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ (Cs + Ct) * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) *
        (σ ^ (3 - α₁) * r ^ 2) := by
    intro C hC hle h
    refine h.trans ?_
    have hw : 0 ≤ M * ((X.card : ℝ) ^ 2 * t ^ 6) :=
      mul_nonneg hM0 (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 6))
    have : 0 ≤ σ ^ (3 - α₁) * r ^ 2 := mul_nonneg hT0 (sq_nonneg r)
    calc C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * r ^ 2)
        = C * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) * (σ ^ (3 - α₁) * r ^ 2) := by ring
      _ ≤ (Cs + Ct) * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) * (σ ^ (3 - α₁) * r ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hw) this
  by_cases hsm : (cC1 N + cK1 N A) * t * σ * ε ≤ ρ / 2
  · have h1 := c.small_case hX hsm
    have h2 := hCs M ρ ν σ r K₂ t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hρ c.ρle hr0 hrΛ
      c.ν0 c.νσ ht1 hP c.dat.K2_nonneg (by rw [← hrε]; exact hK) hS
    rw [← hrε] at h2
    exact hfin Cs hCs0 (by linarith) (h1.trans h2)
  · have h1 := c.tail_case hX
    have hlt : 1 < 2 * (cC1 N + cK1 N A) * t * σ * r := by
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_right hcon hρ.le
      rw [hrε] at hsm
      nlinarith
    have h2 := hCt M ρ σ r t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hρ hr0 hrΛ ht1 hP hlt hS
    rw [← hrε] at h2
    exact hfin Ct hCt0 (by linarith) (h1.trans h2)

end CtxTw

end Balaban.SmallField
