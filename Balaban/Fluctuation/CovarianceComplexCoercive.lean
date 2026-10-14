/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovarianceComplexPath
public import Balaban.Analysis.MatrixResolventLimit

/-!
# Lemma 2.4 (a) for complex data (FLUCTUATION.md §2.4)

`lemma24_a_complex`: if `(α₀, φ₀)` is real data of Theorem I-4c and `(α, φ)` is complex data with
`ℓ² |α - α₀| ≤ ε`, `φ - φ₀` an `ε`-smooth field of size `≤ ε`, `ε ≤ covEps d L (a_k)`, then
`Re (a L⁻² Q*Q + Δ^{(k)}) ≥ ½ covGap`.

Proof. Along the complex line `t ↦ (α₀ + t (α - α₀), φ₀ + t (φ - φ₀))`, which stays in the I-4c
domain for `‖t‖ ε ≤ covMargin` (`path_data`), the entries of the decoupled covariance `C_x(1)` are
analytic (`analyticAt_decCov_path`) and `‖C_x(1) - A_x‖ ≤ B₄ (a_k + x)⁻²` (I-4c (ii)). The
Cauchy estimate on a disc of radius `covMargin / ε` gives
`|⟨v, (C_x(α, φ) - C_x(α₀, φ₀)) v⟩| ≤ 2 ε / covMargin · B₄ (a_k + x)⁻² ‖v‖²`
(`decCov_path_diff_le`). Since `C_x(1) = (x + 𝒜)⁻¹`, letting `x → ∞`
(`norm_quad_sub_le_of_resolvent`) gives `|⟨v, (𝒜 - 𝒜₀) v⟩| ≤ 2 ε B₄ / covMargin ‖v‖²`, and the
real data coercivity `lemma24_a` is perturbed.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Finset Matrix

namespace Balaban.Fluctuation

/-- The constraint-field parameter of the complex-data neighbourhood: `δ₁ = 1/(2(c+1))`,
`c = smallConstX d L 0`, so that `δ₁² c ≤ 1/4`. -/
noncomputable def covDelta (d L : ℕ) : ℝ := (2 * (smallConstX d L 0 + 1))⁻¹

theorem covDelta_pos (d L : ℕ) : 0 < covDelta d L := by
  unfold covDelta; have := smallConstX_pos d L 0; positivity

theorem covDelta_le (d L : ℕ) : covDelta d L ≤ 1 / 6 := by
  have h : 2 ≤ smallConstX d L 0 := by
    unfold smallConstX; have := kConstX_nonneg d L 0; linarith
  unfold covDelta
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

theorem covDelta_sq_mul_le (d L : ℕ) : covDelta d L ^ 2 * smallConstX d L 0 ≤ 1 / 4 := by
  have hc := smallConstX_pos d L 0
  unfold covDelta
  rw [inv_pow, mul_comm, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (smallConstX d L 0)]


/-- The margin of the complex-data neighbourhood (in the units of `ε`). -/
noncomputable def covMargin (d L : ℕ) : ℝ := min (coerciveConst d / 4) (covDelta d L / 8)

theorem covMargin_pos {d : ℕ} (L : ℕ) (hd : 0 < d) : 0 < covMargin d L := by
  unfold covMargin
  exact lt_min (by have := coerciveConst_pos hd; positivity) (by have := covDelta_pos d L; positivity)

theorem covMargin_le_left (d L : ℕ) : covMargin d L ≤ coerciveConst d / 4 := min_le_left _ _
theorem covMargin_le_right (d L : ℕ) : covMargin d L ≤ covDelta d L / 8 := min_le_right _ _

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}

/-- The potential path `α₀ + t (α - α₀)`. -/
def alphaPath (α0 α : G.Ω 1 → ℂ) (t : ℂ) : G.Ω 1 → ℂ := fun w => α0 w + t * (α w - α0 w)

theorem admPot_alphaPath {α0 α : G.Ω 1 → ℂ} {ε : ℝ} {t : ℂ}
    (hmarg : ∀ w, ‖α0 w‖ ≤ coerciveConst d / (4 * G.spacing w ^ 2))
    (hαc : ∀ w, ‖α w - α0 w‖ ≤ ε / G.spacing w ^ 2)
    (ht : ‖t‖ * ε ≤ covMargin d L) : AdmPot G (alphaPath α0 α t) := by
  intro w
  have hsp : 0 < G.spacing (w : CTorus d L N₁ m₁ (k + 1)) := spacing_pos G
  have h1 := hmarg w
  have h2 : ‖t * (α w - α0 w)‖ ≤ ‖t‖ * ε / G.spacing (w : CTorus d L N₁ m₁ (k + 1)) ^ 2 := by
    rw [norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hαc w) (norm_nonneg t)
  have h3 : ‖t‖ * ε / G.spacing (w : CTorus d L N₁ m₁ (k + 1)) ^ 2 ≤
      covMargin d L / G.spacing (w : CTorus d L N₁ m₁ (k + 1)) ^ 2 :=
    div_le_div_of_nonneg_right ht (by positivity)
  have h4 := covMargin_le_left d L
  calc ‖alphaPath α0 α t w‖ ≤ ‖α0 w‖ + ‖t * (α w - α0 w)‖ := norm_add_le _ _
    _ ≤ coerciveConst d / (4 * G.spacing w ^ 2) + covMargin d L / G.spacing w ^ 2 := by linarith
    _ ≤ coerciveConst d / (2 * G.spacing w ^ 2) := by
        have e1 : coerciveConst d / (4 * G.spacing w ^ 2) = (coerciveConst d / 4) / G.spacing w ^ 2 := by
          field_simp
        have e2 : coerciveConst d / (2 * G.spacing w ^ 2) = (coerciveConst d / 2) / G.spacing w ^ 2 := by
          field_simp
        rw [e1, e2, ← add_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)


theorem sqNorm_dot_le {ι : Type*} [Fintype ι] (v w : ι → ℂ) :
    ‖star v ⬝ᵥ w‖ ≤ Real.sqrt (Green.sqNorm v) * Real.sqrt (Green.sqNorm w) := by
  unfold dotProduct Green.sqNorm
  calc ‖∑ i, star v i * w i‖ ≤ ∑ i, ‖star v i * w i‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖w i‖ := Finset.sum_congr rfl fun i _ => by simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

section Lip

variable {α0 α : G.Ω 1 → ℂ} {φ0 φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {δ ε : ℝ}

theorem path_data
    (hfam0 : ∀ x, 0 ≤ x → XData G a aT ν x α0 0 (fun _ => 1))
    (hφ0 : IsConstraintField G δ φ0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ covDelta d L / 2)
    (hφ0r : ∀ y i, star (φ0 y i) = φ0 y i)
    (hmarg : ∀ w, ‖α0 w‖ ≤ coerciveConst d / (4 * G.spacing w ^ 2))
    (hαc : ∀ w, ‖α w - α0 w‖ ≤ ε / G.spacing w ^ 2) (hε : 0 ≤ ε)
    (hφs : IsSmoothField G ε (φ - φ0)) (hφp : ∀ x ∈ G.Ω 1, vn ((φ - φ0) x) ≤ ε)
    {t : ℂ} (ht : ‖t‖ * ε ≤ covMargin d L) :
    (∀ x, 0 ≤ x → XData G a aT ν x (alphaPath α0 α t) 0 (fun _ => 1)) ∧
      IsConstraintField G (covDelta d L) (fieldPath φ0 φ t) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have D := hfam0 x hx
    exact ⟨D.st, admPot_alphaPath hmarg hαc ht, hx, le_rfl, D.big, fun P => by simp⟩
  · exact fieldPath_isConstraintField hφ0 hφ0r hφs hφp hε ht hδ0 hδ (covMargin_le_right d L)
      (covDelta_le d L)


theorem analyticAt_decCov_path
    (hfam0 : ∀ x, 0 ≤ x → XData G a aT ν x α0 0 (fun _ => 1))
    (hφ0 : IsConstraintField G δ φ0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ covDelta d L / 2)
    (hφ0r : ∀ y i, star (φ0 y i) = φ0 y i)
    (hmarg : ∀ w, ‖α0 w‖ ≤ coerciveConst d / (4 * G.spacing w ^ 2))
    (hαc : ∀ w, ‖α w - α0 w‖ ≤ ε / G.spacing w ^ 2) (hε : 0 ≤ ε)
    (hφs : IsSmoothField G ε (φ - φ0)) (hφp : ∀ x ∈ G.Ω 1, vn ((φ - φ0) x) ≤ ε)
    {t : ℂ} (ht : ‖t‖ * ε ≤ covMargin d L) {x : ℝ} (hx : 0 ≤ x) (v : unitPts G × Fin N → ℂ) :
    AnalyticAt ℂ (fun t' : ℂ => star v ⬝ᵥ
      ((decCov G a aT x ν (alphaPath α0 α t') (fun _ => 1) (fieldPath φ0 φ t')
        (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ v)) t := by
  obtain ⟨hfam, hφt⟩ := path_data hfam0 hφ0 hδ0 hδ hφ0r hmarg hαc hε hφs hφp ht
  have D0 := hfam0 0 le_rfl
  set e : DecData G N := ((fun _ => (1 : ℂ)), (fieldPath φ0 φ t, alphaPath α0 α t)) with he
  have hR := rectAt_decCov_weak (N := N) (Q := unitQ G) (P := unitP G) D0.st hx D0.big
    (covDelta_pos d L).le (covDelta_sq_mul_le d L) (e := e)
    (fun w => (hfam x hx).pot w) (fun P => by simp [he, extS_one]) hφt
  let f : ℂ → DecData G N := fun t' => ((fun _ => (1 : ℂ)), (fieldPath φ0 φ t', alphaPath α0 α t'))
  have hf : AnalyticAt ℂ f t := by
    refine analyticAt_const.prod (AnalyticAt.prod ?_ ?_)
    · have : fieldPath φ0 φ = fun t' => φ0 + t' • (φ - φ0) := by
        funext t' y; rfl
      rw [this]
      exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    · have : alphaPath α0 α = fun t' => α0 + t' • (α - α0) := by
        funext t' y; rfl
      rw [this]
      exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hC := RectAt.comp' (f := f) hR hf
  have hC' : RectAt (fun t' : ℂ => decCov G a aT x ν (alphaPath α0 α t') (fun _ => 1)
      (fieldPath φ0 φ t') (unitQ G) (unitP G)) t := by
    intro i j
    have := hC i j
    simp only [f, extS_one] at this
    exact this
  have hD : RectAt (fun t' : ℂ => decCov G a aT x ν (alphaPath α0 α t') (fun _ => 1)
      (fieldPath φ0 φ t') (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) t :=
    hC'.sub (RectAt.const _ t)
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  refine analyticAt_const.mul ?_
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact (hD i j).mul analyticAt_const


theorem decCov_path_diff_le
    (hfam0 : ∀ x, 0 ≤ x → XData G a aT ν x α0 0 (fun _ => 1))
    (hφ0 : IsConstraintField G δ φ0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ covDelta d L / 2)
    (hφ0r : ∀ y i, star (φ0 y i) = φ0 y i)
    (hmarg : ∀ w, ‖α0 w‖ ≤ coerciveConst d / (4 * G.spacing w ^ 2))
    (hαc : ∀ w, ‖α w - α0 w‖ ≤ ε / G.spacing w ^ 2) (hε : 0 < ε)
    (hεm : ε ≤ covMargin d L / 2)
    (hφs : IsSmoothField G ε (φ - φ0)) (hφp : ∀ x ∈ G.Ω 1, vn ((φ - φ0) x) ≤ ε)
    {x : ℝ} (hx : 0 ≤ x) (v : unitPts G × Fin N → ℂ) :
    ‖star v ⬝ᵥ ((decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) -
        decCov G a aT x ν α0 (fun _ => 1) φ0 (unitQ G) (unitP G)) *ᵥ v)‖ ≤
      2 * ε / covMargin d L *
        (covB4 d L (a k) 0 * ((a k + x)⁻¹) ^ 2 * Green.sqNorm v) := by
  have D0 := hfam0 0 le_rfl
  have hd : 0 < d := by have := D0.st.dg.hd; omega
  have hm := covMargin_pos L hd
  set m := covMargin d L with hmdef
  set Aop := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) with hA
  set g : ℂ → ℂ := fun t' => star v ⬝ᵥ
      ((decCov G a aT x ν (alphaPath α0 α t') (fun _ => 1) (fieldPath φ0 φ t')
        (unitQ G) (unitP G) - Aop) *ᵥ v) with hg
  set R : ℝ := m / (2 * ε) with hR
  have hRpos : 0 < R := by positivity
  have h2R : 2 * R = m / ε := by rw [hR]; field_simp
  have hball : ∀ t ∈ Metric.ball (0 : ℂ) (2 * R), ‖t‖ * ε ≤ m := by
    intro t ht
    rw [mem_ball_zero_iff, h2R, lt_div_iff₀ hε] at ht
    exact ht.le
  have hana : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) (2 * R)) := fun t ht =>
    analyticAt_decCov_path hfam0 hφ0 hδ0 hδ hφ0r hmarg hαc hε.le hφs hφp (hball t ht) hx v
  set M : ℝ := covB4 d L (a k) 0 * ((a k + x)⁻¹) ^ 2 * Green.sqNorm v with hM
  have hak : 0 < a k + x := by
    have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)
    have := this.1
    linarith
  have hbd : ∀ t ∈ Metric.ball (0 : ℂ) (2 * R), ‖g t‖ ≤ M := by
    intro t ht
    obtain ⟨hfam, hφt⟩ := path_data hfam0 hφ0 hδ0 hδ hφ0r hmarg hαc hε.le hφs hφp (hball t ht)
    have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
    have h1 := decCov_sub_le (hfam x hx) hφt (covDelta_pos d L).le (covDelta_sq_mul_le d L) hU v
    refine (sqNorm_dot_le v _).trans ?_
    have hc : 0 ≤ covBsq d L (a k) 0 := covBsq_nonneg d L (a k) 0
    have hinv : 0 ≤ (a k + x)⁻¹ := inv_nonneg.2 hak.le
    have h2 : Real.sqrt (Green.sqNorm ((decCov G a aT x ν (alphaPath α0 α t) (fun _ => 1)
        (fieldPath φ0 φ t) (unitQ G) (unitP G) - Aop) *ᵥ v)) ≤
        covB4 d L (a k) 0 * ((a k + x)⁻¹) ^ 2 * Real.sqrt (Green.sqNorm v) := by
      refine (Real.sqrt_le_sqrt h1).trans_eq ?_
      rw [Real.sqrt_mul (mul_nonneg hc (by positivity)), Real.sqrt_mul hc,
        show ((a k + x)⁻¹) ^ 4 = (((a k + x)⁻¹) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      rfl
    calc Real.sqrt (Green.sqNorm v) * _ ≤ Real.sqrt (Green.sqNorm v) *
          (covB4 d L (a k) 0 * ((a k + x)⁻¹) ^ 2 * Real.sqrt (Green.sqNorm v)) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = M := by
          rw [hM]
          have := Real.mul_self_sqrt (Green.sqNorm_nonneg v)
          calc _ = covB4 d L (a k) 0 * ((a k + x)⁻¹) ^ 2 *
                (Real.sqrt (Green.sqNorm v) * Real.sqrt (Green.sqNorm v)) := by ring
            _ = _ := by rw [this]
  have h01 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff, norm_one, hR, le_div_iff₀ (by positivity)]
    linarith
  have h00 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall_self hRpos.le
  have hL := lipschitz_of_analytic_ball hRpos hana hbd h01 h00
  have e1 : g 1 - g 0 = star v ⬝ᵥ ((decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) -
        decCov G a aT x ν α0 (fun _ => 1) φ0 (unitQ G) (unitP G)) *ᵥ v) := by
    have a1 : alphaPath α0 α 1 = α := by funext w; simp [alphaPath]
    have a0 : alphaPath α0 α 0 = α0 := by funext w; simp [alphaPath]
    have f1 : fieldPath φ0 φ 1 = φ := by funext y; simp [fieldPath]
    have f0 : fieldPath φ0 φ 0 = φ0 := by funext y; simp [fieldPath]
    simp only [hg, a1, a0, f1, f0, ← dotProduct_sub, ← Matrix.sub_mulVec]
    congr 2
    abel
  rw [← e1]
  refine hL.trans ?_
  rw [sub_zero, norm_one, mul_one, hR]
  have : M / (m / (2 * ε)) = 2 * ε / m * M := by field_simp
  rw [this]


end Lip

/-- The size `ε_*(d, L, a_k)` of the complex-data neighbourhood of Lemma 2.4 (a). -/
noncomputable def covEps (d L : ℕ) (ak : ℝ) : ℝ :=
  min (covMargin d L / 2) (covGap d L ak * covMargin d L / (4 * (covB4 d L ak 0 + 1)))

theorem covEps_pos {d : ℕ} (L : ℕ) (hd : 0 < d) {ak : ℝ} (hak : 0 < ak) : 0 < covEps d L ak := by
  have hm := covMargin_pos L hd
  have hB := covB4_nonneg d L ak 0
  have hgap : 0 < covGap d L ak := by
    unfold covGap
    have : 0 < ak⁻¹ + covB4 d L ak 0 * (ak⁻¹) ^ 2 := by positivity
    exact inv_pos.2 this
  unfold covEps
  exact lt_min (by positivity) (by positivity)

section Main

variable {α0 α : G.Ω 1 → ℂ} {φ0 φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {δ ε : ℝ}

/-- **Lemma 2.4 (a) for complex data.** Let `(α₀, φ₀)` be real data of Theorem I-4c (in the half
domain `|α₀| ≤ γ₁/2`, with constraint parameter `δ ≤ δ₁/2`), and let `(α, φ)` be complex data with
`ℓ² |α - α₀| ≤ ε`, `φ - φ₀` an `ε`-smooth field with `|φ - φ₀| ≤ ε`, where `ε ≤ ε_*(d, L, a_k)`.
Then `Re (a L⁻² Q*Q + Δ^{(k)}) ≥ ½ covGap`. -/
theorem lemma24_a_complex
    (hfam0 : ∀ x, 0 ≤ x → XData G a aT ν x α0 0 (fun _ => 1))
    (hφ0 : IsConstraintField G δ φ0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ covDelta d L / 2)
    (hα0r : ∀ w, star (α0 w) = α0 w) (hφ0r : ∀ y i, star (φ0 y i) = φ0 y i)
    (hmarg : ∀ w, ‖α0 w‖ ≤ coerciveConst d / (4 * G.spacing w ^ 2))
    (hε : 0 < ε) (hεs : ε ≤ covEps d L (a k))
    (hαc : ∀ w, ‖α w - α0 w‖ ≤ ε / G.spacing w ^ 2)
    (hφs : IsSmoothField G ε (φ - φ0)) (hφp : ∀ x ∈ G.Ω 1, vn ((φ - φ0) x) ≤ ε) :
    Green.IsCoercive (covOp G a aT ν α φ (unitQ G) (unitP G)) (covGap d L (a k) / 2) := by
  have D0 := hfam0 0 le_rfl
  have hd : 0 < d := by have := D0.st.dg.hd; omega
  have hm := covMargin_pos L hd
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)
  have hak0 : 0 < a k := by linarith [hak.1]
  have hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4 := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (smallConstX_pos d L 0).le) (covDelta_sq_mul_le d L)
    have := covDelta_pos d L
    exact pow_le_pow_left₀ hδ0 (by linarith) 2
  obtain ⟨-, hgap, hcoer⟩ := lemma24_a hfam0 hφ0 hδ0 hsm hα0r hφ0r
  have hB := covB4_nonneg d L (a k) 0
  have hεm : ε ≤ covMargin d L / 2 := hεs.trans (min_le_left _ _)
  have hεg : ε ≤ covGap d L (a k) * covMargin d L / (4 * (covB4 d L (a k) 0 + 1)) :=
    hεs.trans (min_le_right _ _)
  have ht1 : ‖(1 : ℂ)‖ * ε ≤ covMargin d L := by rw [norm_one, one_mul]; linarith
  obtain ⟨hfam1, hφ1⟩ := path_data hfam0 hφ0 hδ0 hδ hφ0r hmarg hαc hε.le hφs hφp ht1
  have a1 : alphaPath α0 α 1 = α := by funext w; simp [alphaPath]
  have f1 : fieldPath φ0 φ 1 = φ := by funext y; simp [fieldPath]
  rw [a1] at hfam1
  rw [f1] at hφ1
  have hU := isUnitLatticeB_unit (G := G)
  intro v
  set 𝒜 := covOp G a aT ν α φ (unitQ G) (unitP G) with h𝒜
  set 𝒜0 := covOp G a aT ν α0 φ0 (unitQ G) (unitP G) with h𝒜0
  set η : ℝ := 2 * ε / covMargin d L * (covB4 d L (a k) 0 * Green.sqNorm v) with hη
  have hres := norm_quad_sub_le_of_resolvent 𝒜 𝒜0 v (η := η)
    (fun x hx => (decCov_one_eq hfam1 hφ1 (covDelta_pos d L).le (covDelta_sq_mul_le d L) hU
      hx.le).1)
    (fun x hx => (decCov_one_eq hfam0 hφ0 hδ0 hsm hU hx.le).1) (by
      intro x hx
      have hx0 : 0 ≤ x := by linarith
      have e1 := (decCov_one_eq hfam1 hφ1 (covDelta_pos d L).le (covDelta_sq_mul_le d L) hU hx0).2
      have e2 := (decCov_one_eq hfam0 hφ0 hδ0 hsm hU hx0).2
      rw [← e1, ← e2]
      refine (decCov_path_diff_le hfam0 hφ0 hδ0 hδ hφ0r hmarg hαc hε hεm hφs hφp hx0 v).trans ?_
      have hxpos : 0 < x := by linarith
      have hinv : (a k + x)⁻¹ ≤ x⁻¹ := inv_anti₀ hxpos (by linarith)
      have h2 : ((a k + x)⁻¹) ^ 2 ≤ (x⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2
      have hs0 := Green.sqNorm_nonneg v
      calc 2 * ε / covMargin d L * (covB4 d L (a k) 0 * ((a k + x)⁻¹) ^ 2 * Green.sqNorm v)
          ≤ 2 * ε / covMargin d L * (covB4 d L (a k) 0 * (x⁻¹) ^ 2 * Green.sqNorm v) := by
            gcongr
        _ = η / x ^ 2 := by rw [hη]; field_simp)
  have hq : ∀ A : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ,
      Green.reQuad A v = (star v ⬝ᵥ (A *ᵥ v)).re := by
    intro A; rfl
  have h0v := hcoer v
  rw [hq] at h0v
  have hdiff : (star v ⬝ᵥ (𝒜0 *ᵥ v)).re - (star v ⬝ᵥ (𝒜 *ᵥ v)).re ≤ η := by
    have : star v ⬝ᵥ ((𝒜0 - 𝒜) *ᵥ v) = star v ⬝ᵥ (𝒜0 *ᵥ v) - star v ⬝ᵥ (𝒜 *ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    rw [this] at hres
    have := (Complex.abs_re_le_norm (star v ⬝ᵥ (𝒜0 *ᵥ v) - star v ⬝ᵥ (𝒜 *ᵥ v))).trans hres
    rw [Complex.sub_re] at this
    exact (le_abs_self _).trans this
  have hηle : η ≤ covGap d L (a k) / 2 * Green.sqNorm v := by
    have hs0 := Green.sqNorm_nonneg v
    have hk1 : 2 * ε * covB4 d L (a k) 0 / covMargin d L ≤ covGap d L (a k) / 2 := by
      rw [div_le_iff₀ hm]
      have h4 : ε * (4 * (covB4 d L (a k) 0 + 1)) ≤ covGap d L (a k) * covMargin d L := by
        rwa [le_div_iff₀ (by positivity)] at hεg
      nlinarith
    calc η = (2 * ε * covB4 d L (a k) 0 / covMargin d L) * Green.sqNorm v := by
          rw [hη]; ring
      _ ≤ _ := by gcongr
  show covGap d L (a k) / 2 * Green.sqNorm v ≤ Green.reQuad 𝒜 v
  rw [hq]
  have h1 : covGap d L (a k) * Green.sqNorm v ≤ (star v ⬝ᵥ (𝒜0 *ᵥ v)).re := h0v
  linarith

end Main

end Balaban.Fluctuation
