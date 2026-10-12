/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Covariance
public import Balaban.Localization.DecoupledCovAnalyticFull

/-!
# Complex data near real data: the analytic path and its domain (Lemma 2.4 (a))

For a real datum `(α₀, φ₀)` and a complex datum `(α, φ)` close to it, the affine path
`t ↦ (α₀ + t (α - α₀), φ₀ + t (φ - φ₀))`:

* `fieldPath_isConstraintField`: for `‖t‖ ε ≤ m` the path field stays in the constraint-field class
  `IsConstraintField G δ₁`, when `φ - φ₀` is `ε`-smooth and `ε`-small;
* `rectAt_decCov_weak`: the entries of `C_x(1)` are analytic in `(φ, α)` at every datum satisfying
  the pointwise I-4c premises (the form of `rectAt_decCov_full` without the open-domain strictness).
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Finset Matrix

namespace Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}

theorem extS_one : extS G (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext P; unfold extS; split_ifs <;> rfl

section Cov
variable {x : ℝ} {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ}

/-- Weak form of `rectAt_decCov_full`: only the three pointwise conditions at `e`. -/
theorem rectAt_decCov_weak (S : XSetting G a aT ν) (hx : 0 ≤ x)
    (hM : cstarX d L * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) {e : DecData G N}
    (hα : AdmPot G e.2.2) (hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp 0)
    (hφ : IsConstraintField G δ e.2.1) :
    RectAt (fun p : DecData G N => decCov G a aT x ν p.2.2 (extS G p.1) p.2.1 Q P) e := by
  have D : XData G a aT ν x e.2.2 0 (extS G e.1) := ⟨S, hα, hx, le_rfl, hM, hs⟩
  have hpr : AnalyticAt ℂ (fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ))) e :=
    AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
  have hHx : RectAt (fun p : DecData G N => xDirichletOperator G a aT x ν p.2.2) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (rectAt_xDirichlet (G := G) a aT x ν ((e.1, e.2.2) : DecParams G × (G.Ω 1 → ℂ))) hpr
  have hGs : RectAt (fun p : DecData G N => Gsx G a aT x ν p.2.2 (extS G p.1)) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (matAt_Gsx S hx hα D.isUnit_one_sub) hpr
  have hGl := hGs.liftOp (N := N)
  have hHl := hHx.liftOp (N := N)
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hK : RectAt (fun p : DecData G N =>
      commK (xDirichletOperator G a aT x ν p.2.2) (restrictField G p.2.1)) e := by
    unfold commK
    exact (hF.transpose'.mul hHl).sub (hHx.mul hF.transpose')
  have hMa : RectAt (fun p : DecData G N =>
      decM G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decM constraintM
    exact (hF.transpose'.mul hF).sub ((hK.mul hGl).mul hF)
  have hNa : RectAt (fun p : DecData G N =>
      decN G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decN constraintN
    exact hF.transpose'.sub (hK.mul hGl)
  have hdet : (decM G a aT x ν e.2.2 (extS G e.1) e.2.1).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (decM_isUnit D hφ hδ hsm)).ne_zero
  have hMi := hMa.inv hdet
  have hPi : RectAt (fun p : DecData G N =>
      decPi G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decPi
    exact (((hGl.mul hF).mul hMi).mul hNa)
  unfold decCov
  have hA := RectAt.const (E := DecData G N)
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) e
  refine hA.add (RectAt.smul_const _ ?_)
  exact (((hA.mul (RectAt.const _ e)).mul (hGl.sub hPi)).mul (RectAt.const _ e)).mul hA

end Cov

section Field

theorem vn_smul (c : ℂ) (v : Fin N → ℂ) : vn (c • v) = ‖c‖ * vn v := by
  unfold vn
  rw [← norm_smul]
  rfl

theorem vn_add_smul_le (u w : Fin N → ℂ) (t : ℂ) : vn (u + t • w) ≤ vn u + ‖t‖ * vn w := by
  refine (vn_add _ _).trans ?_
  rw [vn_smul]

/-- The field path `φ₀ + t (φ - φ₀)`. -/
def fieldPath {X : Type*} (φ0 φ : X → Fin N → ℂ) (t : ℂ) : X → Fin N → ℂ :=
  fun y => φ0 y + t • (φ y - φ0 y)

theorem vn_real_le {v : Fin N → ℂ} (hr : ∀ i, star (v i) = v i) {δ : ℝ}
    (h : ‖∑ i, v i * v i - 1‖ ≤ δ) : vn v ≤ 1 + δ := by
  have h1 : vn v ^ 2 = (∑ i, v i * v i).re := by
    rw [vn_sq, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have him : (v i).im = 0 := by
      have := congrArg Complex.im (hr i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, him]
    ring
  have h2 : (∑ i, v i * v i).re ≤ 1 + δ := by
    have h3 : |(∑ i, v i * v i - 1).re| ≤ δ := (Complex.abs_re_le_norm _).trans h
    have h4 := (abs_le.1 h3).2
    simp only [Complex.sub_re, Complex.one_re] at h4
    linarith
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h
  have h5 : vn v ^ 2 ≤ (1 + δ) ^ 2 := by
    rw [h1]
    have : 0 ≤ (∑ i, v i * v i).re := by rw [← h1]; positivity
    nlinarith
  exact abs_le_of_sq_le_sq' h5 (by linarith) |>.2


theorem fieldPath_isConstraintField {φ0 φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {δ δ1 ε m : ℝ} {t : ℂ}
    (h0 : IsConstraintField G δ φ0) (hr : ∀ y i, star (φ0 y i) = φ0 y i)
    (hs : IsSmoothField G ε (φ - φ0)) (hp : ∀ x ∈ G.Ω 1, vn ((φ - φ0) x) ≤ ε)
    (hε : 0 ≤ ε) (ht : ‖t‖ * ε ≤ m) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ1 / 2) (hm : m ≤ δ1 / 8) (hδ1 : δ1 ≤ 1 / 6) :
    IsConstraintField G δ1 (fieldPath φ0 φ t) := by
  have hsp : ∀ x : CTorus d L N₁ m₁ (k + 1), 0 < G.spacing x := fun x => spacing_pos G
  have hδ1' : 0 ≤ δ1 := by linarith
  have hm0 : 0 ≤ m := (mul_nonneg (norm_nonneg t) hε).trans ht
  have hdm : δ + m ≤ δ1 := by linarith
  have hdiff : ∀ y z, fieldPath φ0 φ t y - fieldPath φ0 φ t z =
      (φ0 y - φ0 z) + t • ((φ - φ0) y - (φ - φ0) z) := by
    intro y z; funext i; simp only [fieldPath, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hbd : ∀ {u w : Fin N → ℂ} {A B c : ℝ}, vn u ≤ A * c → vn w ≤ B * c → 0 ≤ c →
      ‖t‖ * B ≤ m → vn (u + t • w) ≤ (A + m) * c := by
    intro u w A B c hu hw hc htB
    refine (vn_add_smul_le u w t).trans ?_
    have : ‖t‖ * vn w ≤ ‖t‖ * (B * c) := mul_le_mul_of_nonneg_left hw (norm_nonneg t)
    nlinarith
  refine ⟨⟨fun x hx μ => ?_, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · have g0 := h0.grad x hx μ
    have g1 := hs.grad x hx μ
    have c0 : 0 < (G.spacing x)⁻¹ := inv_pos.2 (hsp x)
    rw [hdiff, hdiff]
    have e1 : ∀ r : ℝ, r / G.spacing x = r * (G.spacing x)⁻¹ := fun r => div_eq_mul_inv _ _
    refine ⟨?_, ?_⟩
    · have := hbd (u := φ0 (x + Pi.single μ 1) - φ0 x) (w := (φ - φ0) (x + Pi.single μ 1) - (φ - φ0) x)
        (A := δ) (B := ε) (c := (G.spacing x)⁻¹) (by rw [← e1]; exact g0.1) (by rw [← e1]; exact g1.1)
        c0.le ht
      calc _ ≤ _ := this
        _ ≤ δ1 / G.spacing x := by rw [e1]; exact mul_le_mul_of_nonneg_right hdm c0.le
    · have := hbd (u := φ0 (x - Pi.single μ 1) - φ0 x) (w := (φ - φ0) (x - Pi.single μ 1) - (φ - φ0) x)
        (A := δ) (B := ε) (c := (G.spacing x)⁻¹) (by rw [← e1]; exact g0.2) (by rw [← e1]; exact g1.2)
        c0.le ht
      calc _ ≤ _ := this
        _ ≤ δ1 / G.spacing x := by rw [e1]; exact mul_le_mul_of_nonneg_right hdm c0.le
  · have g0 := h0.lap x hx
    have g1 := hs.lap x hx
    have c0 : 0 < (G.spacing x ^ 2)⁻¹ := inv_pos.2 (pow_pos (hsp x) 2)
    have e1 : ∀ r : ℝ, r / G.spacing x ^ 2 = r * (G.spacing x ^ 2)⁻¹ := fun r => div_eq_mul_inv _ _
    have hl : (fun i => ∑ μ : Fin d, (fieldPath φ0 φ t (x + Pi.single μ 1) i +
        fieldPath φ0 φ t (x - Pi.single μ 1) i - 2 * fieldPath φ0 φ t x i)) =
        (fun i => ∑ μ : Fin d, (φ0 (x + Pi.single μ 1) i + φ0 (x - Pi.single μ 1) i - 2 * φ0 x i)) +
          t • (fun i => ∑ μ : Fin d, ((φ - φ0) (x + Pi.single μ 1) i +
            (φ - φ0) (x - Pi.single μ 1) i - 2 * (φ - φ0) x i)) := by
      funext i
      simp only [fieldPath, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      ring
    rw [hl]
    have := hbd (c := (G.spacing x ^ 2)⁻¹) (A := δ) (B := ε) (by rw [← e1]; exact g0)
      (by rw [← e1]; exact g1) c0.le ht
    calc _ ≤ _ := this
      _ ≤ δ1 / G.spacing x ^ 2 := by rw [e1]; exact mul_le_mul_of_nonneg_right hdm c0.le
  · -- bound
    have hv0 : vn (φ0 x) ≤ 1 + δ := vn_real_le (hr x) (by simpa using h0.sq x hx)
    have : fieldPath φ0 φ t x = φ0 x + t • (φ - φ0) x := rfl
    rw [this]
    refine (vn_add_smul_le _ _ t).trans ?_
    have := mul_le_mul_of_nonneg_left (hp x hx) (norm_nonneg t)
    linarith
  · -- sq
    have hv0 : vn (φ0 x) ≤ 1 + δ := vn_real_le (hr x) (by simpa using h0.sq x hx)
    set ψ := (φ - φ0) x with hψ
    have hψn : ‖t‖ * vn ψ ≤ m := (mul_le_mul_of_nonneg_left (hp x hx) (norm_nonneg t)).trans ht
    have e : ∑ i, fieldPath φ0 φ t x i * fieldPath φ0 φ t x i - 1 =
        (∑ i, φ0 x i * φ0 x i - 1) + 2 * t * ∑ i, φ0 x i * ψ i + t ^ 2 * ∑ i, ψ i * ψ i := by
      have hi : ∀ i, fieldPath φ0 φ t x i * fieldPath φ0 φ t x i =
          φ0 x i * φ0 x i + 2 * t * (φ0 x i * ψ i) + t ^ 2 * (ψ i * ψ i) := by
        intro i
        simp only [fieldPath, hψ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp_rw [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [e]
    have c1 : ‖∑ i, φ0 x i * φ0 x i - 1‖ ≤ δ := by simpa using h0.sq x hx
    have c2 : ‖∑ i, φ0 x i * ψ i‖ ≤ vn (φ0 x) * vn ψ := norm_dot_le _ _
    have c3 : ‖∑ i, ψ i * ψ i‖ ≤ vn ψ * vn ψ := norm_dot_le _ _
    have n3 : ‖t‖ * vn ψ ≤ m := hψn
    have n4 : 0 ≤ ‖t‖ * vn ψ := mul_nonneg (norm_nonneg t) (vn_nonneg ψ)
    calc _ ≤ ‖∑ i, φ0 x i * φ0 x i - 1‖ + ‖2 * t * ∑ i, φ0 x i * ψ i‖ + ‖t ^ 2 * ∑ i, ψ i * ψ i‖ :=
          (norm_add₃_le)
      _ ≤ δ + 2 * (1 + δ) * m + m * m := by
          have h2 : ‖2 * t * ∑ i, φ0 x i * ψ i‖ ≤ 2 * (1 + δ) * m := by
            rw [norm_mul, norm_mul]
            have : ‖(2 : ℂ)‖ = 2 := by simp
            rw [this]
            calc 2 * ‖t‖ * ‖∑ i, φ0 x i * ψ i‖ ≤ 2 * ‖t‖ * (vn (φ0 x) * vn ψ) := by gcongr
              _ = 2 * vn (φ0 x) * (‖t‖ * vn ψ) := by ring
              _ ≤ 2 * (1 + δ) * m := by gcongr
          have h3 : ‖t ^ 2 * ∑ i, ψ i * ψ i‖ ≤ m * m := by
            rw [norm_mul, norm_pow]
            calc ‖t‖ ^ 2 * ‖∑ i, ψ i * ψ i‖ ≤ ‖t‖ ^ 2 * (vn ψ * vn ψ) := by gcongr
              _ = (‖t‖ * vn ψ) * (‖t‖ * vn ψ) := by ring
              _ ≤ m * m := by
                have := mul_nonneg (norm_nonneg t) (vn_nonneg ψ)
                gcongr
          linarith
      _ ≤ δ1 := by nlinarith

end Field

end Balaban.Fluctuation
