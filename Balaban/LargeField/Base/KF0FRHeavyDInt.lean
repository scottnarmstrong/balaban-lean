/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRHeavyD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRHeavyDInt`: the integral of one term of the expansion (route FR, (H5))

`notes/phase1/KF0-FR.md` (H5). The integral over the event of the heavy set `H` of the term `D'`
of the expansion is at most `η^{|H|} 2^{|D|} K₀^{|W'|}` (`lintegral_frDterm_le`): the Jacobian
integral of `D'` (`lintegral_jac_sites_le`, with the determinant bound `frJac_le`) and the one-site
bounds of `KF0FRHeavySite`, with the constants

* `T = 2^n e^{-p²/8}` (the Gaussian tail), `M₀ = 2^n e^{2a²}` (the Gaussian moment),
* `J₁ = (β^{-1/2} c₀)^{-(N-1)}`, `c₀ = (1 - 2d/(2d+ν)) (2d+ν)^{-1/2}` (the Jacobian of one site),
* `η ≥ 2T + 2e^{-βν/2+2G} M₀`, `η ≥ T + ε M₀`, `η ≥ (2π)^{-n/2} e^{a²}(e^{-βν/128} + e^{-βν/2+2G}) J₁ W_c`
  (a heavy site), and `(2π)^{-n/2} e^{-βν/128} J₁ W_c ≤ 1` (an ordinary site of `D'`).
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green Balaban.Polymer
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

theorem frLam_true (ε β ν G : ℝ) : frLam ε β ν G true = 1 := by simp [frLam, bandL]

theorem frLam_false (ε β ν G : ℝ) :
    frLam ε β ν G false = ε⁻¹ * Real.exp (-(β * ν / 2)) * Real.exp (2 * G) := by
  simp [frLam, bandL]

theorem frLam'_true (ε β ν G : ℝ) : frLam' ε β ν G true = Real.exp (-(β * ν / 128)) := by
  simp [frLam', bandL']

theorem frLam'_false (ε β ν G : ℝ) :
    frLam' ε β ν G false = ε⁻¹ * Real.exp (-(β * ν / 2)) * Real.exp (2 * G) := by
  simp [frLam', bandL']

/-- The Bernoulli weight of the lower sheet compensates `ε^{-1}`. -/
theorem bern_mul_frLam_false_le {ε : ℝ} (hε : 0 < ε) (β ν G : ℝ) :
    ε / (1 + ε) * (ε⁻¹ * Real.exp (-(β * ν / 2)) * Real.exp (2 * G)) ≤
      Real.exp (-(β * ν / 2) + 2 * G) := by
  rw [Real.exp_add]
  have h1 : ε / (1 + ε) * (ε⁻¹ * Real.exp (-(β * ν / 2)) * Real.exp (2 * G)) =
      (Real.exp (-(β * ν / 2)) * Real.exp (2 * G)) / (1 + ε) := by
    field_simp
  rw [h1, div_le_iff₀ (by linarith)]
  nlinarith [mul_pos (Real.exp_pos (-(β * ν / 2))) (Real.exp_pos (2 * G))]

variable {d ℓ : ℕ} [NeZero ℓ]

/-- **The Jacobian factor of a set of sites**: `det (β^{-1/2} C_R)_{D'D'}` is invertible and
`|det|^{-(N-1)} (∫ w)^{|D'|} ≤ (J₁ W_c)^{|D'|}`. -/
theorem frJac_le {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (R : ℕ) (D' : Finset (Torus d ℓ)) {Wc : ℝ}
    (hWc : ∫⁻ v, ENNReal.ofReal (chartWeight h v) ≤ ENNReal.ofReal Wc) :
    IsUnit ((((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ)
      Subtype.val).det) ∧
    (ENNReal.ofReal |(((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ)
        Subtype.val).det ^ (N - 1)|)⁻¹ *
      (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ D'.card ≤
      ENNReal.ofReal (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) *
        (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) * Wc) ^ D'.card := by
  set c₀ := (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ with hc₀
  have hq : 2 * (d : ℝ) / (2 * d + ν) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hc0 : 0 < c₀ := mul_pos (by linarith) (inv_pos.2 (Real.sqrt_pos.2 (by positivity)))
  set b := (Real.sqrt β)⁻¹ with hb
  have hb0 : 0 < b := inv_pos.2 (Real.sqrt_pos.2 hβ)
  have hsm : (b • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ)
      (Subtype.val : D' → Torus d ℓ) =
      b • (kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ)
        (Subtype.val : D' → Torus d ℓ) := by
    ext i j; simp
  have hdet : ((b • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ) Subtype.val).det =
      b ^ D'.card * ((kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ) Subtype.val).det := by
    rw [hsm, Matrix.det_smul, Fintype.card_coe]
  have hge := det_submatrix_kf0CR_ge (d := d) (m := ℓ) hν R D'
  have hpos : (b * c₀) ^ D'.card ≤
      ((b • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ) Subtype.val).det := by
    rw [hdet, mul_pow]
    exact mul_le_mul_of_nonneg_left hge (by positivity)
  have hpos' : 0 < ((b • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ)
      Subtype.val).det := lt_of_lt_of_le (by positivity) hpos
  refine ⟨isUnit_iff_ne_zero.2 hpos'.ne', ?_⟩
  set x := ((b • kf0CR d ℓ ν R).submatrix (Subtype.val : D' → Torus d ℓ) Subtype.val).det
  have hx : ((b * c₀) ^ (N - 1)) ^ D'.card ≤ |x ^ (N - 1)| := by
    rw [abs_of_pos (pow_pos hpos' _), ← pow_mul, mul_comm (N - 1), pow_mul]
    exact pow_le_pow_left₀ (by positivity) hpos _
  have hxpos : 0 < |x ^ (N - 1)| := abs_pos.2 (pow_ne_zero _ hpos'.ne')
  have hinv : (ENNReal.ofReal |x ^ (N - 1)|)⁻¹ ≤ ENNReal.ofReal ((b * c₀)⁻¹ ^ (N - 1)) ^ D'.card := by
    rw [← ENNReal.ofReal_inv_of_pos hxpos, ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_pow, inv_pow]
    exact inv_anti₀ (by positivity) hx
  calc _ ≤ ENNReal.ofReal ((b * c₀)⁻¹ ^ (N - 1)) ^ D'.card * ENNReal.ofReal Wc ^ D'.card :=
        mul_le_mul' hinv (pow_le_pow_left' hWc _)
    _ = _ := by
        rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity)]

/-- The one-site factor of the integrand of the term `D'`, on the event of `H`. -/
def frASite (p : ℝ) (W H : Finset (Torus d ℓ)) (ε β ν G a θ : ℝ) (D D' W' : Finset (Torus d ℓ))
    (y : Torus d ℓ) (w : perp h × Bool) : ℝ≥0∞ :=
  (frEvt h p W H y).indicator 1 w * ENNReal.ofReal (frSiteFac h ε β ν G a θ D D' W' y w)

/-- The bound of one site: `η` on `H`, `2` on `D`, `K₀` on `W'`. -/
def frCS (η K₀ : ℝ) (H D W' : Finset (Torus d ℓ)) (y : Torus d ℓ) : ℝ :=
  (if y ∈ H then η else 1) * (if y ∈ D then 2 else 1) * (if y ∈ W' then K₀ else 1)

omit [NeZero ℓ] in
theorem frCS_nonneg {η K₀ : ℝ} (hη : 0 ≤ η) (hK : 1 ≤ K₀) (H D W' : Finset (Torus d ℓ))
    (y : Torus d ℓ) : 0 ≤ frCS η K₀ H D W' y := by
  unfold frCS
  have : 0 ≤ (if y ∈ H then η else 1) := by split_ifs <;> linarith
  have : 0 ≤ (if y ∈ W' then K₀ else 1) := by split_ifs <;> linarith
  have : (0 : ℝ) ≤ (if y ∈ D then 2 else 1) := by split_ifs <;> norm_num
  positivity

omit [NeZero ℓ] in
theorem le_frCS_of_mem {η K₀ : ℝ} (hη : 0 ≤ η) (hK : 1 ≤ K₀) {H : Finset (Torus d ℓ)}
    (D W' : Finset (Torus d ℓ)) {y : Torus d ℓ} (hy : y ∈ H) : η ≤ frCS η K₀ H D W' y := by
  unfold frCS
  simp only [hy, ite_true]
  have h2 : (1 : ℝ) ≤ (if y ∈ D then 2 else 1) := by split_ifs <;> norm_num
  have h3 : (1 : ℝ) ≤ (if y ∈ W' then K₀ else 1) := by split_ifs <;> linarith
  calc η = η * 1 * 1 := by ring
    _ ≤ _ := by gcongr

theorem prod_frCS (η K₀ : ℝ) (H D W' : Finset (Torus d ℓ)) :
    ∏ y, frCS η K₀ H D W' y = η ^ H.card * 2 ^ D.card * K₀ ^ W'.card := by
  unfold frCS
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]


/-- The density bound of a site of `D'`: heavy on `H`, ordinary elsewhere. -/
def frAy (Γ₀ ea eb eG K₀ : ℝ) (H : Finset (Torus d ℓ)) (y : Torus d ℓ) : ℝ :=
  if y ∈ H then Γ₀ * ea * (eb + eG) else Γ₀ * (eb * K₀)

omit [NeZero ℓ] in
theorem frAy_nonneg {Γ₀ ea eb eG K₀ : ℝ} (hΓ : 0 ≤ Γ₀) (hea : 0 ≤ ea) (heb : 0 ≤ eb)
    (heG : 0 ≤ eG) (hK : 0 ≤ K₀) (H : Finset (Torus d ℓ)) (y : Torus d ℓ) :
    0 ≤ frAy Γ₀ ea eb eG K₀ H y := by
  unfold frAy; split_ifs <;> positivity

omit [NeZero ℓ] in
/-- A heavy site off `D'`. -/
theorem frHeavyOff {p ε β ν G a θ T M₀ η : ℝ} (hε : 0 < ε) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M₀)
    {W H D D' W' : Finset (Torus d ℓ)} {y : Torus d ℓ} (hyD' : y ∉ D') (hyH : y ∈ H)
    (hXle : ∀ ψ : perp h, (if y ∈ W' then frEx h a θ ψ else 1) ≤ frEx h a θ ψ)
    (hTail : ∫⁻ ψ, Set.indicator {ψ : perp h | p < ‖ψ‖} (fun ψ => ENNReal.ofReal
      (frEx h a θ ψ)) ψ ∂(oneSiteGaussian (perp h)) ≤ ENNReal.ofReal T)
    (hMom : ∫⁻ ψ, ENNReal.ofReal (frEx h a θ ψ) ∂(oneSiteGaussian (perp h)) ≤ ENNReal.ofReal M₀)
    (hη1 : 2 * T + 2 * Real.exp (-(β * ν / 2) + 2 * G) * M₀ ≤ η) (hη2 : T + ε * M₀ ≤ η) :
    ∫⁻ w, frASite h p W H ε β ν G a θ D D' W' y w ∂(frSiteMeasure h ε) ≤ ENNReal.ofReal η := by
  have hev : frEvt h p W H y = (frOrd h p)ᶜ := by simp [frEvt, hyH]
  set L : Bool → ℝ := fun b => (if y ∈ D' then frLam' ε β ν G b else 1) *
    (if y ∈ D \ D' then 2 * frLam ε β ν G b else 1) with hL
  have hL0 : ∀ b, 0 ≤ L b := fun b => by
    have := frLam_nonneg hε.le β ν G b; have := frLam'_nonneg hε.le β ν G b
    simp only [hL]; split_ifs <;> positivity
  have hXm : Measurable fun ψ : perp h => (if y ∈ W' then frEx h a θ ψ else 1) := by
    split_ifs
    · exact measurable_frEx h a θ
    · exact measurable_const
  have h1 := lintegral_heavy_le h (p := p) hε.le L hL0 _ hXm
  have hfun : (fun w => frASite h p W H ε β ν G a θ D D' W' y w) = fun w =>
      (frOrd h p)ᶜ.indicator 1 w *
        ENNReal.ofReal (L w.2 * (if y ∈ W' then frEx h a θ w.1 else 1)) := by
    funext w; simp only [frASite, hev, frSiteFac, hL]
  rw [hfun]
  refine h1.trans ?_
  have hT' : ∫⁻ ψ, Set.indicator {ψ : perp h | p < ‖ψ‖} (fun ψ => ENNReal.ofReal
      (if y ∈ W' then frEx h a θ ψ else 1)) ψ ∂(oneSiteGaussian (perp h)) ≤
      ENNReal.ofReal T := by
    refine le_trans (lintegral_mono fun ψ => ?_) hTail
    by_cases hψ : p < ‖ψ‖
    · simp only [Set.indicator_of_mem (show ψ ∈ {ψ : perp h | p < ‖ψ‖} from hψ)]
      exact ENNReal.ofReal_le_ofReal (hXle ψ)
    · simp only [Set.indicator_of_notMem (show ψ ∉ {ψ : perp h | p < ‖ψ‖} from hψ), le_refl]
  have hM' : ∫⁻ ψ, ENNReal.ofReal (if y ∈ W' then frEx h a θ ψ else 1)
      ∂(oneSiteGaussian (perp h)) ≤ ENNReal.ofReal M₀ :=
    le_trans (lintegral_mono fun ψ => ENNReal.ofReal_le_ofReal (hXle ψ)) hMom
  have hε1 : ε / (1 + ε) ≤ ε := div_le_self hε.le (by linarith)
  have hreal : L true * T + ε / (1 + ε) * L false * M₀ ≤ η := by
    by_cases hyD : y ∈ D \ D'
    · have e1 : L true = 2 := by simp [hL, hyD', hyD, frLam_true]
      have e2 : L false = 2 * (ε⁻¹ * Real.exp (-(β * ν / 2)) * Real.exp (2 * G)) := by
        simp [hL, hyD', hyD, frLam_false]
      rw [e1, e2]
      have := bern_mul_frLam_false_le hε β ν G
      nlinarith
    · have e1 : L true = 1 := by simp [hL, hyD', hyD]
      have e2 : L false = 1 := by simp [hL, hyD', hyD]
      rw [e1, e2]
      nlinarith
  calc ENNReal.ofReal (L true) * ∫⁻ ψ, Set.indicator {ψ : perp h | p < ‖ψ‖} (fun ψ =>
        ENNReal.ofReal (if y ∈ W' then frEx h a θ ψ else 1)) ψ ∂(oneSiteGaussian (perp h)) +
      ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false) *
        ∫⁻ ψ, ENNReal.ofReal (if y ∈ W' then frEx h a θ ψ else 1) ∂(oneSiteGaussian (perp h))
      ≤ ENNReal.ofReal (L true) * ENNReal.ofReal T +
        ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false) * ENNReal.ofReal M₀ := by
        gcongr
    _ = ENNReal.ofReal (L true * T + ε / (1 + ε) * L false * M₀) := by
        rw [← ENNReal.ofReal_mul (hL0 true), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (hL0 false)),
          ← ENNReal.ofReal_add (mul_nonneg (hL0 true) hT0)
            (mul_nonneg (mul_nonneg (by positivity) (hL0 false)) hM0)]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hreal

omit [NeZero ℓ] in
/-- An ordinary site off `D'`. -/
theorem frOrdOff {p ε β ν G a θ η K₀ : ℝ} (hε : 0 < ε) (hK1 : 1 ≤ K₀)
    {W H D D' W' : Finset (Torus d ℓ)} {y : Torus d ℓ} (hyD' : y ∉ D') (hyH : y ∉ H)
    (hyW : y ∈ W)
    (hXK : ∀ ψ : perp h, ‖ψ‖ ≤ p →
      (if y ∈ W' then frEx h a θ ψ else 1) ≤ (if y ∈ W' then K₀ else 1)) :
    ∫⁻ w, frASite h p W H ε β ν G a θ D D' W' y w ∂(frSiteMeasure h ε) ≤
      ENNReal.ofReal (frCS η K₀ H D W' y) := by
  have hev : frEvt h p W H y = frOrd h p := by simp [frEvt, hyH, hyW]
  have hfun : (fun w => frASite h p W H ε β ν G a θ D D' W' y w) = fun w =>
      (frOrd h p).indicator 1 w * ENNReal.ofReal
        ((fun b => (if y ∈ D' then frLam' ε β ν G b else 1) *
          (if y ∈ D \ D' then 2 * frLam ε β ν G b else 1)) w.2 *
        (fun ψ => if y ∈ W' then frEx h a θ ψ else 1) w.1) := by
    funext w; simp only [frASite, hev, frSiteFac]
  rw [hfun]
  refine lintegral_ord_le h (p := p) hε.le (fun b => (if y ∈ D' then frLam' ε β ν G b else 1) *
    (if y ∈ D \ D' then 2 * frLam ε β ν G b else 1)) (fun ψ => if y ∈ W' then frEx h a θ ψ else 1)
    (fun ψ hψ => ?_)
  simp only [hyD', ite_false, one_mul, frCS, hyH, frLam_true]
  have hX := hXK ψ hψ
  have hX0 : 0 ≤ (if y ∈ W' then frEx h a θ ψ else 1) := by
    split_ifs
    · exact (frEx_pos h a _ ψ).le
    · exact zero_le_one
  by_cases hyD : y ∈ D \ D'
  · have hyD2 : y ∈ D := (Finset.mem_sdiff.1 hyD).1
    simp only [hyD, hyD2, ite_true, mul_one]
    nlinarith
  · simp only [hyD, ite_false, one_mul]
    have : (1 : ℝ) ≤ (if y ∈ D then 2 else 1) := by split_ifs <;> norm_num
    have hK0' : 0 ≤ (if y ∈ W' then K₀ else 1) := by split_ifs <;> linarith
    nlinarith

omit [NeZero ℓ] in
/-- A free site (outside `W`). -/
theorem frFreeOff {p ε β ν G a θ η K₀ : ℝ} (hε : 0 < ε) {W H D D' W' : Finset (Torus d ℓ)}
    (hDW : W' ⊆ W) (hDW' : D ⊆ W') {y : Torus d ℓ} (hyD' : y ∉ D') (hyH : y ∉ H)
    (hyW : y ∉ W) :
    ∫⁻ w, frASite h p W H ε β ν G a θ D D' W' y w ∂(frSiteMeasure h ε) ≤
      ENNReal.ofReal (frCS η K₀ H D W' y) := by
  have hev : frEvt h p W H y = Set.univ := by simp [frEvt, hyH, hyW]
  have hyW' : y ∉ W' := fun hy => hyW (hDW hy)
  have hyD : y ∉ D \ D' := fun hy => hyW' (hDW' (Finset.mem_sdiff.1 hy).1)
  have hyD2 : y ∉ D := fun hy => hyW' (hDW' hy)
  have hprob := isProbabilityMeasure_frSiteMeasure h hε.le
  have hfun : (fun w => frASite h p W H ε β ν G a θ D D' W' y w) = fun _ => 1 := by
    funext w; simp [frASite, hev, frSiteFac, hyD', hyD, hyW']
  rw [hfun]
  simp [frCS, hyH, hyD2, hyW']

omit [NeZero ℓ] in
/-- The sites of `D'`. -/
theorem frSitesOn {p ε β ν G a θ K₀ : ℝ} (hε : 0 < ε) (hθ2 : θ ≤ 1 / 8) (ha0 : 0 ≤ a)
    (hθ0 : 0 ≤ θ) (hK₀ : Real.exp (a * p + θ * p ^ 2) ≤ K₀)
    {W H D D' W' : Finset (Torus d ℓ)} (hD'D : D' ⊆ D) (hDW : W' ⊆ W) (hDW' : D ⊆ W') :
    ∀ y ∈ D', ∀ ψ, (∫⁻ b, frASite h p W H ε β ν G a θ D D' W' y (ψ, b) ∂(frBern ε)) *
      ENNReal.ofReal (gDens h ψ) ≤
      ENNReal.ofReal (frAy ((2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2))
        (Real.exp (a ^ 2)) (Real.exp (-(β * ν / 128))) (Real.exp (-(β * ν / 2) + 2 * G))
        K₀ H y) := by
  intro y hyD' ψ
  have hyW' : y ∈ W' := hDW' (hD'D hyD')
  have hyD : y ∉ D \ D' := fun hy => (Finset.mem_sdiff.1 hy).2 hyD'
  by_cases hyH : y ∈ H
  · have hev : frEvt h p W H y = (frOrd h p)ᶜ := by simp [frEvt, hyH]
    have hfun : (fun b => frASite h p W H ε β ν G a θ D D' W' y (ψ, b)) = fun b =>
        (frOrd h p)ᶜ.indicator 1 (ψ, b) * ENNReal.ofReal (frLam' ε β ν G b * frEx h a θ ψ) := by
      funext b; simp [frASite, hev, frSiteFac, hyD', hyD, hyW']
    rw [hfun]
    refine (sup_heavy_le h hε.le hθ2 (frLam' ε β ν G) (frLam'_nonneg hε.le β ν G) ψ).trans ?_
    simp only [frAy, hyH, ite_true, frLam'_true, frLam'_false]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact add_le_add le_rfl (bern_mul_frLam_false_le hε β ν G)
  · have hyW : y ∈ W := hDW hyW'
    have hev : frEvt h p W H y = frOrd h p := by simp [frEvt, hyH, hyW]
    have hfun : (fun b => frASite h p W H ε β ν G a θ D D' W' y (ψ, b)) = fun b =>
        (frOrd h p).indicator 1 (ψ, b) * ENNReal.ofReal (frLam' ε β ν G b * frEx h a θ ψ) := by
      funext b; simp [frASite, hev, frSiteFac, hyD', hyD, hyW']
    rw [hfun]
    refine (sup_ord_le h hε.le (frLam' ε β ν G) (frEx h a θ)
      (K := Real.exp (-(β * ν / 128)) * K₀)
      (mul_nonneg (Real.exp_pos _).le ((Real.exp_pos _).le.trans hK₀)) (fun ψ hψ => ?_) ψ).trans ?_
    · rw [frLam'_true]
      exact mul_le_mul_of_nonneg_left ((frEx_le_of_norm_le h ha0 hθ0 hψ).trans hK₀)
        (Real.exp_pos _).le
    · simp only [frAy, hyH, ite_false]; exact le_rfl

/-- **(H5) The integral of one term of the expansion.** -/
theorem lintegral_frDterm_le (hh : ‖h‖ = 1) {β ν ε G θ p K₀ Wc η : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε) (hp : 0 ≤ p) (hG : 0 ≤ G) (R : ℕ)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4)
    (ha : 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ ≤ p / 8)
    (hK₀ : Real.exp (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ * p + θ / 2 * p ^ 2) ≤ K₀)
    (hWc : ∫⁻ v, ENNReal.ofReal (chartWeight h v) ≤ ENNReal.ofReal Wc)
    (hJord : (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) * Real.exp (-(β * ν / 128)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ 1)
    (hη1 : 2 * (2 ^ Module.finrank ℝ (perp h) * Real.exp (-p ^ 2 / 8)) +
      2 * Real.exp (-(β * ν / 2) + 2 * G) * (2 ^ Module.finrank ℝ (perp h) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η)
    (hη2 : 2 ^ Module.finrank ℝ (perp h) * Real.exp (-p ^ 2 / 8) +
      ε * (2 ^ Module.finrank ℝ (perp h) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η)
    (hη3 : (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) *
      Real.exp ((2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2) *
        (Real.exp (-(β * ν / 128)) + Real.exp (-(β * ν / 2) + 2 * G)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ η)
    (W H D D' : Finset (Torus d ℓ)) (hD'D : D' ⊆ D) (hDW : frSiteHull R D ⊆ W) :
    ∫⁻ ω, (∏ y, (frEvt h p W H y).indicator 1 (ω y)) *
        ENNReal.ofReal ((∏ z ∈ D', chartWeight h (frField d ℓ β ν R (frPsi h ω) z)) *
          ∏ y, frSiteFac h ε β ν G (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) (θ / 2) D D'
            (frSiteHull R D) y (ω y)) ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤
      ENNReal.ofReal (η ^ H.card * 2 ^ D.card * K₀ ^ (frSiteHull R D).card) := by
  set a := 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ with hadef
  set W' := frSiteHull R D with hW'
  set n := Module.finrank ℝ (perp h)
  set Γ₀ := (2 * Real.pi) ^ (-(n : ℝ) / 2) with hΓ₀
  set J₁ := ((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1)
    with hJ₁
  set T := 2 ^ n * Real.exp (-p ^ 2 / 8) with hT
  set M₀ := 2 ^ n * Real.exp (2 * a ^ 2) with hM₀
  set eG := Real.exp (-(β * ν / 2) + 2 * G) with heG
  have ha0 : 0 ≤ a := by positivity
  have hJ₁0 : 0 ≤ J₁ := by
    have : 0 < 1 - 2 * (d : ℝ) / (2 * d + ν) := by
      rw [sub_pos, div_lt_one (by positivity)]; linarith
    positivity
  have hθ2 : θ / 2 ≤ 1 / 8 := by linarith
  have hT0 : 0 ≤ T := by positivity
  have hM0 : 0 ≤ M₀ := by positivity
  have hη0 : 0 ≤ η := le_trans (by positivity) hη2
  have hK1 : 1 ≤ K₀ := le_trans (Real.one_le_exp (by positivity)) hK₀
  have hDW' : D ⊆ W' := subset_frSiteHull R D
  have haSm : ∀ y, Measurable (frASite h p W H ε β ν G a (θ / 2) D D' W' y) := fun y =>
    (measurable_one.indicator (measurableSet_frEvt h p W H y)).mul
      (ENNReal.measurable_ofReal.comp (measurable_frSiteFac h ε β ν G a (θ / 2) D D' W' y))
  -- the integrand factorizes
  have hfac : ∀ ω : Torus d ℓ → perp h × Bool, (∏ y, (frEvt h p W H y).indicator 1 (ω y)) *
      ENNReal.ofReal ((∏ z ∈ D', chartWeight h (frField d ℓ β ν R (frPsi h ω) z)) *
        ∏ y, frSiteFac h ε β ν G a (θ / 2) D D' W' y (ω y)) =
      (∏ y, frASite h p W H ε β ν G a (θ / 2) D D' W' y (ω y)) *
        ∏ z ∈ D', ENNReal.ofReal (chartWeight h
          (matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) (fun y => (ω y).1) z)) := by
    intro ω
    have hu : ∀ z, frField d ℓ β ν R (frPsi h ω) z =
        matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) (fun y => (ω y).1) z := fun z => rfl
    simp only [hu]
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun z _ => chartWeight_nonneg h _),
      ENNReal.ofReal_prod_of_nonneg (fun z _ => chartWeight_nonneg h _),
      ENNReal.ofReal_prod_of_nonneg
        (fun y _ => frSiteFac_nonneg h hε.le β ν G a (θ / 2) D D' W' y _)]
    unfold frASite
    rw [Finset.prod_mul_distrib]
    ring
  have hfacX : ∀ y w, frSiteFac h ε β ν G a (θ / 2) D D' W' y w =
      ((if y ∈ D' then frLam' ε β ν G w.2 else 1) *
        (if y ∈ D \ D' then 2 * frLam ε β ν G w.2 else 1)) *
      (if y ∈ W' then frEx h a (θ / 2) w.1 else 1) := fun y w => rfl
  have hXle : ∀ y (ψ : perp h), (if y ∈ W' then frEx h a (θ / 2) ψ else 1) ≤
      frEx h a (θ / 2) ψ := by
    intro y ψ; split_ifs
    · exact le_rfl
    · exact one_le_frEx h ha0 (by linarith) ψ
  have hXK : ∀ y (ψ : perp h), ‖ψ‖ ≤ p →
      (if y ∈ W' then frEx h a (θ / 2) ψ else 1) ≤ (if y ∈ W' then K₀ else 1) := by
    intro y ψ hψ; split_ifs
    · exact (frEx_le_of_norm_le h ha0 (by linarith) hψ).trans hK₀
    · exact le_rfl
  have hTail : ∫⁻ ψ, Set.indicator {ψ : perp h | p < ‖ψ‖} (fun ψ => ENNReal.ofReal
      (frEx h a (θ / 2) ψ)) ψ ∂(oneSiteGaussian (perp h)) ≤ ENNReal.ofReal T :=
    lintegral_tail_exp_le (E := perp h) ha0 ha hθ2
  have hMom : ∫⁻ ψ, ENNReal.ofReal (frEx h a (θ / 2) ψ) ∂(oneSiteGaussian (perp h)) ≤
      ENNReal.ofReal M₀ := lintegral_exp_lin_sq_le (E := perp h) hθ2
  have hε1 : ε / (1 + ε) ≤ ε := div_le_self hε.le (by linarith)
  obtain ⟨hSD, hJ⟩ := frJac_le h hβ hν R D' hWc
  -- the sites off `D'`
  have hc1 : ∀ y ∉ D', ∫⁻ w, frASite h p W H ε β ν G a (θ / 2) D D' W' y w
      ∂(frSiteMeasure h ε) ≤ ENNReal.ofReal (frCS η K₀ H D W' y) := by
    intro y hyD'
    by_cases hyH : y ∈ H
    · exact (frHeavyOff h hε hT0 hM0 hyD' hyH (hXle y) hTail hMom hη1 hη2).trans
        (ENNReal.ofReal_le_ofReal (le_frCS_of_mem hη0 hK1 D W' hyH))
    · by_cases hyW : y ∈ W
      · exact frOrdOff h hε hK1 hyD' hyH hyW (hXK y)
      · exact frFreeOff h hε hDW hDW' hyD' hyH hyW
  -- the sites of `D'`
  have hA := frSitesOn h (W := W) (H := H) (β := β) (ν := ν) (G := G) hε hθ2 ha0 (by linarith)
    hK₀ hD'D hDW hDW'
  have hc2 : ∀ y ∈ D', ENNReal.ofReal (frAy Γ₀ (Real.exp (a ^ 2)) (Real.exp (-(β * ν / 128)))
      eG K₀ H y) * ENNReal.ofReal (J₁ * Wc) ≤ ENNReal.ofReal (frCS η K₀ H D W' y) := by
    intro y hyD'
    have hyW' : y ∈ W' := hDW' (hD'D hyD')
    have hyD : y ∈ D := hD'D hyD'
    rw [← ENNReal.ofReal_mul (frAy_nonneg (by positivity) (by positivity) (by positivity)
      (by positivity) (by linarith) H y)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hyH : y ∈ H
    · refine le_trans ?_ (le_frCS_of_mem hη0 hK1 D W' hyH)
      simp only [frAy, hyH, ite_true]
      exact hη3
    · simp only [frAy, frCS, hyH, ite_false, hyD, hyW', ite_true, one_mul]
      have : Γ₀ * (Real.exp (-(β * ν / 128)) * K₀) * (J₁ * Wc) =
          (Γ₀ * Real.exp (-(β * ν / 128)) * (J₁ * Wc)) * K₀ := by ring
      rw [this]
      nlinarith
  calc _ = ∫⁻ ω, (∏ y, frASite h p W H ε β ν G a (θ / 2) D D' W' y (ω y)) *
        ∏ z ∈ D', ENNReal.ofReal (chartWeight h
          (matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) (fun y => (ω y).1) z))
        ∂(Measure.pi fun _ => frSiteMeasure h ε) := lintegral_congr fun ω => hfac ω
    _ ≤ ∏ y, ENNReal.ofReal (frCS η K₀ H D W' y) :=
        lintegral_jac_sites_le h hh ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) D' hSD hε.le
          (frASite h p W H ε β ν G a (θ / 2) D D' W') haSm
          (fun y => ENNReal.ofReal (frAy Γ₀ (Real.exp (a ^ 2)) (Real.exp (-(β * ν / 128)))
            eG K₀ H y)) hA (ENNReal.ofReal (J₁ * Wc)) hJ
          (fun y => ENNReal.ofReal (frCS η K₀ H D W' y)) hc1 hc2
    _ = _ := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun y _ => frCS_nonneg hη0 hK1 H D W' y),
          prod_frCS]

end

end Balaban.LargeField.KF0FR
