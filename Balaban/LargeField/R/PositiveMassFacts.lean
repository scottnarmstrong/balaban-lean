module

public import Balaban.LargeField.Characteristic.Reg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Three elementary positive-mass facts (Q13-DECISION §§2, 4, 5)

* `fieldClose_of_real_unit`, `tol_gt_of_flow`, `fieldClose_of_flow`: the real field-test lemma of
  `notes/phase1/Q13-DECISION.md` §2 and inequality (2.1).
* `positiveMass_minimizer_ne`: the one-spin example (4.1)-(4.2) of §4.
* `real_mass_cost`: the per-site real mass cost (5.1) of §5.

Nothing here is a statement about the conventions "A" / "A0" themselves.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section FieldTest

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  (G : GeneratingSet d L N₀ q ϱ)

/-- **Real field-test lemma** (Q13-DECISION §2).  For a real unit-sphere field `φ`
(`IsRealUnitField`) and real unit `h` (`D.h x` real, `∑ ‖D.h x i‖² = 1` on each site), the
`FieldClose` conjunct (landed form: if `0 < ν` then `vn (φ - h) < t / √ν` and
`‖h·h - 1‖ < t² / ν`) holds as soon as `2 √ν < t`: indeed `vn (φ - h) ≤ 2`, `h·h - 1 = 0`. -/
theorem fieldClose_of_real_unit (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (hφ : IsRealUnitField G φ)
    (hh : ∀ x : G.Ω 1, (∀ i, (D.h x i).im = 0) ∧ ∑ i, ‖D.h x i‖ ^ 2 = 1)
    (ν t : ℝ) (ht : 0 < t) (htol : 2 * Real.sqrt ν < t)
    (S : Finset (Torus d (N₀ * L ^ q))) :
    FieldClose G D φ ν S t := by
  intro hνpos x _
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hνpos
  have hvφ : vn (fun i => φ (x, i)) = 1 := by
    have h1 := vn_sq (fun i => φ (x, i))
    rw [(hφ x).2] at h1
    nlinarith [vn_nonneg (fun i => φ (x, i))]
  have hvh : vn (fun i => D.h x i) = 1 := by
    have h1 := vn_sq (fun i => D.h x i)
    rw [(hh x).2] at h1
    nlinarith [vn_nonneg (fun i => D.h x i)]
  constructor
  · have htri : vn (fun i => φ (x, i) - D.h x i) ≤ 2 := by
      unfold vn at *
      have := norm_sub_le (WithLp.toLp 2 (fun i => φ (x, i)) : EuclideanSpace ℂ (Fin N))
        (WithLp.toLp 2 (fun i => D.h x i))
      rw [hvφ, hvh] at this
      have e : (WithLp.toLp 2 (fun i => φ (x, i) - D.h x i) : EuclideanSpace ℂ (Fin N)) =
          WithLp.toLp 2 (fun i => φ (x, i)) - WithLp.toLp 2 (fun i => D.h x i) := rfl
      rw [e]; linarith
    rw [lt_div_iff₀ hs]
    nlinarith
  · have h0 : ∑ i, D.h x i * D.h x i - 1 = 0 := by
      have : ∑ i, D.h x i * D.h x i = ∑ i, ((‖D.h x i‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have him := (hh x).1 i
        rw [Complex.sq_norm, Complex.normSq_apply, him]
        apply Complex.ext <;> simp [him]
      rw [this, ← Complex.ofReal_sum, (hh x).2]; simp
    rw [h0]; simp only [norm_zero]
    positivity

/-- Pure real arithmetic of Q13-DECISION (2.1): with `δ = A₀ λ^{p₀} / √(a β)`, `β ν ≤ E`, and
`A₀² λ^{2p₀} > (64/9) a E`, one has `2 √ν < 3 δ / 4`.  (`lp` stands for `λ^{p₀}`.) -/
theorem tol_gt_of_flow (a A₀ β ν E lp : ℝ) (ha : 0 < a) (hA : 0 < A₀) (hβ : 0 < β)
    (hlp : 0 < lp) (hν : 0 ≤ ν) (hE : β * ν ≤ E)
    (h21 : (64 / 9) * a * E < A₀ ^ 2 * lp ^ 2) :
    2 * Real.sqrt ν < 3 * (A₀ * lp / Real.sqrt (a * β)) / 4 := by
  have hab : 0 < a * β := mul_pos ha hβ
  have hs : 0 < Real.sqrt (a * β) := Real.sqrt_pos.2 hab
  rw [mul_div_assoc', lt_div_iff₀ (by norm_num : (0:ℝ) < 4), mul_assoc, ← mul_assoc,
    mul_comm (2 * Real.sqrt ν) 4, lt_div_iff₀ hs]
  have hsq : 0 ≤ Real.sqrt ν * Real.sqrt (a * β) := by positivity
  have hp : 0 < 3 * (A₀ * lp) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 hp.le
  have e1 : (4 * (2 * Real.sqrt ν) * Real.sqrt (a * β)) ^ 2 = 64 * (a * (β * ν)) := by
    have := Real.sq_sqrt hν
    have := Real.sq_sqrt hab.le
    calc (4 * (2 * Real.sqrt ν) * Real.sqrt (a * β)) ^ 2
        = 64 * (Real.sqrt ν ^ 2) * (Real.sqrt (a * β) ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt hν, Real.sq_sqrt hab.le]; ring
  rw [e1]
  have : a * (β * ν) ≤ a * E := mul_le_mul_of_nonneg_left hE ha.le
  nlinarith

/-- Numerical corollary: the field test holds with tolerance `3δ/4` (the mixed `RegMixedIneq`
field test), `δ = A₀ λ^{p₀} / √(a β)`, under Q13-DECISION (2.1) and `β ν ≤ E`. -/
theorem fieldClose_of_flow (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (hφ : IsRealUnitField G φ)
    (hh : ∀ x : G.Ω 1, (∀ i, (D.h x i).im = 0) ∧ ∑ i, ‖D.h x i‖ ^ 2 = 1)
    (a A₀ β ν E lp : ℝ) (ha : 0 < a) (hA : 0 < A₀) (hβ : 0 < β)
    (hlp : 0 < lp) (hν : 0 ≤ ν) (hE : β * ν ≤ E)
    (h21 : (64 / 9) * a * E < A₀ ^ 2 * lp ^ 2) (S : Finset (Torus d (N₀ * L ^ q))) :
    FieldClose G D φ ν S (3 * (A₀ * lp / Real.sqrt (a * β)) / 4) := by
  have h := tol_gt_of_flow a A₀ β ν E lp ha hA hβ hlp hν hE h21
  refine fieldClose_of_real_unit G D φ hφ hh ν _ ?_ h S
  have : 0 < Real.sqrt (a * β) := Real.sqrt_pos.2 (mul_pos ha hβ)
  positivity

end FieldTest

section OneSpin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The one-spin action `A_m(s) = ½‖s - e‖² + (m/2)‖s - h‖²` of Q13-DECISION §4. -/
noncomputable def oneSpinAction (m : ℝ) (e h s : E) : ℝ :=
  1 / 2 * ‖s - e‖ ^ 2 + m / 2 * ‖s - h‖ ^ 2

/-- The candidate minimizer `s_m = (e + m h) / ‖e + m h‖` (4.1). -/
noncomputable def oneSpinMin (m : ℝ) (e h : E) : E := ‖e + m • h‖⁻¹ • (e + m • h)

/-- (4.1), first step: on unit vectors the action is `1 + m - ⟪e + m h, s⟫`. -/
theorem oneSpinAction_eq (m : ℝ) {e h s : E} (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (hs : ‖s‖ = 1) :
    oneSpinAction m e h s = 1 + m - inner ℝ (e + m • h) s := by
  unfold oneSpinAction
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq, he, hh, hs,
    inner_add_left, inner_smul_left, real_inner_comm s e, real_inner_comm s h]
  simp; ring

theorem norm_add_smul_ge {m : ℝ} (hm : 0 ≤ m) {e h : E} (he : ‖e‖ = 1) (hh : ‖h‖ = 1) :
    1 - m ≤ ‖e + m • h‖ := by
  have := norm_sub_norm_le e (-(m • h))
  simp [norm_smul, abs_of_nonneg hm, he, hh] at this
  simpa [sub_eq_add_neg] using this

theorem norm_add_smul_le {m : ℝ} (hm : 0 ≤ m) {e h : E} (he : ‖e‖ = 1) (hh : ‖h‖ = 1) :
    ‖e + m • h‖ ≤ 1 + m := by
  have := norm_add_le e (m • h)
  simpa [norm_smul, abs_of_nonneg hm, he, hh] using this

/-- (4.1): for `0 ≤ m < 1`, `s_m` is the unique minimizer of `A_m` over unit vectors. -/
theorem oneSpinMin_isMin {m : ℝ} (hm : 0 ≤ m) (hm1 : m < 1) {e h : E}
    (he : ‖e‖ = 1) (hh : ‖h‖ = 1) :
    ‖oneSpinMin m e h‖ = 1 ∧
      (∀ s : E, ‖s‖ = 1 → oneSpinAction m e h (oneSpinMin m e h) ≤ oneSpinAction m e h s) ∧
      (∀ s : E, ‖s‖ = 1 → oneSpinAction m e h s = oneSpinAction m e h (oneSpinMin m e h) →
        s = oneSpinMin m e h) := by
  have hpos : 0 < ‖e + m • h‖ := by linarith [norm_add_smul_ge hm he hh]
  have hsm : ‖oneSpinMin m e h‖ = 1 := by
    unfold oneSpinMin
    rw [norm_smul, norm_inv, norm_norm]; field_simp
  have hinner : inner ℝ (e + m • h) (oneSpinMin m e h) = ‖e + m • h‖ := by
    unfold oneSpinMin
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  refine ⟨hsm, fun s hs => ?_, fun s hs heq => ?_⟩
  · rw [oneSpinAction_eq m he hh hs, oneSpinAction_eq m he hh hsm, hinner]
    have := real_inner_le_norm (e + m • h) s
    rw [hs] at this; linarith
  · rw [oneSpinAction_eq m he hh hs, oneSpinAction_eq m he hh hsm, hinner] at heq
    have h1 : inner ℝ (e + m • h) s = ‖e + m • h‖ * ‖s‖ := by rw [hs]; linarith
    have h2 := (inner_eq_norm_mul_iff_real.1 h1)
    rw [hs, one_smul] at h2
    unfold oneSpinMin
    calc s = ‖e + m • h‖⁻¹ • (‖e + m • h‖ • s) := by
          rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      _ = _ := by rw [← h2]

/-- **Refutation of the zero-centred reference at positive mass** (Q13-DECISION §4, (4.1)).
For unit `e`, `h` with `e ≠ h`, `e ≠ -h` (not parallel; e.g. `e = (cos θ, sin θ)`, `h = e₁`,
`0 < θ < π/2`, in `EuclideanSpace ℝ (Fin 2)`) and `0 < m < 1/2`, the minimizer `s_m` of
`½‖s-e‖² + (m/2)‖s-h‖²` over unit vectors differs from the boundary direction `e`.  Hence the
`δ = 0` case of the tube `K₆δ` of LF-RECONSTRUCTION Lemma III.3.3 (P7 Lemma 2.1) fails for the
massive problem: the reference must lie in a tube `K₆δ + C_m ν`. -/
theorem positiveMass_minimizer_ne {m : ℝ} (hm : 0 < m) (hm1 : m < 1 / 2) {e h : E}
    (he : ‖e‖ = 1) (hh : ‖h‖ = 1) (hne : e ≠ h) (hneg : e ≠ -h) :
    oneSpinMin m e h ≠ e := by
  have hpos : 0 < ‖e + m • h‖ := by linarith [norm_add_smul_ge hm.le he hh]
  intro heq
  unfold oneSpinMin at heq
  have h2 : e + m • h = ‖e + m • h‖ • e := by
    calc e + m • h = ‖e + m • h‖ • (‖e + m • h‖⁻¹ • (e + m • h)) := by
          rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      _ = _ := by rw [heq]
  set c := ‖e + m • h‖ - 1 with hc
  have h3 : h = (c / m) • e := by
    have h4 : m • h = c • e := by
      have : m • h = ‖e + m • h‖ • e - e := by rw [← h2]; abel
      rw [this, hc, sub_smul, one_smul]
    have := congrArg (fun z => m⁻¹ • z) h4
    simpa [smul_smul, inv_mul_cancel₀ hm.ne', div_eq_inv_mul] using this
  have h5 : |c / m| = 1 := by
    have := congrArg norm h3
    rw [norm_smul, he, hh, Real.norm_eq_abs] at this
    linarith
  rcases abs_eq (zero_le_one) |>.1 h5 with h6 | h6
  · exact hne (by rw [h3, h6, one_smul])
  · exact hneg (by rw [h3, h6]; simp)

/-- (4.2): `‖s_m - e‖ ≤ 2m/(1-m) ≤ 4m` for `0 ≤ m < 1/2`. -/
theorem oneSpinMin_dist_le {m : ℝ} (hm : 0 ≤ m) (hm1 : m < 1 / 2) {e h : E}
    (he : ‖e‖ = 1) (hh : ‖h‖ = 1) :
    ‖oneSpinMin m e h - e‖ ≤ 2 * m / (1 - m) ∧ 2 * m / (1 - m) ≤ 4 * m := by
  have hge := norm_add_smul_ge hm he hh
  have hle := norm_add_smul_le hm he hh
  have hpos : 0 < ‖e + m • h‖ := by linarith
  refine ⟨?_, ?_⟩
  · have key : oneSpinMin m e h - e = ‖e + m • h‖⁻¹ • ((e + m • h) - ‖e + m • h‖ • e) := by
      unfold oneSpinMin
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [key, norm_smul, norm_inv, norm_norm]
    have hb : ‖(e + m • h) - ‖e + m • h‖ • e‖ ≤ 2 * m := by
      have t1 : ‖(e + m • h) - ‖e + m • h‖ • e‖
          ≤ ‖m • h‖ + ‖(1 - ‖e + m • h‖) • e‖ := by
        have : (e + m • h) - ‖e + m • h‖ • e = m • h + (1 - ‖e + m • h‖) • e := by
          rw [sub_smul, one_smul]; abel
        rw [this]; exact norm_add_le _ _
      rw [norm_smul, norm_smul, he, hh, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hm] at t1
      have : |1 - ‖e + m • h‖| ≤ m := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    have h1m : 0 < 1 - m := by linarith
    calc ‖e + m • h‖⁻¹ * ‖(e + m • h) - ‖e + m • h‖ • e‖
        ≤ ‖e + m • h‖⁻¹ * (2 * m) := by gcongr
      _ ≤ (1 - m)⁻¹ * (2 * m) := by gcongr
      _ = 2 * m / (1 - m) := by ring
  · have h1m : 0 < 1 - m := by linarith
    rw [div_le_iff₀ h1m]; nlinarith

/-- (v): at `m = 0` the minimizer is `e`. -/
theorem oneSpinMin_zero {e : E} (h : E) (he : ‖e‖ = 1) : oneSpinMin 0 e h = e := by
  simp [oneSpinMin, he]

end OneSpin

section Cost

variable {V : Type*} [NormedAddCommGroup V]

/-- **Per-site real mass cost** (Q13-DECISION (5.1)).  For unit vectors `φ x`, `h` and
`β, ν ≥ 0` with `β ν ≤ E`: `0 ≤ ½ β ν Σ_{x∈C} ‖φ x - h‖² ≤ 2 E |C|`.  Valid only on a common
field and a common support; it is NOT a comparison of minimizers, cutoffs or complex integrals. -/
theorem real_mass_cost {ι : Type*} (C : Finset ι) (φ : ι → V) (h : V)
    (hφ : ∀ x ∈ C, ‖φ x‖ = 1) (hh : ‖h‖ = 1) {β ν E : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (hE : β * ν ≤ E) :
    0 ≤ 1 / 2 * β * ν * ∑ x ∈ C, ‖φ x - h‖ ^ 2 ∧
      1 / 2 * β * ν * ∑ x ∈ C, ‖φ x - h‖ ^ 2 ≤ 2 * E * C.card := by
  have hbn : 0 ≤ β * ν := mul_nonneg hβ hν
  have hsum : ∑ x ∈ C, ‖φ x - h‖ ^ 2 ≤ ∑ _x ∈ C, (4 : ℝ) := by
    refine Finset.sum_le_sum fun x hx => ?_
    have : ‖φ x - h‖ ≤ 2 := by
      have := norm_sub_le (φ x) h; rw [hφ x hx, hh] at this; linarith
    nlinarith [norm_nonneg (φ x - h)]
  have h0 : 0 ≤ ∑ x ∈ C, ‖φ x - h‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  refine ⟨by positivity, ?_⟩
  calc 1 / 2 * β * ν * ∑ x ∈ C, ‖φ x - h‖ ^ 2
      = (1 / 2 * (β * ν)) * ∑ x ∈ C, ‖φ x - h‖ ^ 2 := by ring
    _ ≤ (1 / 2 * (β * ν)) * (C.card * 4) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ (1 / 2 * E) * (C.card * 4) := by
        have : 0 ≤ (C.card : ℝ) * 4 := by positivity
        nlinarith
    _ = 2 * E * C.card := by ring

/-- Exponential form of (5.1): `exp(-2E|C|) ≤ exp(-½βν Σ‖φ x - h‖²) ≤ 1`. -/
theorem real_mass_cost_exp {ι : Type*} (C : Finset ι) (φ : ι → V) (h : V)
    (hφ : ∀ x ∈ C, ‖φ x‖ = 1) (hh : ‖h‖ = 1) {β ν E : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (hE : β * ν ≤ E) :
    Real.exp (-(2 * E * C.card)) ≤ Real.exp (-(1 / 2 * β * ν * ∑ x ∈ C, ‖φ x - h‖ ^ 2)) ∧
      Real.exp (-(1 / 2 * β * ν * ∑ x ∈ C, ‖φ x - h‖ ^ 2)) ≤ 1 := by
  obtain ⟨h1, h2⟩ := real_mass_cost C φ h hφ hh hβ hν hE
  exact ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_one_iff.2 (by linarith)⟩

end Cost

end Balaban.LargeField
