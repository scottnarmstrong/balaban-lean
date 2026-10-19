/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRBand
public import Balaban.LargeField.Base.KF0FRBern
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FROrd`: supports, measurability and ordinary bounds of the terms (route FR, (O))

`notes/phase1/KF0-FR.md` (O). The site term `F_x` depends on the configuration in the ball
`B(x, 2R+1)`, the bond term `F_{x,μ}` in `B(x, R+1)` (`frSupp`, `frF_congr`). A site is ordinary
if `|ψ_x| ≤ p` and its sheet is the upper one (`frOrd`). With `ρ ≥ β^{-1/2} ν^{-1/2} p`, `ρ ≤ 1/2`:

* `norm_frSite_sub_one_le` (O5): if every site of the support is ordinary,
  `|F_x - 1| ≤ 3 (ρ² + Z)`, `Z = βνρ⁴/2 + 2 G_x ρ + θ_Q p²/2 ≤ 1`, `G_x = ∑_i |g_{x,i}|`;
* `norm_frBond_sub_one_le` (O5): `|F_{x,μ} - 1| ≤ βρ⁴/2`.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

variable {d ℓ : ℕ} [NeZero ℓ]

/-! ### Supports -/

/-- The supports of the terms: `B(x, 2R+1)` for a site term, `B(x, R+1)` for a bond term. -/
def frSupp (R : ℕ) : FRTerm d ℓ → Finset (Torus d ℓ)
  | Sum.inl x => Finset.univ.filter fun y => torusDist d ℓ x y ≤ 2 * R + 1
  | Sum.inr (x, _) => Finset.univ.filter fun y => torusDist d ℓ x y ≤ R + 1

/-- The ordinary values of one site: a small Gaussian variable on the upper sheet. -/
def frOrd (p : ℝ) : Set (perp h × Bool) := {w | ‖w.1‖ ≤ p ∧ w.2 = true}

theorem measurableSet_frOrd (p : ℝ) : MeasurableSet (frOrd h p) := by
  refine (measurableSet_le (measurable_norm.comp measurable_fst) measurable_const).inter ?_
  exact measurable_snd (measurableSet_singleton true)

omit [NeZero ℓ] in
theorem torusDist_self_eq (x : Torus d ℓ) : torusDist d ℓ x x = 0 := by
  unfold torusDist; simp [natAbs_cycRep_zero]

theorem torusDist_add_single_le_one (x : Torus d ℓ) (μ : Fin d) :
    torusDist d ℓ x (x + Pi.single μ 1) ≤ 1 := by
  unfold torusDist
  rw [Finset.sum_eq_single μ]
  · simp only [Pi.add_apply, Pi.single_eq_same, sub_add_cancel_left]
    have := natAbs_cycRep_le_of_cast (m := ℓ) (-1 : ZMod ℓ) (-1) (by simp)
    exact_mod_cast this
  · intro i _ hi
    simp [hi, natAbs_cycRep_zero]
  · simp

theorem mem_frSupp_inl_self (R : ℕ) (x : Torus d ℓ) : x ∈ frSupp R (Sum.inl x) := by
  simp [frSupp, torusDist_self_eq]; positivity

/-! ### Locality -/

/-- The whitened field at `x` depends on `ψ` in `B(x, R)`. -/
theorem frField_congr (β ν : ℝ) (R : ℕ) {ψ ψ' : Torus d ℓ → perp h} (x : Torus d ℓ)
    (hψ : ∀ y, torusDist d ℓ x y ≤ R → ψ y = ψ' y) :
    frField d ℓ β ν R ψ x = frField d ℓ β ν R ψ' x := by
  unfold frField matAct
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : torusDist d ℓ x y ≤ R
  · rw [hψ y hy]
  · have : kf0CR d ℓ ν R x y = 0 := kf0CR_eq_zero_of_lt (not_le.1 hy)
    simp [Matrix.smul_apply, this]

theorem frSite_congr (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (x : Torus d ℓ) {ω ω' : Torus d ℓ → perp h × Bool}
    (hω : ∀ y ∈ frSupp R (Sum.inl x), ω y = ω' y) :
    frSite h hh β ν ε R g x ω = frSite h hh β ν ε R g x ω' := by
  have hmem : ∀ y, torusDist d ℓ x y ≤ 2 * R + 1 → ω y = ω' y := fun y hy =>
    hω y (by simp [frSupp, hy])
  have hu : frField d ℓ β ν R (frPsi h ω) x = frField d ℓ β ν R (frPsi h ω') x :=
    frField_congr h β ν R x fun y hy => by
      simp only [frPsi]
      rw [hmem y (by linarith)]
  have hx : ω x = ω' x := hmem x (by rw [torusDist_self_eq]; positivity)
  have hQ : ∀ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E) =
      frQ d ℓ ν R x y * inner ℝ (frPsi h ω' x : E) (frPsi h ω' y : E) := by
    intro y
    by_cases hy : torusDist d ℓ x y ≤ 2 * R + 1
    · simp only [frPsi]; rw [hx, hmem y hy]
    · have : frQ d ℓ ν R x y = 0 := frQ_eq_zero_of_lt (by linarith)
      rw [this, zero_mul, zero_mul]
  unfold frSite
  simp only [frSig]
  rw [hu, hx, Finset.sum_congr rfl fun y _ => hQ y]

theorem frBond_congr (β ν : ℝ) (R : ℕ) (x : Torus d ℓ) (μ : Fin d)
    {ω ω' : Torus d ℓ → perp h × Bool} (hω : ∀ y ∈ frSupp R (Sum.inr (x, μ)), ω y = ω' y) :
    frBond h β ν R x μ ω = frBond h β ν R x μ ω' := by
  have hmem : ∀ y, torusDist d ℓ x y ≤ R + 1 → ω y = ω' y := fun y hy =>
    hω y (by simp [frSupp, hy])
  have h1 := torusDist_add_single_le_one x μ
  have hu : frField d ℓ β ν R (frPsi h ω) x = frField d ℓ β ν R (frPsi h ω') x :=
    frField_congr h β ν R x fun y hy => by
      simp only [frPsi]; rw [hmem y (by linarith)]
  have hu' : frField d ℓ β ν R (frPsi h ω) (x + Pi.single μ 1) =
      frField d ℓ β ν R (frPsi h ω') (x + Pi.single μ 1) :=
    frField_congr h β ν R _ fun y hy => by
      simp only [frPsi]
      rw [hmem y (by linarith [torusDist_triangle_gen x (x + Pi.single μ 1) y])]
  have hx : ω x = ω' x := hmem x (by rw [torusDist_self_eq]; positivity)
  have hx' : ω (x + Pi.single μ 1) = ω' (x + Pi.single μ 1) := hmem _ (by linarith)
  unfold frBond
  simp only [frSig]
  rw [hu, hu', hx, hx']

theorem frF_congr (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (t : FRTerm d ℓ) {ω ω' : Torus d ℓ → perp h × Bool} (hω : ∀ y ∈ frSupp R t, ω y = ω' y) :
    frF h hh β ν ε R g t ω = frF h hh β ν ε R g t ω' := by
  rcases t with x | ⟨x, μ⟩
  · exact frSite_congr h hh β ν ε R g x hω
  · exact frBond_congr h β ν R x μ hω

/-! ### Measurability -/

omit [NeZero ℓ] in
theorem measurable_frPsi : Measurable (frPsi (d := d) (ℓ := ℓ) h) :=
  measurable_pi_iff.2 fun x => measurable_fst.comp (measurable_pi_apply x)

omit [NeZero ℓ] in
theorem measurable_frSig_apply (x : Torus d ℓ) :
    Measurable fun ω : Torus d ℓ → perp h × Bool => frSig h ω x :=
  measurable_snd.comp (measurable_pi_apply x)

theorem measurable_sheetPt_frField (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (x : Torus d ℓ) :
    Measurable fun ω : Torus d ℓ → perp h × Bool =>
      ((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) := by
  have hu : Measurable fun ω : Torus d ℓ → perp h × Bool => frField d ℓ β ν R (frPsi h ω) x :=
    (measurable_pi_apply x).comp ((measurable_frField h β ν R).comp (measurable_frPsi h))
  have hp : Measurable fun ω : Torus d ℓ → perp h × Bool =>
      hemiPt h hh (frField d ℓ β ν R (frPsi h ω) x) :=
    (continuous_hemiPt h hh).measurable.comp hu
  have hset : MeasurableSet {ω : Torus d ℓ → perp h × Bool | frSig h ω x = true} :=
    measurable_frSig_apply h x (measurableSet_singleton true)
  unfold sheetPt
  exact measurable_subtype_coe.comp (Measurable.ite hset hp ((measurable_reflS h).comp hp))

theorem measurable_tN_frField (β ν : ℝ) (R : ℕ) (x : Torus d ℓ) :
    Measurable fun ω : Torus d ℓ → perp h × Bool => tN h (frField d ℓ β ν R (frPsi h ω) x) :=
  (measurable_tN h).comp ((measurable_pi_apply x).comp
    ((measurable_frField h β ν R).comp (measurable_frPsi h)))

omit [NeZero ℓ] in
theorem measurable_sgn_frSig (x : Torus d ℓ) :
    Measurable fun ω : Torus d ℓ → perp h × Bool => sgn (frSig h ω x) :=
  (measurable_from_top (f := sgn)).comp (measurable_frSig_apply h x)

theorem measurable_frF (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (t : FRTerm d ℓ) : Measurable (frF h hh β ν ε R g t) := by
  have hu : ∀ x, Measurable fun ω : Torus d ℓ → perp h × Bool =>
      frField d ℓ β ν R (frPsi h ω) x := fun x =>
    (measurable_pi_apply x).comp ((measurable_frField h β ν R).comp (measurable_frPsi h))
  rcases t with x | ⟨x, μ⟩
  · show Measurable (frSite h hh β ν ε R g x)
    unfold frSite
    have hb : Measurable fun ω : Torus d ℓ → perp h × Bool => bW ε (frSig h ω x) :=
      (measurable_from_top (f := bW ε)).comp (measurable_frSig_apply h x)
    have hw : Measurable fun ω : Torus d ℓ → perp h × Bool =>
        chartWeight h (frField d ℓ β ν R (frPsi h ω) x) := (measurable_chartWeight h).comp (hu x)
    have hs := measurable_sheetPt_frField h hh β ν R x
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact Complex.measurable_ofReal.comp ((hw.mul hb).mul (Real.measurable_exp.comp
        (measurable_const.mul (((measurable_sgn_frSig h x).mul
          (measurable_tN_frField h β ν R x)).sub_const 1 |>.pow_const 2))))
    · refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
      refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
      exact (measurable_pi_apply i).comp ((PiLp.continuous_ofLp 2 _).measurable.comp
        (hs.sub_const h))
    · refine Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (Finset.measurable_sum _ fun y _ => measurable_const.mul ?_)))
      exact (measurable_subtype_coe.comp ((measurable_pi_apply x).comp (measurable_frPsi h))).inner
        (measurable_subtype_coe.comp ((measurable_pi_apply y).comp (measurable_frPsi h)))
  · show Measurable (frBond h β ν R x μ)
    unfold frBond
    refine Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul ?_))
    exact (((measurable_sgn_frSig h _).mul (measurable_tN_frField h β ν R _)).sub
      ((measurable_sgn_frSig h x).mul (measurable_tN_frField h β ν R x))).pow_const 2

/-! ### Ordinary bounds -/

/-- On an ordinary support the whitened field is small. -/
theorem norm_frField_le_of_ord {β ν p ρ : ℝ} (hν : 0 < ν) (hp : 0 ≤ p) (R : ℕ)
    (hρ : (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) ≤ ρ) {ω : Torus d ℓ → perp h × Bool}
    (x : Torus d ℓ) (r : ℕ) (hr : R ≤ r)
    (hω : ∀ y, torusDist d ℓ x y ≤ r → ω y ∈ frOrd h p) :
    ‖frField d ℓ β ν R (frPsi h ω) x‖ ≤ ρ := by
  refine (norm_frField_le_of_small h hν hp R _ x fun y hy => ?_).trans hρ
  have := kf0CR_ne_zero_dist hy
  exact (hω y (this.trans (by exact_mod_cast hr))).1

/-- **(O5) The ordinary bound of a site term.** -/
theorem norm_frSite_sub_one_le (hh : ‖h‖ = 1) {β ν ε p ρ θ G : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    (hp : 0 ≤ p) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ)
    {ω : Torus d ℓ → perp h × Bool}
    (hρ : (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) ≤ ρ) (hρ2 : ρ ≤ 1 / 2)
    (hQ : ∑ y, |frQ d ℓ ν R x y| ≤ θ) (hg : ∑ i, ‖g x i‖ ≤ G)
    (hZ : β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2 ≤ 1)
    (hω : ∀ y ∈ frSupp R (Sum.inl x), ω y ∈ frOrd h p) :
    ‖frSite h hh β ν ε R g x ω - 1‖ ≤
      3 * (ρ ^ 2 + (β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2)) := by
  have hω' : ∀ y, torusDist d ℓ x y ≤ 2 * R + 1 → ω y ∈ frOrd h p := fun y hy =>
    hω y (by simp [frSupp, hy])
  set u := frField d ℓ β ν R (frPsi h ω) x with hudef
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hu : ‖u‖ ≤ ρ := norm_frField_le_of_ord h hν hp R hρ x (2 * R + 1) (by omega)
    fun y hy => hω' y (by exact_mod_cast hy)
  have hu2 : ‖u‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hband : ‖u‖ ^ 2 ≤ 1 / 4 := hu2.trans (by nlinarith)
  have hu1 : ‖u‖ < 1 := norm_lt_one_of_sq_le h hband
  have hxo := hω' x (by rw [torusDist_self_eq]; positivity)
  have hσ : frSig h ω x = true := hxo.2
  have hG0 : 0 ≤ G := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) hg
  have hθ0 : 0 ≤ θ := le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) hQ
  -- the exponent
  set z := frSiteExp h hh β ν R g x ω with hz
  have hz1 : ‖((-(β * ν / 2) * (sgn (frSig h ω x) * tN h u - 1) ^ 2 : ℝ) : ℂ)‖ ≤
      β * ν / 2 * ρ ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hσ]
    simp only [sgn, ite_true, one_mul]
    have h1 := one_sub_tN_le h hu1.le
    have h2 : 0 ≤ 1 - tN h u := by linarith [tN_le_one h u]
    have h3 : (tN h u - 1) ^ 2 ≤ ρ ^ 4 := by nlinarith
    rw [abs_of_nonpos (by have := mul_pos hβ hν; nlinarith [sq_nonneg (tN h u - 1)])]
    have := mul_pos hβ hν
    nlinarith
  have hz2 : ‖∑ i : Fin N, g x i *
      ((((sheetPt h hh (frSig h ω x) u : Sph) : E) - h) i : ℂ)‖ ≤ 2 * G * ρ := by
    have hΦ : ‖((sheetPt h hh (frSig h ω x) u : Sph) : E) - h‖ ≤ 2 * ρ := by
      rw [hσ]
      exact (norm_sheetPt_true_sub_le h hh hu1).trans (by linarith)
    calc _ ≤ ∑ i : Fin N, ‖g x i‖ * (2 * ρ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, Complex.norm_real]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (PiLp.norm_apply_le _ i).trans hΦ
      _ = (∑ i : Fin N, ‖g x i‖) * (2 * ρ) := by rw [Finset.sum_mul]
      _ ≤ G * (2 * ρ) := mul_le_mul_of_nonneg_right hg (by positivity)
      _ = 2 * G * ρ := by ring
  have hz3 : ‖((-(1 / 2) * ∑ y, frQ d ℓ ν R x y *
      inner ℝ (frPsi h ω x : E) (frPsi h ω y : E) : ℝ) : ℂ)‖ ≤ θ * p ^ 2 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)]
    have : |∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)| ≤ θ * p ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ y, |frQ d ℓ ν R x y| * p ^ 2 := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [abs_mul]
            by_cases hy : torusDist d ℓ x y ≤ 2 * R + 1
            · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              refine (abs_real_inner_le_norm _ _).trans ?_
              have h1 : ‖(frPsi h ω x : E)‖ ≤ p := by
                rw [Submodule.norm_coe]; exact hxo.1
              have h2 : ‖(frPsi h ω y : E)‖ ≤ p := by
                rw [Submodule.norm_coe]; exact (hω' y hy).1
              nlinarith [norm_nonneg (frPsi h ω x : E), norm_nonneg (frPsi h ω y : E)]
            · have : frQ d ℓ ν R x y = 0 := frQ_eq_zero_of_lt (by linarith)
              simp [this]
        _ = (∑ y, |frQ d ℓ ν R x y|) * p ^ 2 := by rw [Finset.sum_mul]
        _ ≤ θ * p ^ 2 := mul_le_mul_of_nonneg_right hQ (by positivity)
    linarith
  have hzle : ‖z‖ ≤ β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2 := by
    rw [hz]
    unfold frSiteExp
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hz1 hz2)) hz3)
  have hz1' : ‖z‖ ≤ 1 := hzle.trans hZ
  -- the chart weight
  have hw := abs_chartWeight_sub_one_le h hband
  have hbW : bW ε (frSig h ω x) = 1 := by rw [hσ]; rfl
  rw [frSite_eq, ← hz, ← hudef, hbW, mul_one]
  have hexp : ‖Complex.exp z‖ ≤ 3 := by
    rw [Complex.norm_exp]
    calc Real.exp z.re ≤ Real.exp 1 := Real.exp_le_exp.2 ((Complex.re_le_norm z).trans hz1')
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have e : ((chartWeight h u : ℝ) : ℂ) * Complex.exp z - 1 =
      ((chartWeight h u - 1 : ℝ) : ℂ) * Complex.exp z + (Complex.exp z - 1) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |chartWeight h u - 1| * ‖Complex.exp z‖ ≤ ρ ^ 2 * 3 :=
    mul_le_mul (hw.trans hu2) hexp (norm_nonneg _) (by positivity)
  have h2 := Complex.norm_exp_sub_one_le hz1'
  linarith [norm_nonneg z]

/-- **(O5) The ordinary bound of a bond term.** -/
theorem norm_frBond_sub_one_le {β ν p ρ : ℝ} (hβ : 0 ≤ β) (hν : 0 < ν) (hp : 0 ≤ p) (R : ℕ)
    (x : Torus d ℓ) (μ : Fin d) {ω : Torus d ℓ → perp h × Bool}
    (hρ : (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hω : ∀ y ∈ frSupp R (Sum.inr (x, μ)), ω y ∈ frOrd h p) :
    ‖frBond h β ν R x μ ω - 1‖ ≤ β * ρ ^ 4 / 2 := by
  have hω' : ∀ y, torusDist d ℓ x y ≤ R + 1 → ω y ∈ frOrd h p := fun y hy =>
    hω y (by simp [frSupp, hy])
  have h1 := torusDist_add_single_le_one x μ
  set e := x + Pi.single μ 1
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hux : ‖frField d ℓ β ν R (frPsi h ω) x‖ ≤ ρ :=
    norm_frField_le_of_ord h hν hp R hρ x (R + 1) (by omega) fun y hy => hω' y (by exact_mod_cast hy)
  have hue : ‖frField d ℓ β ν R (frPsi h ω) e‖ ≤ ρ :=
    norm_frField_le_of_ord h hν hp R hρ e R le_rfl fun y hy =>
      hω' y (by linarith [torusDist_triangle_gen x e y])
  have hσx : frSig h ω x = true := (hω' x (by rw [torusDist_self_eq]; positivity)).2
  have hσe : frSig h ω e = true := (hω' e (by linarith)).2
  -- the normal coordinates are within `ρ²` of `1`
  have ht : ∀ v : perp h, ‖v‖ ≤ ρ → 1 - ρ ^ 2 ≤ tN h v ∧ tN h v ≤ 1 := by
    intro v hv
    have hv1 : ‖v‖ ≤ 1 := hv.trans hρ1
    have := one_sub_tN_le h hv1
    have h2 : ‖v‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    exact ⟨by linarith, tN_le_one h v⟩
  obtain ⟨hx1, hx2⟩ := ht _ hux
  obtain ⟨he1, he2⟩ := ht _ hue
  unfold frBond
  rw [hσx, hσe]
  simp only [sgn, ite_true, one_mul]
  set a := (tN h (frField d ℓ β ν R (frPsi h ω) e) - tN h (frField d ℓ β ν R (frPsi h ω) x)) ^ 2
  have ha : a ≤ ρ ^ 4 := by
    have : |tN h (frField d ℓ β ν R (frPsi h ω) e) - tN h (frField d ℓ β ν R (frPsi h ω) x)| ≤
        ρ ^ 2 := by rw [abs_le]; constructor <;> linarith
    calc a = |tN h (frField d ℓ β ν R (frPsi h ω) e) -
          tN h (frField d ℓ β ν R (frPsi h ω) x)| ^ 2 := (sq_abs _).symm
      _ ≤ (ρ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ρ ^ 4 := by ring
  have ha0 : 0 ≤ a := sq_nonneg _
  have hle : Real.exp (-(β / 2) * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hge : 1 - β / 2 * a ≤ Real.exp (-(β / 2) * a) := by
    have := Real.add_one_le_exp (-(β / 2) * a); linarith
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  nlinarith

end

end Balaban.LargeField.KF0FR
