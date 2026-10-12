/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormPinSum
public import Balaban.SmallField.RenormTermwiseCrude
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# PIN-I6 §2: the one-site counterexample

For `m > 0` and `c ≥ 0` the one-site family `oneSite d N c m` (polymer `{0}`, distance `0`)
has the term
`f_m(p, b) = (c/m) [(p·p)(b·b) - (p·b)²] = (c/(2m)) Σ_{ij} (p_i b_j - p_j b_i)²`
(`p` the spin at the centre, `b` the source).  It is entire, `O(N)`-invariant (`oneSite_rot_inv`),
and vanishes to second order at the reference point `(e_{i₀}, m e_{i₀})` (all `w_{ij} = p_i b_j -
p_j b_i` vanish there), so its value and first jets vanish and the four renormalization conditions
hold (`oneSite_sumConds`, the moment because the polymer is a single site).  On the pinned chart
(`pinDom`) it has size `32 N² c m` (`oneSite_pinned_bound`, hence `≤ E₀` for
`c = E₀/(32 N²)`, `m ≤ 1`), but `D²_{b_⊥} f = 2c/m` at the reference (`D2_bperp`).

* `oneSite_hypotheses`: the geometric premises with the pinned bound, `SumConds`, `O(N)`
  invariance, `DataHypAniso` for the constant configuration of PIN-I6 (2.2), `D2_bperp`;
* `oneSite_itw`, `oneSite_itw_ge`: `Itw` equals the term, `|Itw| ≥ (9/64) c σ² ε²` (2.3);
* `pin_no_uniform_constant`: no uniform constant exists in the I-6 bound for the pinned-only
  class (the precise negation);
* `pin_jet_fails`: hence the certificate `PinJetTerm` fails for this family.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem quad_eq_w (p q : Spin N) :
    dot p p * dot q q - dot p q ^ 2 =
      (1 / 2 : ℂ) * ∑ i, ∑ j, (p i * q j - p j * q i) ^ 2 := by
  have h1 : ∑ i, ∑ j, (p i) ^ 2 * (q j) ^ 2 = dot p p * dot q q := by
    simp only [dot, Finset.sum_mul_sum, sq]
  have h2 : ∑ i, ∑ j, (p j) ^ 2 * (q i) ^ 2 = dot p p * dot q q := by
    rw [Finset.sum_comm]; exact h1
  have h3 : ∑ i, ∑ j, (p i * q i) * (p j * q j) = dot p q ^ 2 := by
    simp only [dot, sq, Finset.sum_mul_sum]
  have : ∀ i j, (p i * q j - p j * q i) ^ 2 =
      (p i) ^ 2 * (q j) ^ 2 + (p j) ^ 2 * (q i) ^ 2 - 2 * ((p i * q i) * (p j * q j)) := by
    intro i j; ring
  have h4 : ∑ i, ∑ j, 2 * ((p i * q i) * (p j * q j)) = 2 * dot p q ^ 2 := by
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2, h4]
  ring


/-- aggregated spin of a configuration -/
def pcfg (X : Finset (Site d)) (c : Cfg d N X) : Spin N := fun i => ∑ x : ↥X, c (Sum.inl (x, i))
def bcfg (X : Finset (Site d)) (c : Cfg d N X) : Spin N := fun i => c (Sum.inr i)

noncomputable def quadCfg (X : Finset (Site d)) (c : Cfg d N X) : ℂ :=
  dot (pcfg X c) (pcfg X c) * dot (bcfg X c) (bcfg X c) - dot (pcfg X c) (bcfg X c) ^ 2

noncomputable def wCfg (X : Finset (Site d)) (i j : Fin N) (c : Cfg d N X) : ℂ :=
  pcfg X c i * bcfg X c j - pcfg X c j * bcfg X c i

noncomputable def oneSite (d N : ℕ) (c m : ℝ) : TermFamily d N where
  polys := {{0}}
  dist := fun _ => 0
  term := fun X cfg => ((c / m : ℝ) : ℂ) * quadCfg X cfg

theorem quadCfg_eq_w (X : Finset (Site d)) (c : Cfg d N X) :
    quadCfg X c = (1 / 2 : ℂ) * ∑ i, ∑ j, wCfg X i j c ^ 2 := quad_eq_w _ _

theorem pcfg_rot (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X) :
    pcfg X (rotCfgL R X c) = R.mulVec (pcfg X c) := by
  funext i
  simp only [pcfg, rotCfgL, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Matrix.mulVec,
    dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

theorem bcfg_rot (R : Matrix (Fin N) (Fin N) ℂ) (X : Finset (Site d)) (c : Cfg d N X) :
    bcfg X (rotCfgL R X c) = R.mulVec (bcfg X c) := by
  funext i
  simp [bcfg, rotCfgL, Matrix.mulVec, dotProduct]

theorem quadCfg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (X : Finset (Site d))
    (c : Cfg d N X) : quadCfg X (rotCfgL R X c) = quadCfg X c := by
  unfold quadCfg
  rw [pcfg_rot, bcfg_rot, dot_mulVec_rot hR, dot_mulVec_rot hR, dot_mulVec_rot hR]

theorem pcfg_pack_zero (ψ : Site d → Spin N) (b : Spin N) :
    pcfg ({0} : Finset (Site d)) (pack {0} ψ b) = ψ 0 := by
  funext i
  simp [pcfg, pack]

theorem bcfg_pack (X : Finset (Site d)) (ψ : Site d → Spin N) (b : Spin N) :
    bcfg X (pack X ψ b) = b := rfl


theorem pcfg_refPt (i₀ : Fin N) (ν : ℝ) :
    pcfg ({0} : Finset (Site d)) (refPt i₀ ν {0}) = Pi.single i₀ 1 := pcfg_pack_zero _ _

theorem bcfg_refPt (X : Finset (Site d)) (i₀ : Fin N) (ν : ℝ) :
    bcfg X (refPt i₀ ν X) = (ν : ℂ) • Pi.single i₀ 1 := rfl

theorem wCfg_refPt (i₀ : Fin N) (ν : ℝ) (i j : Fin N) :
    wCfg ({0} : Finset (Site d)) i j (refPt i₀ ν {0}) = 0 := by
  rw [wCfg, pcfg_refPt, bcfg_refPt]
  by_cases hi : i = i₀ <;> by_cases hj : j = i₀ <;> simp [hi, hj]

theorem differentiable_pcfg_apply (X : Finset (Site d)) (i : Fin N) :
    Differentiable ℂ (fun c : Cfg d N X => pcfg X c i) := by
  unfold pcfg; fun_prop

theorem differentiable_bcfg_apply (X : Finset (Site d)) (i : Fin N) :
    Differentiable ℂ (fun c : Cfg d N X => bcfg X c i) := by
  unfold bcfg; fun_prop

theorem differentiable_wCfg (X : Finset (Site d)) (i j : Fin N) :
    Differentiable ℂ (wCfg X i j) := by
  unfold wCfg
  exact ((differentiable_pcfg_apply X i).mul (differentiable_bcfg_apply X j)).sub
    ((differentiable_pcfg_apply X j).mul (differentiable_bcfg_apply X i))

theorem differentiable_quadCfg (X : Finset (Site d)) : Differentiable ℂ (quadCfg (N := N) X) := by
  have : quadCfg (N := N) X = fun c => (1 / 2 : ℂ) * ∑ i, ∑ j, wCfg X i j c ^ 2 := funext (quadCfg_eq_w X)
  rw [this]
  refine (differentiable_const _).mul ?_
  refine Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => ?_
  exact (differentiable_wCfg X i j).pow 2

theorem differentiable_oneSite (c m : ℝ) (X : Finset (Site d)) :
    Differentiable ℂ ((oneSite d N c m).term X) :=
  (differentiable_const _).mul (differentiable_quadCfg X)

/-- The first derivative of the quadratic form at a point where all `w i j` vanish is zero. -/
theorem hasFDerivAt_quadCfg_zero {c : Cfg d N ({0} : Finset (Site d))}
    (hc : ∀ i j, wCfg {0} i j c = 0) : HasFDerivAt (𝕜 := ℂ) (quadCfg (N := N) ({0} : Finset (Site d))) 0 c := by
  have : quadCfg (N := N) ({0} : Finset (Site d)) = fun c => (1 / 2 : ℂ) * ∑ i, ∑ j, wCfg {0} i j c ^ 2 :=
    funext (quadCfg_eq_w _)
  rw [this]
  have h2 : ∀ i j, HasFDerivAt (𝕜 := ℂ) (fun c => wCfg ({0} : Finset (Site d)) i j c ^ 2) 0 c := by
    intro i j
    have hw := (differentiable_wCfg ({0} : Finset (Site d)) i j c).hasFDerivAt
    have h := hw.mul hw
    have e : (fun c => wCfg ({0} : Finset (Site d)) i j c ^ 2) =
        (wCfg ({0} : Finset (Site d)) i j * wCfg ({0} : Finset (Site d)) i j) := by
      funext x; simp [sq]
    rw [e]
    refine h.congr_fderiv ?_
    ext v; simp [hc i j]
  have h3 : HasFDerivAt (𝕜 := ℂ) (fun c => ∑ i, ∑ j, wCfg ({0} : Finset (Site d)) i j c ^ 2) 0 c := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => h2 i j))
    simpa using this
  exact (h3.const_mul (1 / 2 : ℂ)).congr_fderiv (by ext v; simp)


theorem analyticAt_pi_apply_pin {ι : Type*} [Fintype ι] (j : ι) (x : ι → ℂ) :
    AnalyticAt ℂ (fun c : ι → ℂ => c j) x :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt x

theorem analyticAt_wCfg (X : Finset (Site d)) (i j : Fin N) (x : Cfg d N X) :
    AnalyticAt ℂ (wCfg X i j) x := by
  have hp : ∀ i : Fin N, AnalyticAt ℂ (fun c : Cfg d N X => pcfg X c i) x := fun i =>
    Finset.analyticAt_fun_sum _ fun y _ => analyticAt_pi_apply_pin (Sum.inl (y, i)) x
  have hb : ∀ i : Fin N, AnalyticAt ℂ (fun c : Cfg d N X => bcfg X c i) x := fun i =>
    analyticAt_pi_apply_pin (Sum.inr i) x
  exact ((hp i).mul (hb j)).sub ((hp j).mul (hb i))

theorem analyticAt_oneSite (c m : ℝ) (X : Finset (Site d)) (x : Cfg d N X) :
    AnalyticAt ℂ ((oneSite d N c m).term X) x := by
  have : (oneSite d N c m).term X =
      fun cfg => ((c / m : ℝ) : ℂ) * ((1 / 2 : ℂ) * ∑ i, ∑ j, wCfg X i j cfg ^ 2) := by
    funext cfg; show _ * quadCfg X cfg = _; rw [quadCfg_eq_w]
  rw [this]
  refine analyticAt_const.mul (analyticAt_const.mul ?_)
  exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ =>
    (analyticAt_wCfg X i j x).pow 2

section Family

variable {c m : ℝ} {i₀ i₁ : Fin N}

theorem oneSite_polys {X : Finset (Site d)} (hX : X ∈ (oneSite d N c m).polys) :
    X = {0} := Set.mem_singleton_iff.mp hX

theorem term_ref_zero (i₀ : Fin N) (ν : ℝ) :
    (oneSite d N c m).term {0} (refPt i₀ ν {0}) = 0 := by
  show ((c / m : ℝ) : ℂ) * quadCfg _ _ = 0
  rw [quadCfg_eq_w]; simp [wCfg_refPt]

theorem fderiv_ref_zero (i₀ : Fin N) (ν : ℝ) :
    fderiv ℂ ((oneSite d N c m).term {0}) (refPt i₀ ν {0}) = 0 := by
  have h := (hasFDerivAt_quadCfg_zero (c := refPt i₀ ν ({0} : Finset (Site d)))
    (wCfg_refPt i₀ ν)).const_mul (((c / m : ℝ) : ℂ))
  exact (h.congr_fderiv (by ext v; simp)).fderiv

theorem oneSite_sumConds (i₀ i₁ : Fin N) (ν : ℝ) : SumConds (oneSite d N c m) i₀ i₁ ν := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (tsum_congr fun X => ?_).trans tsum_zero
    rcases X with ⟨X, hX⟩
    obtain rfl := oneSite_polys hX
    exact term_ref_zero i₀ ν
  · refine (tsum_congr fun X => ?_).trans tsum_zero
    rcases X with ⟨X, hX⟩
    obtain rfl := oneSite_polys hX
    simp [fderiv_ref_zero]
  · refine (tsum_congr fun X => ?_).trans tsum_zero
    rcases X with ⟨X, hX⟩
    obtain rfl := oneSite_polys hX
    simp [tensA, fderiv_ref_zero]
  · refine (tsum_congr fun X => ?_).trans tsum_zero
    rcases X with ⟨X, hX⟩
    obtain rfl := oneSite_polys hX
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
    have h1 := Finset.mem_singleton.mp x.2
    have h2 := Finset.mem_singleton.mp x'.2
    simp [h1, h2]

theorem oneSite_rot_inv {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (X : Finset (Site d))
    (cfg : Cfg d N X) :
    (oneSite d N c m).term X (rotCfgL R X cfg) = (oneSite d N c m).term X cfg := by
  show ((c / m : ℝ) : ℂ) * quadCfg X _ = ((c / m : ℝ) : ℂ) * quadCfg X _
  rw [quadCfg_rot hR]


theorem quad_line (hne : i₀ ≠ i₁) (ν : ℝ) (t : ℂ) :
    quadCfg ({0} : Finset (Site d))
      (refPt i₀ ν {0} + t • (Pi.single (Sum.inr i₁) 1 : Cfg d N {0})) = t ^ 2 := by
  have hp : pcfg ({0} : Finset (Site d))
      (refPt i₀ ν {0} + t • (Pi.single (Sum.inr i₁) 1 : Cfg d N {0})) = Pi.single i₀ 1 := by
    funext i
    simp [pcfg, refPt, pack]
  have hb : bcfg ({0} : Finset (Site d))
      (refPt i₀ ν {0} + t • (Pi.single (Sum.inr i₁) 1 : Cfg d N {0})) =
      (ν : ℂ) • (Pi.single i₀ 1 : Spin N) + t • (Pi.single i₁ 1 : Spin N) := by
    funext i
    by_cases h : i = i₁
    · subst h
      simp [bcfg, refPt, pack, Pi.single_apply, hne.symm]
    · simp [bcfg, refPt, pack, Pi.single_apply, h]
  unfold quadCfg
  rw [hp, hb]
  simp only [dot_add_right, dot_smul_right, dot_single_right]
  simp [hne, hne.symm]
  ring

theorem D2_bperp (hne : i₀ ≠ i₁) :
    D2 ((oneSite d N c m).term {0}) (refPt i₀ m {0}) (Pi.single (Sum.inr i₁) 1)
      (Pi.single (Sum.inr i₁) 1) = ((2 * c / m : ℝ) : ℂ) := by
  have han : AnalyticOnNhd ℂ ((oneSite d N c m).term {0}) (ball (refPt i₀ m ({0} : Finset (Site d))) 1) :=
    fun x _ => analyticAt_oneSite c m _ x
  rw [← iteratedDeriv_two_line one_pos han]
  have : (fun t : ℂ => (oneSite d N c m).term {0}
      (refPt i₀ m {0} + t • (Pi.single (Sum.inr i₁) 1 : Cfg d N {0}))) =
      fun t : ℂ => ((c / m : ℝ) : ℂ) * t ^ 2 := by
    funext t
    show ((c / m : ℝ) : ℂ) * quadCfg _ _ = _
    rw [quad_line hne]
  rw [this]
  simp
  ring


/-- The pinned chart of the counterexample: spins bounded by `2`, source bounded by `2 m`
(`b = m h`, `‖h‖ ≤ 2`). -/
def pinDom (d N : ℕ) (m : ℝ) : Set ((Site d → Spin N) × Spin N) :=
  {q | (∀ x, ‖q.1 x‖ ≤ 2) ∧ ‖q.2‖ ≤ 2 * m}

/-- **The pinned bound**: on the pinned chart the family has size `32 N² c m`. -/
theorem oneSite_pinned_bound (hm : 0 < m) (hc : 0 ≤ c) {q : (Site d → Spin N) × Spin N}
    (hq : q ∈ pinDom d N m) :
    ‖(oneSite d N c m).term {0} (pack {0} q.1 q.2)‖ ≤ 32 * (N : ℝ) ^ 2 * c * m := by
  obtain ⟨hp, hb⟩ := hq
  show ‖((c / m : ℝ) : ℂ) * quadCfg _ _‖ ≤ _
  unfold quadCfg
  rw [pcfg_pack_zero, bcfg_pack]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : ‖dot (q.1 0) (q.1 0)‖ ≤ N * (2 * 2) :=
    (norm_dot_le _ _).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hp 0) (hp 0) (norm_nonneg _) (by norm_num)) hN)
  have h2 : ‖dot q.2 q.2‖ ≤ N * (2 * m * (2 * m)) :=
    (norm_dot_le _ _).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hb hb (norm_nonneg _) (by positivity)) hN)
  have h3 : ‖dot (q.1 0) q.2‖ ≤ N * (2 * (2 * m)) :=
    (norm_dot_le _ _).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul (hp 0) hb (norm_nonneg _) (by norm_num)) hN)
  have hq : ‖dot (q.1 0) (q.1 0) * dot q.2 q.2 - dot (q.1 0) q.2 ^ 2‖ ≤
      32 * (N : ℝ) ^ 2 * m ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_pow]
    have e1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have e2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith
  rw [norm_mul]
  have hcm : ‖((c / m : ℝ) : ℂ)‖ = c / m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hc hm.le)]
  rw [hcm]
  calc c / m * ‖dot (q.1 0) (q.1 0) * dot q.2 q.2 - dot (q.1 0) q.2 ^ 2‖
      ≤ c / m * (32 * (N : ℝ) ^ 2 * m ^ 2) :=
        mul_le_mul_of_nonneg_left hq (div_nonneg hc hm.le)
    _ = _ := by field_simp


/-- The geometric premises hold for the one-site family with the pinned bound `E₀`. -/
theorem oneSite_premisesGeom (hN : i₀ ≠ i₁) (hm : 0 < m) (hm1 : m ≤ 1) (hc : 0 ≤ c)
    {E₀ : ℝ} (hcE : 32 * (N : ℝ) ^ 2 * c ≤ E₀) (κ A K₀ : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K₀) :
    PremisesGeom (oneSite d N c m) i₀ i₁ E₀ κ A K₀ (pinDom d N m) := by
  have hpol : ∀ X ∈ (oneSite d N c m).polys, X = {0} := fun X hX => oneSite_polys hX
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX; rw [hpol X hX]; simp
  · intro X _; exact le_rfl
  · intro X hX x hx
    rw [hpol X hX, Finset.mem_singleton] at hx
    subst hx
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, Int.cast_zero]
    show (0 : ℝ) ≤ A * (1 + 0)
    linarith
  · have : Finite ↥(oneSite d N c m).polys := (Set.finite_singleton _).to_subtype
    exact Summable.of_finite
  · have hfin : Finite ↥(oneSite d N c m).polys := Set.finite_singleton _ |>.to_subtype
    have e : (∑' X : ↥(oneSite d N c m).polys, wt κ X.1 ((oneSite d N c m).dist X.1)) =
        wt κ ({0} : Finset (Site d)) 0 :=
      tsum_singleton (({0} : Finset (Site d))) (fun X => wt κ X 0)
    rw [e]
    simp [wt, hK]
  · intro X hX q hq
    rw [hpol X hX]
    refine (oneSite_pinned_bound hm hc hq).trans ?_
    have hd : (oneSite d N c m).dist ({0} : Finset (Site d)) = 0 := rfl
    rw [hd]
    simp only [mul_zero, Real.exp_zero, mul_one]
    calc 32 * (N : ℝ) ^ 2 * c * m ≤ E₀ * 1 := by
          have h0 : 0 ≤ 32 * (N : ℝ) ^ 2 * c := by positivity
          nlinarith
      _ = E₀ := mul_one _

end Family


/-- The spin `a e_{i₀} + s e_{i₁}`. -/
noncomputable def spin2 (i₀ i₁ : Fin N) (a s : ℝ) : Spin N :=
  (a : ℂ) • Pi.single i₀ 1 + (s : ℂ) • Pi.single i₁ 1

/-- The constant spin `cos θ e_{i₀} + sin θ e_{i₁}`. -/
noncomputable def spinTheta (i₀ i₁ : Fin N) (θ : ℝ) : Spin N := spin2 i₀ i₁ (Real.cos θ) (Real.sin θ)

/-- The source `m e_{i₀}`. -/
noncomputable def srcRef (i₀ : Fin N) (m : ℝ) : Spin N := (m : ℂ) • Pi.single i₀ 1

section Itw

variable {c m : ℝ} {i₀ i₁ : Fin N}

theorem dot_spin2_self (hne : i₀ ≠ i₁) (a s : ℝ) :
    dot (spin2 i₀ i₁ a s) (spin2 i₀ i₁ a s) = (a : ℂ) ^ 2 + (s : ℂ) ^ 2 := by
  unfold spin2
  simp only [dot_add_right, dot_smul_right, dot_single_right]
  simp [hne, hne.symm]
  ring

theorem dot_spin2_src (hne : i₀ ≠ i₁) (a s m : ℝ) :
    dot (spin2 i₀ i₁ a s) (srcRef i₀ m) = (m : ℂ) * (a : ℂ) := by
  unfold spin2 srcRef
  simp only [dot_add_left, dot_smul_left, dot_single_left]
  simp [hne.symm]
  ring

theorem dot_src_self (m : ℝ) (i₀ : Fin N) : dot (srcRef i₀ m) (srcRef i₀ m) = (m : ℂ) ^ 2 := by
  unfold srcRef
  simp only [dot_smul_right, dot_single_right]
  simp
  ring

theorem oneSite_term_data (hne : i₀ ≠ i₁) (hm : m ≠ 0) (a s : ℝ) (has : a ^ 2 + s ^ 2 = 1) :
    (oneSite d N c m).term {0} (pack {0} (fun _ => spin2 i₀ i₁ a s) (srcRef i₀ m)) =
      ((c * m * s ^ 2 : ℝ) : ℂ) := by
  show ((c / m : ℝ) : ℂ) * quadCfg _ _ = _
  unfold quadCfg
  rw [pcfg_pack_zero, bcfg_pack, dot_spin2_self hne, dot_spin2_src hne, dot_src_self]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h' : (a : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast has
  push_cast
  field_simp
  rw [h']
  linear_combination (-(c : ℂ)) * h'

/-- **The one-site `Itw` is the term itself**: all reference jets vanish and the spin is
constant. -/
theorem oneSite_itw (hne : i₀ ≠ i₁) (hm : m ≠ 0) (a s : ℝ) (has : a ^ 2 + s ^ 2 = 1) :
    Itw (oneSite d N c m) i₀ i₁ m {0} (fun _ => spin2 i₀ i₁ a s) (srcRef i₀ m) =
      ((c * m * s ^ 2 : ℝ) : ℂ) := by
  unfold Itw
  rw [oneSite_term_data hne hm a s has]
  have h1 : Ttw (oneSite d N c m) i₀ m {0} (fun _ => spin2 i₀ i₁ a s) (srcRef i₀ m) = 0 := by
    unfold Ttw
    simp [term_ref_zero, tensA, fderiv_ref_zero]
  have h2 : Ax (oneSite d N c m) i₀ m (fun _ => spin2 i₀ i₁ a s) {0} = 0 := by
    unfold Ax
    simp [tensA, fderiv_ref_zero]
  have h3 : Phitw (oneSite d N c m) i₀ i₁ m {0} (fun _ => spin2 i₀ i₁ a s) = 0 := by
    unfold Phitw gradInv
    simp [dot]
  rw [h1, h2, h3]; ring

end Itw


section Data

variable {i₀ i₁ : Fin N}

theorem norm_spin2_le (a s : ℝ) (ha : |a| ≤ 1) (hs : |s| ≤ 1) : ‖spin2 i₀ i₁ a s‖ ≤ 2 := by
  unfold spin2
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Pi.norm_single, Pi.norm_single, norm_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  linarith

theorem src_close_spin2 (hne : i₀ ≠ i₁) (a s m B : ℝ) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (ha : |1 - a| ≤ B) (hs : |s| ≤ B) :
    ‖srcRef i₀ m - (m : ℂ) • spin2 i₀ i₁ a s‖ ≤ m * B := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have : (srcRef i₀ m - (m : ℂ) • spin2 i₀ i₁ a s) i =
      (m : ℂ) * (((1 - a : ℝ) : ℂ) * (Pi.single i₀ 1 : Spin N) i -
        ((s : ℝ) : ℂ) * (Pi.single i₁ 1 : Spin N) i) := by
    simp [srcRef, spin2]
    ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
  refine mul_le_mul_of_nonneg_left ?_ hm
  by_cases h0' : i = i₀
  · subst h0'
    have : i ≠ i₁ := hne
    simp [this]
    have e : ‖(1 : ℂ) - a‖ = |1 - a| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e]; exact ha
  · by_cases h1' : i = i₁
    · subst h1'
      simp [h0']
      exact hs
    · simp [h0', h1']
      exact hB

theorem cos_sin_close {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) :
    |1 - Real.cos θ| ≤ θ ∧ |Real.sin θ| ≤ θ := by
  have hc : 1 - Real.cos θ ≤ θ := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    nlinarith
  have hc0 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hs : Real.sin θ ≤ θ := Real.sin_le h0.le
  have hs0 : 0 ≤ Real.sin θ := by
    have := Real.sin_gt_sub_cube h0
    nlinarith [sq_nonneg θ, mul_pos h0 h0]
  exact ⟨by rw [abs_of_nonneg hc0]; exact hc, by rw [abs_of_nonneg hs0]; exact hs⟩


theorem norm_srcRef (i₀ : Fin N) {m : ℝ} (hm : 0 ≤ m) : ‖srcRef i₀ m‖ = m := by
  unfold srcRef
  rw [norm_smul, Pi.norm_single, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm,
    mul_one]

theorem uInv_spinTheta (hne : i₀ ≠ i₁) (θ : ℝ) :
    uInv (fun _ : Site d => spinTheta i₀ i₁ θ) = 1 := by
  unfold uInv spinTheta
  have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [dot_spin2_self hne, h]
  exact sqrtC_eq (by ring) (by simp)

/-- **The data of the counterexample satisfy the anisotropic data hypotheses**
(`DataHypAniso`) on the pinned chart: the constant spin `cos θ e_{i₀} + sin θ e_{i₁}`,
`θ = ε/2`, and the source `σ² e_{i₀}`. -/
theorem oneSite_dataHyp (hne : i₀ ≠ i₁) {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    DataHypAniso (pinDom d N (σ ^ 2)) (σ ^ 2) σ ε 0
      (fun _ : Site d => spinTheta i₀ i₁ (ε / 2)) (srcRef i₀ (σ ^ 2)) := by
  have hθ0 : 0 < ε / 2 := by positivity
  have hθ1 : ε / 2 ≤ 1 := by linarith
  obtain ⟨hc, hs⟩ := cos_sin_close hθ0 hθ1
  have hm0 : 0 ≤ σ ^ 2 := by positivity
  have hτ : 0 ≤ σ ^ 2 * ε := by positivity
  have hmem : ((fun _ : Site d => spinTheta i₀ i₁ (ε / 2)), srcRef i₀ (σ ^ 2)) ∈
      pinDom d N (σ ^ 2) := by
    refine ⟨fun x => norm_spin2_le _ _ (Real.abs_cos_le_one _) (Real.abs_sin_le_one _), ?_⟩
    rw [norm_srcRef i₀ hm0]; linarith
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_, ?_, hmem, hmem⟩, ?_⟩
  · intro x
    have h : (Real.cos (ε / 2) : ℂ) ^ 2 + (Real.sin (ε / 2) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq _
    show ‖dot (spinTheta i₀ i₁ (ε / 2)) (spinTheta i₀ i₁ (ε / 2)) - 1‖ ≤ _
    unfold spinTheta
    rw [dot_spin2_self hne, h]; simpa using hτ
  · exact norm_spin2_le _ _ (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  · intro x μ; simp only [sub_self, norm_zero]; positivity
  · have := src_close_spin2 (i₀ := i₀) hne (Real.cos (ε / 2)) (Real.sin (ε / 2)) (σ ^ 2) (ε / 2)
      hm0 hθ0.le hc hs
    refine this.trans ?_
    nlinarith
  · intro x μ μ'; simp
  · have hu := uInv_spinTheta (d := d) hne (ε / 2)
    show ‖vInv (fun _ : Site d => spinTheta i₀ i₁ (ε / 2)) (srcRef i₀ (σ ^ 2)) - ((σ ^ 2 : ℝ) : ℂ)‖
      ≤ _
    unfold vInv
    rw [hu, div_one]
    unfold spinTheta
    rw [dot_spin2_src hne]
    have e : (((σ ^ 2 : ℝ) : ℂ)) * (Real.cos (ε / 2) : ℂ) - ((σ ^ 2 : ℝ) : ℂ) =
        (((σ ^ 2 : ℝ) * (Real.cos (ε / 2) - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0]
    have h2 := Real.one_sub_sq_div_two_le_cos (x := ε / 2)
    have h3 : |Real.cos (ε / 2) - 1| = 1 - Real.cos (ε / 2) := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [Real.cos_le_one (ε / 2)])
    rw [h3]
    have : 1 - Real.cos (ε / 2) ≤ ε ^ 2 := by nlinarith
    nlinarith

end Data


section Final

variable {i₀ i₁ : Fin N}

/-- **The lower bound (2.3)**: `|Itw| ≥ (9/64) c σ² ε²` at the constant configuration. -/
theorem oneSite_itw_ge (hne : i₀ ≠ i₁) {c m ε : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (9 / 64) * c * m * ε ^ 2 ≤
      ‖Itw (oneSite d N c m) i₀ i₁ m {0} (fun _ : Site d => spinTheta i₀ i₁ (ε / 2))
        (srcRef i₀ m)‖ := by
  unfold spinTheta
  rw [oneSite_itw hne hm.ne' _ _ (Real.cos_sq_add_sin_sq _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hθ0 : 0 < ε / 2 := by positivity
  have h := Real.sin_gt_sub_cube hθ0
  have h1 : 3 / 4 * (ε / 2) ≤ Real.sin (ε / 2) := by nlinarith [sq_nonneg ε, mul_pos hε hε]
  have h2 : (3 / 4 * (ε / 2)) ^ 2 ≤ Real.sin (ε / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have : 0 ≤ c * m := by positivity
  nlinarith

/-- **Counterexample (PIN-I6 §2): the one-site family satisfies every hypothesis of the I-6
data/geometry package except bounded analyticity on `TubeAniso`.**  With `c = E₀/(32 N²)` and
`m = σ² ≤ 1`: the geometric premises with the pinned bound `E₀`, the four renormalization
conditions, `O(N)` invariance, the data hypotheses `DataHypAniso`, and the transverse source
second derivative `D²_{b_⊥} f = 2c/m` at the reference point. -/
theorem oneSite_hypotheses (hne : i₀ ≠ i₁) {E₀ : ℝ} (hE : 0 < E₀) {σ ε : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (κ A K₀ : ℝ) (hA : 0 ≤ A) (hK : 1 ≤ K₀) :
    PremisesGeom (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)) i₀ i₁ E₀ κ A K₀
        (pinDom d N (σ ^ 2)) ∧
      SumConds (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)) i₀ i₁ (σ ^ 2) ∧
      (∀ (R : Matrix (Fin N) (Fin N) ℂ), IsOrth R → ∀ (X : Finset (Site d)) (cfg : Cfg d N X),
        (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)).term X (rotCfgL R X cfg) =
          (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)).term X cfg) ∧
      DataHypAniso (pinDom d N (σ ^ 2)) (σ ^ 2) σ ε 0
        (fun _ : Site d => spinTheta i₀ i₁ (ε / 2)) (srcRef i₀ (σ ^ 2)) ∧
      D2 ((oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)).term {0}) (refPt i₀ (σ ^ 2) {0})
          (Pi.single (Sum.inr i₁) 1) (Pi.single (Sum.inr i₁) 1) =
        ((2 * (E₀ / (32 * (N : ℝ) ^ 2)) / σ ^ 2 : ℝ) : ℂ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  have hc : 0 ≤ E₀ / (32 * (N : ℝ) ^ 2) := by positivity
  have hm : 0 < σ ^ 2 := by positivity
  have hm1 : σ ^ 2 ≤ 1 := by nlinarith
  refine ⟨oneSite_premisesGeom hne hm hm1 hc (E₀ := E₀) (by
      rw [mul_div_cancel₀ _ (by positivity)]) κ A K₀ hA hK, oneSite_sumConds i₀ i₁ _,
    fun R hR X cfg => oneSite_rot_inv hR X cfg, oneSite_dataHyp hne hσ hε hε1,
    D2_bperp hne⟩

/-- **PIN-I6 §2, the precise negation.**  Fix `E₀ > 0`, `0 < α₁ < 1` and the scales
`0 < ε ≤ r ≤ 1`, `ε ≤ 1/4`.  There is no constant `C` such that, for all `0 < σ ≤ 1`,
the one-site family with `c = E₀/(32 N²)`, `m = ν = σ²` obeys the I-6 termwise bound
`‖Itw‖ ≤ C E₀ σ^{3-α₁} (ε/r)²` at the constant configuration `ψ ≡ cos(ε/2) e_{i₀} + sin(ε/2) e_{i₁}`,
`b = σ² e_{i₀}`, although all the data and sum hypotheses hold
(`oneSite_hypotheses`). -/
theorem pin_no_uniform_constant (hne : i₀ ≠ i₁) {E₀ α₁ r ε : ℝ} (hE : 0 < E₀) (hα1 : α₁ < 1)
    (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ¬ ∃ C : ℝ, ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ‖Itw (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)) i₀ i₁ (σ ^ 2) {0}
          (fun _ : Site d => spinTheta i₀ i₁ (ε / 2)) (srcRef i₀ (σ ^ 2))‖ ≤
        C * E₀ * (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  rintro ⟨C, hC⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  set K : ℝ := 9 / (64 * 32 * (N : ℝ) ^ 2) with hK
  have hK0 : 0 < K := by positivity
  set q : ℝ := 1 - α₁ with hq
  have hq0 : 0 < q := by linarith
  -- the inequality for every σ
  have key : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → K * r ^ 2 ≤ C * σ ^ q := by
    intro σ hσ hσ1
    have h1 := oneSite_itw_ge (d := d) (N := N) hne (c := E₀ / (32 * (N : ℝ) ^ 2)) (m := σ ^ 2)
      (by positivity) (by positivity) hε (by linarith)
    have h2 := hC σ hσ hσ1
    have h3 : σ ^ (3 - α₁) = σ ^ 2 * σ ^ q := by
      rw [hq, show (3 : ℝ) - α₁ = 2 + (1 - α₁) by ring, Real.rpow_add hσ]
      norm_cast
    have h4 := h1.trans h2
    rw [h3] at h4
    have hεr : 0 < ε ^ 2 := by positivity
    have e1 : 9 / 64 * (E₀ / (32 * (N : ℝ) ^ 2)) * σ ^ 2 * ε ^ 2 =
        K * E₀ * σ ^ 2 * ε ^ 2 := by rw [hK]; field_simp
    have e2 : C * E₀ * (σ ^ 2 * σ ^ q * (ε / r) ^ 2) =
        (C * σ ^ q) * E₀ * σ ^ 2 * ε ^ 2 / r ^ 2 := by field_simp
    rw [e1, e2] at h4
    have hpos : 0 < E₀ * σ ^ 2 * ε ^ 2 := by positivity
    have h5 : K * r ^ 2 * (E₀ * σ ^ 2 * ε ^ 2) ≤ (C * σ ^ q) * (E₀ * σ ^ 2 * ε ^ 2) := by
      have hr2 : 0 < r ^ 2 := by positivity
      rw [div_eq_mul_inv] at h4
      have : K * E₀ * σ ^ 2 * ε ^ 2 * r ^ 2 ≤ C * σ ^ q * E₀ * σ ^ 2 * ε ^ 2 := by
        have h6 := mul_le_mul_of_nonneg_right h4 hr2.le
        have e3 : C * σ ^ q * E₀ * σ ^ 2 * ε ^ 2 * (r ^ 2)⁻¹ * r ^ 2 =
            C * σ ^ q * E₀ * σ ^ 2 * ε ^ 2 := by field_simp
        rw [e3] at h6
        linarith
      nlinarith
    exact le_of_mul_le_mul_right h5 hpos
  by_cases hC0 : C ≤ 0
  · have := key 1 one_pos le_rfl
    rw [Real.one_rpow] at this
    nlinarith [mul_pos hK0 (pow_pos hr 2)]
  · push Not at hC0
    set t : ℝ := K * r ^ 2 / (2 * C) with ht
    have ht0 : 0 < t := by positivity
    set σ : ℝ := min 1 (t ^ (1 / q)) with hσ
    have hσ0 : 0 < σ := lt_min one_pos (Real.rpow_pos_of_pos ht0 _)
    have hσ1 : σ ≤ 1 := min_le_left _ _
    have h1 : σ ^ q ≤ t := by
      calc σ ^ q ≤ (t ^ (1 / q)) ^ q :=
            Real.rpow_le_rpow hσ0.le (min_le_right _ _) hq0.le
        _ = t := by rw [← Real.rpow_mul ht0.le, one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one]
    have := key σ hσ0 hσ1
    have h2 : C * σ ^ q ≤ C * t := mul_le_mul_of_nonneg_left h1 hC0.le
    have h3 : C * t = K * r ^ 2 / 2 := by rw [ht]; field_simp
    nlinarith [mul_pos hK0 (pow_pos hr 2)]


/-- **The reference-jet certificate fails for the counterexample**: the certificate
`PinJetTerm` (with the frame rotation of the data) cannot hold, for all `0 < σ ≤ 1`, at the
constant configuration; otherwise `termwise_irrelevant_pin` would give a uniform constant,
contradicting `pin_no_uniform_constant`.  (The failing field is `potential`, (3.1).) -/
theorem pin_jet_fails (hne : i₀ ≠ i₁) {E₀ α₁ r ε : ℝ} (hE : 0 < E₀) (hα0 : 0 < α₁)
    (hα1 : α₁ < 1) (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (hεr : ε ≤ r)
    (κ : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ¬ ∃ (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ),
      Frame i₀ σ ε (fun _ : Site d => spinTheta i₀ i₁ (ε / 2)) u R ∧
      PinJetTerm (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)) i₀ i₁ (σ ^ 2) r E₀ κ 0 1
        (fun _ : Site d => spinTheta i₀ i₁ (ε / 2)) (srcRef i₀ (σ ^ 2)) σ ε R {0} := by
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_pin d N 0 1 0 α₁ le_rfl le_rfl le_rfl hα0 hα1
  by_contra hcon
  push Not at hcon
  refine pin_no_uniform_constant (d := d) hne hE hα1 hr hε hε1 ⟨C, fun σ hσ hσ1 => ?_⟩
  obtain ⟨hG, -, -, hD, -⟩ := oneSite_hypotheses (d := d) hne hE hσ hσ1 hε (by linarith) κ 0 1
    le_rfl le_rfl
  have hτ : σ ^ 2 * ε ≤ 1 / 4 := by nlinarith
  have h := hC _ i₀ i₁ (σ ^ 2) r E₀ κ 1 _ hG _ _ σ ε 0 hD {0} (Set.mem_singleton _) hr hr1 hε
    (by linarith) hσ hσ1 hτ (by positivity) le_rfl hE.le (by simp) (hcon σ hσ hσ1)
  have hd : (oneSite d N (E₀ / (32 * (N : ℝ) ^ 2)) (σ ^ 2)).dist ({0} : Finset (Site d)) = 0 :=
    rfl
  rw [hd, mul_zero, Real.exp_zero, mul_one] at h
  exact h

end Final

end Balaban.SmallField
