/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FROrd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRHeavyPt`: the pointwise majorant of a product of terms (route FR, (H1)–(H4))

`notes/phase1/KF0-FR.md` (H). For a set `A` of terms with site part `D` (`A.toLeft`) and the union
`W'` of the site supports of `D`, at every configuration (`prod_norm_frF_le`):

`∏_{t∈A} |F_t| ≤ ∏_{x∈D} (2 Λ̃(σ_x) + w(u_x) Λ̃'(σ_x)) ∏_{y∈W'} e^{a|ψ_y| + θ|ψ_y|²/2}`,

with `Λ̃ = Λ · e^{2G 1[-]}`, `Λ̃' = Λ' · e^{2G 1[-]}` (`frLam`, `frLam'`), `a = 2 G β^{-1/2} ν^{-1/2}`,
`θ` a bound on the absolute row sums of `Q_R`, `G` a bound on `∑_i |g_{x,i}|`. The bond terms are at
most `1` (`norm_frBond_le_one`); the site terms are bounded by the band split, the source bound and
the defect rows (`norm_frSite_le`).
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- The inner-band sheet weight with the source of the lower sheet. -/
def frLam (ε β ν G : ℝ) (b : Bool) : ℝ := bandL ε β ν b * (if b then 1 else Real.exp (2 * G))

/-- The outer-band sheet weight with the source of the lower sheet. -/
def frLam' (ε β ν G : ℝ) (b : Bool) : ℝ := bandL' ε β ν b * (if b then 1 else Real.exp (2 * G))

theorem frLam_nonneg {ε : ℝ} (hε : 0 ≤ ε) (β ν G : ℝ) (b : Bool) : 0 ≤ frLam ε β ν G b := by
  unfold frLam; have := bandL_nonneg hε β ν b; split_ifs <;> positivity

theorem frLam'_nonneg {ε : ℝ} (hε : 0 ≤ ε) (β ν G : ℝ) (b : Bool) : 0 ≤ frLam' ε β ν G b := by
  unfold frLam'; have := bandL'_nonneg hε β ν b; split_ifs <;> positivity

/-- `|Φ_σ(u) - h| ≤ 2|u| + 2 · 1[σ = -]`. -/
theorem norm_sheetPt_sub_le (hh : ‖h‖ = 1) (b : Bool) (ξ : perp h) :
    ‖((sheetPt h hh b ξ : Sph) : E) - h‖ ≤ 2 * ‖ξ‖ + (if b then 0 else 2) := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    linarith [norm_sheetPt_sub_le_two h hh false ξ, norm_nonneg ξ]
  · simp only [ite_true, add_zero]
    by_cases hξ : ‖ξ‖ < 1
    · exact norm_sheetPt_true_sub_le h hh hξ
    · linarith [norm_sheetPt_sub_le_two h hh true ξ, not_lt.1 hξ]

variable {d ℓ : ℕ} [NeZero ℓ]

theorem norm_frBond_le_one {β ν : ℝ} (hβ : 0 ≤ β) (R : ℕ) (x : Torus d ℓ) (μ : Fin d)
    (ω : Torus d ℓ → perp h × Bool) : ‖frBond h β ν R x μ ω‖ ≤ 1 := by
  unfold frBond
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (sgn (frSig h ω (x + Pi.single μ 1)) *
    tN h (frField d ℓ β ν R (frPsi h ω) (x + Pi.single μ 1)) -
      sgn (frSig h ω x) * tN h (frField d ℓ β ν R (frPsi h ω) x))])

/-- **The pointwise bound of a site term** (H1)–(H2). -/
theorem norm_frSite_le (hh : ‖h‖ = 1) {β ν ε G : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε)
    (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ) (ω : Torus d ℓ → perp h × Bool)
    (hg : ∑ i, ‖g x i‖ ≤ G) :
    ‖frSite h hh β ν ε R g x ω‖ ≤
      (2 * frLam ε β ν G (frSig h ω x) +
          chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x)) *
        Real.exp (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖ +
          -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) := by
  set u := frField d ℓ β ν R (frPsi h ω) x with hu
  set σ := frSig h ω x with hσ
  have hG0 : 0 ≤ G := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) hg
  have hβν : 0 ≤ β * ν := (mul_pos hβ hν).le
  have hw0 := chartWeight_nonneg h u
  -- the source
  have hsrc : ‖Complex.exp (∑ i : Fin N, g x i *
      ((((sheetPt h hh σ u : Sph) : E) - h) i : ℂ))‖ ≤
      Real.exp (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖) *
        (if σ then 1 else Real.exp (2 * G)) := by
    rw [Complex.norm_exp]
    have h1 : ‖∑ i : Fin N, g x i * ((((sheetPt h hh σ u : Sph) : E) - h) i : ℂ)‖ ≤
        G * (2 * ‖u‖ + (if σ then 0 else 2)) := by
      calc _ ≤ ∑ i : Fin N, ‖g x i‖ * ‖((sheetPt h hh σ u : Sph) : E) - h‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_mul, Complex.norm_real]
            exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ i) (norm_nonneg _)
        _ = (∑ i : Fin N, ‖g x i‖) * ‖((sheetPt h hh σ u : Sph) : E) - h‖ := by
            rw [Finset.sum_mul]
        _ ≤ G * (2 * ‖u‖ + (if σ then 0 else 2)) :=
            mul_le_mul hg (norm_sheetPt_sub_le h hh σ u) (norm_nonneg _) hG0
    have h2 : G * (2 * ‖u‖) ≤ 2 * G * (Real.sqrt β)⁻¹ *
        ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖ := by
      have := norm_frField_le h (β := β) hν R (frPsi h ω) x
      nlinarith
    refine (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans h1)).trans ?_
    cases σ
    · simp only [Bool.false_eq_true, ite_false]
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    · simp only [ite_true, add_zero, mul_one]
      exact Real.exp_le_exp.2 h2
  have hband := band_split h hε hβν σ u
  unfold frSite
  rw [← hu, ← hσ]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by unfold bW; split_ifs <;> positivity),
    abs_of_pos (Real.exp_pos _)]
  have hbW0 : 0 ≤ bW ε σ := by unfold bW; split_ifs <;> positivity
  have hsplit : chartWeight h u * bW ε σ *
      Real.exp (-(β * ν / 2) * (sgn σ * tN h u - 1) ^ 2) * (if σ then 1 else Real.exp (2 * G)) ≤
      2 * frLam ε β ν G σ + chartWeight h u * frLam' ε β ν G σ := by
    have hc : 0 ≤ (if σ then (1 : ℝ) else Real.exp (2 * G)) := by split_ifs <;> positivity
    calc _ ≤ (2 * bandL ε β ν σ + chartWeight h u * bandL' ε β ν σ) *
          (if σ then 1 else Real.exp (2 * G)) := mul_le_mul_of_nonneg_right hband hc
      _ = _ := by unfold frLam frLam'; ring
  have hA0 : 0 ≤ chartWeight h u * bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h u - 1) ^ 2) :=
    by positivity
  calc chartWeight h u * bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h u - 1) ^ 2) *
        ‖Complex.exp (∑ i : Fin N, g x i * ((((sheetPt h hh σ u : Sph) : E) - h) i : ℂ))‖ *
        Real.exp (-(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E))
      ≤ chartWeight h u * bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h u - 1) ^ 2) *
        (Real.exp (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖) *
          (if σ then 1 else Real.exp (2 * G))) *
        Real.exp (-(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) := by
        gcongr
    _ = (chartWeight h u * bW ε σ * Real.exp (-(β * ν / 2) * (sgn σ * tN h u - 1) ^ 2) *
          (if σ then 1 else Real.exp (2 * G))) *
        Real.exp (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖ +
          -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) := by
        rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsplit (Real.exp_pos _).le

/-- The union of the site supports of a set of sites. -/
def frSiteHull (R : ℕ) (D : Finset (Torus d ℓ)) : Finset (Torus d ℓ) :=
  D.biUnion fun x => frSupp R (Sum.inl x)

theorem subset_frSiteHull (R : ℕ) (D : Finset (Torus d ℓ)) : D ⊆ frSiteHull R D := fun x hx =>
  Finset.mem_biUnion.2 ⟨x, hx, mem_frSupp_inl_self R x⟩

/-- **(H2)–(H3) The exponents of a set of site terms**: with row sums of `|Q_R|` at most `θ`,
`∑_{x∈D} (2Gβ^{-1/2} ∑_y C_R(x,y)|ψ_y| - ½ ∑_y Q_R(x,y)⟨ψ_x,ψ_y⟩) ≤ ∑_{y∈W'} (a|ψ_y| + θ|ψ_y|²/2)`. -/
theorem sum_site_exponents_le {β ν G θ : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hG : 0 ≤ G) (R : ℕ)
    (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ) (D : Finset (Torus d ℓ))
    (ψ : Torus d ℓ → perp h) :
    ∑ x ∈ D, (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖ψ y‖ +
        -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) ≤
      ∑ y ∈ frSiteHull R D, (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ * ‖ψ y‖ +
        θ / 2 * ‖ψ y‖ ^ 2) := by
  have hsuppC : ∀ x ∈ D, ∀ y, kf0CR d ℓ ν R x y ≠ 0 → y ∈ frSiteHull R D := by
    intro x hx y hy
    have := kf0CR_ne_zero_dist hy
    exact Finset.mem_biUnion.2 ⟨x, hx, by simp [frSupp]; linarith⟩
  have hsuppQ : ∀ x ∈ D, ∀ y, frQ d ℓ ν R x y ≠ 0 → y ∈ frSiteHull R D := by
    intro x hx y hy
    by_contra hn
    refine hy (frQ_eq_zero_of_lt ?_)
    have : ¬ torusDist d ℓ x y ≤ 2 * R + 1 := fun hle =>
      hn (Finset.mem_biUnion.2 ⟨x, hx, by simp [frSupp, hle]⟩)
    linarith
  have h1 := sum_sum_mul_le (kf0CR d ℓ ν R) (kf0CR_nonneg hν R) (kf0CR_symm ν R)
    (c := (Real.sqrt ν)⁻¹) (fun x => by
      have := kf0CR_rowAbs_le (d := d) (m := ℓ) hν R x
      simpa [abs_of_nonneg (kf0CR_nonneg hν R x _)] using this)
    (fun y => ‖ψ y‖) (fun y => norm_nonneg _) hsuppC
  have h2 := sum_sum_abs_mul_le (frQ d ℓ ν R) (frQ_symm ν R) hQ (fun y => ‖ψ y‖)
    (subset_frSiteHull R D) hsuppQ
  have h3 : ∀ x, -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E) ≤
      (1 / 2) * ∑ y, |frQ d ℓ ν R x y| * |‖ψ x‖| * |‖ψ y‖| := by
    intro x
    have : -(∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) ≤
        ∑ y, |frQ d ℓ ν R x y| * |‖ψ x‖| * |‖ψ y‖| := by
      refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun y _ => ?_))
      rw [abs_mul, abs_norm, abs_norm, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_real_inner_le_norm (ψ x : E) (ψ y : E)
      simpa [Submodule.norm_coe] using this
    linarith
  have hc : 0 ≤ 2 * G * (Real.sqrt β)⁻¹ := by positivity
  calc _ ≤ ∑ x ∈ D, (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖ψ y‖ +
        (1 / 2) * ∑ y, |frQ d ℓ ν R x y| * |‖ψ x‖| * |‖ψ y‖|) :=
        Finset.sum_le_sum fun x _ => add_le_add le_rfl (h3 x)
    _ = 2 * G * (Real.sqrt β)⁻¹ * ∑ x ∈ D, ∑ y, kf0CR d ℓ ν R x y * ‖ψ y‖ +
        (1 / 2) * ∑ x ∈ D, ∑ y, |frQ d ℓ ν R x y| * |‖ψ x‖| * |‖ψ y‖| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * G * (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * ∑ y ∈ frSiteHull R D, ‖ψ y‖) +
        (1 / 2) * (θ * ∑ y ∈ frSiteHull R D, ‖ψ y‖ ^ 2) := by
        gcongr
    _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring

/-- **(H4) The pointwise majorant of a product of terms.** -/
theorem prod_norm_frF_le (hh : ‖h‖ = 1) {β ν ε G θ : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε)
    (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (hg : ∀ x, ∑ i, ‖g x i‖ ≤ G)
    (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ) (A : Finset (FRTerm d ℓ))
    (ω : Torus d ℓ → perp h × Bool) :
    ∏ t ∈ A, ‖frF h hh β ν ε R g t ω‖ ≤
      (∏ x ∈ A.toLeft, (2 * frLam ε β ν G (frSig h ω x) +
          chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x))) *
        ∏ y ∈ frSiteHull R A.toLeft, Real.exp (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ *
          ‖frPsi h ω y‖ + θ / 2 * ‖frPsi h ω y‖ ^ 2) := by
  have hG0 : 0 ≤ G := by
    rcases isEmpty_or_nonempty (Torus d ℓ) with hι | ⟨⟨x⟩⟩
    · exact (hι.false 0).elim
    · exact le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hg x)
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  have hbonds : ∏ t ∈ A.toRight, ‖frF h hh β ν ε R g (Sum.inr t) ω‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun t _ => ?_
    obtain ⟨x, μ⟩ := t
    exact norm_frBond_le_one h (hβ.le) R x μ ω
  have hsites : ∏ x ∈ A.toLeft, ‖frF h hh β ν ε R g (Sum.inl x) ω‖ ≤
      ∏ x ∈ A.toLeft, ((2 * frLam ε β ν G (frSig h ω x) +
          chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x)) *
        Real.exp (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖ +
          -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E))) :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun x _ =>
      norm_frSite_le h hh hβ hν hε R g x ω (hg x)
  have hexp := sum_site_exponents_le h hβ hν hG0 R hQ A.toLeft (frPsi h ω)
  have hP0 : 0 ≤ ∏ x ∈ A.toLeft, (2 * frLam ε β ν G (frSig h ω x) +
      chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x)) :=
    Finset.prod_nonneg fun x _ => add_nonneg (mul_nonneg (by norm_num)
      (frLam_nonneg hε.le β ν G _)) (mul_nonneg (chartWeight_nonneg h _)
        (frLam'_nonneg hε.le β ν G _))
  calc (∏ x ∈ A.toLeft, ‖frF h hh β ν ε R g (Sum.inl x) ω‖) *
        ∏ t ∈ A.toRight, ‖frF h hh β ν ε R g (Sum.inr t) ω‖
      ≤ (∏ x ∈ A.toLeft, ((2 * frLam ε β ν G (frSig h ω x) +
          chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x)) *
        Real.exp (2 * G * (Real.sqrt β)⁻¹ * ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖ +
          -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)))) * 1 :=
        mul_le_mul hsites hbonds (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (Finset.prod_nonneg fun x _ => mul_nonneg (add_nonneg (mul_nonneg (by norm_num)
            (frLam_nonneg hε.le β ν G _)) (mul_nonneg (chartWeight_nonneg h _)
              (frLam'_nonneg hε.le β ν G _))) (Real.exp_pos _).le)
    _ = (∏ x ∈ A.toLeft, (2 * frLam ε β ν G (frSig h ω x) +
          chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x))) *
        Real.exp (∑ x ∈ A.toLeft, (2 * G * (Real.sqrt β)⁻¹ *
          ∑ y, kf0CR d ℓ ν R x y * ‖frPsi h ω y‖ +
          -(1 / 2) * ∑ y, frQ d ℓ ν R x y * inner ℝ (frPsi h ω x : E) (frPsi h ω y : E))) := by
        rw [mul_one, Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ _ := by
        rw [← Real.exp_sum]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hP0

end

end Balaban.LargeField.KF0FR
