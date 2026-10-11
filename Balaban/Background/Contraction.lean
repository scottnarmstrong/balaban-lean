/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Calculus
public import Balaban.Background.Data
public import Balaban.Background.ContractionCore
public import Balaban.Analysis.Contraction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The perturbed system with independent data (BACKGROUND.md §5.1, Proposition 5.1)
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}


section Algebra

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The scalar product `v · w = ∑ᵢ vᵢ wᵢ` of two vector fields on `Ω₁` (bilinear). -/
def vdot (v w : G.Ω 1 × Fin N → ℂ) : G.Ω 1 → ℂ := fun x => ∑ i, v (x, i) * w (x, i)

theorem commK_apply' (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ : G.Ω 1 → Fin N → ℂ)
    (s : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    (commK H φ *ᵥ s) x = ∑ i, φ x i * (liftOp N H *ᵥ s) (x, i) -
      (H *ᵥ fun y => ∑ i, φ y i * s (y, i)) x := by
  unfold commK
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Pi.sub_apply, fieldMul_transpose_mulVec]
  congr 1
  show ∑ y, H x y * ((fieldMul φ)ᵀ *ᵥ s) y = _
  exact Finset.sum_congr rfl fun y _ => by rw [fieldMul_transpose_mulVec]

variable (G a ν) in
/-- **The perturbed system (P-1), (P-2)** (BACKGROUND.md §5.1; P2 (3.20) at `λ = ∞`):
`(H_D(α₀) + δα) δφ = F_s - δα φ₀` and `(φ₀ + δφ)·(φ₀ + δφ) = 1` on `Ω₁`. -/
def IsPerturbed (α₀ : G.Ω 1 → ℂ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) : Prop :=
  (liftOp N (dirichletOperator G a ν α₀) *ᵥ δφ + (fun p => δα p.1 * δφ p) =
      fun p => Fs p - δα p.1 * φ₀ p.1 p.2) ∧
    ∀ x : G.Ω 1, ∑ i, (φ₀ x i + δφ (x, i)) * (φ₀ x i + δφ (x, i)) = 1

theorem liftOp_dirichlet_add (a : ℕ → ℝ) (ν : ℝ) (α₀ δα : G.Ω 1 → ℂ) (w : G.Ω 1 × Fin N → ℂ)
    (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a ν (α₀ + δα)) *ᵥ w) p =
      (liftOp N (dirichletOperator G a ν α₀) *ᵥ w) p + δα p.1 * w p := by
  obtain ⟨x, i⟩ := p
  rw [liftOp_mulVec, liftOp_mulVec, dirichletOperator_eq_add G a ν (α₀ + δα) α₀,
    Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
  simp

theorem liftOp_dirichlet_two (a : ℕ → ℝ) (ν : ℝ) (α₀ δα : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ)
    (x : G.Ω 1) :
    (dirichletOperator G a ν (α₀ + 2 * δα) *ᵥ u) x =
      (dirichletOperator G a ν α₀ *ᵥ u) x + 2 * δα x * u x := by
  rw [dirichletOperator_eq_add G a ν (α₀ + 2 * δα) α₀, Matrix.add_mulVec, Pi.add_apply,
    Matrix.mulVec_diagonal]
  simp [mul_assoc]

/-- **Identity (5.2)**: for a solution of (P-1), with
`u = 2 φ₀·δφ + δφ·δφ + g`,  `(H₀ + 2δα) u = 2 (𝒩(δα) - δα)`. -/
theorem identity52 (a : ℕ → ℝ) (ν : ℝ) (α₀ δα : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ)
    (h1 : liftOp N (dirichletOperator G a ν α₀) *ᵥ δφ + (fun p => δα p.1 * δφ p) =
      fun p => Fs p - δα p.1 * φ₀ p.1 p.2) (x : G.Ω 1) :
    (dirichletOperator G a ν (α₀ + 2 * δα) *ᵥ
        fun y => 2 * ∑ i, φ₀ y i * δφ (y, i) + ∑ i, δφ (y, i) * δφ (y, i) + gdef G φ₀ y) x =
      2 * (Nmap G (dirichletOperator G a ν α₀) true φ₀ Fs δφ x - δα x) := by
  rw [liftOp_dirichlet_two]
  set H₀ := dirichletOperator G a ν α₀ with hH₀
  have hlin : (H₀ *ᵥ fun y => 2 * ∑ i, φ₀ y i * δφ (y, i) + ∑ i, δφ (y, i) * δφ (y, i) +
      gdef G φ₀ y) x =
      2 * (H₀ *ᵥ fun y => ∑ i, φ₀ y i * δφ (y, i)) x +
        (H₀ *ᵥ fun y => ∑ i, δφ (y, i) * δφ (y, i)) x + (H₀ *ᵥ gdef G φ₀) x := by
    have hfun : (fun y : G.Ω 1 => 2 * ∑ i, φ₀ y i * δφ (y, i) + ∑ i, δφ (y, i) * δφ (y, i) +
        gdef G φ₀ y) = (2 : ℂ) • (fun y : G.Ω 1 => ∑ i, φ₀ y i * δφ (y, i)) +
        (fun y : G.Ω 1 => ∑ i, δφ (y, i) * δφ (y, i)) + gdef G φ₀ := by
      funext y; simp
    rw [hfun, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul]
    simp
  have hK := commK_apply' H₀ (restrictField G φ₀) δφ x
  have hR := Rvec_eq H₀ δφ δφ x
  have hpt : ∀ i, (liftOp N H₀ *ᵥ δφ) (x, i) =
      Fs (x, i) - δα x * (φ₀ x i + δφ (x, i)) := by
    intro i
    have := congrFun h1 (x, i)
    simp only [Pi.add_apply] at this
    linear_combination this
  unfold Nmap
  simp only [↓reduceIte]
  rw [hlin]
  simp only [hpt] at hK hR
  have ea : (H₀ *ᵥ fun y => ∑ i, φ₀ y i * δφ (y, i)) x =
      ∑ i, φ₀ x i * (Fs (x, i) - δα x * (φ₀ x i + δφ (x, i))) -
        (commK H₀ (restrictField G φ₀) *ᵥ δφ) x := by
    rw [hK]; simp only [restrictField]; ring
  rw [ea]
  have eb : (H₀ *ᵥ fun y => ∑ i, δφ (y, i) * δφ (y, i)) x =
      2 * ∑ i, δφ (x, i) * (Fs (x, i) - δα x * (φ₀ x i + δφ (x, i))) +
        Rvec H₀ δφ δφ x := by
    linear_combination -hR
  rw [eb]
  have e1 : ∑ i, φ₀ x i * (Fs (x, i) - δα x * (φ₀ x i + δφ (x, i))) =
      ∑ i, φ₀ x i * Fs (x, i) - δα x * (∑ i, φ₀ x i * φ₀ x i + ∑ i, φ₀ x i * δφ (x, i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, δφ (x, i) * (Fs (x, i) - δα x * (φ₀ x i + δφ (x, i))) =
      ∑ i, δφ (x, i) * Fs (x, i) - δα x * (∑ i, φ₀ x i * δφ (x, i) + ∑ i, δφ (x, i) * δφ (x, i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i) =
      ∑ i, φ₀ x i * Fs (x, i) + ∑ i, δφ (x, i) * Fs (x, i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  have eg : gdef G φ₀ x = ∑ i, φ₀ x i * φ₀ x i - 1 := rfl
  rw [eg]
  ring

end Algebra

section Core

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α₀ : G.Ω 1 → ℂ}
  {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {δ₀ Fb Gb : ℝ}

variable (G a ν) in
/-- The Green family of `G_D`: `𝒢(α) = H_D(α)⁻¹`. -/
noncomputable def greenD (α : G.Ω 1 → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  (dirichletOperator G a ν α)⁻¹

/-- **The instance of the abstract family**: `α ↦ H_D(α)⁻¹` is a `GreenFamily` with
`B = greenSupConst d L` on the polydisc `|α|₂ ≤ γ₁ = gamma1 d`, by the bridge lemma
(`GreenSetting.green_bound`) and the resolvent difference bound (`GreenSetting.green_sub_bound`). -/
theorem GreenSetting.family (S : GreenSetting G a ν) :
    GreenFamily G N (greenD G a ν) (greenSupConst d L) (gamma1 d) where
  B_nn := greenSupConst_nonneg d L
  bound := fun hα g _ hC hg => SupBounds.star (S.green_bound hα g hC hg)
  diff := fun hα hα' g _ _ hC hg hΔ0 hΔ => SupBounds.star (S.green_sub_bound hα hα' g hC hg hΔ0 hΔ)


/-- The bound for `|𝒩(0)|₂` for `G_D`: the abstract `coreBound` with `B = greenSupConst d L`,
`K = commKConst d L N` and `R = 2d + 8`. -/
noncomputable def selfBound (d L N : ℕ) [NeZero L] (δ₀ Fb Gb : ℝ) : ℝ :=
  coreBound N (greenSupConst d L) (commKConst d L N) (2 * d + 8) δ₀ Fb Gb

theorem liftOp_inv_mulVec {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hM : IsUnit M)
    (w : G.Ω 1 × Fin N → ℂ) : liftOp N M⁻¹ *ᵥ (liftOp N M *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← liftOp_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hM),
    liftOp_one, Matrix.one_mulVec]

theorem liftOp_mulVec_inv {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hM : IsUnit M)
    (w : G.Ω 1 × Fin N → ℂ) : liftOp N M *ᵥ (liftOp N M⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← liftOp_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM),
    liftOp_one, Matrix.one_mulVec]


theorem dphi_eq (S : GreenSetting G a ν) {δα : G.Ω 1 → ℂ}
    (hα : Small G (α₀ + δα) (gamma1 d)) :
    liftOp N (dirichletOperator G a ν (α₀ + δα)) *ᵥ dphi G (greenD G a ν) α₀ φ₀ Fs δα =
      Fsrc φ₀ Fs δα :=
  liftOp_mulVec_inv (S.isUnit hα) _


/-- The constraint is equivalent to `u = 0`. -/
theorem constraint_iff_u (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (δφ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) :
    (∑ i, (φ₀ x i + δφ (x, i)) * (φ₀ x i + δφ (x, i)) = 1) ↔
      2 * ∑ i, φ₀ x i * δφ (x, i) + ∑ i, δφ (x, i) * δφ (x, i) + gdef G φ₀ x = 0 := by
  have e : ∑ i, (φ₀ x i + δφ (x, i)) * (φ₀ x i + δφ (x, i)) =
      ∑ i, φ₀ x i * φ₀ x i + 2 * ∑ i, φ₀ x i * δφ (x, i) + ∑ i, δφ (x, i) * δφ (x, i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  have : gdef G φ₀ x = ∑ i, φ₀ x i * φ₀ x i - 1 := rfl
  rw [this]
  constructor <;> intro h <;> linear_combination h

theorem isPerturbed_dphi_iff (S : GreenSetting G a ν) {δα : G.Ω 1 → ℂ}
    (hα : Small G (α₀ + δα) (gamma1 d)) (δφ : G.Ω 1 × Fin N → ℂ) :
    (liftOp N (dirichletOperator G a ν α₀) *ᵥ δφ + (fun p => δα p.1 * δφ p) =
      fun p => Fs p - δα p.1 * φ₀ p.1 p.2) ↔ δφ = dphi G (greenD G a ν) α₀ φ₀ Fs δα := by
  have hU := S.isUnit hα
  have key : (liftOp N (dirichletOperator G a ν α₀) *ᵥ δφ + (fun p => δα p.1 * δφ p) =
      fun p => Fs p - δα p.1 * φ₀ p.1 p.2) ↔
      liftOp N (dirichletOperator G a ν (α₀ + δα)) *ᵥ δφ = Fsrc φ₀ Fs δα := by
    have : liftOp N (dirichletOperator G a ν (α₀ + δα)) *ᵥ δφ =
        liftOp N (dirichletOperator G a ν α₀) *ᵥ δφ + (fun p => δα p.1 * δφ p) := by
      funext p; rw [liftOp_dirichlet_add]; rfl
    rw [this]; rfl
  rw [key]
  constructor
  · intro h
    unfold dphi greenD
    rw [← h, liftOp_inv_mulVec hU]
  · intro h
    rw [h]; exact dphi_eq S hα

/-- A fixed point of `𝒩` in the ball gives a solution of (P-1), (P-2): the `G_D`-specific step
(identity (5.2) and the invertibility of `H_D(α₀ + 2 δα)`). -/
theorem perturbed_of_fixed (S : GreenSetting G a ν) (hα₀ : Small G α₀ δ₀) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hpoly : δ₀ + 2 * ρ ≤ gamma1 d) {δα : G.Ω 1 → ℂ} (hsmall : Small G δα ρ)
    (hfix : Nmap G (dirichletOperator G a ν α₀) true φ₀ Fs
      (dphi G (greenD G a ν) α₀ φ₀ Fs δα) = δα) :
    IsPerturbed G a ν α₀ φ₀ Fs (dphi G (greenD G a ν) α₀ φ₀ Fs δα) δα := by
  have hα1 : Small G (α₀ + δα) (gamma1 d) := fun x =>
    ((hα₀.add hsmall) x).trans (by linarith)
  have hU2 := S.isUnit (α := α₀ + 2 * δα) fun x =>
    ((hα₀.add (small_two_mul hsmall)) x).trans (by linarith)
  have hP1 := (isPerturbed_dphi_iff S hα1 (dphi G (greenD G a ν) α₀ φ₀ Fs δα)).2 rfl
  have hu : ∀ x : G.Ω 1, 2 * ∑ i, φ₀ x i * dphi G (greenD G a ν) α₀ φ₀ Fs δα (x, i) +
      ∑ i, dphi G (greenD G a ν) α₀ φ₀ Fs δα (x, i) * dphi G (greenD G a ν) α₀ φ₀ Fs δα (x, i) +
        gdef G φ₀ x = 0 := by
    have hz : (dirichletOperator G a ν (α₀ + 2 * δα) *ᵥ fun y => 2 * ∑ i, φ₀ y i *
        dphi G (greenD G a ν) α₀ φ₀ Fs δα (y, i) + ∑ i, dphi G (greenD G a ν) α₀ φ₀ Fs δα (y, i) *
        dphi G (greenD G a ν) α₀ φ₀ Fs δα (y, i) + gdef G φ₀ y) = 0 := by
      funext x
      rw [identity52 a ν α₀ δα φ₀ Fs _ hP1 x, congrFun hfix x]
      simp
    exact fun x => congrFun (Matrix.eq_zero_of_mulVec_eq_zero
      ((Matrix.isUnit_iff_isUnit_det _).1 hU2).ne_zero hz) x
  exact ⟨hP1, fun x => (constraint_iff_u φ₀ _ x).2 (hu x)⟩


/-- **Proposition 5.1 (core for `G_D`)**: the abstract core (`prop51_core` for the family
`H_D(α)⁻¹`, mode U) plus the `G_D`-specific step.  Under the numerical conditions of `CoreHyp`, the
perturbed system (P-1), (P-2) has a solution with `|δα|₂ ≤ 2 sb`, `SupBounds` of `δφ`, and it is
the only one with `|δα|₂ ≤ ρ`. -/
theorem prop51_core_D (S : GreenSetting G a ν)
    (H : Setup G (dirichletOperator G a ν α₀) true (commKConst d L N) (2 * d + 8) α₀ φ₀ Fs
      δ₀ Fb Gb) {ρ : ℝ}
    (hC : CoreHyp N (greenSupConst d L) (commKConst d L N) (2 * d + 8) (gamma1 d) δ₀ Fb Gb ρ) :
    ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
      IsPerturbed G a ν α₀ φ₀ Fs δφ δα ∧
      Small G δα (2 * selfBound d L N δ₀ Fb Gb) ∧
      SupBounds G δφ (greenSupConst d L * (Fb + 3 / 2 * (2 * selfBound d L N δ₀ Fb Gb))) ∧
      ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ), IsPerturbed G a ν α₀ φ₀ Fs δφ' δα' →
        Small G δα' ρ → δφ' = δφ ∧ δα' = δα := by
  obtain ⟨δα, hsmall, hfix, hsb, -, huniq⟩ := prop51_core (S.family (N := N)) H hC
  have hρ := hC.ρ_nn
  have hsb0 := coreBound_nonneg (N := N) (greenSupConst_nonneg d L) H.Kc_nn H.Rc_nn H.δ₀_nn
    H.Fb_nn H.Gb_nn
  have hr2 : δ₀ + 2 * selfBound d L N δ₀ Fb Gb ≤ gamma1 d := by
    have := hC.self; have := hC.poly
    unfold selfBound; linarith
  have hP := perturbed_of_fixed S H.alpha0 hρ hC.poly hsmall hfix
  refine ⟨dphi G (greenD G a ν) α₀ φ₀ Fs δα, δα, hP, hsb, ?_, ?_⟩
  · exact S.green_bound (H.poly hsb hr2) _ (by have := H.Fb_nn; unfold selfBound; positivity)
      (Fsrc_bd H hsb)
  · intro δφ' δα' hP' hs'
    obtain ⟨hP1', hP2'⟩ := hP'
    have hα' : Small G (α₀ + δα') (gamma1 d) := fun x =>
      ((H.alpha0.add hs') x).trans (by linarith [hC.poly])
    have hdφ := (isPerturbed_dphi_iff S hα' δφ').1 hP1'
    have hu' := fun x => (constraint_iff_u φ₀ δφ' x).1 (hP2' x)
    have hz : (dirichletOperator G a ν (α₀ + 2 * δα') *ᵥ fun y => 2 * ∑ i, φ₀ y i * δφ' (y, i) +
        ∑ i, δφ' (y, i) * δφ' (y, i) + gdef G φ₀ y) = 0 := by
      funext x
      have hu0 : (fun y : G.Ω 1 => 2 * ∑ i, φ₀ y i * δφ' (y, i) + ∑ i, δφ' (y, i) * δφ' (y, i) +
        gdef G φ₀ y) = 0 := funext hu'
      rw [hu0]; simp
    have hfix' : Nmap G (dirichletOperator G a ν α₀) true φ₀ Fs
        (dphi G (greenD G a ν) α₀ φ₀ Fs δα') = δα' := by
      funext x
      have := identity52 a ν α₀ δα' φ₀ Fs δφ' hP1' x
      rw [congrFun hz x] at this
      rw [← hdφ]
      have h2 : (2 : ℂ) * (Nmap G (dirichletOperator G a ν α₀) true φ₀ Fs δφ' x - δα' x) = 0 := by
        simpa using this.symm
      have := (mul_eq_zero.1 h2).resolve_left (by norm_num)
      exact sub_eq_zero.1 this
    have := huniq δα' hs' hfix'
    exact ⟨by rw [hdφ, this], this⟩

end Core

section Constants

/-- Arithmetic for the Lipschitz condition of `CoreHyp`. -/
theorem arith_lip {A B1 B Fb δ₀ ρ τ x y z : ℝ} (hA : 1 ≤ A) (hB1 : 1 ≤ B1) (hB : 0 ≤ B)
    (hBB : B ≤ B1) (hτ : 15 * A * B1 ^ 2 * τ = 1) (hτ0 : 0 ≤ τ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) (hx : x ≤ A) (hy : y ≤ A) (hz : z ≤ A)
    (hF0 : 0 ≤ Fb) (hδ0 : 0 ≤ δ₀) (hρ0 : 0 ≤ ρ)
    (hF : Fb ≤ τ / 3) (hδ : δ₀ ≤ τ / 3) (hρ : 3 / 2 * ρ ≤ τ / 3) :
    (x * Fb + y * δ₀ + z * (B * (Fb + 3 / 2 * ρ))) * (B * (3 / 2 + B * (Fb + 3 / 2 * ρ))) ≤ 1 / 2 := by
  have hτ1 : τ ≤ 1 / 15 := by
    have : 1 ≤ A * B1 ^ 2 := by nlinarith [one_le_pow₀ hB1 (n := 2)]
    nlinarith
  set D := B * (Fb + 3 / 2 * ρ) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDle : D ≤ B1 * (2 * τ / 3) := by
    rw [hD]
    exact mul_le_mul hBB (by linarith) (by positivity) (by linarith)
  have hBt : B1 * τ ≤ 1 / 15 := by
    have h1 : 0 ≤ A * B1 - 1 := by nlinarith
    nlinarith [mul_nonneg h1 (mul_nonneg (by linarith : 0 ≤ B1) hτ0)]
  have hD1 : D ≤ 1 := by nlinarith
  have h1 : x * Fb + y * δ₀ + z * D ≤ 4 / 3 * A * B1 * τ := by
    have e1 : x * Fb ≤ A * (τ / 3) := mul_le_mul hx hF hF0 (by linarith)
    have e2 : y * δ₀ ≤ A * (τ / 3) := mul_le_mul hy hδ hδ0 (by linarith)
    have e3 : z * D ≤ A * (B1 * (2 * τ / 3)) := mul_le_mul hz hDle hD0 (by linarith)
    nlinarith [mul_nonneg (by linarith : 0 ≤ A) hτ0, mul_nonneg (mul_nonneg (by linarith : 0 ≤ A) (by linarith : 0 ≤ B1 - 1)) hτ0]
  have h2 : B * (3 / 2 + D) ≤ 5 / 2 * B1 := by nlinarith
  have h3 : 0 ≤ x * Fb + y * δ₀ + z * D := by positivity
  calc _ ≤ (4 / 3 * A * B1 * τ) * (5 / 2 * B1) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 10 / 3 * (A * B1 ^ 2 * τ) := by ring
    _ ≤ 1 / 2 := by nlinarith

/-- Arithmetic for the self-map condition of `CoreHyp`. -/
theorem arith_self {A B1 B Fb Gb δ₀ x y e δ₁ CF : ℝ} (hA : 1 ≤ A) (hB1 : 1 ≤ B1) (hB : 0 ≤ B)
    (hBB : B ≤ B1) (hx : x ≤ A) (hy : y ≤ A)
    (hxe : x * e ≤ A) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ 1) (hF0 : 0 ≤ Fb) (hBF : B1 * Fb ≤ 1)
    (hFb : Fb = CF * δ₁) (hGb : Gb = 5 * δ₁) :
    x * ((3 / 2 + B * Fb) * Fb) + y * δ₀ * (B * Fb) + 1 / 2 * (x * (e * ((B * Fb) * (B * Fb)))) +
      1 / 2 * Gb ≤ (5 * A * B1 * CF + 5 / 2) * δ₁ := by
  have hD0 : 0 ≤ B * Fb := by positivity
  have hD1 : B * Fb ≤ 1 := by nlinarith
  have hDF : B * Fb ≤ B1 * Fb := mul_le_mul_of_nonneg_right hBB hF0
  have t1 : x * ((3 / 2 + B * Fb) * Fb) ≤ A * (5 / 2 * Fb) := by
    refine mul_le_mul hx (mul_le_mul (by linarith) le_rfl hF0 (by norm_num)) (by positivity) (by linarith)
  have t2 : y * δ₀ * (B * Fb) ≤ A * (B1 * Fb) := by
    have : y * δ₀ ≤ A * 1 := mul_le_mul hy hδ hδ0 (by linarith)
    calc y * δ₀ * (B * Fb) ≤ (A * 1) * (B1 * Fb) := mul_le_mul this hDF hD0 (by linarith)
      _ = _ := by ring
  have t3 : x * (e * ((B * Fb) * (B * Fb))) ≤ A * (B1 * Fb) := by
    have : x * (e * ((B * Fb) * (B * Fb))) = (x * e) * ((B * Fb) * (B * Fb)) := by ring
    rw [this]
    have h4 : (B * Fb) * (B * Fb) ≤ B1 * Fb := by nlinarith
    exact mul_le_mul hxe h4 (by positivity) (by linarith)
  have hCF : 0 ≤ CF * δ₁ := hFb ▸ hF0
  have : A * (5 / 2 * Fb) + A * (B1 * Fb) + 1 / 2 * (A * (B1 * Fb)) ≤ 4 * A * B1 * Fb := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ A) hF0, mul_nonneg (mul_nonneg (by linarith : 0 ≤ A) (by linarith : 0 ≤ B1 - 1)) hF0]
  have hfin : x * ((3 / 2 + B * Fb) * Fb) + y * δ₀ * (B * Fb) +
      1 / 2 * (x * (e * ((B * Fb) * (B * Fb)))) + 1 / 2 * Gb ≤ 4 * A * B1 * Fb + 1 / 2 * Gb := by
    linarith
  refine hfin.trans ?_
  rw [hGb, hFb]
  have hq : 0 ≤ A * B1 * (CF * δ₁) := by
    have : 0 ≤ A * B1 := by positivity
    exact mul_nonneg this hCF
  nlinarith

variable (d L N : ℕ) [NeZero L]

/-- Constants of Proposition 5.1: they depend on `(d, L, N)` only. -/
noncomputable def cA : ℝ := 1 + commKConst d L N + N * (2 * d + 8) + N
noncomputable def cB1 : ℝ := greenSupConst d L + 1
noncomputable def cTau : ℝ := 1 / (15 * cA d L N * cB1 d L ^ 2)
/-- `C_F = 3 + 2 d L²`: `|F_s|₂ ≤ C_F δ₁`. -/
noncomputable def cF : ℝ := 3 + 2 * d * (L : ℝ) ^ 2
noncomputable def cN : ℝ := 5 * cA d L N * cB1 d L * cF d L + 5 / 2
/-- The radius `c₆` of Proposition 5.1. -/
noncomputable def c6 : ℝ := min (gamma1 d / 4) (2 * cTau d L N / 9)
/-- The smallness `δ_*` of Proposition 5.1. -/
noncomputable def deltaStar : ℝ :=
  min (min (cTau d L N / 3) (gamma1 d / 4)) (min (min 1 (c6 d L N / (2 * cN d L N)))
    (cTau d L N / (3 * cF d L)))
/-- The constant `K₂` of Proposition 5.1. -/
noncomputable def cK2 : ℝ := cB1 d L * (cF d L + 3 * cN d L N) + 2 * cN d L N

omit [NeZero L] in
theorem cA_ge : 1 ≤ cA d L N := by
  unfold cA commKConst
  have : (0 : ℝ) ≤ N * (2 * d + 8) := by positivity
  have : (0 : ℝ) ≤ N * (2 * d * L + 1 + 4 * d) := by positivity
  have : (0 : ℝ) ≤ N := by positivity
  linarith

theorem cB1_ge : 1 ≤ cB1 d L := by
  unfold cB1; have := greenSupConst_nonneg d L; linarith

omit [NeZero L] in
theorem cF_pos : 0 < cF d L := by unfold cF; positivity

theorem cTau_pos : 0 < cTau d L N := by
  have := cA_ge d L N; have := cB1_ge d L
  unfold cTau; positivity

theorem cTau_spec : 15 * cA d L N * cB1 d L ^ 2 * cTau d L N = 1 := by
  have := cA_ge d L N; have := cB1_ge d L
  unfold cTau; field_simp

theorem cN_pos : 0 < cN d L N := by
  have := cA_ge d L N; have := cB1_ge d L; have := cF_pos d L
  unfold cN; positivity

theorem c6_pos (hd : 0 < d) : 0 < c6 d L N := by
  have := gamma1_pos hd; have := cTau_pos d L N
  unfold c6; positivity

theorem deltaStar_pos (hd : 0 < d) : 0 < deltaStar d L N := by
  have := gamma1_pos hd; have := cTau_pos d L N; have := c6_pos d L N hd
  have := cN_pos d L N; have := cF_pos d L
  unfold deltaStar; positivity

variable {d L N}

theorem selfBound_le (hd : 0 < d) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar d L N) (hδ₁ : δ₁ ≤ deltaStar d L N) :
    selfBound d L N δ₀ (cF d L * δ₁) (5 * δ₁) ≤ cN d L N * δ₁ := by
  have hτ := cTau_pos d L N
  have hA := cA_ge d L N
  have hB1 := cB1_ge d L
  have hcF := cF_pos d L
  have hB0 := greenSupConst_nonneg d L
  have hs1 : deltaStar d L N ≤ cTau d L N / 3 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hs3 : deltaStar d L N ≤ 1 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs5 : deltaStar d L N ≤ cTau d L N / (3 * cF d L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hFb : cF d L * δ₁ ≤ cTau d L N / 3 := by
    have : δ₁ ≤ cTau d L N / (3 * cF d L) := hδ₁.trans hs5
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hFb0 : 0 ≤ cF d L * δ₁ := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hK0 : (0 : ℝ) ≤ commKConst d L N := by unfold commKConst; positivity
  have hz0 : (0 : ℝ) ≤ N * (2 * d + 8) := by positivity
  have hKA : commKConst d L N ≤ cA d L N := by unfold cA; linarith
  have hNA : (N : ℝ) ≤ cA d L N := by unfold cA; linarith
  have hzA : (N : ℝ) * (2 * d + 8) ≤ cA d L N := by unfold cA; linarith
  have hBB : greenSupConst d L ≤ cB1 d L := by unfold cB1; linarith
  have hBF : cB1 d L * (cF d L * δ₁) ≤ 1 := by
    have hBt : cB1 d L * cTau d L N ≤ 1 / 15 := by
      have h1 : 0 ≤ cA d L N * cB1 d L - 1 := by nlinarith
      have := cTau_spec d L N
      nlinarith [mul_nonneg h1 (mul_nonneg (by linarith : 0 ≤ cB1 d L) hτ.le)]
    nlinarith
  have hself := arith_self (A := cA d L N) (B1 := cB1 d L) (B := greenSupConst d L)
    (Fb := cF d L * δ₁) (Gb := 5 * δ₁) (δ₀ := δ₀) (x := N) (y := commKConst d L N)
    (e := 2 * d + 8) (δ₁ := δ₁) (CF := cF d L) hA hB1 hB0 hBB hNA hKA hzA h0
    (hδ₀.trans hs3) hFb0 hBF rfl rfl
  unfold selfBound coreBound
  unfold cN
  exact hself

theorem coreHyp_small (hd : 0 < d) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar d L N) (hδ₁ : δ₁ ≤ deltaStar d L N) :
    CoreHyp N (greenSupConst d L) (commKConst d L N) (2 * d + 8) (gamma1 d) δ₀ (cF d L * δ₁)
      (5 * δ₁) (c6 d L N) := by
  have hg := gamma1_pos hd
  have hτ := cTau_pos d L N
  have hA := cA_ge d L N
  have hB1 := cB1_ge d L
  have hcF := cF_pos d L
  have hcN := cN_pos d L N
  have hc6 := c6_pos d L N hd
  have hB0 := greenSupConst_nonneg d L
  have hs1 : deltaStar d L N ≤ cTau d L N / 3 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hs2 : deltaStar d L N ≤ gamma1 d / 4 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hs3 : deltaStar d L N ≤ 1 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs4 : deltaStar d L N ≤ c6 d L N / (2 * cN d L N) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs5 : deltaStar d L N ≤ cTau d L N / (3 * cF d L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hc6a : c6 d L N ≤ gamma1 d / 4 := min_le_left _ _
  have hc6b : c6 d L N ≤ 2 * cTau d L N / 9 := min_le_right _ _
  have hFb : cF d L * δ₁ ≤ cTau d L N / 3 := by
    have : δ₁ ≤ cTau d L N / (3 * cF d L) := hδ₁.trans hs5
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hFb0 : 0 ≤ cF d L * δ₁ := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hK0 : (0 : ℝ) ≤ commKConst d L N := by unfold commKConst; positivity
  have hz0 : (0 : ℝ) ≤ N * (2 * d + 8) := by positivity
  have hNA : (N : ℝ) ≤ cA d L N := by unfold cA; linarith
  have hKA : commKConst d L N ≤ cA d L N := by unfold cA; linarith
  have hzA : (N : ℝ) * (2 * d + 8) ≤ cA d L N := by unfold cA; linarith
  have hBB : greenSupConst d L ≤ cB1 d L := by unfold cB1; linarith
  refine ⟨hc6.le, by linarith, by positivity, ?_, ?_⟩
  · exact arith_lip (A := cA d L N) (B1 := cB1 d L) (B := greenSupConst d L) (Fb := cF d L * δ₁)
      (δ₀ := δ₀) (ρ := c6 d L N) (τ := cTau d L N) (x := N) (y := commKConst d L N)
      (z := N * (2 * d + 8)) hA hB1 hB0 hBB (cTau_spec d L N) hτ.le hN0 hK0 hz0 hNA hKA hzA
      hFb0 h0 hc6.le hFb (hδ₀.trans hs1) (by linarith)
  · have := selfBound_le (N := N) (L := L) hd h0 h1 hδ₀ hδ₁
    unfold selfBound at this
    have hδ' : δ₁ ≤ c6 d L N / (2 * cN d L N) := hδ₁.trans hs4
    rw [le_div_iff₀ (by positivity)] at hδ'
    nlinarith

end Constants

section Source

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The source `F_s = Q* a δΨ + 𝔟(δΨ) + f₁` of (P-1). -/
noncomputable def pertSource (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
    (δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  qStar G a δΨ + boundaryTerm G δΨ + f₁

/-- `|F_s|₂ ≤ (3 + 2 d L²) δ₁` (BACKGROUND.md Prop 5.1, `𝒞_F δ₁`): uses that wall sites are in
layer `1`. -/
theorem pertSource_bound (S : GreenSetting G a ν) {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁)
    (hf : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖f₁ (x, i)‖ ≤ δ₁)
    (x : G.Ω 1) (i : Fin N) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖pertSource G a δΨ f₁ (x, i)‖ ≤ cF d L * δ₁ := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hsp : G.spacing p = (L : ℝ) ^ G.layerIndex p := G.spacing_eq hj1 hjk hxl
  have hℓ : 0 < G.spacing p ^ 2 := by have := spacing_pos G (x := p); positivity
  have hdx : ∀ y ∈ dataSites G, ∀ i, ‖δΨ y i‖ ≤ δ₁ := fun y hy i => (norm_le_vn _ i).trans (hΨ y hy)
  have hpx : p ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
  -- the three pieces
  have t1 : G.spacing p ^ 2 * ‖qStar G a δΨ (x, i)‖ ≤ 2 * δ₁ := by
    unfold qStar
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by
      have := (S.weights _ hj1 hjk).1; positivity)]
    have h2 := (S.weights _ hj1 hjk).2
    have hc : G.spacing p ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2) =
        a (G.layerIndex p) := by
      rw [hsp]; field_simp
    calc G.spacing p ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2 * ‖δΨ x i‖)
        = a (G.layerIndex p) * ‖δΨ x i‖ := by rw [← mul_assoc, hc]
      _ ≤ 2 * δ₁ := mul_le_mul h2 (hdx p hpx i) (norm_nonneg _) (by norm_num)
  have t2 : G.spacing p ^ 2 * ‖boundaryTerm G δΨ (x, i)‖ ≤ 2 * d * (L : ℝ) ^ 2 * δ₁ := by
    unfold boundaryTerm
    change G.spacing p ^ 2 * ‖∑ μ : Fin d, ((if p + Pi.single μ 1 ∈ collar G then
        δΨ (p + Pi.single μ 1) i else 0) + (if p - Pi.single μ 1 ∈ collar G then
        δΨ (p - Pi.single μ 1) i else 0))‖ ≤ 2 * d * (L : ℝ) ^ 2 * δ₁
    by_cases hcol : ∃ μ : Fin d, p + Pi.single μ 1 ∈ collar G ∨ p - Pi.single μ 1 ∈ collar G
    · obtain ⟨μ, hμ⟩ := hcol
      have hone : G.layerIndex p = 1 := by
        rcases hμ with h | h
        · exact layerIndex_eq_one_of_adj_not_mem S.sep_gt_one (by have := S.hL; omega) x.2
            ((mem_collar G).1 h).1 ⟨μ, Or.inl rfl⟩
        · exact layerIndex_eq_one_of_adj_not_mem S.sep_gt_one (by have := S.hL; omega) x.2
            ((mem_collar G).1 h).1 ⟨μ, Or.inr (by simp)⟩
      have hs2 : G.spacing p ^ 2 = (L : ℝ) ^ 2 := by rw [hsp, hone]; ring
      have hterm : ∀ y : Torus d (N₀ * L ^ k), ‖(if y ∈ collar G then δΨ y i else 0)‖ ≤ δ₁ := by
        intro y
        by_cases hy : y ∈ collar G
        · simp only [hy, ↓reduceIte]
          exact hdx y ((mem_dataSites G).2 (Or.inr hy)) i
        · simp [hy, hδ₁]
      have hsum : ‖∑ μ : Fin d, ((if p + Pi.single μ 1 ∈ collar G then δΨ (p + Pi.single μ 1) i
          else 0) + (if p - Pi.single μ 1 ∈ collar G then δΨ (p - Pi.single μ 1) i else 0))‖ ≤
          2 * d * δ₁ := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ μ : Fin d, ‖(if p + Pi.single μ 1 ∈ collar G then δΨ (p + Pi.single μ 1) i else 0) +
              (if p - Pi.single μ 1 ∈ collar G then δΨ (p - Pi.single μ 1) i else 0)‖
            ≤ ∑ _μ : Fin d, (δ₁ + δ₁) := Finset.sum_le_sum fun μ _ =>
              (norm_add_le _ _).trans (add_le_add (hterm _) (hterm _))
          _ = 2 * d * δ₁ := by simp; ring
      rw [hs2]
      calc (L : ℝ) ^ 2 * ‖∑ μ : Fin d, ((if p + Pi.single μ 1 ∈ collar G then
              δΨ (p + Pi.single μ 1) i else 0) + (if p - Pi.single μ 1 ∈ collar G then
              δΨ (p - Pi.single μ 1) i else 0))‖ ≤ (L : ℝ) ^ 2 * (2 * d * δ₁) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    · push Not at hcol
      have : ∀ μ : Fin d, ((if p + Pi.single μ 1 ∈ collar G then δΨ (p + Pi.single μ 1) i else 0) +
          (if p - Pi.single μ 1 ∈ collar G then δΨ (p - Pi.single μ 1) i else 0)) = 0 := by
        intro μ; simp [(hcol μ).1, (hcol μ).2]
      simp only [this, Finset.sum_const_zero, norm_zero, mul_zero]
      positivity
  have t3 := hf x i
  unfold pertSource
  simp only [Pi.add_apply]
  calc G.spacing p ^ 2 * ‖qStar G a δΨ (x, i) + boundaryTerm G δΨ (x, i) + f₁ (x, i)‖
      ≤ G.spacing p ^ 2 * (‖qStar G a δΨ (x, i)‖ + ‖boundaryTerm G δΨ (x, i)‖ + ‖f₁ (x, i)‖) :=
        mul_le_mul_of_nonneg_left (norm_add₃_le) hℓ.le
    _ = G.spacing p ^ 2 * ‖qStar G a δΨ (x, i)‖ + G.spacing p ^ 2 * ‖boundaryTerm G δΨ (x, i)‖ +
        G.spacing p ^ 2 * ‖f₁ (x, i)‖ := by ring
    _ ≤ cF d L * δ₁ := by unfold cF; nlinarith

variable {α₀ : G.Ω 1 → ℂ} {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δ₀ δ₁ : ℝ}

/-- `|H₀ g|₂ ≤ 5 δ₁` from the hypothesis (P4): `|g|₀ ≤ δ₁` and `|Δ g̃|₂ ≤ δ₁`
(BACKGROUND.md has the sum `|g|₀ + |Δ g̃|₂ ≤ δ₁` and the constant `4`; here the two suprema are
bounded separately). -/
theorem Hg_bound (S : GreenSetting G a ν) (hα₀ : ∀ x : G.Ω 1,
      G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₀ x‖ ≤ δ₀) (hδ₀ : δ₀ ≤ 1) (hδ₁ : 0 ≤ δ₁)
    (hg0 : ∀ x : G.Ω 1, ‖gdef G φ₀ x‖ ≤ δ₁)
    (hgl : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖negLap (zeroExt (G.Ω 1) (gdef G φ₀)) (x : Torus d (N₀ * L ^ k))‖ ≤ δ₁)
    (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖(dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x‖ ≤ 5 * δ₁ := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hsp : G.spacing p = (L : ℝ) ^ G.layerIndex p := G.spacing_eq hj1 hjk hxl
  have hℓ : 0 < G.spacing p ^ 2 := by have := spacing_pos G (x := p); positivity
  rw [dirichlet_apply]
  have hz : ∀ y, ‖zeroExt (G.Ω 1) (gdef G φ₀) y‖ ≤ δ₁ := by
    intro y
    by_cases hy : y ∈ G.Ω 1
    · have := hg0 ⟨y, hy⟩
      simpa [zeroExt, hy] using this
    · simp [zeroExt, hy, hδ₁]
  have b1 := blockTerm_norm_le (G := G) S.weights x.2 (f := zeroExt (G.Ω 1) (gdef G φ₀)) hz
  have hc : G.spacing p ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2) ≤ 2 := by
    have h2 := (S.weights _ hj1 hjk).2
    rw [hsp]
    have : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex p) ^ 2 := by positivity
    calc ((L : ℝ) ^ G.layerIndex p) ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2)
        = a (G.layerIndex p) := by field_simp
      _ ≤ 2 := h2
  have hnu : ν * G.spacing p ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ S.mass) S.massLe
    exact pow_le_pow_left₀ (spacing_pos G).le (spacing_le G x.2) 2
  have e1 : G.spacing p ^ 2 * ‖blockTerm G a (zeroExt (G.Ω 1) (gdef G φ₀)) p‖ ≤ 2 * δ₁ := by
    calc _ ≤ G.spacing p ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2 * δ₁) :=
          mul_le_mul_of_nonneg_left b1 hℓ.le
      _ = (G.spacing p ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2)) * δ₁ := by ring
      _ ≤ 2 * δ₁ := mul_le_mul_of_nonneg_right hc hδ₁
  have e2 : G.spacing p ^ 2 * ‖(ν : ℂ) * gdef G φ₀ x‖ ≤ δ₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg S.mass]
    calc G.spacing p ^ 2 * (ν * ‖gdef G φ₀ x‖) = (ν * G.spacing p ^ 2) * ‖gdef G φ₀ x‖ := by ring
      _ ≤ 1 * δ₁ := mul_le_mul hnu (hg0 x) (norm_nonneg _) zero_le_one
      _ = δ₁ := one_mul _
  have e3 : G.spacing p ^ 2 * ‖α₀ x * gdef G φ₀ x‖ ≤ δ₁ := by
    rw [norm_mul]
    calc G.spacing p ^ 2 * (‖α₀ x‖ * ‖gdef G φ₀ x‖) = (G.spacing p ^ 2 * ‖α₀ x‖) * ‖gdef G φ₀ x‖ := by ring
      _ ≤ 1 * δ₁ := mul_le_mul ((hα₀ x).trans hδ₀) (hg0 x) (norm_nonneg _) zero_le_one
      _ = δ₁ := one_mul _
  have e0 := hgl x
  calc G.spacing p ^ 2 * ‖negLap (zeroExt (G.Ω 1) (gdef G φ₀)) p +
        blockTerm G a (zeroExt (G.Ω 1) (gdef G φ₀)) p + ν * gdef G φ₀ x + α₀ x * gdef G φ₀ x‖
      ≤ G.spacing p ^ 2 * (‖negLap (zeroExt (G.Ω 1) (gdef G φ₀)) p‖ +
        ‖blockTerm G a (zeroExt (G.Ω 1) (gdef G φ₀)) p‖ + ‖(ν : ℂ) * gdef G φ₀ x‖ +
        ‖α₀ x * gdef G φ₀ x‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hℓ.le
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ 5 * δ₁ := by nlinarith

variable (G a ν) in
/-- The hypotheses (P1)–(P4) of Proposition 5.1 (BACKGROUND.md §5.1), with
`δ₀, δ₁ ≤ δ_* = deltaStar`.  (P1) the collar/block field `δΨ` has `|δΨ| ≤ δ₁` on `Ω₁ ∪ C`
(block-constancy of `δΨ` is *not* needed and not assumed); (P2) `φ₀` is smooth (`IsSmoothField`)
with `|φ₀| ≤ 3/2` on `Ω₁`; (P3) `|α₀|₂ ≤ δ₀`, `|f₁|₂ ≤ δ₁`; (P4) the defect `g = φ₀ · φ₀ - 1`
satisfies `|g|₀ ≤ δ₁` and `|Δ g̃|₂ ≤ δ₁` (`g̃` the zero extension). -/
structure Prop51Hyp (α₀ : G.Ω 1 → ℂ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) (δ₀ δ₁ : ℝ) : Prop where
  green : GreenSetting G a ν
  δ₀_nn : 0 ≤ δ₀
  δ₁_nn : 0 ≤ δ₁
  δ₀_le : δ₀ ≤ deltaStar d L N
  δ₁_le : δ₁ ≤ deltaStar d L N
  smooth : IsSmoothField G δ₀ φ₀
  phiBd : ∀ x ∈ G.Ω 1, vn (φ₀ x) ≤ 3 / 2
  alpha0 : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₀ x‖ ≤ δ₀
  f₁_bd : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖f₁ (x, i)‖ ≤ δ₁
  dPsi : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁
  g0 : ∀ x : G.Ω 1, ‖gdef G φ₀ x‖ ≤ δ₁
  gl : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
    ‖negLap (zeroExt (G.Ω 1) (gdef G φ₀)) (x : Torus d (N₀ * L ^ k))‖ ≤ δ₁

variable {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {f₁ : G.Ω 1 × Fin N → ℂ}

theorem selfBound_nonneg {δ₀ Fb Gb : ℝ} (h1 : 0 ≤ δ₀) (h2 : 0 ≤ Fb) (h3 : 0 ≤ Gb) :
    0 ≤ selfBound d L N δ₀ Fb Gb := by
  have := greenSupConst_nonneg d L
  have hK : 0 ≤ commKConst d L N := by unfold commKConst; positivity
  exact coreBound_nonneg this hK (by positivity) h1 h2 h3

theorem deltaStar_le_one : deltaStar d L N ≤ 1 :=
  (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

/-- The data of Proposition 5.1 give the `Setup` of the abstract core (mode U) for `H₀ = H_D(α₀)`:
the three operator bounds are the landed `Hg_bound`, `commK_bound` and `Rvec_bound`. -/
theorem Prop51Hyp.setup (H : Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁) :
    Setup G (dirichletOperator G a ν α₀) true (commKConst d L N) (2 * d + 8) α₀ φ₀
      (pertSource G a δΨ f₁) δ₀ (cF d L * δ₁) (5 * δ₁) where
  δ₀_nn := H.δ₀_nn
  Fb_nn := by have := cF_pos d L; have := H.δ₁_nn; positivity
  Gb_nn := by have := H.δ₁_nn; positivity
  Kc_nn := by unfold commKConst; positivity
  Rc_nn := by positivity
  phiBd := H.phiBd
  alpha0 := H.alpha0
  Fs_bd := pertSource_bound H.green H.δ₁_nn H.dPsi H.f₁_bd
  g_bd := fun _ x => Hg_bound H.green H.alpha0 (H.δ₀_le.trans deltaStar_le_one) H.δ₁_nn H.g0 H.gl x
  comm_bd := fun hV hs x => commK_bound (by have := H.green.hd; omega)
    (by have := H.green.hL; omega) H.green.weights ν α₀ H.smooth H.δ₀_nn hV hs x
  R_bd := fun hV hW hv hw x => Rvec_bound H.green.weights H.green.mass H.green.massLe
    (fun y => (H.alpha0 y).trans (H.δ₀_le.trans deltaStar_le_one)) hV hW hv hw x

/-- **Proposition 5.1 (existence, uniqueness, bounds)** (BACKGROUND.md §5.1; P2 Lemma 3.2 and
Prop 3.1 at `λ = ∞`).  There are constants `c₆ = c6 d L N`, `δ_* = deltaStar d L N`,
`K₂ = cK2 d L N` depending only on `(d, L, N)` such that under (P1)–(P4) with `δ₀, δ₁ ≤ δ_*`
the system (P-1), (P-2) has a solution with `|δφ|₀, |∂δφ|₁, |Δ^D δφ|₂ ≤ K₂ δ₁` and
`|δα|₂ ≤ K₂ δ₁`, and it is the only solution with `|δα|₂ ≤ c₆`.  Norms are the component-wise
suprema (`SupBounds`, `Small`). -/
theorem prop51_exists_unique (hd : 0 < d) (H : Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁) :
    ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
      IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ δα ∧
      Small G δα (cK2 d L N * δ₁) ∧ SupBounds G δφ (cK2 d L N * δ₁) ∧
      ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
        IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ' δα' →
        Small G δα' (c6 d L N) → δφ' = δφ ∧ δα' = δα := by
  have hS := H.setup
  have hC := coreHyp_small hd H.δ₀_nn H.δ₁_nn H.δ₀_le H.δ₁_le
  obtain ⟨δφ, δα, hP, hsmall, hsup, huniq⟩ := prop51_core_D H.green hS hC
  have hsb := selfBound_le (N := N) (L := L) hd H.δ₀_nn H.δ₁_nn H.δ₀_le H.δ₁_le
  have hsb0 := selfBound_nonneg (d := d) (L := L) (N := N) H.δ₀_nn hS.Fb_nn hS.Gb_nn
  have hB1 := cB1_ge d L
  have hF := cF_pos d L
  have hN := cN_pos d L N
  have hδ1 := H.δ₁_nn
  refine ⟨δφ, δα, hP, ?_, ?_, huniq⟩
  · intro x
    refine (hsmall x).trans ?_
    unfold cK2
    nlinarith [mul_nonneg (by linarith : 0 ≤ cB1 d L) (mul_nonneg hF.le hδ1), mul_nonneg hN.le hδ1,
      mul_nonneg (mul_nonneg (by linarith : 0 ≤ cB1 d L) hN.le) hδ1]
  · refine hsup.mono ?_
    unfold cK2
    have hB := greenSupConst_nonneg d L
    have : greenSupConst d L ≤ cB1 d L := by unfold cB1; linarith
    calc greenSupConst d L * (cF d L * δ₁ + 3 / 2 * (2 * selfBound d L N δ₀ (cF d L * δ₁) (5 * δ₁)))
        ≤ cB1 d L * (cF d L * δ₁ + 3 * (cN d L N * δ₁)) := by
          refine mul_le_mul this (by linarith) (by positivity) (by linarith)
      _ ≤ _ := by nlinarith [mul_nonneg hN.le hδ1]

end Source

end Balaban.Background
