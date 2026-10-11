/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Calculus
public import Balaban.Background.Data
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

/-- `R` is symmetric. -/
theorem Rsc_comm (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (u w : G.Ω 1 → ℂ) : Rsc H u w = Rsc H w u := by
  unfold Rsc
  rw [mul_comm u w]
  funext x
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

/-- Polarisation: `R(v,v) - R(v',v') = R(v - v', v + v')`. -/
theorem Rvec_sub_self (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v v' : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Rvec H v v x - Rvec H v' v' x = Rvec H (v - v') (v + v') x := by
  unfold Rvec
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ (s t : G.Ω 1 × Fin N → ℂ), comp G (s - t) i = comp G s i - comp G t i := fun s t => rfl
  have hc' : ∀ (s t : G.Ω 1 × Fin N → ℂ), comp G (s + t) i = comp G s i + comp G t i := fun s t => rfl
  rw [hc, hc']
  generalize comp G v i = a
  generalize comp G v' i = b
  unfold Rsc
  have e : (a - b) * (a + b) = a * a - b * b := by funext y; simp [Pi.mul_apply]; ring
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  rw [e]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Pi.sub_apply, Pi.add_apply]
  ring


variable (G a ν) in
/-- The defect `g = φ₀ · φ₀ - 1` on `Ω₁` (BACKGROUND.md (P4)). -/
def gdef (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : G.Ω 1 → ℂ :=
  fun x => ∑ i, φ₀ x i * φ₀ x i - 1

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
/-- The map `𝒩` of (5.2): `𝒩 = (φ₀ + δφ)·F_s - K δφ + ½ R(δφ) + ½ H₀ g̃`. -/
noncomputable def Nmap (α₀ : G.Ω 1 → ℂ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs δφ : G.Ω 1 × Fin N → ℂ) : G.Ω 1 → ℂ := fun x =>
  ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)
    - (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x
    + (1 / 2) * Rvec (dirichletOperator G a ν α₀) δφ δφ x
    + (1 / 2) * (dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x

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
      2 * (Nmap G a ν α₀ φ₀ Fs δφ x - δα x) := by
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

/-- The standing data of the perturbed system (BACKGROUND.md Prop 5.1 (P2)–(P4)), with the
bounds as numbers: `φ₀` smooth with constant `δ₀` and `|φ₀| ≤ 3/2`, `|α₀|₂ ≤ δ₀`, `|F_s|₂ ≤ Fb`
and `|H₀ g|₂ ≤ Gb` for `g = φ₀·φ₀ - 1`. -/
structure Setup (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ) (δ₀ Fb Gb : ℝ) :
    Prop where
  green : GreenSetting G a ν
  δ₀_nn : 0 ≤ δ₀
  δ₀_le : δ₀ ≤ 1
  Fb_nn : 0 ≤ Fb
  Gb_nn : 0 ≤ Gb
  smooth : IsSmoothField G δ₀ φ₀
  phiBd : ∀ x ∈ G.Ω 1, vn (φ₀ x) ≤ 3 / 2
  alpha0 : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₀ x‖ ≤ δ₀
  Fs_bd : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Fs (x, i)‖ ≤ Fb
  g_bd : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
    ‖(dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x‖ ≤ Gb

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α₀ : G.Ω 1 → ℂ}
  {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {δ₀ Fb Gb : ℝ}

/-- The source of the linear problem: `F_s - δα φ₀`. -/
def Fsrc (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    G.Ω 1 × Fin N → ℂ := fun p => Fs p - δα p.1 * φ₀ p.1 p.2

variable (G a ν α₀ φ₀ Fs) in
/-- `δφ(δα) = G(α₀ + δα) (F_s - δα φ₀)`. -/
noncomputable def dphi (δα : G.Ω 1 → ℂ) : G.Ω 1 × Fin N → ℂ :=
  liftOp N (dirichletOperator G a ν (α₀ + δα))⁻¹ *ᵥ Fsrc φ₀ Fs δα

/-- `|δα|₂ ≤ r`. -/
def Small (G : GeneratingSet d L N₀ k ϱ) (δα : G.Ω 1 → ℂ) (r : ℝ) : Prop :=
  ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ ≤ r

theorem Setup.poly (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δα : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) (hr : δ₀ + r ≤ gamma1 d) :
    ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(α₀ + δα) x‖ ≤ gamma1 d := by
  intro x
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  calc _ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α₀ x‖ + ‖δα x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hp
    _ = _ + _ := by ring
    _ ≤ δ₀ + r := add_le_add (H.alpha0 x) (hδα x)
    _ ≤ _ := hr

theorem Fsrc_bd (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δα : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) (x : G.Ω 1) (i : Fin N) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Fsrc φ₀ Fs δα (x, i)‖ ≤ Fb + 3 / 2 * r := by
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have h1 : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (H.phiBd x x.2)
  calc _ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖Fs (x, i)‖ + ‖δα x‖ * ‖φ₀ x i‖) := by
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hp
        rw [norm_mul]
    _ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Fs (x, i)‖ +
        (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖) * ‖φ₀ x i‖ := by ring
    _ ≤ Fb + r * (3 / 2) := by
        refine add_le_add (H.Fs_bd x i) (mul_le_mul (hδα x) h1 (norm_nonneg _) ?_)
        exact le_trans (mul_nonneg hp (norm_nonneg _)) (hδα x)
    _ = _ := by ring

theorem dphi_sup (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δα : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) (hr0 : 0 ≤ r) (hr : δ₀ + r ≤ gamma1 d) :
    SupBounds G (dphi G a ν α₀ φ₀ Fs δα) (greenSupConst d L * (Fb + 3 / 2 * r)) := by
  have := H.Fb_nn
  exact H.green.green_bound (H.poly hδα hr) _ (by positivity) (Fsrc_bd H hδα)

theorem liftOp_inv_mulVec {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hM : IsUnit M)
    (w : G.Ω 1 × Fin N → ℂ) : liftOp N M⁻¹ *ᵥ (liftOp N M *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← liftOp_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hM),
    liftOp_one, Matrix.one_mulVec]

theorem liftOp_mulVec_inv {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hM : IsUnit M)
    (w : G.Ω 1 × Fin N → ℂ) : liftOp N M *ᵥ (liftOp N M⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← liftOp_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM),
    liftOp_one, Matrix.one_mulVec]

theorem dphi_eq (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δα : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) (hr : δ₀ + r ≤ gamma1 d) :
    liftOp N (dirichletOperator G a ν (α₀ + δα)) *ᵥ dphi G a ν α₀ φ₀ Fs δα = Fsrc φ₀ Fs δα :=
  liftOp_mulVec_inv (H.green.isUnit (H.poly hδα hr)) _

/-- The difference identity:
`δφ(δα) - δφ(δα') = -G(α₀ + δα)[(δα - δα')(φ₀ + δφ(δα'))]`. -/
theorem dphi_diff (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δα δα' : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) (hδα' : Small G δα' r) (hr : δ₀ + r ≤ gamma1 d) :
    dphi G a ν α₀ φ₀ Fs δα - dphi G a ν α₀ φ₀ Fs δα' =
      liftOp N (dirichletOperator G a ν (α₀ + δα))⁻¹ *ᵥ
        fun p => -((δα p.1 - δα' p.1) * (φ₀ p.1 p.2 + dphi G a ν α₀ φ₀ Fs δα' p)) := by
  have hU := H.green.isUnit (H.poly hδα hr)
  have e1 := dphi_eq H hδα hr
  have e2 := dphi_eq H hδα' hr
  rw [← liftOp_inv_mulVec hU (dphi G a ν α₀ φ₀ Fs δα - dphi G a ν α₀ φ₀ Fs δα')]
  congr 1
  ext p
  rw [Matrix.mulVec_sub, Pi.sub_apply, e1]
  have hA : α₀ + δα = (α₀ + δα') + (δα - δα') := by abel
  rw [hA, liftOp_dirichlet_add (α₀ := α₀ + δα')]
  have := congrFun e2 p
  rw [this]
  simp only [Fsrc, Pi.sub_apply]
  ring

theorem dphi_diff_sup (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δα δα' : G.Ω 1 → ℂ} {r Δ D1 : ℝ}
    (hδα : Small G δα r) (hδα' : Small G δα' r) (hr : δ₀ + r ≤ gamma1 d) (hΔ0 : 0 ≤ Δ)
    (hD1 : 0 ≤ D1) (hΔ : Small G (δα - δα') Δ)
    (hv : ∀ (x : G.Ω 1) (i : Fin N), ‖dphi G a ν α₀ φ₀ Fs δα' (x, i)‖ ≤ D1) :
    SupBounds G (dphi G a ν α₀ φ₀ Fs δα - dphi G a ν α₀ φ₀ Fs δα')
      (greenSupConst d L * (Δ * (3 / 2 + D1))) := by
  rw [dphi_diff H hδα hδα' hr]
  refine H.green.green_bound (H.poly hδα hr) _ (by positivity) (fun x i => ?_)
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have h1 : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (H.phiBd x x.2)
  simp only [norm_neg, norm_mul]
  calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        (‖δα x - δα' x‖ * ‖φ₀ x i + dphi G a ν α₀ φ₀ Fs δα' (x, i)‖)
      = (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x - δα' x‖) *
        ‖φ₀ x i + dphi G a ν α₀ φ₀ Fs δα' (x, i)‖ := by ring
    _ ≤ Δ * (3 / 2 + D1) := mul_le_mul (hΔ x) ((norm_add_le _ _).trans (add_le_add h1 (hv x i)))
        (norm_nonneg _) hΔ0

theorem Setup.alpha_le_one (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₀ x‖ ≤ 1 := (H.alpha0 x).trans H.δ₀_le

/-- Bound of `𝒩` for any `δφ` with `|δφ|₀, |∂δφ|₁ ≤ D`. -/
theorem Nmap_bound (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δφ : G.Ω 1 × Fin N → ℂ} {D : ℝ}
    (hD : 0 ≤ D) (hδφ : StarBound G δφ D) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Nmap G a ν α₀ φ₀ Fs δφ x‖ ≤
      N * ((3 / 2 + D) * Fb) + commKConst d L N * δ₀ * D + 1 / 2 * (N * ((2 * d + 8) * (D * D))) +
        1 / 2 * Gb := by
  have hd : 0 < d := by have := H.green.hd; omega
  have hL : 1 ≤ L := by have := H.green.hL; omega
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have hFb := H.Fb_nn
  set ℓ2 := G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 with hℓ2
  have t1 : ℓ2 * ‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)‖ ≤ N * ((3 / 2 + D) * Fb) := by
    calc ℓ2 * ‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)‖
        ≤ ℓ2 * ∑ i, ‖(φ₀ x i + δφ (x, i)) * Fs (x, i)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp
      _ = ∑ i, (‖φ₀ x i + δφ (x, i)‖ * (ℓ2 * ‖Fs (x, i)‖)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring
      _ ≤ ∑ _i : Fin N, ((3 / 2 + D) * Fb) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (H.phiBd x x.2)
          have h2 : ‖δφ (x, i)‖ ≤ D := by simpa [svec_of_mem] using hδφ.val x i
          exact mul_le_mul ((norm_add_le _ _).trans (add_le_add h1 h2)) (H.Fs_bd x i)
            (by positivity) (by positivity)
      _ = _ := by simp
  have t2 := commK_bound hd hL H.green.weights ν α₀ H.smooth H.δ₀_nn hD hδφ x
  have t3 := Rvec_bound H.green.weights H.green.mass H.green.massLe H.alpha_le_one hD hD hδφ hδφ x
  have t4 := H.g_bd x
  unfold Nmap
  calc ℓ2 * ‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i) -
        (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x +
        1 / 2 * Rvec (dirichletOperator G a ν α₀) δφ δφ x +
        1 / 2 * (dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x‖
      ≤ ℓ2 * (‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)‖ +
        ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x‖ +
        ‖1 / 2 * Rvec (dirichletOperator G a ν α₀) δφ δφ x‖ +
        ‖1 / 2 * (dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hp
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ = ℓ2 * ‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)‖ +
        ℓ2 * ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x‖ +
        1 / 2 * (ℓ2 * ‖Rvec (dirichletOperator G a ν α₀) δφ δφ x‖) +
        1 / 2 * (ℓ2 * ‖(dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x‖) := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
        ring
    _ ≤ _ := by linarith

theorem Nmap_sub (a : ℕ → ℝ) (ν : ℝ) (α₀ : G.Ω 1 → ℂ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs δφ δφ' : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Nmap G a ν α₀ φ₀ Fs δφ x - Nmap G a ν α₀ φ₀ Fs δφ' x =
      ∑ i, (δφ - δφ') (x, i) * Fs (x, i) -
        (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x +
        1 / 2 * Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x := by
  unfold Nmap
  rw [← Rvec_sub_self, Matrix.mulVec_sub, Pi.sub_apply]
  have : ∑ i, (δφ - δφ') (x, i) * Fs (x, i) =
      ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i) - ∑ i, (φ₀ x i + δφ' (x, i)) * Fs (x, i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [this]
  ring

theorem Nmap_diff_bound (H : Setup G a ν α₀ φ₀ Fs δ₀ Fb Gb) {δφ δφ' : G.Ω 1 × Fin N → ℂ}
    {E D D' : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hw : StarBound G (δφ - δφ') E) (h1 : StarBound G δφ D) (h2 : StarBound G δφ' D')
    (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Nmap G a ν α₀ φ₀ Fs δφ x - Nmap G a ν α₀ φ₀ Fs δφ' x‖ ≤
      N * (E * Fb) + commKConst d L N * δ₀ * E +
        1 / 2 * (N * ((2 * d + 8) * (E * (D + D')))) := by
  have hd : 0 < d := by have := H.green.hd; omega
  have hL : 1 ≤ L := by have := H.green.hL; omega
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have hFb := H.Fb_nn
  set ℓ2 := G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 with hℓ2
  have t1 : ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖ ≤ N * (E * Fb) := by
    calc ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖
        ≤ ℓ2 * ∑ i, ‖(δφ - δφ') (x, i) * Fs (x, i)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp
      _ = ∑ i, (‖(δφ - δφ') (x, i)‖ * (ℓ2 * ‖Fs (x, i)‖)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring
      _ ≤ ∑ _i : Fin N, (E * Fb) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 : ‖(δφ - δφ') (x, i)‖ ≤ E := by simpa [svec_of_mem] using hw.val x i
          exact mul_le_mul h2 (H.Fs_bd x i) (by positivity) hE
      _ = _ := by simp
  have t2 := commK_bound hd hL H.green.weights ν α₀ H.smooth H.δ₀_nn hE hw x
  have t3 := Rvec_bound H.green.weights H.green.mass H.green.massLe H.alpha_le_one hE
    (add_nonneg hD hD') hw (h1.add h2) x
  rw [Nmap_sub]
  calc ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i) -
        (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x +
        1 / 2 * Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x‖
      ≤ ℓ2 * (‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖ +
        ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x‖ +
        ‖1 / 2 * Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x‖) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) hp
    _ = ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖ +
        ℓ2 * ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x‖ +
        1 / 2 * (ℓ2 * ‖Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x‖) := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
        ring
    _ ≤ _ := by linarith

end Core

end Balaban.Background
