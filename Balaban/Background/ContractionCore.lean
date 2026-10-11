/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.AbstractGreen
public import Balaban.Analysis.Contraction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fixed-point core of Proposition 5.1 for an abstract Green family

BACKGROUND.md §5.1 (Proposition 5.1) and LOCALIZATION.md §3.2 (Theorem I-4a), requirement R-B2.
Nothing here mentions `dirichletOperator`: the Green's function is an abstract family `𝒢`
(`GreenFamily`), the operator `H₀` entering the commutator and `R` terms is an arbitrary matrix
with the two bounds of `Setup`, and the map `𝒩` has a mode parameter `ιU`:

* mode U (`ιU = true`): `𝒩 = (φ₀ + δφ)·F_s - K δφ + ½ R(δφ) + ½ H₀ g̃`;
* mode P (`ιU = false`): the same without the last term.

The core stops at the fixed point of `δα ↦ 𝒩(δφ(δα))`: `exists_fixed`, `prop51_core`.  The passage
from the fixed point to the system (P-1), (P-2) is specific to `G_D` and lives in
`Balaban/Background/Contraction.lean`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Algebra

variable {G : GeneratingSet d L N₀ k ϱ}

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

end Algebra

section Core

variable {G : GeneratingSet d L N₀ k ϱ}

variable (G) in
/-- The map `𝒩` of (5.2), with the mode parameter `ιU`:
`𝒩 = (φ₀ + δφ)·F_s - K δφ + ½ R(δφ) + ι_U ½ H₀ g̃`. -/
noncomputable def Nmap (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) : G.Ω 1 → ℂ := fun x =>
  ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)
    - (commK H₀ (restrictField G φ₀) *ᵥ δφ) x
    + (1 / 2) * Rvec H₀ δφ δφ x
    + (if ιU then (1 / 2) * (H₀ *ᵥ gdef G φ₀) x else 0)

variable (G) in
/-- `δφ(δα) = 𝒢(α₀ + δα) (F_s - δα φ₀)`. -/
noncomputable def dphi (𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    G.Ω 1 × Fin N → ℂ :=
  liftOp N (𝒢 (α₀ + δα)) *ᵥ Fsrc φ₀ Fs δα

/-- The standing data of the core (BACKGROUND.md Prop 5.1 (P2)–(P4)), with the bounds as numbers:
`|φ₀| ≤ 3/2`, `|α₀|₂ ≤ δ₀`, `|F_s|₂ ≤ Fb`, and, in mode U, `|H₀ g|₂ ≤ Gb` for `g = φ₀·φ₀ - 1`;
the commutator bound `|K s|₂ ≤ Kc δ₀ V` and the bound `|R(v,w)|₂ ≤ N Rc V W` of `H₀` for fields
with `|·|₀, |∂·|₁ ≤ V`, `W`. -/
structure Setup (G : GeneratingSet d L N₀ k ϱ) (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (Kc Rc : ℝ) (α₀ : G.Ω 1 → ℂ) (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (Fs : G.Ω 1 × Fin N → ℂ) (δ₀ Fb Gb : ℝ) : Prop where
  δ₀_nn : 0 ≤ δ₀
  Fb_nn : 0 ≤ Fb
  Gb_nn : 0 ≤ Gb
  Kc_nn : 0 ≤ Kc
  Rc_nn : 0 ≤ Rc
  phiBd : ∀ x ∈ G.Ω 1, vn (φ₀ x) ≤ 3 / 2
  alpha0 : Small G α₀ δ₀
  Fs_bd : SrcBound G Fs Fb
  g_bd : ιU = true → ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
    ‖(H₀ *ᵥ gdef G φ₀) x‖ ≤ Gb
  comm_bd : ∀ {s : G.Ω 1 × Fin N → ℂ} {V : ℝ}, 0 ≤ V → StarBound G s V → ∀ x : G.Ω 1,
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖(commK H₀ (restrictField G φ₀) *ᵥ s) x‖ ≤ Kc * δ₀ * V
  R_bd : ∀ {v w : G.Ω 1 × Fin N → ℂ} {V W : ℝ}, 0 ≤ V → 0 ≤ W → StarBound G v V →
    StarBound G w W → ∀ x : G.Ω 1,
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Rvec H₀ v w x‖ ≤ N * (Rc * (V * W))

variable {𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ} {H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ}
  {ιU : Bool} {B Kc Rc γ : ℝ} {α₀ : G.Ω 1 → ℂ}
  {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {δ₀ Fb Gb : ℝ}

theorem Setup.poly (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {δα : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) (hr : δ₀ + r ≤ γ) : Small G (α₀ + δα) γ := fun x =>
  ((H.alpha0.add hδα) x).trans hr

theorem Fsrc_bd (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {δα : G.Ω 1 → ℂ} {r : ℝ}
    (hδα : Small G δα r) : SrcBound G (Fsrc φ₀ Fs δα) (Fb + 3 / 2 * r) := by
  intro x i
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

theorem dphi_star (hG : GreenFamily G N 𝒢 B γ) (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb)
    {δα : G.Ω 1 → ℂ} {r : ℝ} (hδα : Small G δα r) (hr0 : 0 ≤ r) (hr : δ₀ + r ≤ γ) :
    StarBound G (dphi G 𝒢 α₀ φ₀ Fs δα) (B * (Fb + 3 / 2 * r)) := by
  have := H.Fb_nn
  exact hG.bound (H.poly hδα hr) _ (by positivity) (Fsrc_bd H hδα)

/-- The difference of two solutions of the linear problem, from the difference bound of the
family: `δφ(δα) - δφ(δα') = (𝒢(α) - 𝒢(α'))(F_s - δα' φ₀) - 𝒢(α)((δα - δα') φ₀)`. -/
theorem dphi_diff_star (hG : GreenFamily G N 𝒢 B γ) (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb)
    {δα δα' : G.Ω 1 → ℂ} {r Δ : ℝ} (hδα : Small G δα r) (hδα' : Small G δα' r) (hr0 : 0 ≤ r)
    (hr : δ₀ + r ≤ γ) (hΔ0 : 0 ≤ Δ) (hΔ : Small G (δα - δα') Δ) :
    StarBound G (dphi G 𝒢 α₀ φ₀ Fs δα - dphi G 𝒢 α₀ φ₀ Fs δα')
      (B * (Δ * (3 / 2 + B * (Fb + 3 / 2 * r)))) := by
  have hFb := H.Fb_nn
  have e : dphi G 𝒢 α₀ φ₀ Fs δα - dphi G 𝒢 α₀ φ₀ Fs δα' =
      (liftOp N (𝒢 (α₀ + δα)) - liftOp N (𝒢 (α₀ + δα'))) *ᵥ Fsrc φ₀ Fs δα' +
        liftOp N (𝒢 (α₀ + δα)) *ᵥ (Fsrc φ₀ Fs δα - Fsrc φ₀ Fs δα') := by
    unfold dphi
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
    abel
  have h1 := hG.diff (H.poly hδα hr) (H.poly hδα' hr) (Fsrc φ₀ Fs δα') (by positivity)
    (Fsrc_bd H hδα') hΔ0 (by rw [add_sub_add_left_eq_sub]; exact hΔ)
  have hB := hG.B_nn
  have h2 := hG.bound (H.poly hδα hr) (Fsrc φ₀ Fs δα - Fsrc φ₀ Fs δα') (C := Δ * (3 / 2))
    (by positivity) (fun x i => by
      have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
      have hφ : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (H.phiBd x x.2)
      have e2 : (Fsrc φ₀ Fs δα - Fsrc φ₀ Fs δα') (x, i) = -((δα x - δα' x) * φ₀ x i) := by
        simp only [Fsrc, Pi.sub_apply]; ring
      rw [e2, norm_neg, norm_mul]
      calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖δα x - δα' x‖ * ‖φ₀ x i‖)
          = (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x - δα' x‖) * ‖φ₀ x i‖ := by ring
        _ ≤ Δ * (3 / 2) := mul_le_mul (hΔ x) hφ (norm_nonneg _) hΔ0)
  rw [e]
  exact (h1.add h2).mono (le_of_eq (by ring))

theorem Setup.alpha_le (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α₀ x‖ ≤ δ₀ := H.alpha0 x

/-- Bound of `𝒩` for any `δφ` with `|δφ|₀, |∂δφ|₁ ≤ D`. -/
theorem Nmap_bound (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {δφ : G.Ω 1 × Fin N → ℂ} {D : ℝ}
    (hD : 0 ≤ D) (hδφ : StarBound G δφ D) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Nmap G H₀ ιU φ₀ Fs δφ x‖ ≤
      N * ((3 / 2 + D) * Fb) + Kc * δ₀ * D + 1 / 2 * (N * (Rc * (D * D))) + 1 / 2 * Gb := by
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  have hFb := H.Fb_nn
  have hGb := H.Gb_nn
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
  have t2 := H.comm_bd hD hδφ x
  have t3 := H.R_bd hD hD hδφ hδφ x
  have t4 : ℓ2 * ‖(if ιU then (1 / 2) * (H₀ *ᵥ gdef G φ₀) x else 0)‖ ≤ 1 / 2 * Gb := by
    cases ιU
    · simp only [Bool.false_eq_true, ite_false, norm_zero, mul_zero]; positivity
    · have := H.g_bd rfl x
      simp only [ite_true, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
      calc ℓ2 * (1 / 2 * ‖(H₀ *ᵥ gdef G φ₀) x‖) = 1 / 2 * (ℓ2 * ‖(H₀ *ᵥ gdef G φ₀) x‖) := by ring
        _ ≤ _ := by linarith
  unfold Nmap
  calc ℓ2 * ‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i) -
        (commK H₀ (restrictField G φ₀) *ᵥ δφ) x + 1 / 2 * Rvec H₀ δφ δφ x +
        (if ιU then (1 / 2) * (H₀ *ᵥ gdef G φ₀) x else 0)‖
      ≤ ℓ2 * (‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)‖ +
        ‖(commK H₀ (restrictField G φ₀) *ᵥ δφ) x‖ +
        ‖1 / 2 * Rvec H₀ δφ δφ x‖ +
        ‖(if ιU then (1 / 2) * (H₀ *ᵥ gdef G φ₀) x else 0)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hp
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ = ℓ2 * ‖∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)‖ +
        ℓ2 * ‖(commK H₀ (restrictField G φ₀) *ᵥ δφ) x‖ +
        1 / 2 * (ℓ2 * ‖Rvec H₀ δφ δφ x‖) +
        ℓ2 * ‖(if ιU then (1 / 2) * (H₀ *ᵥ gdef G φ₀) x else 0)‖ := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
        ring
    _ ≤ _ := by linarith

theorem Nmap_sub (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ δφ' : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Nmap G H₀ ιU φ₀ Fs δφ x - Nmap G H₀ ιU φ₀ Fs δφ' x =
      ∑ i, (δφ - δφ') (x, i) * Fs (x, i) -
        (commK H₀ (restrictField G φ₀) *ᵥ (δφ - δφ')) x +
        1 / 2 * Rvec H₀ (δφ - δφ') (δφ + δφ') x := by
  unfold Nmap
  rw [← Rvec_sub_self, Matrix.mulVec_sub, Pi.sub_apply]
  have : ∑ i, (δφ - δφ') (x, i) * Fs (x, i) =
      ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i) - ∑ i, (φ₀ x i + δφ' (x, i)) * Fs (x, i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  rw [this]
  ring

theorem Nmap_diff_bound (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb)
    {δφ δφ' : G.Ω 1 × Fin N → ℂ} {E D D' : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (hw : StarBound G (δφ - δφ') E) (h1 : StarBound G δφ D) (h2 : StarBound G δφ' D')
    (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Nmap G H₀ ιU φ₀ Fs δφ x - Nmap G H₀ ιU φ₀ Fs δφ' x‖ ≤
      N * (E * Fb) + Kc * δ₀ * E + 1 / 2 * (N * (Rc * (E * (D + D')))) := by
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
  have t2 := H.comm_bd hE hw x
  have t3 := H.R_bd hE (add_nonneg hD hD') hw (h1.add h2) x
  rw [Nmap_sub]
  calc ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i) -
        (commK H₀ (restrictField G φ₀) *ᵥ (δφ - δφ')) x +
        1 / 2 * Rvec H₀ (δφ - δφ') (δφ + δφ') x‖
      ≤ ℓ2 * (‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖ +
        ‖(commK H₀ (restrictField G φ₀) *ᵥ (δφ - δφ')) x‖ +
        ‖1 / 2 * Rvec H₀ (δφ - δφ') (δφ + δφ') x‖) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) hp
    _ = ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖ +
        ℓ2 * ‖(commK H₀ (restrictField G φ₀) *ᵥ (δφ - δφ')) x‖ +
        1 / 2 * (ℓ2 * ‖Rvec H₀ (δφ - δφ') (δφ + δφ') x‖) := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
        ring
    _ ≤ _ := by linarith

variable (G 𝒢 H₀ ιU α₀ φ₀ Fs) in
/-- The rescaled map `ξ ↦ ℓ² 𝒩(δφ(δα(ξ)))`. -/
noncomputable def Smap (ξ : G.Ω 1 → ℂ) : G.Ω 1 → ℂ := fun x =>
  ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) *
    Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs (toAlpha G ξ)) x

theorem norm_Smap (ξ : G.Ω 1 → ℂ) (x : G.Ω 1) :
    ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x‖ = G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs (toAlpha G ξ)) x‖ := by
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  unfold Smap
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]

/-- The bound for `|𝒩(0)|₂`: with `D₀ = B F_b`,
`N (3/2 + D₀) F_b + K δ₀ D₀ + ½ N R D₀² + ½ G_b`. -/
noncomputable def coreBound (N : ℕ) (B Kc Rc δ₀ Fb Gb : ℝ) : ℝ :=
  N * ((3 / 2 + B * Fb) * Fb) + Kc * δ₀ * (B * Fb) +
    1 / 2 * (N * (Rc * ((B * Fb) * (B * Fb)))) + 1 / 2 * Gb

/-- The numerical conditions of the fixed point argument (`ρ` the radius of the ball of `|δα|₂`,
`γ` the radius of the polydisc of the family). -/
structure CoreHyp (N : ℕ) (B Kc Rc γ δ₀ Fb Gb ρ : ℝ) : Prop where
  ρ_nn : 0 ≤ ρ
  poly : δ₀ + 2 * ρ ≤ γ
  D1_le : 0 ≤ B * (Fb + 3 / 2 * ρ)
  lip : (N * Fb + Kc * δ₀ + N * Rc * (B * (Fb + 3 / 2 * ρ))) *
    (B * (3 / 2 + B * (Fb + 3 / 2 * ρ))) ≤ 1 / 2
  self : coreBound N B Kc Rc δ₀ Fb Gb ≤ ρ / 2

theorem Smap_lip (hG : GreenFamily G N 𝒢 B γ) (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {ρ : ℝ}
    (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ) {ξ ξ' : G.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ)
    (hξ' : ∀ x, ‖ξ' x‖ ≤ ρ) (x : G.Ω 1) :
    ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x - Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ' x‖ ≤ 1 / 2 * ‖ξ - ξ'‖ := by
  have hB0 : 0 ≤ B := hG.B_nn
  have hFb := H.Fb_nn
  have hr : δ₀ + ρ ≤ γ := by linarith [hC.poly, hC.ρ_nn]
  have hs := small_toAlpha G ξ hξ
  have hs' := small_toAlpha G ξ' hξ'
  have hDs := dphi_star hG H hs hC.ρ_nn hr
  have hDs' := dphi_star hG H hs' hC.ρ_nn hr
  have hΔ0 : 0 ≤ ‖ξ - ξ'‖ := norm_nonneg _
  have hΔ : Small G (toAlpha G ξ - toAlpha G ξ') ‖ξ - ξ'‖ := by
    rw [toAlpha_sub]
    exact small_toAlpha G _ (fun y => norm_le_pi_norm (ξ - ξ') y)
  have hdiff := dphi_diff_star hG H hs hs' hC.ρ_nn hr hΔ0 hΔ
  have hE0 : 0 ≤ B * (‖ξ - ξ'‖ * (3 / 2 + B * (Fb + 3 / 2 * ρ))) := by
    have := hC.D1_le; have := hC.ρ_nn; positivity
  have key := Nmap_diff_bound H hE0 hC.D1_le hC.D1_le hdiff hDs hDs' x
  have hnorm : ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x - Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ' x‖ =
      G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs (toAlpha G ξ)) x -
          Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs (toAlpha G ξ')) x‖ := by
    have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
    unfold Smap
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
  rw [hnorm]
  refine key.trans ?_
  have e : ∀ B D1 : ℝ, N * (B * (‖ξ - ξ'‖ * (3 / 2 + D1)) * Fb) +
      Kc * δ₀ * (B * (‖ξ - ξ'‖ * (3 / 2 + D1))) +
      1 / 2 * (N * (Rc * (B * (‖ξ - ξ'‖ * (3 / 2 + D1)) * (D1 + D1)))) =
      ‖ξ - ξ'‖ * ((N * Fb + Kc * δ₀ + N * Rc * D1) *
        (B * (3 / 2 + D1))) := by intro B D1; ring
  rw [e]
  calc _ ≤ ‖ξ - ξ'‖ * (1 / 2) := mul_le_mul_of_nonneg_left hC.lip hΔ0
    _ = _ := by ring

theorem coreBound_nonneg (hB : 0 ≤ B) (hK : 0 ≤ Kc) (hR : 0 ≤ Rc) {δ₀ Fb Gb : ℝ} (h1 : 0 ≤ δ₀)
    (h2 : 0 ≤ Fb) (h3 : 0 ≤ Gb) : 0 ≤ coreBound N B Kc Rc δ₀ Fb Gb := by
  unfold coreBound
  positivity

theorem Smap_zero_bound (hG : GreenFamily G N 𝒢 B γ)
    (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {ρ : ℝ} (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ)
    (x : G.Ω 1) : ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x‖ ≤ coreBound N B Kc Rc δ₀ Fb Gb := by
  have hr : δ₀ + 0 ≤ γ := by linarith [hC.poly, hC.ρ_nn]
  have h0 : Small G (toAlpha G (0 : G.Ω 1 → ℂ)) 0 :=
    small_toAlpha G _ (fun y => by simp)
  have hD := dphi_star hG H h0 le_rfl hr
  have hF := H.Fb_nn
  have hB0 := hG.B_nn
  have hD0 : 0 ≤ B * Fb := by positivity
  have hs : StarBound G (dphi G 𝒢 α₀ φ₀ Fs (toAlpha G 0)) (B * Fb) := by
    simpa using hD
  rw [norm_Smap]
  exact Nmap_bound H hD0 hs x

theorem Smap_lip_norm (hG : GreenFamily G N 𝒢 B γ)
    (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {ρ : ℝ} (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ)
    (ξ ξ' : G.Ω 1 → ℂ) (hξ : ξ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ)
    (hξ' : ξ' ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ) :
    ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ - Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ'‖ ≤ 1 / 2 * ‖ξ - ξ'‖ := by
  rw [mem_closedBall_zero_iff] at hξ hξ'
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => ?_
  exact Smap_lip hG H hC (fun y => (norm_le_pi_norm ξ y).trans hξ)
    (fun y => (norm_le_pi_norm ξ' y).trans hξ') x

theorem Smap_mem_ball (hG : GreenFamily G N 𝒢 B γ)
    (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb) {ρ : ℝ} (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ) :
    ∀ ξ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ,
      Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ := by
  have hρ := hC.ρ_nn
  intro ξ hξ
  rw [mem_closedBall_zero_iff] at hξ ⊢
  refine (pi_norm_le_iff_of_nonneg hρ).2 fun x => ?_
  have h1 := Smap_lip hG H hC (ξ := ξ) (ξ' := 0) (fun y => (norm_le_pi_norm ξ y).trans hξ)
    (fun y => by simp [hρ]) x
  have h0 := Smap_zero_bound hG H hC x
  have := hC.self
  have e : ‖(ξ - 0)‖ ≤ ρ := by simpa using hξ
  calc ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x‖ ≤ ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x -
        Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x‖ + ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x‖ := by
        have := norm_add_le (Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x - Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x)
          (Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x)
        simpa using this
    _ ≤ ρ := by linarith

/-- The fixed point of `δα ↦ 𝒩(δφ(δα))` in the ball `|δα|₂ ≤ ρ`: existence, the size
`|δα|₂ ≤ 2 coreBound`, and uniqueness in the ball. -/
theorem exists_fixed (hG : GreenFamily G N 𝒢 B γ) (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb)
    {ρ : ℝ} (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ) :
    ∃ δα : G.Ω 1 → ℂ, Small G δα ρ ∧
      Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs δα) = δα ∧
      Small G δα (2 * coreBound N B Kc Rc δ₀ Fb Gb) ∧
      ∀ δα' : G.Ω 1 → ℂ, Small G δα' ρ →
        Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs δα') = δα' → δα' = δα := by
  have hρ := hC.ρ_nn
  have hmaps := Smap_mem_ball hG H hC
  obtain ⟨ξ, hξB, hfix, huniq, -⟩ := Balaban.Analysis.exists_unique_fixedPoint_closedBall
    (S := Smap G 𝒢 H₀ ιU α₀ φ₀ Fs) hρ (by norm_num) (by norm_num) hmaps
    (fun ξ hξ ξ' hξ' => Smap_lip_norm hG H hC ξ ξ' hξ hξ')
  rw [mem_closedBall_zero_iff] at hξB
  have hξx : ∀ x, ‖ξ x‖ ≤ ρ := fun x => (norm_le_pi_norm ξ x).trans hξB
  have hfixx : ∀ x, Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x = ξ x := fun x => congrFun hfix x
  refine ⟨toAlpha G ξ, small_toAlpha G ξ hξx, ?_, ?_, ?_⟩
  · funext x
    have hp : ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
      exact_mod_cast (by positivity : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≠ 0)
    have := hfixx x
    unfold Smap at this
    simp only [toAlpha]
    rw [eq_div_iff hp, mul_comm]
    exact this
  · have hb0 := coreBound_nonneg (N := N) hG.B_nn H.Kc_nn H.Rc_nn H.δ₀_nn H.Fb_nn H.Gb_nn
    have hb : ‖ξ‖ ≤ 2 * coreBound N B Kc Rc δ₀ Fb Gb := by
      have hx : ∀ x, ‖ξ x‖ ≤ 1 / 2 * ‖ξ‖ + coreBound N B Kc Rc δ₀ Fb Gb := by
        intro x
        have h1 := Smap_lip hG H hC (ξ := ξ) (ξ' := 0) hξx (fun y => by simp [hρ]) x
        have h0 := Smap_zero_bound hG H hC x
        have e : ‖(ξ - 0)‖ = ‖ξ‖ := by simp
        rw [e] at h1
        calc ‖ξ x‖ = ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x‖ := by rw [hfixx]
          _ ≤ ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x - Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x‖ +
              ‖Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x‖ := by
            have := norm_add_le (Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ x - Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x)
              (Smap G 𝒢 H₀ ιU α₀ φ₀ Fs 0 x)
            simpa using this
          _ ≤ _ := by linarith
      have := (pi_norm_le_iff_of_nonneg (by positivity)).2 hx
      linarith
    exact small_toAlpha G ξ (fun x => (norm_le_pi_norm ξ x).trans hb)
  · intro δα' hs' hf'
    have := huniq (ofAlpha G δα') ?_ ?_
    · rw [← this, toAlpha_ofAlpha]
    · rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg hρ).2 fun x => ?_
      rw [norm_ofAlpha]; exact hs' x
    · funext x
      unfold Smap
      rw [toAlpha_ofAlpha, hf']
      rfl

/-- The fixed point of `Smap` in the rescaled variable is a fixed point of `𝒩 ∘ δφ`. -/
theorem fixed_of_Smap_fixed {ξ : G.Ω 1 → ℂ} (hfix : Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ = ξ) :
    Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs (toAlpha G ξ)) = toAlpha G ξ := by
  funext x
  have hp : ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
    exact_mod_cast (by positivity : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≠ 0)
  have := congrFun hfix x
  unfold Smap at this
  simp only [toAlpha]
  rw [eq_div_iff hp, mul_comm]
  exact this

/-- **Proposition 5.1 (core), abstract Green family, modes U and P.**  Under the numerical
conditions of `CoreHyp`, `δα ↦ 𝒩(δφ(δα))` has a fixed point `δα` with `|δα|₂ ≤ 2 coreBound`;
`δφ = dphi δα` has `|δφ|₀, |∂δφ|₁ ≤ B (F_b + 3/2 · 2 coreBound)`; and `δα` is the only fixed point
with `|δα|₂ ≤ ρ`. -/
theorem prop51_core (hG : GreenFamily G N 𝒢 B γ) (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb)
    {ρ : ℝ} (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ) :
    ∃ δα : G.Ω 1 → ℂ, Small G δα ρ ∧
      Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs δα) = δα ∧
      Small G δα (2 * coreBound N B Kc Rc δ₀ Fb Gb) ∧
      StarBound G (dphi G 𝒢 α₀ φ₀ Fs δα) (B * (Fb + 3 / 2 * (2 * coreBound N B Kc Rc δ₀ Fb Gb))) ∧
      ∀ δα' : G.Ω 1 → ℂ, Small G δα' ρ →
        Nmap G H₀ ιU φ₀ Fs (dphi G 𝒢 α₀ φ₀ Fs δα') = δα' → δα' = δα := by
  obtain ⟨δα, hs, hfix, hsb, huniq⟩ := exists_fixed hG H hC
  have hb0 := coreBound_nonneg (N := N) hG.B_nn H.Kc_nn H.Rc_nn H.δ₀_nn H.Fb_nn H.Gb_nn
  have hρ := hC.ρ_nn
  have hr2 : δ₀ + 2 * coreBound N B Kc Rc δ₀ Fb Gb ≤ γ := by linarith [hC.poly, hC.self]
  exact ⟨δα, hs, hfix, hsb, dphi_star hG H hsb (by positivity) hr2, huniq⟩

end Core

end Balaban.Background
