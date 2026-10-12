/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.TaylorCauchy

/-!
# The Cauchy lemma for `g`-derivatives (OBSERVABLES.md Lemma 3.2), abstract form

Let `p` be a seminorm on a complex normed space `E` (in the application `E` is the space of
complex sources `g` and `p` is the `ℓ¹` norm `‖g‖₁`), and let `a : E → ℂ` be analytic on the open
unit ball `{p < 1}` with `|a| ≤ B` there.  Then at the centre `0`:

* `norm_fderiv_zero_le`: `|a'(0) v| ≤ B` for `p v ≤ 1`;
* `norm_D2_diag_zero_le`: `|a''(0)(v, v)| ≤ 2 B` for `p v ≤ 1`;
* `norm_D2_zero_le`: `|a''(0)(u, v)| ≤ 4 B` for `p u ≤ 1`, `p v ≤ 1` (polarization:
  `a''(u, v) = a''(s, s) - a''(t, t)`, `s = (u + v)/2`, `t = (u - v)/2`).

These are sharper than the constants `2B`, `8B`, `32B` of the document (`norm_fderiv_zero_le_two`,
`norm_D2_zero_le_doc` record the document's constants).  Locality (`a` depends on `g` only through
`g|_Y`) is treated in `Balaban/Observables/CauchyPackages.lean`.
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.Observables

open Balaban.SmallField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The open unit ball `{p < 1}` of a seminorm. -/
def seminormBall (p : Seminorm ℂ E) : Set E := {g | p g < 1}

theorem isOpen_seminormBall {p : Seminorm ℂ E} (hp : Continuous p) : IsOpen (seminormBall p) :=
  isOpen_lt hp continuous_const

theorem zero_mem_seminormBall (p : Seminorm ℂ E) : (0 : E) ∈ seminormBall p := by
  simp [seminormBall]

theorem smul_mem_seminormBall {p : Seminorm ℂ E} {v : E} (hv : p v ≤ 1) {l : ℂ} (hl : ‖l‖ < 1) :
    l • v ∈ seminormBall p := by
  show p (l • v) < 1
  rw [map_smul_eq_mul]
  calc ‖l‖ * p v ≤ ‖l‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ < 1 := by simpa using hl

/-- Cauchy estimate for the Taylor coefficients along a line through `0` inside the unit ball of
a seminorm: `|(d/dλ)^n a(λ v)|₀| ≤ n! B` for `p v ≤ 1`. -/
theorem norm_iteratedDeriv_line_zero_le {p : Seminorm ℂ E} (hp : Continuous p) {f : E → ℂ}
    {B : ℝ} (hf : DifferentiableOn ℂ f (seminormBall p))
    (hB : ∀ g ∈ seminormBall p, ‖f g‖ ≤ B) {v : E} (hv : p v ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (fun l : ℂ => f (l • v)) 0‖ ≤ n.factorial * B := by
  set g : ℂ → ℂ := fun l => f (l • v) with hg
  have key : ∀ r, 0 < r → r < 1 → ‖iteratedDeriv n g 0‖ * r ^ n ≤ n.factorial * B := by
    intro r hr hr1
    have hgd : DifferentiableOn ℂ g (closedBall 0 r) := by
      intro l hl
      have hl' : ‖l‖ < 1 := lt_of_le_of_lt (by simpa using hl) hr1
      have h1 : DifferentiableAt ℂ (fun l : ℂ => l • v) l := by fun_prop
      have hmem : l • v ∈ seminormBall p := smul_mem_seminormBall hv hl'
      have h2 : DifferentiableAt ℂ f (l • v) :=
        (hf (l • v) hmem).differentiableAt ((isOpen_seminormBall hp).mem_nhds hmem)
      exact (h2.comp l h1).differentiableWithinAt
    have hcl : DiffContOnCl ℂ g (ball (0 : ℂ) r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rwa [closure_ball _ hr.ne']
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hcl
      (C := B) (fun l hl => hB _ (smul_mem_seminormBall hv (by
        rw [mem_sphere_zero_iff_norm.mp hl]; exact hr1)))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have := Analysis.mul_pow_le_of_forall_lt (a := ‖iteratedDeriv n g 0‖) (b := n.factorial * B)
    (ρ := 1) n one_pos key
  simpa using this

/-- First derivative at `0`: `|a'(0) v| ≤ B` for `p v ≤ 1`. -/
theorem norm_fderiv_zero_le {p : Seminorm ℂ E} (hp : Continuous p) {f : E → ℂ} {B : ℝ}
    (hf : DifferentiableOn ℂ f (seminormBall p)) (hB : ∀ g ∈ seminormBall p, ‖f g‖ ≤ B)
    {v : E} (hv : p v ≤ 1) : ‖fderiv ℂ f 0 v‖ ≤ B := by
  have h0 : DifferentiableAt ℂ f 0 :=
    (hf 0 (zero_mem_seminormBall p)).differentiableAt
      ((isOpen_seminormBall hp).mem_nhds (zero_mem_seminormBall p))
  have := norm_iteratedDeriv_line_zero_le hp hf hB hv 1
  have e := iteratedDeriv_one_line (f := f) (c := 0) (z := v) (by simpa using h0)
  simp only [zero_add] at e
  rw [e] at this
  simpa using this

/-- The document's constant: `|a'(0) v| ≤ 2 B`. -/
theorem norm_fderiv_zero_le_two {p : Seminorm ℂ E} (hp : Continuous p) {f : E → ℂ} {B : ℝ}
    (hf : DifferentiableOn ℂ f (seminormBall p)) (hB : ∀ g ∈ seminormBall p, ‖f g‖ ≤ B)
    {v : E} (hv : p v ≤ 1) : ‖fderiv ℂ f 0 v‖ ≤ 2 * B := by
  have h := norm_fderiv_zero_le hp hf hB hv
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (zero_mem_seminormBall p))
  linarith

/-- An analytic function on the unit ball is analytic on a norm ball around `0`. -/
theorem exists_ball_subset {p : Seminorm ℂ E} (hp : Continuous p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : E) ρ ⊆ seminormBall p := by
  obtain ⟨ρ, hρ, h⟩ := Metric.isOpen_iff.mp (isOpen_seminormBall hp) 0 (zero_mem_seminormBall p)
  exact ⟨ρ, hρ, h⟩

/-- Pure second derivative: `|a''(0)(v, v)| ≤ 2 B` for `p v ≤ 1`. -/
theorem norm_D2_diag_zero_le {p : Seminorm ℂ E} (hp : Continuous p) {f : E → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (seminormBall p)) (hB : ∀ g ∈ seminormBall p, ‖f g‖ ≤ B)
    {v : E} (hv : p v ≤ 1) : ‖D2 f 0 v v‖ ≤ 2 * B := by
  obtain ⟨ρ, hρ, hsub⟩ := exists_ball_subset hp
  have e := iteratedDeriv_two_line (f := f) (c := 0) (z := v) hρ (fun x hx => hf x (hsub hx))
  have := norm_iteratedDeriv_line_zero_le hp hf.differentiableOn hB hv 2
  simp only [zero_add] at e
  rw [e] at this
  simpa [Nat.factorial, mul_comm] using this

/-- Mixed second derivative by polarization: `|a''(0)(u, v)| ≤ 4 B` for `p u, p v ≤ 1`. -/
theorem norm_D2_zero_le {p : Seminorm ℂ E} (hp : Continuous p) {f : E → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (seminormBall p)) (hB : ∀ g ∈ seminormBall p, ‖f g‖ ≤ B)
    {u v : E} (hu : p u ≤ 1) (hv : p v ≤ 1) : ‖D2 f 0 u v‖ ≤ 4 * B := by
  have h0 : AnalyticAt ℂ f 0 := hf 0 (zero_mem_seminormBall p)
  set s : E := (1 / 2 : ℂ) • (u + v) with hs
  set t : E := (1 / 2 : ℂ) • (u - v) with ht
  have hps : p s ≤ 1 := by
    rw [hs, map_smul_eq_mul]
    have : p (u + v) ≤ 2 := by
      calc p (u + v) ≤ p u + p v := map_add_le_add p u v
        _ ≤ 2 := by linarith
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2]; linarith
  have hpt : p t ≤ 1 := by
    rw [ht, map_smul_eq_mul]
    have : p (u - v) ≤ 2 := by
      calc p (u - v) ≤ p u + p v := map_sub_le_add p u v
        _ ≤ 2 := by linarith
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2]; linarith
  have hid : D2 f 0 u v = D2 f 0 s s - D2 f 0 t t := by
    have hsym := D2_symm h0 u v
    have e1 : D2 f 0 s s = (1 / 4 : ℂ) * (D2 f 0 u u + D2 f 0 u v + D2 f 0 v u + D2 f 0 v v) := by
      simp only [hs, D2_smul_left, D2_smul_right, D2_add_left, D2_add_right]; ring
    have e2 : D2 f 0 t t = (1 / 4 : ℂ) * (D2 f 0 u u - D2 f 0 u v - D2 f 0 v u + D2 f 0 v v) := by
      simp only [ht, D2_smul_left, D2_smul_right, D2_sub_left, D2_sub_right]; ring
    rw [e1, e2, ← hsym]; ring
  have h1 := norm_D2_diag_zero_le hp hf hB hps
  have h2 := norm_D2_diag_zero_le hp hf hB hpt
  rw [hid]
  calc ‖D2 f 0 s s - D2 f 0 t t‖ ≤ ‖D2 f 0 s s‖ + ‖D2 f 0 t t‖ := norm_sub_le _ _
    _ ≤ 4 * B := by linarith

/-- The document's constant: `|a''(0)(u, v)| ≤ 32 B` for `p u, p v ≤ 1`. -/
theorem norm_D2_zero_le_doc {p : Seminorm ℂ E} (hp : Continuous p) {f : E → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (seminormBall p)) (hB : ∀ g ∈ seminormBall p, ‖f g‖ ≤ B)
    {u v : E} (hu : p u ≤ 1) (hv : p v ≤ 1) : ‖D2 f 0 u v‖ ≤ 32 * B := by
  have h := norm_D2_zero_le hp hf hB hu hv
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (zero_mem_seminormBall p))
  linarith

end Balaban.Observables
