module

public import Balaban.LargeField.History.StepSpine
public import Balaban.LargeField.Counter.LF2
public import Balaban.LargeField.Region.Generating
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The steps of a flow's region history, and the numerics of the spine construction

`FlowSteps S n R k₀` is the sequence of steps `𝕋_k → 𝕋_{k+1}` of Definition I.3.1 with the
parameters of the counter `S` (`R_base = S.Rb`, `λ = S.lam`, the critical side `crit_j` of the
hull closure for `j ≤ k₀`).  `Zpre k` is the set `Z^pre_k` (empty for `k = 0`), `Comp k` the
type of its components for the width `ω_k`.

The numerical facts of the spine construction follow from the typing conditions `Setting.Ok` and
`s_* ≥ 4`, `s' ≥ 5`: `StepGeom` and `SpineNum` for every step.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The critical side of the hull closure at scale `j`: `crit_j` if `j ≤ k₀`, none otherwise. -/
noncomputable def critOpt (S : Setting) (k0 j : ℕ) : Option ℕ :=
  if j ≤ k0 then some (S.crit j) else none

theorem Setting.omega_eq_omegaW (S : Setting) (j : ℕ) :
    S.omega j = omegaW S.L S.Rb S.lam j := by
  cases j with
  | zero => simp [Setting.omega, omegaW]
  | succ j => simp [Setting.omega, omegaW]

theorem Setting.radiusUnit_eq (S : Setting) (j : ℕ) : radiusUnit S.Rb S.lam j = S.r j := rfl

theorem Setting.Ok.two_le_r {S : Setting} (ok : S.Ok) (j : ℕ) : 2 ≤ S.r j := by
  have h1 := ok.one_le_lam j
  have h2 := ok.two_le_Rb
  have h3 : (2 : ℝ) ≤ S.Rb * S.lam j ^ 2 := by nlinarith
  have h4 : (2 : ℝ) ≤ (S.r j : ℝ) := h3.trans (Setting.le_r j)
  exact_mod_cast h4

/-- The numerical hypotheses of the spine construction hold for every step. -/
theorem Setting.Ok.spineNum {S : Setting} (ok : S.Ok) (s4 : 4 ≤ S.sS) (s5 : 5 ≤ S.sP) (k : ℕ) :
    RegionStep.SpineNum S.d S.L (S.r k) (S.omega (k + 1)) (S.rho k) (S.rho (k + 1)) (S.D (k + 1)) := by
  have hL := ok.cast_L_ge
  have hc := ok.c0_sS
  have hc5 : (5 : ℝ) ≤ S.c0 * (1 - 1 / (S.L : ℝ)) := by
    have : (4 : ℝ) ≤ S.sS := by exact_mod_cast s4
    linarith
  have hc6 : (6 : ℝ) ≤ S.c0 := by
    have := ok.c0_sP
    have : (5 : ℝ) + 1 ≤ S.c0 := by
      have h5 : (5 : ℝ) ≤ S.sP := by exact_mod_cast s5
      have h6 : (S.sP : ℝ) + 1 ≤ S.c0 := by exact_mod_cast this
      linarith
    linarith
  have hrk : (2 : ℝ) ≤ S.r k := by exact_mod_cast ok.two_le_r k
  have hrm : (S.r k : ℝ) ≤ S.r (k + 1) := by exact_mod_cast ok.r_mono (Nat.le_succ k)
  have hx : (S.L : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hL
  have hx0 : 0 < (S.L : ℝ)⁻¹ := by positivity
  have hc0 : (0 : ℝ) ≤ S.c0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : (1 : ℝ) / S.L = (S.L : ℝ)⁻¹ := one_div _
    rw [e1] at hc5
    unfold Setting.rho
    push_cast
    have h1 : (S.c0 : ℝ) * (S.L : ℝ)⁻¹ ≤ S.c0 - 5 := by nlinarith
    have h2 : (S.c0 : ℝ) * (S.L : ℝ)⁻¹ * S.r k ≤ (S.c0 - 5) * S.r k :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : (S.c0 : ℝ) * S.r k ≤ S.c0 * S.r (k + 1) := mul_le_mul_of_nonneg_left hrm hc0
    rw [div_eq_mul_inv]
    nlinarith
  · unfold Setting.rho
    push_cast
    nlinarith
  · have := Setting.omega_eq_omegaW S (k + 1)
    rw [this]
    have := le_omegaW S.L S.Rb S.lam (k + 1)
    omega
  · unfold Setting.D
    have hω : (1 : ℝ) ≤ S.omega (k + 1) := by
      have := Setting.omega_eq_omegaW S (k + 1)
      have h := le_omegaW S.L S.Rb S.lam (k + 1)
      rw [← this] at h
      have : (1 : ℕ) ≤ S.omega (k + 1) := by omega
      exact_mod_cast this
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    linarith

/-- The steps `𝕋_k → 𝕋_{k+1}` of the region calculus with the parameters of the counter `S`
(radii `R`, `n_k = L n_{k+1}`), and the side conditions `s_* ≥ 4`, `s' ≥ 5`. -/
structure FlowSteps (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 : ℕ) where
  ok : S.Ok
  s4 : 4 ≤ S.sS
  s5 : 5 ≤ S.sP
  RH : RadiusHyp S.L S.Rb S.lam R
  hnn : ∀ k, n k = S.L * n (k + 1)
  step : ∀ k, RegionStep S.d S.L (n k) (n (k + 1)) (R (k - 1)) (R k)

namespace FlowSteps

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (F : FlowSteps S n R k0)

/-- `Z^pre_k` (empty for `k = 0`). -/
noncomputable def Zpre : ∀ k, Set (Torus S.d (n k))
  | 0 => ∅
  | k + 1 => (F.step k).Zpre (S.omega (k + 1)) (critOpt S k0 (k + 1))

/-- `Z^pre_k` as a finite set. -/
noncomputable abbrev Zp (k : ℕ) : Finset (Torus S.d (n k)) := finOf (F.Zpre k)

/-- The components of `Z^pre_k` (width `ω_k`). -/
abbrev Comp (k : ℕ) : Type := ↥(comps (S.omega k) (F.Zp k))

theorem Zp_zero : F.Zp 0 = ∅ := by
  ext x; simp [Zp, Zpre]

theorem isEmpty_comp_zero : IsEmpty (F.Comp 0) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨x, hx⟩ := comp_nonempty c.2
  have := comp_subset c.2 hx
  rw [F.Zp_zero] at this
  simp at this

include F in
theorem stepGeom (k : ℕ) :
    StepGeom S.L (n k) (n (k + 1)) (S.omega k) (S.omega (k + 1)) (S.r k) (R (k - 1)) (R k) := by
  have hL := F.ok.two_le_L
  have hRp : R (k - 1) ≤ S.Rb * S.lam k ^ 2 := by
    cases k with
    | zero => simpa using F.RH.le 0
    | succ k => exact F.RH.prev_le (by omega)
  have hrad := F.RH.stepRadii hL k rfl hRp
  rw [← Setting.omega_eq_omegaW, Setting.radiusUnit_eq] at hrad
  have h1 : S.omega k ≤ S.omega (k + 1) := F.ok.omega_mono (Nat.le_succ k)
  have h2 : S.L + 11 ≤ S.omega (k + 1) := by
    rw [Setting.omega_eq_omegaW]; exact le_omegaW _ _ _ _
  have h3 : S.L + 11 ≤ S.omega k := by
    rw [Setting.omega_eq_omegaW]; exact le_omegaW _ _ _ _
  exact ⟨F.hnn k, hrad, coarse_width_lt hL h1 h2, by omega, by omega⟩

end FlowSteps

end Balaban.LargeField
