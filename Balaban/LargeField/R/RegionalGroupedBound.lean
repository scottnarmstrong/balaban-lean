/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalSourceTerm
public import Balaban.LargeField.R.RegionalTails
public import Balaban.LargeField.R.RegionEnergyAlgebra
public import Balaban.LargeField.R.RegionalBoundArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The grouped regional correction, assembled (Q13-GROUPED §1-§3)

The marginal term of the renormalization step on the region `R` minus the restricted correction of
P5 (1.8) is `B_j = Σ_{y∈R} A_j(y) - Corr_j(R, B)` (`AtermRegion a s R - corrSum ...`).  This file
puts the pieces that landed separately into one chain.

* **(T1) Abstract assembly.**  `grouped_le_of_far`, `grouped_le`, `grouped_le_centred`,
  `grouped_mismatch_corr_le`: from the kernel tail, the near source bound and the triangle
  inequality (`AtermRegion_sub_corrSum`, `far_crossing_le`, `grouped_mismatch_le`).
* **(T2) Power form.**  `grouped_bound_power` and `omitted_tail_power`: under the single hypothesis
  structure `GroupedInputs`, `‖B_j‖ ≤ |R| (C₁ + C₂) E₀ s^(d+α₃)` and the omitted tail is at most
  `|R| C_T E₀ s^(d+α₃)`, with `s = L^{-(k-j)}` (`scaleJ`).  The constants are
  `C_T = K0 d L κ₀ e^{2 L (κ-κ₀)} (p / (e (κ-κ₀) c_h R_*))^p` (`tailConst`, the constant of
  `rate_power_form`, `p = d + α₃`, `c_h = M / L^(m₀+m₁)`), `C₁ = C₀² K_r K_R C_T` (`farConst`), and
  `C₂ = 4 C_s Cmom K0 C₀³ K_r² K_R²` (`v2Const`, `C_s = sourceConstC B`).
* **(T3) The landed regional energy.**  `EresAt_eq_remainder_add_grouped_of_radialCoeff` and
  `EresAt_sub_remainder_le_of_radialCoeff`: `EresAt = Σ_{y∈R} I_j(y) + B_j - (omitted tail)` and the
  bound of the last two by `|R| (C₁ + C₂ + C_T) E₀ s^(d+α₃)`, under the explicit premise `hv1`
  (the correction coefficient `v₁` is the marginal kernel `a`); `EresJ2_sub_remainder_le_of_radialCoeff`
  is the same statement for `EresJ2`.
* **(T4) Sum over scales.**  `charge_sum_grouped`: summed over the gaps `q - j ≥ n₁`, with at most
  `Γ_E s^{-d}` centres per new cube, the charge per new cube is at most
  `Γ_E (C₁ + C₂ + C_T) E₀ L^{-n₁ α₃} / (1 - L^{-α₃})` (from `charge_sum_le`).
* `groupedInputs_nonempty`: `GroupedInputs` is inhabited (zero kernels, any data).

## What is and is not proved

Nothing here bounds the actual renormalization-group terms unconditionally.  Every field of
`GroupedInputs` is an input of one of the landed theorems; none is a step of a proof.  The
inputs that are open for the actual terms are listed in the table below.

## Status of the premises (T5)

LANDED means the named theorem would discharge the premise once instantiated; OPEN-INPUT means a
class bound that exists in another form but is not yet connected; OPEN means not proved anywhere.

| premise (field) | status |
| --- | --- |
| typing data `L^m₀ ∣ N₁`, `j ≤ k`; entropy `Σ e^{-κ₀ sizeJ} ≤ K0` | LANDED (`entropy_polyUniv`) |
| weights `0 ≤ sizeJ`, `D ≤ sizeJ + 2L` | LANDED (`polyUniv_weights`, from `treeLenCovOne_ge_dist`) |
| halo distance `sizeJ ≥ c_h R_{k-1} L^{k-j} - 2L` | LANDED (`regionalHaloDistance`, `sizeJ_ge_of_halo_pair`) |
| exponent identity `3 + 2α = d + α₃ + α₁` (`hrel`) | LANDED as arithmetic (`three_add_two_mul_eq`) once `α = (d-2)/2-γ`, `α₃ = 1-2γ-α₁` |
| `aligned : R' ⊆ alignedIn j Y` | LANDED for `R' = alignedIn j Y` (`alignedIn_mono`) |
| `collar : sset(Y^≈) ⊆ Bc` | OPEN-INPUT.  For the landed `Bc = alignedIn j (thickY R Y)` it holds only if every site of the fine set of `Y^≈` is `L^j`-aligned; the halo lemma has no alignment clause, so for non-aligned `x` the kernel `a(x - y)` would have to be shown to vanish.  Needs a refinement of `farCrossing_le_of_halo` (kernel supported on aligned differences). |
| `a_decomp` (`a` is the sum of per-polymer coefficients over `polyUniv`), `v2_decomp` | OPEN-INPUT.  `aCoefX` is a function on `Finset (Site d)`, `a` here on `CTorus`; the identification through `unlift` and the paving average is `regionalRadialCoefficient` (W245 landed the conditional form `aCoef_avgFamilyA_eq_v1_of_M1`). |
| `a_coeff`, `v2_coeff` (`Σ_x ‖c X y x‖ ≤ A e^{-κ sizeJ}`, `A = E₀/r`, `4E₀/r²`) | OPEN-INPUT.  `PinJet.term.tensA_le` is `‖tensA‖ ≤ E₀ e^{-κ d_j}/r` per site and `tensB_le` is `≤ 4E₀ e^{-κ d_j}/r²` per pair; `aCoefX_norm_le` has the same per-site form.  The tail lemmas need the row sum over `x ∈ X`, so a factor `|X|` is missing, to be absorbed in the rate (`|X| ≤ C e^{ε sizeJ}`, which lowers `κ`); and `T.dist X` has to be identified with `sizeJ`. |
| `E_bound` (`‖E_j(y, X)‖ ≤ E₀ e^{-κ sizeJ X}`) | OPEN-INPUT (H4 polymer decay for the polymers of `polyUniv`; `PremisesTermAniso.bdd_dom`) |
| `s_data` (`‖ψ·ψ - 1‖ ≤ σ²ε`, `σ = C₀ s`, `ε = ε_q`) | OPEN-INPUT (the `DataHyp` size bound; here for all sites, because `far_crossing_le` is stated that way) |
| `src_data` (pointwise source bound) | OPEN-INPUT: `pair_bound_of_data` discharges it from `‖ψ_x - ψ_y‖₂ ≤ D σ ε`, `‖ν_j h - ν' ψ_y‖₂ ≤ σ²ε`, `‖ψ‖₂ ≤ B`, `σ²ε ≤ 1/2`, `ν' ≤ σ²`; the landed `DataHyp.adj` is nearest-neighbour only, a bridge to all `x ∈ Bc` is being written separately |
| uniform bound `B` on `‖ψ‖₂`; `σ²ε ≤ 1/2` | OPEN-INPUT (inside `src_data`) |
| scale relation `ε_q/ε_j ≤ K_R s^α`, `0 ≤ 2 + α` | OPEN-INPUT (I6 spin bounds) |
| the identification `v₁ = a` (`hv1` of T3) | OPEN (`regionalRadialCoefficient`) |
| polymer/cube count `|R'| ≤ Γ_E s^{-d}` (T4) | OPEN (cube assignment) |
| `regionalEnergyIdentity`, `regionalCommonTube`, `regionalTailAssignment` | OPEN, not used here |

### Fit of the pieces

1. `farCrossing_polyUniv_le_power` takes a constant `Bs` for `‖s‖` and gives `s^p` with
   `p = d + α₃`.  With `s_x = ψ_x·ψ_x` the constant would be about `3/2` and the bound would need
   `A₀ ≲ E₀`, but `A₀ = E₀ K_r / ε_j` carries the scale `ε_j`.  Because the pair term only sees
   `s_x - s_y`, `farCrossing a s = farCrossing a (s - 1)`, and `Bs = σ²ε = (C₀ s)² ε_q` is allowed;
   then `Bs · A₀ ≤ C₀² K_r K_R E₀ s^{2+α}` and `s^{2+α} ≤ 1` (needs `2 + α ≥ 0`).  The sharper
   note estimate (6) with exponent `p - 2 - α` is therefore not used, only the weaker
   `s^{d+α₃}`; the constant is `C₁ = C₀² K_r K_R C_T` and not `K_a C₀² K_r K_R (p'/(e ρ c_h R_*))^{p'}`.
2. The rate is `ρ = κ - κ₀` with `κ₀ ≥ aEnt + 1` (entropy) and `κ₀ < κ`: the class rate must exceed
   the entropy rate by a positive margin; `C_T` contains `e^{2 L ρ}` from the halo constant
   `H = c_h R_{k-1} L^{k-j} - 2L`, `c_h = M / L^(m₀+m₁)`.
3. `d` real versus natural: the theorems carry a real exponent `dd`; the field `dd_eq` ties it to
   `S.d`.
4. The collar premise (above) is the one place where the landed `Bc = alignedIn j (thickY R Y)`
   does not match the landed tail lemma.
5. The notation `R` is the radius sequence of the context, `R'` the centre set.

### Scheme A

Nothing in the statements refers to a background field or to two backgrounds: `B_j` is the
marginal term minus the restricted P5 (1.8) correction at one composed field `ψ`.  The theorem is
therefore usable by both schemes.  Scheme A enters only through the identification of the field
`ψ` (`C.psiJ`) and the premise `hv1`.
-/

@[expose] public section

open Finset Real Balaban.LargeField.RegionEnergyAlgebra Balaban.LargeField.RegionalFlux

namespace Balaban.LargeField.RegionalGroupedBound

/-! ### (T1) Abstract assembly -/

section Abstract

open Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
/-- The correction splits into the `v₁` pair sum and the `v₂` part. -/
theorem corrSum_eq_pair_add_v2Part
    (v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ) :
    corrSum v₁ v₂ νj R Bc ψ h =
      ∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * v₁ y x * (dot (ψ x) (ψ x) - dot (ψ y) (ψ y)) +
        v2Part v₂ νj R Bc ψ h := by
  unfold corrSum corrPair v2Part
  simp_rw [Finset.sum_add_distrib]

/-- The far crossing sum only sees differences of `s`: a constant shift does not change it. -/
theorem farCrossing_sub_const {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    (a s : ι → ℂ) (c : ℂ) (R Bc : Finset ι) :
    farCrossing a (fun x => s x - c) R Bc = farCrossing a s R Bc := by
  unfold farCrossing pairHalf
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **(T1), core.**  If the far crossing sum is at most `F` and the near source part at most `V`,
then `‖AtermRegion - corrSum‖ ≤ F + V`.  The correction uses the coefficient `v₁(y, x) = a(x - y)`. -/
theorem grouped_le_of_far
    (a : Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    {F V : ℝ} (hF : ‖farCrossing a (fun x => dot (ψ x) (ψ x)) R Bc‖ ≤ F)
    (hV : ‖v2Part v₂ νj R Bc ψ h‖ ≤ V) :
    ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R -
        corrSum (fun y x => a (x - y)) v₂ νj R Bc ψ h‖ ≤ F + V := by
  rw [AtermRegion_sub_corrSum]
  exact (norm_sub_le _ _).trans (add_le_add hF hV)

/-- **(T1).**  From the kernel tail `Σ_{x∉Bc} ‖a(x - y)‖ ≤ τ` for `y ∈ R`, `‖s x‖ ≤ Bs`, and the
near-source bound `‖v2Part‖ ≤ |R| β₂`:
`‖AtermRegion - corrSum‖ ≤ |R| (Bs τ + β₂)`. -/
theorem grouped_le
    (a : Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    {Bs τ β₂ : ℝ} (hs : ∀ x, ‖dot (ψ x) (ψ x)‖ ≤ Bs)
    (hτ : ∀ y ∈ R, ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ τ)
    (hβ : ‖v2Part v₂ νj R Bc ψ h‖ ≤ R.card * β₂) :
    ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R -
        corrSum (fun y x => a (x - y)) v₂ νj R Bc ψ h‖ ≤ R.card * (Bs * τ + β₂) := by
  have := grouped_le_of_far a v₂ νj R Bc ψ h (far_crossing_le a _ R Bc hs hτ) hβ
  refine this.trans (le_of_eq ?_)
  ring

/-- **(T1), centred form.**  The same with the bound `‖s x - 1‖ ≤ Bs` (the small-field datum is
close to the unit sphere); the far crossing sum only depends on differences of `s`. -/
theorem grouped_le_centred
    (a : Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    {Bs τ β₂ : ℝ} (hs : ∀ x, ‖dot (ψ x) (ψ x) - 1‖ ≤ Bs)
    (hτ : ∀ y ∈ R, ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ τ)
    (hβ : ‖v2Part v₂ νj R Bc ψ h‖ ≤ R.card * β₂) :
    ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R -
        corrSum (fun y x => a (x - y)) v₂ νj R Bc ψ h‖ ≤ R.card * (Bs * τ + β₂) := by
  have h1 := far_crossing_le a (fun x => dot (ψ x) (ψ x) - 1) R Bc hs hτ
  rw [farCrossing_sub_const] at h1
  have := grouped_le_of_far a v₂ νj R Bc ψ h h1 hβ
  refine this.trans (le_of_eq ?_)
  ring

/-- **(T1), coefficient mismatch.**  If the correction uses a coefficient `v₁(y, x)` with
`‖v₁ y x - a(x - y)‖ ≤ ε y x`, there is the additional term `Bs Σ_{y∈R} Σ_{x∈Bc} ε y x`. -/
theorem grouped_mismatch_corr_le
    (a : Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (ε : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℝ)
    {Bs τ β₂ : ℝ} (hs : ∀ x, ‖dot (ψ x) (ψ x)‖ ≤ Bs)
    (hτ : ∀ y ∈ R, ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ τ)
    (hβ : ‖v2Part v₂ νj R Bc ψ h‖ ≤ R.card * β₂)
    (hc : ∀ y x, ‖v₁ y x - a (x - y)‖ ≤ ε y x) :
    ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R - corrSum v₁ v₂ νj R Bc ψ h‖ ≤
      R.card * (Bs * τ + β₂) + Bs * ∑ y ∈ R, ∑ x ∈ Bc, ε y x := by
  have hm := grouped_mismatch_le a (fun x => dot (ψ x) (ψ x)) R Bc v₁ ε hs hc
  have hf := far_crossing_le a (fun x => dot (ψ x) (ψ x)) R Bc hs hτ
  rw [corrSum_eq_pair_add_v2Part]
  have e : AtermRegion a (fun x => dot (ψ x) (ψ x)) R -
      (∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * v₁ y x * (dot (ψ x) (ψ x) - dot (ψ y) (ψ y)) +
        v2Part v₂ νj R Bc ψ h) =
      (AtermRegion a (fun x => dot (ψ x) (ψ x)) R -
        ∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * v₁ y x * (dot (ψ x) (ψ x) - dot (ψ y) (ψ y)) -
          farCrossing a (fun x => dot (ψ x) (ψ x)) R Bc) +
        farCrossing a (fun x => dot (ψ x) (ψ x)) R Bc - v2Part v₂ νj R Bc ψ h := by ring
  rw [e]
  calc _ ≤ ‖(AtermRegion a (fun x => dot (ψ x) (ψ x)) R -
        ∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * v₁ y x * (dot (ψ x) (ψ x) - dot (ψ y) (ψ y)) -
          farCrossing a (fun x => dot (ψ x) (ψ x)) R Bc) +
        farCrossing a (fun x => dot (ψ x) (ψ x)) R Bc‖ + ‖v2Part v₂ νj R Bc ψ h‖ :=
        norm_sub_le _ _
    _ ≤ (Bs * ∑ y ∈ R, ∑ x ∈ Bc, ε y x + Bs * τ * R.card) + R.card * β₂ :=
        add_le_add ((norm_add_le _ _).trans (add_le_add hm hf)) hβ
    _ = _ := by ring

end Abstract

end Balaban.LargeField.RegionalGroupedBound
