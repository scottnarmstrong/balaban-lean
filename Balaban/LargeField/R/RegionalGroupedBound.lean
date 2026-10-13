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

**Convention note (Q13-ALIGN, 13 October 2026).**  `AtermRegion`/`AtermCentre` are finite algebra
over every site `x` of the index torus.  With the block-constant kernel `w ↦ a (unlift j w)` of
the landed correction they sum over every fine site, which is *not* the renormalization A-term of
P5 (1.8) and P1 (3.104): there the sum runs over the sites of the scale-`j` lattice (the
`L^j`-aligned fine sites), each counted once, with no factor `L^{-jd}`.  The source-facing
statements are the aligned ones of `RegionalAligned.lean` (kernel `alignedKernel`) and
`RegionalAlignedSource.lean` (`EresJ2_eq_aterm_aCoef_far_aligned`,
`EresJ2_sub_remainder_le_aligned_of_class`).

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
* `groupedInputs_nonempty`: `GroupedInputs` is inhabited (zero kernels, any data, `ν_j = 0`).  An
  inhabitant with a nonzero kernel is not given: `GroupedInputs` lives on the torus of an
  `SFCtx`, and no concrete context is available (the `ZMod 5` examples of `RegionalTails` are for
  the abstract lemmas only).

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
/-! ### (T2) The power form for the landed objects -/

section Concrete

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.LargeField.RegionShrink
  Balaban.LargeField.RegionalTails Balaban.LargeField.RegionalSourceTerm
  Balaban.LargeField.RegionalArith Balaban.SmallField.Def6

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The scale `s = L^{-(k-j)}` of the inherited level `j` seen from the current level `k`. -/
noncomputable def scaleJ (L k j : ℕ) : ℝ := (((L : ℝ) ^ (k - j))⁻¹)

/-- The distance weight `D(y, x) = supDist y x / L^(j+m₀+m₁)` (distance in units of `a_j`). -/
noncomputable def distWeight (j : ℕ) (y x : Localization.CTorus S.d S.L C.N₁ m₁ k) : ℝ :=
  (supDist y x : ℝ) / (S.L : ℝ) ^ (j + C.m₀ + m₁)

/-- The constant `C_T = K0 e^{2 L ρ} (p / (e ρ c_h R_*))^p` of `rate_power_form`,
`ρ = κ - κ₀`, `c_h = M / L^(m₀+m₁)`, `p = d + α₃`. -/
noncomputable def tailConst (κ κ₀ Rs dd α₃ : ℝ) : ℝ :=
  K0 S.d S.L κ₀ * exp (2 * S.L * (κ - κ₀)) *
    ((dd + α₃) / (exp 1 * ((κ - κ₀) * ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * Rs))) ^ (dd + α₃)

/-- The constant `C₁ = C₀² K_r K_R C_T` of the far crossing term. -/
noncomputable def farConst (κ κ₀ Rs dd α₃ C₀ K_r K_R : ℝ) : ℝ :=
  C₀ ^ 2 * K_r * K_R * tailConst C κ κ₀ Rs dd α₃

/-- The constant `C₂ = 4 C_s Cmom K0 C₀³ K_r² K_R²` of the near source term, `C_s = sourceConstC B`. -/
noncomputable def v2Const (κ κ₀ B C₀ K_r K_R : ℝ) : ℝ :=
  4 * sourceConstC B * Cmom (2 * S.L) (κ - κ₀) * K0 S.d S.L κ₀ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2

theorem K0_nonneg (d L : ℕ) (κ₀ : ℝ) : 0 ≤ K0 d L κ₀ := by
  unfold K0
  exact div_nonneg (Real.exp_pos _).le (sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num)))

theorem scaleJ_pos (L k j : ℕ) [NeZero L] : 0 < scaleJ L k j := by
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold scaleJ
  positivity

theorem scaleJ_le_one (L k j : ℕ) [NeZero L] : scaleJ L k j ≤ 1 := by
  have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold scaleJ
  exact inv_le_one_of_one_le₀ (one_le_pow₀ this)

/-- The sizes and distance weights of `polyUniv` (typing data `hN`, `hj` only): `0 ≤ sizeJ` and
`D(y, x) ≤ sizeJ X + 2 L` for `x, y ∈ X`. -/
theorem polyUniv_weights {j : ℕ} (_hN : S.L ^ C.m₀ ∣ C.N₁) (_hj : j ≤ k) :
    (∀ X ∈ polyUniv C j, 0 ≤ Def6.sizeJ C.m₀ j X) ∧
    (∀ X ∈ polyUniv C j, ∀ y ∈ X, ∀ x ∈ X,
      distWeight C j y x ≤ Def6.sizeJ C.m₀ j X + 2 * S.L) := by
  refine ⟨fun X _ => ?_, fun X hX y hyX x hxX => ?_⟩
  · unfold Def6.sizeJ
    exact treeLenCovOne_nonneg _ _ _
  · have := treeLenCovOne_ge_dist (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (K := k) C.m₀ j
      (exists_cover_struct (m₀ := C.m₀) (j := j) ((mem_polyUniv C).1 hX)) hyX hxX
    unfold Def6.sizeJ distWeight
    linarith

theorem distWeight_nonneg (j : ℕ) (y x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    0 ≤ distWeight C j y x := by
  unfold distWeight
  positivity

/-- Scalar inequality behind the far term: `Bs · (C_T A₀ s^p) ≤ C₁ E₀ s^p` for
`Bs = (C₀ s)² ε_q`, `A₀ = E₀ K_r / ε_j`, `ε_q/ε_j ≤ K_R s^α`, `s ≤ 1`, `2 + α ≥ 0`. -/
theorem far_scalar {C₀ K_r K_R CT E₀ εj εq s α p : ℝ} (hCT : 0 ≤ CT) (hE : 0 ≤ E₀)
    (hKr : 0 < K_r) (hεj : 0 < εj) (hεq : 0 ≤ εq) (hs : 0 < s) (hs1 : s ≤ 1) (hα : 0 ≤ 2 + α)
    (hR : εq / εj ≤ K_R * s ^ α) :
    (C₀ * s) ^ 2 * εq * (CT * (E₀ / (εj / K_r)) * s ^ p) ≤ (C₀ ^ 2 * K_r * K_R * CT) * E₀ * s ^ p := by
  have hsα : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have hKR : 0 ≤ K_R := by
    have : 0 ≤ K_R * s ^ α := le_trans (div_nonneg hεq hεj.le) hR
    exact (mul_nonneg_iff_of_pos_right hsα).1 this
  have hsp : 0 < s ^ p := Real.rpow_pos_of_pos hs p
  have h1 : εq ≤ εj * (K_R * s ^ α) := by rwa [div_le_iff₀ hεj, mul_comm] at hR
  have h3 : εq * K_r / εj ≤ K_r * (K_R * s ^ α) := by
    rw [div_le_iff₀ hεj]; nlinarith [h1, hKr]
  have h2 : s ^ 2 * s ^ α ≤ 1 := by
    have e : s ^ 2 * s ^ α = s ^ (2 + α) := by
      rw [Real.rpow_add hs, show (s ^ (2 : ℝ)) = s ^ 2 by norm_cast]
    rw [e]; exact Real.rpow_le_one hs.le hs1 hα
  have e : (C₀ * s) ^ 2 * εq * (CT * (E₀ / (εj / K_r)) * s ^ p) =
      (C₀ ^ 2 * CT * E₀ * s ^ p * s ^ 2) * (εq * K_r / εj) := by
    field_simp
  rw [e]
  have hnn : 0 ≤ C₀ ^ 2 * CT * E₀ * s ^ p * s ^ 2 := by positivity
  calc (C₀ ^ 2 * CT * E₀ * s ^ p * s ^ 2) * (εq * K_r / εj)
      ≤ (C₀ ^ 2 * CT * E₀ * s ^ p * s ^ 2) * (K_r * (K_R * s ^ α)) :=
        mul_le_mul_of_nonneg_left h3 hnn
    _ = (C₀ ^ 2 * K_r * K_R * CT * E₀ * s ^ p) * (s ^ 2 * s ^ α) := by ring
    _ ≤ (C₀ ^ 2 * K_r * K_R * CT * E₀ * s ^ p) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

open Classical in
/-- **The hypotheses of the grouped regional bound** at the inherited level `j`, for the centres
`R'`, the collar `Bc`, the composed field `ψ`, the source `h` and the coefficient `ν_j`.

Every field is a class input, a data bound, a numeric relation or a geometric inclusion; the field
that should discharge it is named.  The kernel `a`, the coefficient `v₂`, the per-polymer
coefficients `c`, `cv` and the activity `E` are arguments.

* `aligned`, `collar`: geometry.  `aligned` holds for `R' = alignedIn j Y` (`alignedIn_mono`);
  `collar` is the inclusion of the fine set of `Y^≈` in the support of the correction.
* numeric: `E₀_nonneg`, `κ₀_ge` (entropy margin `κ₀ ≥ aEnt + 1`), `κ₀_lt` (rate `ρ = κ - κ₀ > 0`),
  `Rs_pos`, `Rs_le` (`0 < R_* ≤ R_{k-1}`), `M_pos`, `p_pos`, `dd_eq` (`d` real is `S.d`),
  `α₁_nonneg`, `hrel` (`3 + 2α = d + α₃ + α₁`, `three_add_two_mul_eq`), `α_ge` (`0 ≤ 2 + α`),
  `C₀_nonneg`, `K_r_pos`, `B_nonneg`, `εj_pos`, `εq_nonneg`, `scale_rel` (`ε_q/ε_j ≤ K_R s^α`,
  the I6 spin bound).
* class inputs: `a_decomp`, `a_coeff` (the kernel is the sum of per-polymer coefficients with row
  sums `≤ (E₀ K_r / ε_j) e^{-κ sizeJ}`; PinJet `tensA_le`), `v2_decomp`, `v2_coeff` (same for
  `v₂` with `4 E₀ K_r² / ε_j²`; PinJet `tensB_le`), `E_bound` (H4 polymer decay).
* data bounds: `s_data` (`‖ψ·ψ - 1‖ ≤ σ² ε`, `σ = C₀ s`, `ε = ε_q`), `src_data` (the pointwise
  source bound of `pair_bound_of_data`). -/
structure GroupedInputs (j : ℕ) (Y : Set (Torus S.d (n k)))
    (R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (h : Fin N → ℂ) (νj : ℝ) (a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ)
    (E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ) : Prop where
  aligned : R' ⊆ C.alignedIn j Y
  collar : ∀ x, x ∈ C.sset (thickY R Y) → x ∈ Bc
  E₀_nonneg : 0 ≤ E₀
  κ₀_ge : aEnt S.d S.L + 1 ≤ κ₀
  κ₀_lt : κ₀ < κ
  Rs_pos : 0 < Rs
  Rs_le : Rs ≤ R (k - 1)
  M_pos : 0 < M
  p_pos : 0 < dd + α₃
  dd_eq : dd = (S.d : ℝ)
  α₁_nonneg : 0 ≤ α₁
  hrel : 3 + 2 * α = dd + α₃ + α₁
  α_ge : 0 ≤ 2 + α
  C₀_nonneg : 0 ≤ C₀
  K_r_pos : 0 < K_r
  B_nonneg : 0 ≤ B
  εj_pos : 0 < εj
  εq_nonneg : 0 ≤ εq
  scale_rel : εq / εj ≤ K_R * scaleJ S.L k j ^ α
  a_decomp : ∀ y ∈ R', ∀ x, a (x - y) =
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), c X y x
  a_coeff : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
      (E₀ / (εj / K_r)) * exp (-κ * Def6.sizeJ C.m₀ j X)
  v2_decomp : ∀ y ∈ R', ∀ x, v₂ y x =
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), cv X y x
  v2_coeff : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖cv X y x‖ ≤
      (4 * E₀ / (εj / K_r) ^ 2) * exp (-κ * Def6.sizeJ C.m₀ j X)
  E_bound : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ‖E y X‖ ≤ E₀ * exp (-κ * Def6.sizeJ C.m₀ j X)
  s_data : ∀ x, ‖dot (ψ x) (ψ x) - 1‖ ≤ (C₀ * scaleJ S.L k j) ^ 2 * εq
  src_data : ∀ y ∈ R', ∀ x ∈ Bc,
    ‖(νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y)))‖ ≤
      sourceConstC B * (distWeight C j y x ^ 2 + distWeight C j y x) *
        (C₀ * scaleJ S.L k j) ^ 3 * εq ^ 2

variable {C}

theorem GroupedInputs.tailConst_nonneg {j : ℕ} {Y : Set (Torus S.d (n k))}
    {R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)} {ψ : Fld S.d S.L C.N₁ m₁ k N}
    {h : Fin N → ℂ} {νj : ℝ} {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputs C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    0 ≤ tailConst C κ κ₀ Rs dd α₃ := by
  have hK0 := K0_nonneg S.d S.L κ₀
  unfold tailConst
  have hρ : 0 < κ - κ₀ := sub_pos.2 g.κ₀_lt
  have hM : (0 : ℝ) < M := by exact_mod_cast g.M_pos
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hRs := g.Rs_pos
  have hp := g.p_pos
  have hc : (0 : ℝ) < (M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁) := by positivity
  have hden : 0 < exp 1 * ((κ - κ₀) * ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * Rs) := by positivity
  exact mul_nonneg (mul_nonneg hK0 (Real.exp_pos _).le)
    (Real.rpow_nonneg (div_nonneg hp.le hden.le) _)

theorem GroupedInputs.K_R_nonneg {j : ℕ} {Y : Set (Torus S.d (n k))}
    {R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)} {ψ : Fld S.d S.L C.N₁ m₁ k N}
    {h : Fin N → ℂ} {νj : ℝ} {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputs C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    0 ≤ K_R := by
  have hsα : 0 < scaleJ S.L k j ^ α := Real.rpow_pos_of_pos (scaleJ_pos S.L k j) α
  have : 0 ≤ K_R * scaleJ S.L k j ^ α :=
    le_trans (div_nonneg g.εq_nonneg g.εj_pos.le) g.scale_rel
  exact (mul_nonneg_iff_of_pos_right hsα).1 this

/-- The three constants are nonnegative. -/
theorem GroupedInputs.consts_nonneg {j : ℕ} {Y : Set (Torus S.d (n k))}
    {R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)} {ψ : Fld S.d S.L C.N₁ m₁ k N}
    {h : Fin N → ℂ} {νj : ℝ} {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputs C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    0 ≤ farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R ∧ 0 ≤ v2Const (S := S) κ κ₀ B C₀ K_r K_R := by
  have hKR := g.K_R_nonneg
  have hCT := g.tailConst_nonneg
  have hK0 := K0_nonneg S.d S.L κ₀
  have hKr := g.K_r_pos.le
  have hL : (0 : ℝ) ≤ 2 * S.L := by positivity
  have hCm := cmom_nonneg hL (sub_pos.2 g.κ₀_lt)
  have hB := g.B_nonneg
  refine ⟨?_, ?_⟩
  · unfold farConst; positivity
  · unfold v2Const sourceConstC; have := g.C₀_nonneg; positivity

open Classical in
/-- **(T2) The grouped regional correction in power form.**
`‖Σ_{y∈R'} A_j(y) - Corr_j(R', Bc)‖ ≤ |R'| (C₁ + C₂) E₀ s^(d+α₃)`, `s = L^{-(k-j)}`, for the
kernel `a` and `v₁(y, x) = a(x - y)` in the correction.  Typing data `L^m₀ ∣ N₁`, `j ≤ k`;
the other hypotheses are collected in `GroupedInputs`. -/
theorem grouped_bound_power {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    {Y : Set (Torus S.d (n k))} {R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {h : Fin N → ℂ} {νj : ℝ}
    {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputs C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R' -
        corrSum (fun y x => a (x - y)) v₂ νj R' Bc ψ h‖ ≤
      R'.card * ((farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R + v2Const (S := S) κ κ₀ B C₀ K_r K_R) *
        E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
  have hs0 := scaleJ_pos S.L k j
  have hs1 := scaleJ_le_one S.L k j
  have hK0 := K0_nonneg S.d S.L κ₀
  have hCT : 0 ≤ tailConst C κ κ₀ Rs dd α₃ := g.tailConst_nonneg
  have hA₀ : 0 ≤ E₀ / (εj / K_r) := by
    have := g.E₀_nonneg; have := g.εj_pos; have := g.K_r_pos; positivity
  -- far crossing
  have hfar := farCrossing_polyUniv_le_power C hN hj c a (fun x => dot (ψ x) (ψ x) - 1) Y R' Bc
    g.aligned g.collar (A₀ := E₀ / (εj / K_r)) (κ := κ) (κ₀ := κ₀)
    (Bs := (C₀ * scaleJ S.L k j) ^ 2 * εq) (Rs := Rs) (d := dd) (α₃ := α₃) hA₀ g.κ₀_ge g.κ₀_lt
    g.Rs_pos g.Rs_le g.M_pos g.p_pos g.s_data g.a_decomp g.a_coeff
  rw [farCrossing_sub_const] at hfar
  have hfar2 : ‖farCrossing a (fun x => dot (ψ x) (ψ x)) R' Bc‖ ≤
      R'.card * (farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
    refine hfar.trans ?_
    rw [mul_comm _ (R'.card : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have := far_scalar (C₀ := C₀) (K_r := K_r) (K_R := K_R) (CT := tailConst C κ κ₀ Rs dd α₃)
      (E₀ := E₀) (εj := εj) (εq := εq) (s := scaleJ S.L k j) (α := α) (p := dd + α₃) hCT
      g.E₀_nonneg g.K_r_pos g.εj_pos g.εq_nonneg hs0 hs1 g.α_ge g.scale_rel
    unfold farConst
    exact this
  -- near source term
  obtain ⟨hsz, hD⟩ := polyUniv_weights C hN hj
  have hv2 := v2Part_le_power (polyUniv C j) cv v₂ νj R' Bc ψ h (Def6.sizeJ C.m₀ j)
    (distWeight C j) (E₀ := E₀) (K₀ := K0 S.d S.L κ₀) (κ := κ) (κ₀ := κ₀) (c₀ := 2 * S.L)
    (Cs := sourceConstC B) (C₀ := C₀) (K_r := K_r) (K_R := K_R) (s := scaleJ S.L k j) (α := α)
    (εj := εj) (εq := εq) (r := εj / K_r) (dd := dd) (α₁ := α₁) (α₃ := α₃) g.E₀_nonneg hK0
    (by positivity) g.κ₀_lt (by unfold sourceConstC; have := g.B_nonneg; positivity) g.C₀_nonneg
    g.K_r_pos hs0 hs1 g.εj_pos g.εq_nonneg rfl g.scale_rel g.hrel g.α₁_nonneg
    (fun y hy x => g.v2_decomp y hy x)
    (fun y hy X hX hyX => g.v2_coeff y hy X ((mem_polyUniv C).1 hX) hyX)
    (fun y _ X hX _ => hsz X hX)
    (fun y _ x => distWeight_nonneg C j y x)
    (fun y _ X hX hyX x hxX => hD X hX y hyX x hxX)
    (fun y _ => entropy_polyUniv C hN hj y g.κ₀_ge) g.src_data
  have hv2' : ‖v2Part v₂ νj R' Bc ψ h‖ ≤
      R'.card * (v2Const (S := S) κ κ₀ B C₀ K_r K_R * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
    unfold v2Const; exact hv2
  have := grouped_le_of_far a v₂ νj R' Bc ψ h hfar2 hv2'
  refine this.trans (le_of_eq ?_)
  ring

open Classical in
/-- **(T2) The omitted tail in power form.**
`‖Σ_{y∈R'} tailAt‖ ≤ |R'| C_T E₀ s^(d+α₃)`. -/
theorem omitted_tail_power {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    {Y : Set (Torus S.d (n k))} {R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {h : Fin N → ℂ} {νj : ℝ}
    {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputs C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖∑ y ∈ R', tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖ ≤
      R'.card * (tailConst C κ κ₀ Rs dd α₃ * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y ∈ R', ‖tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖
      ≤ ∑ _y ∈ R', tailConst C κ κ₀ Rs dd α₃ * E₀ * scaleJ S.L k j ^ (dd + α₃) :=
        Finset.sum_le_sum fun y hy =>
          tailAt_polyUniv_le_power C hN hj E Y (g.aligned hy) g.E₀_nonneg g.κ₀_ge g.κ₀_lt g.Rs_pos
            g.Rs_le g.M_pos g.p_pos (g.E_bound y hy)
    _ = _ := by simp

/-! ### (T3) The landed regional energy -/

variable (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N))

open Classical in
/-- **(T3) The decomposition of the landed regional energy.**  With the premise `hv1` that the
correction coefficient `v₁` is the marginal kernel `a` (`regionalRadialCoefficient`),
`EresAt = Σ_{y∈R'} I_j(y) + (Σ_{y∈R'} A_j(y) - Corr_j) - (omitted tail)`,
where `I_j(y) = Efull - AtermCentre` is the remainder of the I6 decomposition. -/
theorem EresAt_eq_remainder_add_grouped_of_radialCoeff (j : ℕ)
    (R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (hv1 : ∀ y x, vc.v1 j (unlift j (x - y)) = a (x - y)) :
    EresAt C vc hv j R' Bc Bp ψ =
      ∑ y ∈ R', (Efull (polyUniv C j) (polyTerm C hv j ψ) y -
          AtermCentre a (fun x => dot (ψ x) (ψ x)) y) +
        (AtermRegion a (fun x => dot (ψ x) (ψ x)) R' -
          corrSum (fun y x => a (x - y)) (fun y x => vc.v2 j (unlift j (x - y)))
            (nuIdeal S.L k (C.sf.ν k) j) R' Bc ψ (hC hv)) -
        ∑ y ∈ R', tailAt (polyUniv C j) (polyTerm C hv j ψ) Bp y := by
  rw [EresAt_eq_energyAt, energyAt_decomposition]
  have h1 : (fun y x => vc.v1 j (unlift j (x - y))) = fun y x => a (x - y) :=
    funext fun y => funext fun x => hv1 y x
  have h2 : RegionShrink.pairSum (corrFn C vc hv j ψ) R' Bc =
      corrSum (fun y x => vc.v1 j (unlift j (x - y))) (fun y x => vc.v2 j (unlift j (x - y)))
        (nuIdeal S.L k (C.sf.ν k) j) R' Bc ψ (hC hv) := rfl
  rw [h2, h1]

open Classical in
/-- **(T3) The bound.**  Under `GroupedInputs` (for `ν_j = nuIdeal`, `v₂ = vc.v2 ∘ unlift`,
the activity `polyTerm`) and `hv1`:
`‖EresAt - Σ_{y∈R'} I_j(y)‖ ≤ |R'| (C₁ + C₂ + C_T) E₀ s^(d+α₃)`, `Bp = sset(Y^≈)`. -/
theorem EresAt_sub_remainder_le_of_radialCoeff {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    {Y : Set (Torus S.d (n k))} {R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv1 : ∀ y x, vc.v1 j (unlift j (x - y)) = a (x - y))
    (g : GroupedInputs C j Y R' Bc ψ (hC hv) (nuIdeal S.L k (C.sf.ν k) j) a
      (fun y x => vc.v2 j (unlift j (x - y))) c cv (polyTerm C hv j ψ)
      E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresAt C vc hv j R' Bc (C.sset (thickY R Y)) ψ -
        ∑ y ∈ R', (Efull (polyUniv C j) (polyTerm C hv j ψ) y -
          AtermCentre a (fun x => dot (ψ x) (ψ x)) y)‖ ≤
      R'.card * ((farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R + v2Const (S := S) κ κ₀ B C₀ K_r K_R +
        tailConst C κ κ₀ Rs dd α₃) * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
  rw [EresAt_eq_remainder_add_grouped_of_radialCoeff vc hv j R' Bc _ ψ a hv1]
  have e : ∀ I G T : ℂ, I + G - T - I = G - T := fun I G T => by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := grouped_bound_power hN hj g
  have h2 := omitted_tail_power hN hj g
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  ring

open Classical in
/-- **(T3) for `EresJ2`** at the regions of `Y`: `R' = alignedIn j Y`, `Bc = alignedIn j (thickY R Y)`,
the composed field `psiJ`.  **Superseded:** the `collar` field of `GroupedInputs` is false at the
landed `Bc` (a non-aligned site of the fine set of `Y^≈` is not in `Bc`), and `hv1` for all `x, y`
makes the all-fine-site A-term, not the source A-term.  Use
`RegionalAligned.EresJ2_sub_remainder_le_aligned_of_radialCoeff` (or
`RegionalAlignedSource.EresJ2_sub_remainder_le_aligned_of_class`). -/
theorem EresJ2_sub_remainder_le_of_radialCoeff {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    {a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {c cv : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv1 : ∀ y x, vc.v1 j (unlift j (x - y)) = a (x - y))
    (g : GroupedInputs C j Y (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.psiJ Y ψk hv j)
      (hC hv) (nuIdeal S.L k (C.sf.ν k) j) a (fun y x => vc.v2 j (unlift j (x - y))) c cv
      (polyTerm C hv j (C.psiJ Y ψk hv j)) E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresJ2 C vc Y ψk hv j -
        ∑ y ∈ C.alignedIn j Y, (Efull (polyUniv C j) (polyTerm C hv j (C.psiJ Y ψk hv j)) y -
          AtermCentre a (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) y)‖ ≤
      (C.alignedIn j Y).card * ((farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R +
        v2Const (S := S) κ κ₀ B C₀ K_r K_R + tailConst C κ κ₀ Rs dd α₃) * E₀ *
          scaleJ S.L k j ^ (dd + α₃)) := by
  rw [EresJ2_eq_EresAt]
  exact EresAt_sub_remainder_le_of_radialCoeff vc hv hN hj hv1 g

/-! ### (T4) The sum over scales -/

/-- The sites of the torus of the context. -/
abbrev SiteT (C : SFCtx S n R M K N k m₁ ϱ) : Type := Localization.CTorus S.d S.L C.N₁ m₁ k

open Classical in
/-- The charge of one inherited level: the grouped regional correction plus the omitted tail. -/
noncomputable def groupedCharge (j : ℕ) (Y : Set (Torus S.d (n k))) (R' Bc : Finset (SiteT C))
    (ψ : Fld S.d S.L C.N₁ m₁ k N) (h : Fin N → ℂ) (νj : ℝ) (a : SiteT C → ℂ)
    (v₂ : SiteT C → SiteT C → ℂ) (E : SiteT C → Set (SiteT C) → ℂ) : ℝ :=
  ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R' - corrSum (fun y x => a (x - y)) v₂ νj R' Bc ψ h‖ +
    ‖∑ y ∈ R', tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖

theorem scaleJ_rpow_eq (L k m : ℕ) [NeZero L] (hm : m ≤ k) :
    scaleJ L k (k - m) = (L : ℝ) ^ (-(m : ℝ)) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold scaleJ
  rw [Nat.sub_sub_self hm, Real.rpow_neg hL.le, Real.rpow_natCast]

open Classical in
/-- **(T4) The sum over scales.**  For each gap `m = k - j` with `n₁ ≤ m ≤ k` suppose
`GroupedInputs` at the level `j = k - m` (with common constants, `ε_j` and the data depending on
`j`) and at most `Γ_E s^{-d}` centres, `s = L^{-m}`.  Then the charge per new cube, summed over the
gaps `m ≥ n₁`, is at most
`Γ_E (C₁ + C₂ + C_T) E₀ L^{-n₁ α₃} / (1 - L^{-α₃})`. -/
theorem charge_sum_grouped (hN : S.L ^ C.m₀ ∣ C.N₁) (hL : 1 < (S.L : ℝ))
    (Y : Set (Torus S.d (n k))) (R' Bc : ℕ → Finset (SiteT C)) (ψ : ℕ → Fld S.d S.L C.N₁ m₁ k N)
    (h : Fin N → ℂ) (νj : ℕ → ℝ) (a : ℕ → SiteT C → ℂ) (v₂ : ℕ → SiteT C → SiteT C → ℂ)
    (c cv : ℕ → Set (SiteT C) → SiteT C → SiteT C → ℂ) (E : ℕ → SiteT C → Set (SiteT C) → ℂ)
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εq Γ : ℝ} (εj : ℕ → ℝ) (n₁ : ℕ) (hn₁ : n₁ ≤ k)
    (hα₃ : 0 < α₃) (hΓ : 0 ≤ Γ)
    (hin : ∀ m, n₁ ≤ m → m ≤ k →
      GroupedInputs C (k - m) Y (R' (k - m)) (Bc (k - m)) (ψ (k - m)) h (νj (k - m)) (a (k - m))
        (v₂ (k - m)) (c (k - m)) (cv (k - m)) (E (k - m)) E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B
        (εj (k - m)) εq)
    (hcard : ∀ m, n₁ ≤ m → m ≤ k →
      ((R' (k - m)).card : ℝ) ≤ Γ * scaleJ S.L k (k - m) ^ (-dd)) (n : ℕ) :
    ∑ i ∈ Finset.range n, (if n₁ + i ≤ k then
        groupedCharge (C := C) (k - (n₁ + i)) Y (R' (k - (n₁ + i))) (Bc (k - (n₁ + i)))
          (ψ (k - (n₁ + i))) h (νj (k - (n₁ + i))) (a (k - (n₁ + i))) (v₂ (k - (n₁ + i)))
          (E (k - (n₁ + i))) else 0) ≤
      Γ * (farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R + v2Const (S := S) κ κ₀ B C₀ K_r K_R +
          tailConst C κ κ₀ Rs dd α₃) * E₀ *
        ((S.L : ℝ) ^ (-((n₁ : ℝ) * α₃)) / (1 - (S.L : ℝ) ^ (-α₃))) := by
  set Kc := farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R + v2Const (S := S) κ κ₀ B C₀ K_r K_R +
    tailConst C κ κ₀ Rs dd α₃ with hKc
  have g0 := hin n₁ le_rfl hn₁
  have hKnn : 0 ≤ Kc := by
    have := g0.consts_nonneg; have := g0.tailConst_nonneg
    rw [hKc]; linarith [this]
  have hE0 := g0.E₀_nonneg
  -- the charge sequence
  let cs : ℕ → ℝ := fun m => if n₁ ≤ m ∧ m ≤ k then
    groupedCharge (C := C) (k - m) Y (R' (k - m)) (Bc (k - m)) (ψ (k - m)) h (νj (k - m))
      (a (k - m)) (v₂ (k - m)) (E (k - m)) else 0
  have hcs : ∀ m, cs m ≤ Γ * Kc * E₀ * (S.L : ℝ) ^ (-((m : ℝ) * α₃)) := by
    intro m
    by_cases hm : n₁ ≤ m ∧ m ≤ k
    · simp only [cs, hm, and_self, ↓reduceIte]
      obtain ⟨hm1, hm2⟩ := hm
      have g := hin m hm1 hm2
      have hj : k - m ≤ k := Nat.sub_le _ _
      have h1 := grouped_bound_power hN hj g
      have h2 := omitted_tail_power hN hj g
      have hs0 := scaleJ_pos S.L k (k - m)
      have hcd := hcard m hm1 hm2
      have hnn : 0 ≤ Kc * E₀ * scaleJ S.L k (k - m) ^ (dd + α₃) := by positivity
      unfold groupedCharge
      calc _ ≤ ((R' (k - m)).card : ℝ) * (Kc * E₀ * scaleJ S.L k (k - m) ^ (dd + α₃)) := by
            refine (add_le_add h1 h2).trans (le_of_eq ?_)
            rw [hKc]; ring
        _ ≤ Γ * scaleJ S.L k (k - m) ^ (-dd) * (Kc * E₀ * scaleJ S.L k (k - m) ^ (dd + α₃)) :=
            mul_le_mul_of_nonneg_right hcd hnn
        _ = Γ * Kc * E₀ * scaleJ S.L k (k - m) ^ α₃ := by
            have : scaleJ S.L k (k - m) ^ (-dd) * scaleJ S.L k (k - m) ^ (dd + α₃) =
                scaleJ S.L k (k - m) ^ α₃ := by
              rw [← Real.rpow_add hs0]; congr 1; ring
            calc _ = Γ * Kc * E₀ * (scaleJ S.L k (k - m) ^ (-dd) *
                  scaleJ S.L k (k - m) ^ (dd + α₃)) := by ring
              _ = _ := by rw [this]
        _ = _ := by
            rw [scaleJ_rpow_eq S.L k m hm2]
            have hL0 : (0 : ℝ) < S.L := by linarith
            rw [← Real.rpow_mul hL0.le]
            congr 3
            ring
    · simp only [cs, hm, ↓reduceIte]
      positivity
  have hsum := charge_sum_le hL hα₃ hΓ hKnn hE0 n₁ n cs hcs
  refine le_trans (le_of_eq ?_) hsum
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : n₁ + i ≤ k
  · simp [cs, hi]
  · simp [cs, hi]

/-! ### Non-vacuity of `GroupedInputs` -/

open Classical in
/-- **`GroupedInputs` is inhabited.**  For any context with `R_{k-1} > 0`, `M > 0`, any
composed field `ψ`, source `h` and region `Y`: the zero kernel, zero coefficients and zero
activity with `ν_j = 0`, the collar the whole torus, and `C₀` large enough to cover the data
`ψ·ψ - 1` satisfy every field (`E₀ = ε_j = ε_q = K_r = 1`, `α₁ = B = 0`, `α₃ = 1`, `d = S.d`,
`κ₀ = aEnt + 1`, `κ = κ₀ + 1`, `R_* = R_{k-1}`, `α = (d - 2)/2`). -/
theorem groupedInputs_nonempty (j : ℕ) (hRpos : 0 < R (k - 1)) (hM : 0 < M)
    (Y : Set (Torus S.d (n k))) (ψ : Fld S.d S.L C.N₁ m₁ k N) (h : Fin N → ℂ) :
    ∃ E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ,
      Nonempty (GroupedInputs C j Y (C.alignedIn j Y) Finset.univ ψ h 0 (fun _ => 0)
        (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
        E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) := by
  have hs := scaleJ_pos S.L k j
  set s := scaleJ S.L k j with hsdef
  set T : ℝ := ∑ x, ‖dot (ψ x) (ψ x) - 1‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => norm_nonneg _
  have hsα : 0 < s ^ ((S.d - 2 : ℝ) / 2) := Real.rpow_pos_of_pos hs _
  have hC0 : 0 ≤ (T + 1) / s := by positivity
  have hCs : 0 ≤ sourceConstC 0 := by unfold sourceConstC; norm_num
  refine ⟨1, aEnt S.d S.L + 2, aEnt S.d S.L + 1, R (k - 1), (S.d : ℝ), 1, 0, ((S.d : ℝ) - 2) / 2,
    (T + 1) / s, 1, (s ^ (((S.d : ℝ) - 2) / 2))⁻¹, 0, 1, 1, ⟨?_⟩⟩
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  exact
  { aligned := subset_rfl
    collar := fun x _ => Finset.mem_univ x
    E₀_nonneg := zero_le_one
    κ₀_ge := le_rfl
    κ₀_lt := by linarith
    Rs_pos := hRpos
    Rs_le := le_rfl
    M_pos := hM
    p_pos := by linarith
    dd_eq := rfl
    α₁_nonneg := le_rfl
    hrel := by ring
    α_ge := by linarith
    C₀_nonneg := hC0
    K_r_pos := one_pos
    B_nonneg := le_rfl
    εj_pos := one_pos
    εq_nonneg := zero_le_one
    scale_rel := by
      rw [inv_mul_cancel₀ hsα.ne']; norm_num
    a_decomp := fun y _ x => by simp
    a_coeff := fun y _ X _ _ => by
      simp only [norm_zero, Finset.sum_const_zero]; positivity
    v2_decomp := fun y _ x => by simp
    v2_coeff := fun y _ X _ _ => by
      simp only [norm_zero, Finset.sum_const_zero]; positivity
    E_bound := fun y _ X _ _ => by
      simp only [norm_zero]; positivity
    s_data := fun x => by
      have e : (T + 1) / s * s = T + 1 := div_mul_cancel₀ _ hs.ne'
      rw [e]
      have : ‖dot (ψ x) (ψ x) - 1‖ ≤ T :=
        Finset.single_le_sum (f := fun x => ‖dot (ψ x) (ψ x) - 1‖) (fun x _ => norm_nonneg _)
          (Finset.mem_univ x)
      nlinarith
    src_data := fun y _ x _ => by
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      have hD := distWeight_nonneg C j y x
      have hcs : 0 ≤ (T + 1) / s * s := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hCs (add_nonneg (sq_nonneg _) hD))
        (pow_nonneg hcs 3)) (sq_nonneg _) }

end Concrete

end Balaban.LargeField.RegionalGroupedBound
