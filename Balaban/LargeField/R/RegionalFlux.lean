/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Corr
public import Balaban.SmallField.RenormTorus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The finite algebra of the regional marginal flux (REGIONAL §1, §6 item 1)

For a finite additive group of sites `ι`, an even kernel `a` and a function `s` (in the source
`s x = ψ(x)·ψ(x)`), the centred marginal term is `A(y) = ½ Σ_x a(x - y) (s x - s y)`.

* `regional_marginal_flux_finset`: REGIONAL (1.3), the `R × R` part cancels.
* `regional_flux_diff_le`: the direct bound on the uncancelled flux (REGIONAL (1.3a)); the
  triangle inequality gives the constant `(2 Bψ + U) U Ka |R|` (no factor `1/2`).
* `regional_flux_ne_zero_example`: the crossing sum is not zero for a proper subset.
* `corr_minus_flux`: the grouped boundary quantity `𝓑 = Σ_{y∈R} A(y) - corrSum` of REGIONAL (1.2).
  No bound on `𝓑` is asserted (that is the open `regionalMarginalRemainder`).

Relation to the landed objects: `Aterm` is defined at the centre `0` only, as a sum over
polymers; `Aterm_torus_sum` is the whole-torus statement in the reindexed form
`½ Σ_z a(z) (g(y + z) - g(y))`.  `AtermCentre` is the same expression with `x = y + z`
(`AtermCentre_eq_shift`), and `AtermRegion` is the regional sum of (1.3); for `R = univ` it is `0`
(`AtermRegion_univ`), which is the finite-sum content of `Aterm_torus_sum`.
-/

@[expose] public section

open Finset

namespace Balaban.LargeField.RegionalFlux

section Algebra

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

/-- The centred marginal term `A(y) = ½ Σ_x a(x - y) (s x - s y)` (REGIONAL §1). -/
noncomputable def AtermCentre (a : ι → ℂ) (s : ι → ℂ) (y : ι) : ℂ :=
  (1 / 2 : ℂ) * ∑ x, a (x - y) * (s x - s y)

/-- The regional marginal sum `Σ_{y ∈ R} A(y)` (left side of REGIONAL (1.3)). -/
noncomputable def AtermRegion (a : ι → ℂ) (s : ι → ℂ) (R : Finset ι) : ℂ :=
  ∑ y ∈ R, AtermCentre a s y

/-- The crossing flux `½ Σ_{y∈R} Σ_{x∉R} a(x - y)(s x - s y)` (right side of (1.3)). -/
noncomputable def crossFlux (a : ι → ℂ) (s : ι → ℂ) (R : Finset ι) : ℂ :=
  (1 / 2 : ℂ) * ∑ y ∈ R, ∑ x ∈ Rᶜ, a (x - y) * (s x - s y)

omit [DecidableEq ι] in
/-- `AtermCentre` is the reindexed form `½ Σ_z a(z)(s(y+z) - s y)` used in `Aterm_torus_sum`. -/
theorem AtermCentre_eq_shift (a s : ι → ℂ) (y : ι) :
    AtermCentre a s y = (1 / 2 : ℂ) * ∑ z, a z * (s (y + z) - s y) := by
  unfold AtermCentre
  congr 1
  refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_).symm
  intro z
  simp

/-- **REGIONAL (1.3)** (item 1): for an even kernel the `R × R` part of the regional marginal sum
cancels by the swap `x ↔ y`. -/
theorem regional_marginal_flux_finset (a s : ι → ℂ) (hev : ∀ z, a (-z) = a z) (R : Finset ι) :
    AtermRegion a s R = crossFlux a s R := by
  classical
  unfold AtermRegion AtermCentre crossFlux
  rw [← Finset.mul_sum]
  congr 1
  have split : ∀ y, ∑ x, a (x - y) * (s x - s y) =
      ∑ x ∈ R, a (x - y) * (s x - s y) + ∑ x ∈ Rᶜ, a (x - y) * (s x - s y) := fun y =>
    (Finset.sum_add_sum_compl R _).symm
  simp_rw [split, Finset.sum_add_distrib]
  have key : ∑ y ∈ R, ∑ x ∈ R, a (x - y) * (s x - s y) = 0 := by
    have h : ∑ y ∈ R, ∑ x ∈ R, a (x - y) * (s x - s y) =
        -∑ y ∈ R, ∑ x ∈ R, a (x - y) * (s x - s y) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have : y - x = -(x - y) := by abel
      rw [this, hev]; ring
    have h2 : (2 : ℂ) * ∑ y ∈ R, ∑ x ∈ R, a (x - y) * (s x - s y) = 0 := by
      linear_combination h
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [key, zero_add]

/-- **Whole-torus cancellation**: for `R = univ` the regional sum is `0` (finite-sum content of
`Aterm_torus_sum`; here the kernel must be even). -/
theorem AtermRegion_univ (a s : ι → ℂ) (hev : ∀ z, a (-z) = a z) :
    AtermRegion a s Finset.univ = 0 := by
  rw [regional_marginal_flux_finset a s hev]
  simp [crossFlux]

/-- The crossing flux is additive in `s`. -/
theorem crossFlux_sub (a s s' : ι → ℂ) (R : Finset ι) :
    crossFlux a s R - crossFlux a s' R = crossFlux a (fun x => s x - s' x) R := by
  unfold crossFlux
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **REGIONAL (1.3a)**, abstract form: if `‖Δs z‖ ≤ c` and `Σ_x ‖a(x - y)‖ ≤ Ka`, then the
difference of crossing fluxes is at most `c · Ka · |R|` (each crossing term has two `Δs` values,
so the factor `½` of the note cancels against the `2`). -/
theorem crossFlux_le (a D : ι → ℂ) (R : Finset ι) {c Ka : ℝ} (hc : 0 ≤ c)
    (hD : ∀ z, ‖D z‖ ≤ c) (hK : ∀ y, ∑ x, ‖a (x - y)‖ ≤ Ka) :
    ‖crossFlux a D R‖ ≤ c * Ka * R.card := by
  unfold crossFlux
  have hx : ∀ y, ‖∑ x ∈ Rᶜ, a (x - y) * (D x - D y)‖ ≤ 2 * c * Ka := by
    intro y
    calc ‖∑ x ∈ Rᶜ, a (x - y) * (D x - D y)‖
        ≤ ∑ x ∈ Rᶜ, ‖a (x - y)‖ * (2 * c) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
          linarith [hD x, hD y]
      _ ≤ ∑ x, ‖a (x - y)‖ * (2 * c) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun x _ _ => mul_nonneg (norm_nonneg _) (by positivity)
      _ = (∑ x, ‖a (x - y)‖) * (2 * c) := (Finset.sum_mul _ _ _).symm
      _ ≤ Ka * (2 * c) := mul_le_mul_of_nonneg_right (hK y) (by positivity)
      _ = 2 * c * Ka := by ring
  calc ‖(1 / 2 : ℂ) * ∑ y ∈ R, ∑ x ∈ Rᶜ, a (x - y) * (D x - D y)‖
      = (1 / 2) * ‖∑ y ∈ R, ∑ x ∈ Rᶜ, a (x - y) * (D x - D y)‖ := by
        rw [norm_mul]; simp
    _ ≤ (1 / 2) * ∑ y ∈ R, (2 * c * Ka) :=
        mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hx y)) (by norm_num)
    _ = c * Ka * R.card := by simp; ring

end Algebra

section Fields

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The bound on `Δs`** (REGIONAL §1): for a bilinear form `β` with `‖β v w‖ ≤ ‖v‖‖w‖`
(the scalar product `ψ·ψ`), `‖ψ⁰‖ ≤ Bψ`, `‖ψᵐ - ψ⁰‖ ≤ U` give `‖β ψᵐ ψᵐ - β ψ⁰ ψ⁰‖ ≤ (2Bψ+U)U`. -/
theorem sq_diff_le (β : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (hβ : ∀ v w, ‖β v w‖ ≤ ‖v‖ * ‖w‖)
    {p q : E} {Bψ U : ℝ} (hp : ‖p‖ ≤ Bψ) (hd : ‖q - p‖ ≤ U) (hB : 0 ≤ Bψ) (hU : 0 ≤ U) :
    ‖β q q - β p p‖ ≤ (2 * Bψ + U) * U := by
  have e : β q q - β p p = β (q - p) q + β p (q - p) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  have hq : ‖q‖ ≤ Bψ + U := by
    have : q = (q - p) + p := by abel
    calc ‖q‖ = ‖(q - p) + p‖ := by rw [← this]
      _ ≤ ‖q - p‖ + ‖p‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [e]
  calc ‖β (q - p) q + β p (q - p)‖ ≤ ‖β (q - p) q‖ + ‖β p (q - p)‖ := norm_add_le _ _
    _ ≤ ‖q - p‖ * ‖q‖ + ‖p‖ * ‖q - p‖ := add_le_add (hβ _ _) (hβ _ _)
    _ ≤ U * (Bψ + U) + Bψ * U := by
        gcongr
    _ = (2 * Bψ + U) * U := by ring

/-- **REGIONAL (1.3a)** (item 1, constant checked).  For two fields `ψ⁰, ψᵐ` with
`‖ψ⁰ z‖ ≤ Bψ`, `‖ψᵐ z - ψ⁰ z‖ ≤ U` and `Σ_x ‖a(x-y)‖ ≤ Ka`, the difference of the regional
marginal sums `Σ_{y∈R} A(y)` (even kernel) obeys
`‖ΔA(R)‖ ≤ (2Bψ+U) U Ka |R|`.  The algebra gives this constant, without the factor `½` of the
note's (1.3a): every crossing term contains two values of `Δs`, so the `½` is absorbed. -/
theorem regional_flux_diff_le (a : ι → ℂ) (hev : ∀ z, a (-z) = a z)
    (β : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) (hβ : ∀ v w, ‖β v w‖ ≤ ‖v‖ * ‖w‖)
    (ψ0 ψm : ι → E) {Bψ U Ka : ℝ} (hB : 0 ≤ Bψ) (hU : 0 ≤ U)
    (h0 : ∀ z, ‖ψ0 z‖ ≤ Bψ) (hm : ∀ z, ‖ψm z - ψ0 z‖ ≤ U)
    (hK : ∀ y, ∑ x, ‖a (x - y)‖ ≤ Ka) (R : Finset ι) :
    ‖AtermRegion a (fun x => β (ψm x) (ψm x)) R - AtermRegion a (fun x => β (ψ0 x) (ψ0 x)) R‖
      ≤ (2 * Bψ + U) * U * Ka * R.card := by
  rw [regional_marginal_flux_finset _ _ hev, regional_marginal_flux_finset _ _ hev,
    crossFlux_sub]
  exact crossFlux_le a _ R (by positivity)
    (fun z => sq_diff_le β hβ (h0 z) (hm z) hB hU) hK

end Fields

section Example

/-- The even nearest-neighbour kernel on `ZMod 5`. -/
def nnKernel (z : ZMod 5) : ℂ := if z = 1 ∨ z = -1 then 1 else 0

/-- The test function `1_{x = 1}`. -/
def bump (x : ZMod 5) : ℂ := if x = 1 then 1 else 0

theorem nnKernel_even (z : ZMod 5) : nnKernel (-z) = nnKernel z := by
  have h : (-z = 1 ∨ -z = -1) ↔ (z = 1 ∨ z = -1) := by revert z; decide
  unfold nnKernel
  simp only [h]

theorem crossFlux_nn_example : crossFlux nnKernel bump {0} = 1 / 2 := by
  have : (({0} : Finset (ZMod 5))ᶜ) = {1, 2, 3, 4} := by decide
  simp only [crossFlux, this]
  rw [Finset.sum_singleton]
  rw [show ({1, 2, 3, 4} : Finset (ZMod 5)) = insert 1 (insert 2 (insert 3 {4})) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have n2 : (2 : ZMod 5) ≠ 1 := by decide
  have n2' : (2 : ZMod 5) ≠ -1 := by decide
  have n3 : (3 : ZMod 5) ≠ 1 := by decide
  have n3' : (3 : ZMod 5) ≠ -1 := by decide
  have m1 : (-1 : ZMod 5) ≠ 1 := by decide
  have p4 : (4 : ZMod 5) = -1 := by decide
  have n0 : (0 : ZMod 5) ≠ 1 := by decide
  simp [nnKernel, bump, n2, n2', n3, n3', m1, p4, n0]

/-- **Non-example of restriction (REGIONAL §1)**: on `ZMod 5` with the even nearest-neighbour
kernel and `s = 1_{x=1}`, the crossing flux for the proper subset `R = {0}` is `1/2 ≠ 0`, while
the regional sum for `R = univ` vanishes (`AtermRegion_univ`). -/
theorem regional_flux_ne_zero_example :
    ∃ (a s : ZMod 5 → ℂ) (R : Finset (ZMod 5)), (∀ z, a (-z) = a z) ∧
      crossFlux a s R ≠ 0 ∧ AtermRegion a s R ≠ 0 ∧ AtermRegion a s Finset.univ = 0 :=
  ⟨nnKernel, bump, {0}, nnKernel_even, by rw [crossFlux_nn_example]; norm_num,
    by rw [regional_marginal_flux_finset _ _ nnKernel_even, crossFlux_nn_example]; norm_num,
    AtermRegion_univ _ _ nnKernel_even⟩

end Example

section Boundary

open Balaban.LargeField.Def7v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **The grouped boundary quantity of REGIONAL (1.2)**: `𝓑(R, B) = Σ_{y∈R} A(y) - corrSum(R,B)`
with `corrSum` the P5 (1.8) restricted sum.  `A` is a centred marginal term. -/
noncomputable def boundaryB
    (v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (a : Localization.CTorus d L N₁ m₁ k → ℂ) (R B : Finset (Localization.CTorus d L N₁ m₁ k))
    (ψ : Balaban.SmallField.Def6.Fld d L N₁ m₁ k N) (h : Fin N → ℂ) : ℂ :=
  AtermRegion a (fun x => Balaban.SmallField.dot (ψ x) (ψ x)) R - corrSum v₁ v₂ νj R B ψ h

/-- **REGIONAL (1.2)(ii)**: `𝓑(R,B) = (crossing flux (1.3)) - corrSum(R,B)`, for an even kernel. -/
theorem corr_minus_flux
    {v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ} {νj : ℝ}
    {a : Localization.CTorus d L N₁ m₁ k → ℂ} (hev : ∀ z, a (-z) = a z)
    (R B : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Balaban.SmallField.Def6.Fld d L N₁ m₁ k N) (h : Fin N → ℂ) :
    boundaryB v₁ v₂ νj a R B ψ h =
      crossFlux a (fun x => Balaban.SmallField.dot (ψ x) (ψ x)) R - corrSum v₁ v₂ νj R B ψ h := by
  unfold boundaryB
  rw [regional_marginal_flux_finset _ _ hev]

/-- **REGIONAL (1.2)(i)**: for `R = B = univ` and symmetric `v₁, v₂`, even `a`: `𝓑 = 0`
(from `regional_marginal_flux_finset` and `corrSum_self_eq_zero`). -/
theorem boundaryB_univ
    {v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ} {νj : ℝ}
    {a : Localization.CTorus d L N₁ m₁ k → ℂ} (hev : ∀ z, a (-z) = a z)
    (hs₁ : ∀ y x, v₁ y x = v₁ x y) (hs₂ : ∀ y x, v₂ y x = v₂ x y)
    (ψ : Balaban.SmallField.Def6.Fld d L N₁ m₁ k N) (h : Fin N → ℂ) :
    boundaryB v₁ v₂ νj a Finset.univ Finset.univ ψ h = 0 := by
  unfold boundaryB
  rw [AtermRegion_univ _ _ hev, corrSum_self_eq_zero hs₁ hs₂, sub_zero]

/-- More generally, whenever the two summation sets of `corrSum` agree (`R = B`) and the crossing
flux vanishes, `𝓑 = 0`. -/
theorem boundaryB_eq_zero_of_flux
    {v₁ v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ} {νj : ℝ}
    {a : Localization.CTorus d L N₁ m₁ k → ℂ} (hev : ∀ z, a (-z) = a z)
    (hs₁ : ∀ y x, v₁ y x = v₁ x y) (hs₂ : ∀ y x, v₂ y x = v₂ x y)
    (R : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Balaban.SmallField.Def6.Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (hflux : crossFlux a (fun x => Balaban.SmallField.dot (ψ x) (ψ x)) R = 0) :
    boundaryB v₁ v₂ νj a R R ψ h = 0 := by
  rw [corr_minus_flux hev, hflux, corrSum_self_eq_zero hs₁ hs₂, sub_zero]

end Boundary

end Balaban.LargeField.RegionalFlux
