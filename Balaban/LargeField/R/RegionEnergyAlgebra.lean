/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalFlux
public import Balaban.LargeField.R.RegionShrink
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The grouped regional energy term (Q13-TESTS §A (A1)-(A3), Q13-FACTOR (1.1)-(1.2))

For a finite additive group of sites `ι`, a kernel `a`, a function `s` (in the source
`s x = ψ(x)·ψ(x)`) and finsets `R`, `Bc`, write `p(y, x) = ½ a(x - y)(s x - s y)`.

* `pairHalf`, `farCrossing`: `p` and the far crossing sum `Σ_{y∈R} Σ_{x∉Bc} p(y, x)`.
* `pairHalf_antisymm`, `sum_pairHalf_self_eq_zero`: for an even kernel `p` is antisymmetric and its
  double sum over `R × R` vanishes.
* `grouped_eq_far_crossing`: `AtermRegion a s R - Σ_{y∈R} Σ_{x∈Bc} p(y, x)` is the far crossing
  sum.  This needs neither evenness of `a` nor `R ⊆ Bc` (the regional sum is by definition the
  double sum over `R × univ`, and `univ` splits into `Bc` and `Bcᶜ`); evenness and `R ⊆ Bc` are
  needed only to read the left side as a sum of crossing pairs (`grouped_eq_far_crossing_even`).
* `far_crossing_le`, `grouped_mismatch_le`: the bounds (iv), (v) of the brief, under their named
  premises.
* `energyAt_decomposition`, `energyAt_eq_remainder_add_far`: the regrouping of `energyAt`.
* `AtermRegion_sub_corrSum`: the instance with the landed `corrSum` on `CTorus`.
* `nn_example_*`: the `ZMod 5` examples.

Nothing here is a bound on the actual renormalization-group terms.  Whether the coefficient
`v₁^{(j)}(y, x)` equals the marginal kernel `a_j(x - y)` for the actual terms is the I6 relation
(`notes/phase1/PIN-I6.md`); it is not proved in this file.
-/

@[expose] public section

open Finset Balaban.LargeField.RegionalFlux

namespace Balaban.LargeField.RegionEnergyAlgebra

section Algebra

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

/-- The pair term `p(y, x) = ½ a(x - y)(s x - s y)`. -/
noncomputable def pairHalf (a s : ι → ℂ) (y x : ι) : ℂ :=
  (1 / 2 : ℂ) * a (x - y) * (s x - s y)

/-- The far crossing sum `Σ_{y∈R} Σ_{x∉Bc} p(y, x)`. -/
noncomputable def farCrossing (a s : ι → ℂ) (R Bc : Finset ι) : ℂ :=
  ∑ y ∈ R, ∑ x ∈ Bcᶜ, pairHalf a s y x

omit [Fintype ι] [DecidableEq ι] in
/-- (i) For an even kernel the pair term is antisymmetric. -/
theorem pairHalf_antisymm (a s : ι → ℂ) (hev : ∀ z, a (-z) = a z) (y x : ι) :
    pairHalf a s y x = -pairHalf a s x y := by
  unfold pairHalf
  have : y - x = -(x - y) := by abel
  rw [this, hev]; ring

omit [Fintype ι] [DecidableEq ι] in
/-- (i) For an even kernel the double sum of `p` over `R × R` vanishes. -/
theorem sum_pairHalf_self_eq_zero (a s : ι → ℂ) (hev : ∀ z, a (-z) = a z) (R : Finset ι) :
    ∑ y ∈ R, ∑ x ∈ R, pairHalf a s y x = 0 := by
  have h : ∑ y ∈ R, ∑ x ∈ R, pairHalf a s y x = -∑ y ∈ R, ∑ x ∈ R, pairHalf a s y x := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => pairHalf_antisymm a s hev x y
  have h2 : (2 : ℂ) * ∑ y ∈ R, ∑ x ∈ R, pairHalf a s y x = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

omit [DecidableEq ι] in
/-- The regional sum is the double sum of `p` over `R × univ`. -/
theorem AtermRegion_eq_sum_pairHalf (a s : ι → ℂ) (R : Finset ι) :
    AtermRegion a s R = ∑ y ∈ R, ∑ x, pairHalf a s y x := by
  unfold AtermRegion AtermCentre pairHalf
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- (ii) For an even kernel the crossing flux is the double sum of `p` over `R × Rᶜ`. -/
theorem crossFlux_eq_sum_pairHalf (a s : ι → ℂ) (R : Finset ι) :
    crossFlux a s R = ∑ y ∈ R, ∑ x ∈ Rᶜ, pairHalf a s y x := by
  unfold crossFlux pairHalf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- (iii) **Grouped identity**: removing from the regional sum all pairs ending in `Bc` leaves
the far crossing sum.  No hypothesis on `a` or on `R ⊆ Bc` is needed. -/
theorem grouped_eq_far_crossing (a s : ι → ℂ) (R Bc : Finset ι) :
    AtermRegion a s R - ∑ y ∈ R, ∑ x ∈ Bc, pairHalf a s y x = farCrossing a s R Bc := by
  rw [AtermRegion_eq_sum_pairHalf, farCrossing, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_add_sum_compl Bc]
  ring

/-- (iii) in the form of the brief: for an even kernel and `R ⊆ Bc`, the crossing flux minus the
pairs ending in `Bc` is the far crossing sum, and the pairs of `R × (Bc \ R)` are the ones removed. -/
theorem grouped_eq_far_crossing_even (a s : ι → ℂ) (hev : ∀ z, a (-z) = a z) {R Bc : Finset ι}
    (hR : R ⊆ Bc) :
    crossFlux a s R - ∑ y ∈ R, ∑ x ∈ Bc \ R, pairHalf a s y x = farCrossing a s R Bc := by
  rw [← regional_marginal_flux_finset a s hev, ← grouped_eq_far_crossing a s R Bc]
  have hsplit : ∑ y ∈ R, ∑ x ∈ Bc, pairHalf a s y x =
      ∑ y ∈ R, ∑ x ∈ R, pairHalf a s y x + ∑ y ∈ R, ∑ x ∈ Bc \ R, pairHalf a s y x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_comm]
    exact (Finset.sum_sdiff hR).symm
  rw [hsplit, sum_pairHalf_self_eq_zero a s hev, zero_add]

/-- (iv) **Far bound**: if `‖s x‖ ≤ Bs` and the kernel tail beyond the collar,
`Σ_{x∉Bc} ‖a(x - y)‖`, is at most `τ` for every `y ∈ R`, then the far crossing sum is at most
`Bs · τ · |R|`.  (Premises are the bound on `s` and the tail bound; nothing about the actual
renormalization-group terms.) -/
theorem far_crossing_le (a s : ι → ℂ) (R Bc : Finset ι) {Bs τ : ℝ}
    (hs : ∀ x, ‖s x‖ ≤ Bs) (hτ : ∀ y ∈ R, ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ τ) :
    ‖farCrossing a s R Bc‖ ≤ Bs * τ * R.card := by
  unfold farCrossing
  have hy : ∀ y ∈ R, ‖∑ x ∈ Bcᶜ, pairHalf a s y x‖ ≤ Bs * τ := by
    intro y hyR
    have hB : 0 ≤ Bs := (norm_nonneg _).trans (hs y)
    calc ‖∑ x ∈ Bcᶜ, pairHalf a s y x‖
        ≤ ∑ x ∈ Bcᶜ, ‖a (x - y)‖ * Bs := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          unfold pairHalf
          rw [norm_mul, norm_mul]
          have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          have h3 : ‖s x - s y‖ ≤ 2 * Bs := (norm_sub_le _ _).trans (by linarith [hs x, hs y])
          rw [h2]
          nlinarith [norm_nonneg (a (x - y)), norm_nonneg (s x - s y)]
      _ = (∑ x ∈ Bcᶜ, ‖a (x - y)‖) * Bs := (Finset.sum_mul _ _ _).symm
      _ ≤ τ * Bs := mul_le_mul_of_nonneg_right (hτ y hyR) hB
      _ = Bs * τ := by ring
  calc ‖∑ y ∈ R, ∑ x ∈ Bcᶜ, pairHalf a s y x‖
      ≤ ∑ y ∈ R, ‖∑ x ∈ Bcᶜ, pairHalf a s y x‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ R, Bs * τ := Finset.sum_le_sum hy
    _ = Bs * τ * R.card := by simp; ring

/-- (v) **Coefficient mismatch**: if the correction uses coefficients `c(y, x)` with
`‖c y x - a (x - y)‖ ≤ ε y x`, and `‖s x‖ ≤ Bs`, the regional sum minus the correction over
`R × Bc` differs from the far crossing sum by at most `Bs · Σ_{y∈R} Σ_{x∈Bc} ε y x`. -/
theorem grouped_mismatch_le (a s : ι → ℂ) (R Bc : Finset ι) (c : ι → ι → ℂ) (ε : ι → ι → ℝ)
    {Bs : ℝ} (hs : ∀ x, ‖s x‖ ≤ Bs) (hc : ∀ y x, ‖c y x - a (x - y)‖ ≤ ε y x) :
    ‖AtermRegion a s R - ∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * c y x * (s x - s y) -
        farCrossing a s R Bc‖ ≤ Bs * ∑ y ∈ R, ∑ x ∈ Bc, ε y x := by
  have e : AtermRegion a s R - ∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * c y x * (s x - s y) -
      farCrossing a s R Bc =
      ∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * (a (x - y) - c y x) * (s x - s y) := by
    rw [← grouped_eq_far_crossing a s R Bc, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold pairHalf
    ring
  rw [e]
  calc ‖∑ y ∈ R, ∑ x ∈ Bc, (1 / 2 : ℂ) * (a (x - y) - c y x) * (s x - s y)‖
      ≤ ∑ y ∈ R, ∑ x ∈ Bc, ‖(1 / 2 : ℂ) * (a (x - y) - c y x) * (s x - s y)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => norm_sum_le _ _)
    _ ≤ ∑ y ∈ R, ∑ x ∈ Bc, Bs * ε y x := by
        refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun x _ => ?_
        have hB : 0 ≤ Bs := (norm_nonneg _).trans (hs y)
        rw [norm_mul, norm_mul]
        have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        have h3 : ‖s x - s y‖ ≤ 2 * Bs := (norm_sub_le _ _).trans (by linarith [hs x, hs y])
        have h4 : ‖a (x - y) - c y x‖ ≤ ε y x := by rw [norm_sub_rev]; exact hc y x
        rw [h2]
        nlinarith [norm_nonneg (a (x - y) - c y x), norm_nonneg (s x - s y)]
    _ = Bs * ∑ y ∈ R, ∑ x ∈ Bc, ε y x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]

end Algebra

/-! ### The regrouping of `energyAt` -/

section Energy

open Balaban.LargeField.RegionShrink

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

open Classical in
/-- The unrestricted centre sum `Efull y = Σ_{X ∈ U, y ∈ X} E y X`. -/
noncomputable def Efull (U : Finset (Set ι)) (E : ι → Set ι → ℂ) (y : ι) : ℂ :=
  ∑ X ∈ U.filter (fun X => y ∈ X), E y X

open Classical in
/-- The tail `Σ_{X ∈ U, y ∈ X, X ⊄ Bp} E y X` of polymers leaving the support `Bp`. -/
noncomputable def tailAt (U : Finset (Set ι)) (E : ι → Set ι → ℂ) (Bp : Set ι) (y : ι) : ℂ :=
  ∑ X ∈ U.filter (fun X => y ∈ X ∧ ¬ X ⊆ Bp), E y X

omit [AddCommGroup ι] [Fintype ι] [DecidableEq ι] in
theorem polyAt_eq_Efull_sub_tailAt (U : Finset (Set ι)) (E : ι → Set ι → ℂ) (Bp : Set ι)
    (y : ι) : polyAt U E Bp y = Efull U E y - tailAt U E Bp y := by
  classical
  unfold polyAt Efull tailAt
  rw [eq_sub_iff_add_eq, ← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext X
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  · rw [Finset.disjoint_left]
    intro X h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2.2

omit [DecidableEq ι] in
/-- **(A2) at the level of `energyAt`**: a regrouping, valid for every `a, s` and every activity
`E` (no relation between `E` and `a` is used). `Efull y - AtermCentre a s y` is the remainder
`I(y)` of the I6 decomposition. -/
theorem energyAt_decomposition (U : Finset (Set ι)) (E : ι → Set ι → ℂ) (c : ι → ι → ℂ)
    (a s : ι → ℂ) (R Bc : Finset ι) (Bp : Set ι) :
    energyAt U E c R Bc Bp =
      ∑ y ∈ R, (Efull U E y - AtermCentre a s y) + (AtermRegion a s R - RegionShrink.pairSum c R Bc) -
        ∑ y ∈ R, tailAt U E Bp y := by
  unfold energyAt AtermRegion
  simp_rw [polyAt_eq_Efull_sub_tailAt, Finset.sum_sub_distrib]
  ring

/-- Combined with the grouped identity: if the correction coefficients are
`c y x = ½ a(x - y)(s x - s y)`, the middle term of `energyAt_decomposition` is the far crossing
sum. -/
theorem energyAt_eq_remainder_add_far (U : Finset (Set ι)) (E : ι → Set ι → ℂ)
    (a s : ι → ℂ) (R Bc : Finset ι) (Bp : Set ι) :
    energyAt U E (pairHalf a s) R Bc Bp =
      ∑ y ∈ R, (Efull U E y - AtermCentre a s y) + farCrossing a s R Bc -
        ∑ y ∈ R, tailAt U E Bp y := by
  rw [energyAt_decomposition U E (pairHalf a s) a s R Bc Bp, ← grouped_eq_far_crossing]
  rfl

end Energy

/-! ### The instance with the landed correction -/

section Instance

open Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- The `v₂` part of `corrSum`: `Σ_{y∈R} Σ_{x∈Bc} v₂ y x (νj (⟨h, ψ₀ x⟩ - ⟨h, ψ₀ y⟩))`. -/
noncomputable def v2Part
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N)
    (h : Fin N → ℂ) : ℂ :=
  ∑ y ∈ R, ∑ x ∈ Bc, v₂ y x * ((νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y))))

/-- **The instance on `CTorus`** with `s x = ψ x · ψ x` and the landed `corrSum` with
`v₁ y x = a (x - y)`: the regional sum minus `corrSum` is the far crossing sum minus the
`v₂` part.  (`CTorus` is a finite additive commutative group, so `RegionalFlux` applies as is.) -/
theorem AtermRegion_sub_corrSum
    (a : Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N)
    (h : Fin N → ℂ) :
    AtermRegion a (fun x => dot (ψ x) (ψ x)) R - corrSum (fun y x => a (x - y)) v₂ νj R Bc ψ h =
      farCrossing a (fun x => dot (ψ x) (ψ x)) R Bc - v2Part v₂ νj R Bc ψ h := by
  have hc : corrSum (fun y x => a (x - y)) v₂ νj R Bc ψ h =
      ∑ y ∈ R, ∑ x ∈ Bc, pairHalf a (fun x => dot (ψ x) (ψ x)) y x + v2Part v₂ νj R Bc ψ h := by
    unfold corrSum corrPair v2Part pairHalf
    simp_rw [Finset.sum_add_distrib]
  rw [hc, ← grouped_eq_far_crossing]
  ring

end Instance

/-! ### Examples on `ZMod 5` -/

section Example

/-- `R = {0}` and the collar `Bc = {4, 0, 1}` of width one. -/
def collar : Finset (ZMod 5) := {4, 0, 1}

/-- (a) The unpaired regional sum is `1/2`, while the far crossing sum is `0`: the kernel has
range one and the collar has width one, so every crossing pair ends inside the collar. -/
theorem nn_example_unpaired_far :
    AtermRegion nnKernel bump {0} = 1 / 2 ∧ farCrossing nnKernel bump {0} collar = 0 := by
  refine ⟨?_, ?_⟩
  · rw [regional_marginal_flux_finset _ _ nnKernel_even, crossFlux_nn_example]
  · have hc : collarᶜ = ({2, 3} : Finset (ZMod 5)) := by decide
    unfold farCrossing
    rw [hc]
    rw [Finset.sum_singleton, Finset.sum_pair (by decide)]
    have h2 : nnKernel 2 = 0 := by unfold nnKernel; split_ifs with h <;> first | rfl | exact absurd h (by decide)
    have h3 : nnKernel 3 = 0 := by unfold nnKernel; split_ifs with h <;> first | rfl | exact absurd h (by decide)
    simp only [pairHalf, sub_zero, h2, h3]
    ring

/-- The even kernel of range two on `ZMod 5`: it is `1` away from `0`. -/
def wideKernel (z : ZMod 5) : ℂ := if z = 0 then 0 else 1

/-- The test function `1_{x = 2}`. -/
def bump2 (x : ZMod 5) : ℂ := if x = 2 then 1 else 0

theorem wideKernel_even (z : ZMod 5) : wideKernel (-z) = wideKernel z := by
  unfold wideKernel
  simp

/-- (b) With `Bc = R` the far crossing sum is the whole crossing flux, here `1/2 ≠ 0`. -/
theorem nn_example_far_ne_zero_of_collar_eq : farCrossing nnKernel bump {0} {0} = 1 / 2 := by
  have h := grouped_eq_far_crossing nnKernel bump {0} {0}
  rw [← h, regional_marginal_flux_finset _ _ nnKernel_even, crossFlux_nn_example]
  simp [pairHalf, nnKernel, bump]

/-- (b) With a collar of width one and a kernel of range two, the far crossing sum is `1/2 ≠ 0`. -/
theorem wide_example_far : farCrossing wideKernel bump2 {0} collar = 1 / 2 := by
  have hc : collarᶜ = ({2, 3} : Finset (ZMod 5)) := by decide
  unfold farCrossing
  rw [hc, Finset.sum_singleton, Finset.sum_pair (by decide)]
  have h2 : wideKernel 2 = 1 := by unfold wideKernel; split_ifs with h <;> first | rfl | exact absurd h (by decide)
  have h3 : wideKernel 3 = 1 := by unfold wideKernel; split_ifs with h <;> first | rfl | exact absurd h (by decide)
  have b2 : bump2 2 = 1 := by unfold bump2; split_ifs with h <;> first | rfl | exact absurd rfl h
  have b3 : bump2 3 = 0 := by unfold bump2; split_ifs with h <;> first | rfl | exact absurd h (by decide)
  have b0 : bump2 0 = 0 := by unfold bump2; split_ifs with h <;> first | rfl | exact absurd h (by decide)
  simp only [pairHalf, sub_zero, h2, h3, b2, b3, b0]
  ring

end Example

end Balaban.LargeField.RegionEnergyAlgebra
