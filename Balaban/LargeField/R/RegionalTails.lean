/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.HaloDistance
public import Balaban.LargeField.R.RegionEnergyAlgebra
public import Balaban.LargeField.R.RegionalBoundArith
public import Balaban.Fluctuation.HatLabelsAct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The two tails of the grouped regional estimate (Q13-GROUPED §2-§3, estimates (4) and (8))

Two sums are exponentially small in the halo distance.

* **Omitted tail (8).**  `tailAt U E Bp y`, the sum of the activities over the polymers through the
  centre `y` that leave the support `Bp`.
* **Coefficient tail (4), first inequality.**  `Σ_{x ∉ Bc} ‖a(x - y)‖`, the kernel beyond the
  collar, when the kernel is a sum of per-polymer coefficients.

Both rest on one abstract split (`sum_le_of_size`): if the activities decay at rate `κ` in a size
`sz`, if the weighted count `Σ e^{-κ₀ sz}` over the polymers through the centre is at most `K₀`
(entropy), and if the polymers in the sum have `sz ≥ H`, then the sum is at most
`E₀ K₀ e^{-(κ - κ₀) H}`.

## Which entropy statement is used

The landed statement is `Balaban.Fluctuation.entropy_thick`
(`Balaban/Fluctuation/HatLabelsAct.lean`, from `G2_X` in `SizeModEntropy.lean`): for a finite
family of `IsDj` domains and a `π_j`-cube `□`,
`Σ_{Z ⊇ □} e^{-κ₀ treeLenCovOne Z} ≤ K0 d L κ₀` provided `aEnt d L + 1 ≤ κ₀`.  It is a weighted
sum bound, not a bound on the number of polymers of each size.  `entropy_polyUniv` bridges it to
the polymers of `polyUniv` through a site `y`: `IsPolyDom ⇒ IsDj` (`isDj_of_isPolyDom`), a polymer
through `y` contains the whole `π_j`-cell of `y` (`cell_subset_cube`), and `sizeJ` is
`treeLenCovOne` by definition.  The hypotheses of the bridge are typing data only: `L ^ m₀ ∣ N₁`
and `j ≤ k`.

## Results

`sum_le_of_size` (S); `tailAt_le_of_halo`, `sum_tailAt_le_of_halo` (T, abstract);
`kernel_tail_le_of_halo`, `farCrossing_le_of_halo` (K, abstract, with `far_crossing_le`);
`rate_power_form` (P); the instances for `polyUniv`/`sizeJ`/`regionalHaloDistance`:
`entropy_polyUniv`, `tailAt_polyUniv_le_of_halo`, `sum_tailAt_polyUniv_le_of_halo`,
`farCrossing_polyUniv_le_of_halo_of_collar`, `tailAt_polyUniv_le_power`,
`farCrossing_polyUniv_le_power`; and `example_tail`, `example_kernel_tail` on `ZMod 5`.
The names with `_of_halo` take the geometry from `regionalHaloDistance` /
`sizeJ_ge_of_halo_pair`; `_of_collar` records the geometric choice of the collar `Bc` (the fine
set of `Y^≈` lies in `Bc`).

## What is and is not proved

* The note's hypothesis (4)/(8) "the number of size-`n` polymers at a centre is at most
  `K_cnt e^{κ_cnt n}`" is not used; the theorems use the weighted form above, which is what is
  landed.  The two are equivalent up to the constants (the counting form gives the weighted form
  when `κ₀ > κ_cnt`).
* The landed entropy bound needs `κ₀ ≥ aEnt d L + 1`.  The rate in the tail estimates is
  `ρ = κ - κ₀`, so the activity decay rate `κ` of the class bounds must exceed `aEnt d L + 1`;
  this is the compatibility with `ρ = κ_E - κ_cnt > 0` of the note, with `κ_cnt = aEnt d L + 1`.
* The activity bounds `‖E y X‖ ≤ E₀ e^{-κ sizeJ X}`, the coefficient bounds
  `Σ_x ‖c_X(y, x)‖ ≤ A₀ e^{-κ sizeJ X}` and the identification of the kernel `a` with the
  marginal coefficient `v₁` are inputs (hypotheses).  Nothing here bounds the actual
  renormalization-group terms.
* The second inequality of (4) (the moments `D² + D` of `v₂`) is not proved.
-/

@[expose] public section

open Finset Real

namespace Balaban.LargeField.RegionalTails

/-! ### The abstract split of the rate -/

/-- `e^{-κ sz} ≤ e^{-(κ-κ₀) H} e^{-κ₀ sz}` when `κ₀ ≤ κ` and `H ≤ sz`. -/
theorem exp_split_le {κ κ₀ H sz : ℝ} (hκ : κ₀ ≤ κ) (hH : H ≤ sz) :
    exp (-κ * sz) ≤ exp (-(κ - κ₀) * H) * exp (-κ₀ * sz) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_nonneg (sub_nonneg.2 hκ) (sub_nonneg.2 hH)]

/-- **(S) Abstract split of the rate.**  If `f X ≤ E₀ e^{-κ sz X}` on a finite family `U'`, every
`X ∈ U'` has `sz X ≥ H`, `κ₀ ≤ κ`, and `Σ_{X∈U'} e^{-κ₀ sz X} ≤ K₀`, then
`Σ_{X∈U'} f X ≤ E₀ K₀ e^{-(κ-κ₀) H}`. -/
theorem sum_le_of_size {α : Type*} (U' : Finset α) (f sz : α → ℝ) {E₀ K₀ κ κ₀ H : ℝ}
    (hE₀ : 0 ≤ E₀) (hκ : κ₀ ≤ κ) (hf : ∀ X ∈ U', f X ≤ E₀ * exp (-κ * sz X))
    (hH : ∀ X ∈ U', H ≤ sz X) (hent : ∑ X ∈ U', exp (-κ₀ * sz X) ≤ K₀) :
    ∑ X ∈ U', f X ≤ E₀ * K₀ * exp (-(κ - κ₀) * H) := by
  calc ∑ X ∈ U', f X ≤ ∑ X ∈ U', E₀ * exp (-(κ - κ₀) * H) * exp (-κ₀ * sz X) := by
        refine Finset.sum_le_sum fun X hX => (hf X hX).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (exp_split_le hκ (hH X hX)) hE₀
    _ = E₀ * exp (-(κ - κ₀) * H) * ∑ X ∈ U', exp (-κ₀ * sz X) := (Finset.mul_sum _ _ _).symm
    _ ≤ E₀ * exp (-(κ - κ₀) * H) * K₀ :=
        mul_le_mul_of_nonneg_left hent (mul_nonneg hE₀ (Real.exp_pos _).le)
    _ = E₀ * K₀ * exp (-(κ - κ₀) * H) := by ring

/-- (S) with the entropy bound stated on a larger family `U ⊇ U'`. -/
theorem sum_le_of_size_subset {α : Type*} (U U' : Finset α) (hsub : U' ⊆ U) (f sz : α → ℝ)
    {E₀ K₀ κ κ₀ H : ℝ} (hE₀ : 0 ≤ E₀) (hκ : κ₀ ≤ κ)
    (hf : ∀ X ∈ U', f X ≤ E₀ * exp (-κ * sz X)) (hH : ∀ X ∈ U', H ≤ sz X)
    (hent : ∑ X ∈ U, exp (-κ₀ * sz X) ≤ K₀) :
    ∑ X ∈ U', f X ≤ E₀ * K₀ * exp (-(κ - κ₀) * H) :=
  sum_le_of_size U' f sz hE₀ hκ hf hH
    ((Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans hent)

/-! ### (T) the omitted tail, abstract -/

section Tail

open Balaban.LargeField.RegionEnergyAlgebra

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

omit [AddCommGroup ι] [Fintype ι] [DecidableEq ι] in
open Classical in
/-- **(T) Omitted tail, abstract form.**  For a centre `y`: if the activities through `y` satisfy
`‖E y X‖ ≤ E₀ e^{-κ sz X}`, the entropy at `y` is `Σ_{X∈U, y∈X} e^{-κ₀ sz X} ≤ K₀`, and every
polymer through `y` leaving `Bp` has `sz X ≥ H` (the geometric premise `hgeom`), then
`‖tailAt U E Bp y‖ ≤ E₀ K₀ e^{-(κ-κ₀) H}`. -/
theorem tailAt_le_of_halo (U : Finset (Set ι)) (E : ι → Set ι → ℂ) (Bp : Set ι) (y : ι)
    (sz : Set ι → ℝ) {E₀ K₀ κ κ₀ H : ℝ} (hE₀ : 0 ≤ E₀) (hκ : κ₀ ≤ κ)
    (hE : ∀ X ∈ U, y ∈ X → ‖E y X‖ ≤ E₀ * exp (-κ * sz X))
    (hgeom : ∀ X ∈ U, y ∈ X → ¬ X ⊆ Bp → H ≤ sz X)
    (hent : ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀) :
    ‖tailAt U E Bp y‖ ≤ E₀ * K₀ * exp (-(κ - κ₀) * H) := by
  unfold tailAt
  refine (norm_sum_le _ _).trans ?_
  refine sum_le_of_size_subset (U.filter (fun X => y ∈ X)) _ ?_ (fun X => ‖E y X‖) sz hE₀ hκ
    ?_ ?_ hent
  · intro X hX
    simp only [Finset.mem_filter] at hX ⊢
    exact ⟨hX.1, hX.2.1⟩
  · intro X hX
    simp only [Finset.mem_filter] at hX
    exact hE X hX.1 hX.2.1
  · intro X hX
    simp only [Finset.mem_filter] at hX
    exact hgeom X hX.1 hX.2.1 hX.2.2

omit [AddCommGroup ι] [Fintype ι] [DecidableEq ι] in
open Classical in
/-- Summed over the centres of a region `R`: `‖Σ_{y∈R} tailAt‖ ≤ |R| · E₀ K₀ e^{-(κ-κ₀) H}`. -/
theorem sum_tailAt_le_of_halo (U : Finset (Set ι)) (E : ι → Set ι → ℂ) (Bp : Set ι)
    (R : Finset ι) (sz : Set ι → ℝ) {E₀ K₀ κ κ₀ H : ℝ} (hE₀ : 0 ≤ E₀) (hκ : κ₀ ≤ κ)
    (hE : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ‖E y X‖ ≤ E₀ * exp (-κ * sz X))
    (hgeom : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ¬ X ⊆ Bp → H ≤ sz X)
    (hent : ∀ y ∈ R, ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀) :
    ‖∑ y ∈ R, tailAt U E Bp y‖ ≤ R.card * (E₀ * K₀ * exp (-(κ - κ₀) * H)) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y ∈ R, ‖tailAt U E Bp y‖ ≤ ∑ _y ∈ R, E₀ * K₀ * exp (-(κ - κ₀) * H) :=
        Finset.sum_le_sum fun y hy =>
          tailAt_le_of_halo U E Bp y sz hE₀ hκ (hE y hy) (hgeom y hy) (hent y hy)
    _ = R.card * (E₀ * K₀ * exp (-(κ - κ₀) * H)) := by simp

end Tail

/-! ### (K) the coefficient tail, abstract -/

section Kernel

open Balaban.LargeField.RegionEnergyAlgebra

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

open Classical in
/-- **(K) Coefficient tail, abstract form.**  Let the kernel be a sum of per-polymer coefficients,
`a(x - y) = Σ_{X∈U, y∈X, x∈X} c X y x` (hypothesis `ha`, for the centre `y`), with
`Σ_{x∈X} ‖c X y x‖ ≤ A₀ e^{-κ sz X}` for `X ∈ U` through `y`.  If a polymer through `y` that
contains a site `x ∉ Bc` has `sz X ≥ H` (`hgeom`), and the entropy at `y` is at most `K₀`, then
`Σ_{x∉Bc} ‖a(x - y)‖ ≤ A₀ K₀ e^{-(κ-κ₀) H}`. -/
theorem kernel_tail_le_of_halo (U : Finset (Set ι)) (c : Set ι → ι → ι → ℂ) (a : ι → ℂ)
    (Bc : Finset ι) (y : ι) (sz : Set ι → ℝ) {A₀ K₀ κ κ₀ H : ℝ} (hA₀ : 0 ≤ A₀) (hκ : κ₀ ≤ κ)
    (ha : ∀ x, a (x - y) = ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ X ∈ U, y ∈ X → ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
      A₀ * exp (-κ * sz X))
    (hgeom : ∀ X ∈ U, y ∈ X → ∀ x ∈ X, x ∉ Bc → H ≤ sz X)
    (hent : ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀) :
    ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ A₀ * K₀ * exp (-(κ - κ₀) * H) := by
  -- the per-polymer mass outside the collar
  set g : Set ι → ℝ := fun X => ∑ x ∈ Bcᶜ, if x ∈ X then ‖c X y x‖ else 0 with hg
  have h1 : ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ ∑ X ∈ U.filter (fun X => y ∈ X), g X := by
    calc ∑ x ∈ Bcᶜ, ‖a (x - y)‖
        ≤ ∑ x ∈ Bcᶜ, ∑ X ∈ U.filter (fun X => y ∈ X), (if x ∈ X then ‖c X y x‖ else 0) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [ha x]
          refine (norm_sum_le _ _).trans ?_
          rw [← Finset.sum_filter, Finset.filter_filter]
      _ = _ := Finset.sum_comm
  have h2 : ∀ X ∈ U.filter (fun X => y ∈ X),
      g X ≤ A₀ * exp (-(κ - κ₀) * H) * exp (-κ₀ * sz X) := by
    intro X hX
    obtain ⟨hXU, hyX⟩ := Finset.mem_filter.1 hX
    by_cases hex : ∃ x ∈ Bcᶜ, x ∈ X
    · obtain ⟨x, hxB, hxX⟩ := hex
      have hH : H ≤ sz X := hgeom X hXU hyX x hxX (by simpa using hxB)
      have hgc : g X ≤ ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => ?_
        split_ifs <;> simp
      refine hgc.trans ((hc X hXU hyX).trans ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exp_split_le hκ hH) hA₀
    · push Not at hex
      have : g X = 0 := Finset.sum_eq_zero fun x hx => by simp [hex x hx]
      rw [this]
      exact mul_nonneg (mul_nonneg hA₀ (Real.exp_pos _).le) (Real.exp_pos _).le
  calc ∑ x ∈ Bcᶜ, ‖a (x - y)‖ ≤ ∑ X ∈ U.filter (fun X => y ∈ X), g X := h1
    _ ≤ ∑ X ∈ U.filter (fun X => y ∈ X), A₀ * exp (-(κ - κ₀) * H) * exp (-κ₀ * sz X) :=
        Finset.sum_le_sum h2
    _ = A₀ * exp (-(κ - κ₀) * H) * ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ A₀ * exp (-(κ - κ₀) * H) * K₀ :=
        mul_le_mul_of_nonneg_left hent (mul_nonneg hA₀ (Real.exp_pos _).le)
    _ = A₀ * K₀ * exp (-(κ - κ₀) * H) := by ring

open Classical in
/-- **(K) combined with `far_crossing_le`.**  Under the hypotheses of `kernel_tail_le_of_halo` at
every centre `y ∈ R`, with `‖s x‖ ≤ Bs`:
`‖farCrossing a s R Bc‖ ≤ Bs · (A₀ K₀ e^{-(κ-κ₀) H}) · |R|`. -/
theorem farCrossing_le_of_halo (U : Finset (Set ι)) (c : Set ι → ι → ι → ℂ) (a s : ι → ℂ)
    (R Bc : Finset ι) (sz : Set ι → ℝ) {A₀ K₀ κ κ₀ H Bs : ℝ} (hA₀ : 0 ≤ A₀) (hκ : κ₀ ≤ κ)
    (hs : ∀ x, ‖s x‖ ≤ Bs)
    (ha : ∀ y ∈ R, ∀ x, a (x - y) = ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
      A₀ * exp (-κ * sz X))
    (hgeom : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ∀ x ∈ X, x ∉ Bc → H ≤ sz X)
    (hent : ∀ y ∈ R, ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀) :
    ‖farCrossing a s R Bc‖ ≤ Bs * (A₀ * K₀ * exp (-(κ - κ₀) * H)) * R.card :=
  far_crossing_le a s R Bc hs fun y hy =>
    kernel_tail_le_of_halo U c a Bc y sz hA₀ hκ (ha y hy) (hc y hy) (hgeom y hy) (hent y hy)

end Kernel

/-! ### Power form (P) -/

section Power

open Balaban.LargeField.RegionalArith

/-- **(P) Power form of the rate.**  With the halo bound `H = c Rq P - 2 Lc` (`P = L^(k-j)`, `c` the
constant `c_h`, `Rq` the radius, `Lc` the constant `L`), `ρ > 0`, a lower radius `Rs ≤ Rq`, `s = 1/P`
and the exponent `p = d + α₃ > 0`:
`E₀ K₀ e^{-ρ H} ≤ C_T E₀ s^p` with `C_T = K₀ e^{2 Lc ρ} (p / (e ρ c Rs))^p`. -/
theorem rate_power_form {E₀ K₀ ρ c Rq Rs P Lc d α₃ : ℝ} (hE₀ : 0 ≤ E₀) (hK₀ : 0 ≤ K₀)
    (hP : 0 < P) (hρ : 0 < ρ) (hc : 0 < c) (hRs : 0 < Rs) (hRq : Rs ≤ Rq) (hp : 0 < d + α₃) :
    E₀ * K₀ * exp (-ρ * (c * Rq * P - 2 * Lc)) ≤
      (K₀ * exp (2 * Lc * ρ) * ((d + α₃) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃)) * E₀ *
        (P⁻¹) ^ (d + α₃) := by
  have hs : 0 < P⁻¹ := inv_pos.2 hP
  have h := tail_term_le hs hρ hc hRs hRq hp
  have e1 : exp (-ρ * (c * Rq * P - 2 * Lc)) = exp (2 * Lc * ρ) * exp (-(ρ * c * Rq / P⁻¹)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e1]
  have h2 : 0 ≤ E₀ * K₀ * exp (2 * Lc * ρ) := by positivity
  calc E₀ * K₀ * (exp (2 * Lc * ρ) * exp (-(ρ * c * Rq / P⁻¹)))
      = (E₀ * K₀ * exp (2 * Lc * ρ)) * exp (-(ρ * c * Rq / P⁻¹)) := by ring
    _ ≤ (E₀ * K₀ * exp (2 * Lc * ρ)) *
          (((d + α₃) / (exp 1 * (ρ * c * Rs))) ^ (d + α₃) * (P⁻¹) ^ (d + α₃)) :=
        mul_le_mul_of_nonneg_left h h2
    _ = _ := by ring

end Power



/-! ### The instance for `polyUniv`, `sizeJ` and the halo distance -/

section Instance

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.RegionShrink Balaban.LargeField.RegionEnergyAlgebra

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- Membership in the finite universe of admissible polymers. -/
theorem mem_polyUniv {j : ℕ} {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} :
    X ∈ polyUniv C j ↔ Def6.IsPolyDom C.m₀ j X := by
  unfold polyUniv
  exact Set.Finite.mem_toFinset _

open Classical in
/-- **Entropy for the polymers through a site.**  For `κ₀ ≥ aEnt d L + 1`, the polymers of
`polyUniv C j` through the site `y` satisfy `Σ e^{-κ₀ sizeJ X} ≤ K0 d L κ₀`.  Bridge from
`entropy_thick`: `IsPolyDom ⇒ IsDj`, and a polymer through `y` contains the `π_j`-cell of `y`.
Typing data only: `L ^ m₀ ∣ N₁` and `j ≤ k`. -/
theorem entropy_polyUniv {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (y : Localization.CTorus S.d S.L C.N₁ m₁ k) {κ₀ : ℝ} (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀) :
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X), exp (-κ₀ * Def6.sizeJ C.m₀ j X) ≤
      K0 S.d S.L κ₀ := by
  set 𝒵 := (polyUniv C j).filter (fun X => y ∈ X) with h𝒵
  have hmem : ∀ Z ∈ 𝒵, Def6.IsPolyDom C.m₀ j Z ∧ y ∈ Z := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hZ
    exact ⟨(mem_polyUniv C).1 h1, h2⟩
  have hD : ∀ Z ∈ 𝒵, IsDj C.m₀ j Z := fun Z hZ => Def6.isDj_of_isPolyDom (hmem Z hZ).1
  have hent := entropy_thick (m₁ := m₁) (K := k) (m₀ := C.m₀) (j := j) hN hj 𝒵 hD hκ₀
    ⟨cbase (cellSide S.L C.m₀ m₁ j) y, aligned_cbase y, Set.subset_univ _⟩
  refine le_trans (le_of_eq ?_) hent
  rw [← Finset.sum_coe_sort 𝒵]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have hZ := Z.2
  obtain ⟨hZP, hyZ⟩ := hmem Z.1 hZ
  have hbox : Localization.box (cbase (cellSide S.L C.m₀ m₁ j) y) (cellSide S.L C.m₀ m₁ j) ⊆ Z := by
    obtain ⟨b, hb, hyb, hbZ⟩ := (hD Z.1 hZ).2.1 y hyZ
    exact (cell_subset_cube (cellSide_dvd hN hj) (cellSide_pos C.m₀ m₁ j) hb hyb).trans hbZ
  split_ifs with h
  · rfl
  · exact absurd hbox h

open Classical in
/-- **The omitted tail for the landed objects** (note (8)).  For a centre
`y ∈ alignedIn j Y`, `j ≤ k`, `κ₀ ≥ aEnt d L + 1`, `κ₀ ≤ κ`, and activities with
`‖E_j(y, X)‖ ≤ E₀ e^{-κ sizeJ X}` (the class bound, an input):
`‖tailAt (polyUniv C j) E (sset (thickY R Y)) y‖ ≤ E₀ K₀ e^{-(κ-κ₀) H}` with
`H = c_h R_{k-1} L^(k-j) - 2 L`, `c_h = M / L^(m₀+m₁)`. -/
theorem tailAt_polyUniv_le_of_halo {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ)
    (Y : Set (Torus S.d (n k))) {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : y ∈ C.alignedIn j Y)
    {E₀ κ κ₀ : ℝ} (hE₀ : 0 ≤ E₀) (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hE : ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X → ‖E y X‖ ≤ E₀ * exp (-κ * Def6.sizeJ C.m₀ j X)) :
    ‖tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖ ≤
      E₀ * K0 S.d S.L κ₀ * exp (-(κ - κ₀) *
        (((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * R (k - 1) * (S.L : ℝ) ^ (k - j) - 2 * S.L)) := by
  have hysY : y ∈ C.sset Y := (Finset.mem_filter.1 hy).2.2
  refine tailAt_le_of_halo (polyUniv C j) E (C.sset (thickY R Y)) y (Def6.sizeJ C.m₀ j) hE₀ hκ
    (fun X hX hyX => hE X ((mem_polyUniv C).1 hX) hyX)
    (fun X hX hyX hnot =>
      regionalHaloDistance C hj ((mem_polyUniv C).1 hX) hyX hysY hnot)
    (entropy_polyUniv C hN hj y hκ₀)

open Classical in
/-- The tail summed over the centres `y ∈ R'` of the region (all in `alignedIn j Y`), a multiple
`|R'|` of the single-centre bound. -/
theorem sum_tailAt_polyUniv_le_of_halo {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ)
    (Y : Set (Torus S.d (n k))) {E₀ κ κ₀ : ℝ} (hE₀ : 0 ≤ E₀) (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hE : ∀ y ∈ C.alignedIn j Y, ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      ‖E y X‖ ≤ E₀ * exp (-κ * Def6.sizeJ C.m₀ j X)) :
    ‖∑ y ∈ C.alignedIn j Y, tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖ ≤
      (C.alignedIn j Y).card * (E₀ * K0 S.d S.L κ₀ * exp (-(κ - κ₀) *
        (((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * R (k - 1) * (S.L : ℝ) ^ (k - j) - 2 * S.L))) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y ∈ C.alignedIn j Y, ‖tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖
      ≤ ∑ _y ∈ C.alignedIn j Y, E₀ * K0 S.d S.L κ₀ * exp (-(κ - κ₀) *
        (((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * R (k - 1) * (S.L : ℝ) ^ (k - j) - 2 * S.L)) :=
        Finset.sum_le_sum fun y hy =>
          tailAt_polyUniv_le_of_halo C hN hj E Y hy hE₀ hκ₀ hκ (hE y hy)
    _ = _ := by simp

open Classical in
/-- **The coefficient tail and the far crossing sum for the landed objects** (note (4), first
inequality).  The kernel `a` is a sum of per-polymer coefficients `c X y x` over the polymers of
`polyUniv C j` through `y` and `x` (`ha`, with the identification of `a` an input), with
`Σ_{x∈X} ‖c X y x‖ ≤ A₀ e^{-κ sizeJ X}`.  The premise `hBc` is the geometric choice of the
collar: the fine set of the thickening `Y^≈` lies in `Bc` (so `x ∉ Bc` is off `Y^≈`, and the pair
form of the halo distance applies).  Then
`‖farCrossing a s R' Bc‖ ≤ Bs · (A₀ K₀ e^{-(κ-κ₀) H}) · |R'|` for any `R' ⊆ alignedIn j Y`. -/
theorem farCrossing_polyUniv_le_of_halo_of_collar {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (c : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (a s : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ) (Y : Set (Torus S.d (n k)))
    (R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)) (hR' : R' ⊆ C.alignedIn j Y)
    (hBc : ∀ x, x ∈ C.sset (thickY R Y) → x ∈ Bc)
    {A₀ κ κ₀ Bs : ℝ} (hA₀ : 0 ≤ A₀) (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hs : ∀ x, ‖s x‖ ≤ Bs)
    (ha : ∀ y ∈ R', ∀ x, a (x - y) =
      ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
        A₀ * exp (-κ * Def6.sizeJ C.m₀ j X)) :
    ‖farCrossing a s R' Bc‖ ≤ Bs * (A₀ * K0 S.d S.L κ₀ * exp (-(κ - κ₀) *
      (((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * R (k - 1) * (S.L : ℝ) ^ (k - j) - 2 * S.L))) *
        R'.card := by
  refine farCrossing_le_of_halo (polyUniv C j) c a s R' Bc (Def6.sizeJ C.m₀ j) hA₀ hκ hs ha
    (fun y hy X hX => hc y hy X ((mem_polyUniv C).1 hX)) ?_
    (fun y _ => entropy_polyUniv C hN hj y hκ₀)
  intro y hy X hX hyX x hxX hxB
  have hyY : y ∈ C.sset Y := (Finset.mem_filter.1 (hR' hy)).2.2
  have hXP := (mem_polyUniv C).1 hX
  have hxn : x ∉ C.sset (thickY R Y) := fun h => hxB (hBc x h)
  have h := sizeJ_ge_of_halo_pair C hXP hyX hxX hyY hxn
  rw [sigma_div_cell C hj] at h
  have hc0 : (0 : ℝ) ≤ ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * (S.L : ℝ) ^ (k - j) := by
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hR : R (k - 1) ≤ (⌊R (k - 1)⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  nlinarith

open Classical in
/-- **(P) for the omitted tail of the landed objects.**  With `ρ = κ - κ₀ > 0`, `c_h = M / L^(m₀+m₁)
> 0`, a lower radius `0 < Rs ≤ R_{k-1}`, `s = L^{-(k-j)}` and `p = d + α₃ > 0`:
`‖tailAt‖ ≤ C_T E₀ s^p`, `C_T = K₀ e^{2 L ρ} (p / (e ρ c_h Rs))^p`, `K₀ = K0 d L κ₀`. -/
theorem tailAt_polyUniv_le_power {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (E : Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ)
    (Y : Set (Torus S.d (n k))) {y : Localization.CTorus S.d S.L C.N₁ m₁ k}
    (hy : y ∈ C.alignedIn j Y) {E₀ κ κ₀ Rs d α₃ : ℝ} (hE₀ : 0 ≤ E₀)
    (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀) (hκ : κ₀ < κ) (hRs : 0 < Rs) (hRq : Rs ≤ R (k - 1))
    (hM : 0 < M) (hp : 0 < d + α₃)
    (hE : ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      ‖E y X‖ ≤ E₀ * exp (-κ * Def6.sizeJ C.m₀ j X)) :
    ‖tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖ ≤
      (K0 S.d S.L κ₀ * exp (2 * S.L * (κ - κ₀)) *
        ((d + α₃) / (exp 1 * ((κ - κ₀) * ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * Rs))) ^ (d + α₃)) *
        E₀ * (((S.L : ℝ) ^ (k - j))⁻¹) ^ (d + α₃) := by
  have hK : 0 ≤ K0 S.d S.L κ₀ := by
    unfold K0
    refine div_nonneg (Real.exp_pos _).le (sub_nonneg.2 ?_)
    exact (Real.exp_le_one_iff.2 (by norm_num))
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have h1 := tailAt_polyUniv_le_of_halo C hN hj E Y hy hE₀ hκ₀ hκ.le hE
  refine h1.trans ?_
  have h2 := rate_power_form (E₀ := E₀) (K₀ := K0 S.d S.L κ₀) (ρ := κ - κ₀)
    (c := (M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) (Rq := R (k - 1)) (Rs := Rs)
    (P := (S.L : ℝ) ^ (k - j)) (Lc := S.L) (d := d) (α₃ := α₃) hE₀ hK (by positivity)
    (sub_pos.2 hκ) (by have : (0 : ℝ) < M := by exact_mod_cast hM
                       positivity) hRs hRq hp
  exact h2

open Classical in
/-- **(P) for the far crossing sum of the landed objects**: under the hypotheses of
`farCrossing_polyUniv_le_of_halo_of_collar`, with `ρ = κ - κ₀ > 0`, `0 < Rs ≤ R_{k-1}`, `M > 0`,
`s = L^{-(k-j)}`, `p = d + α₃ > 0`:
`‖farCrossing a s R' Bc‖ ≤ Bs · (C_T A₀ s^p) · |R'|`, `C_T = K₀ e^{2 L ρ} (p / (e ρ c_h Rs))^p`. -/
theorem farCrossing_polyUniv_le_power {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (c : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (a s : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ) (Y : Set (Torus S.d (n k)))
    (R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)) (hR' : R' ⊆ C.alignedIn j Y)
    (hBc : ∀ x, x ∈ C.sset (thickY R Y) → x ∈ Bc)
    {A₀ κ κ₀ Bs Rs d α₃ : ℝ} (hA₀ : 0 ≤ A₀) (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀) (hκ : κ₀ < κ)
    (hRs : 0 < Rs) (hRq : Rs ≤ R (k - 1)) (hM : 0 < M) (hp : 0 < d + α₃)
    (hs : ∀ x, ‖s x‖ ≤ Bs)
    (ha : ∀ y ∈ R', ∀ x, a (x - y) =
      ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
        A₀ * exp (-κ * Def6.sizeJ C.m₀ j X)) :
    ‖farCrossing a s R' Bc‖ ≤ Bs * ((K0 S.d S.L κ₀ * exp (2 * S.L * (κ - κ₀)) *
        ((d + α₃) / (exp 1 * ((κ - κ₀) * ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * Rs))) ^ (d + α₃)) *
          A₀ * (((S.L : ℝ) ^ (k - j))⁻¹) ^ (d + α₃)) * R'.card := by
  have hK : 0 ≤ K0 S.d S.L κ₀ := by
    unfold K0
    refine div_nonneg (Real.exp_pos _).le (sub_nonneg.2 ?_)
    exact (Real.exp_le_one_iff.2 (by norm_num))
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hB : 0 ≤ Bs := by
    by_cases hx : Nonempty (Localization.CTorus S.d S.L C.N₁ m₁ k)
    · obtain ⟨x⟩ := hx
      exact (norm_nonneg _).trans (hs x)
    · exact absurd ⟨0⟩ hx
  have h1 := farCrossing_polyUniv_le_of_halo_of_collar C hN hj c a s Y R' Bc hR' hBc hA₀ hκ₀ hκ.le
    hs ha hc
  have h2 := rate_power_form (E₀ := A₀) (K₀ := K0 S.d S.L κ₀) (ρ := κ - κ₀)
    (c := (M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) (Rq := R (k - 1)) (Rs := Rs)
    (P := (S.L : ℝ) ^ (k - j)) (Lc := S.L) (d := d) (α₃ := α₃) hA₀ hK (by positivity)
    (sub_pos.2 hκ) (by have : (0 : ℝ) < M := by exact_mod_cast hM
                       positivity) hRs hRq hp
  refine h1.trans ?_
  have h3 : A₀ * K0 S.d S.L κ₀ * exp (-(κ - κ₀) *
      (((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * R (k - 1) * (S.L : ℝ) ^ (k - j) - 2 * S.L)) ≤
      (K0 S.d S.L κ₀ * exp (2 * S.L * (κ - κ₀)) *
        ((d + α₃) / (exp 1 * ((κ - κ₀) * ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * Rs))) ^ (d + α₃)) *
          A₀ * (((S.L : ℝ) ^ (k - j))⁻¹) ^ (d + α₃) := h2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hB) (Nat.cast_nonneg _)

end Instance

/-! ### Non-vacuity: intervals on `ZMod 5` -/

section Example

open Balaban.LargeField.RegionEnergyAlgebra

/-- The polymer `{0}`. -/
def polyA : Set (ZMod 5) := {0}

/-- The polymer `{0, 1}`. -/
def polyB : Set (ZMod 5) := {0, 1}

open Classical in
/-- The family of polymers. -/
noncomputable def exU : Finset (Set (ZMod 5)) := {polyA, polyB}

/-- The size: the number of sites. -/
noncomputable def exSz (X : Set (ZMod 5)) : ℝ := (X.ncard : ℝ)

/-- The activity `e^{-2 |X|}`. -/
noncomputable def exE (_y : ZMod 5) (X : Set (ZMod 5)) : ℂ := ((Real.exp (-2 * exSz X) : ℝ) : ℂ)

theorem polyA_ne_polyB : polyA ≠ polyB := by
  intro h
  have : (1 : ZMod 5) ∈ polyB := by simp [polyB]
  rw [← h] at this
  simp [polyA] at this
  exact absurd this (by decide)

theorem ncard_polyA : exSz polyA = 1 := by
  simp [exSz, polyA]

theorem ncard_polyB : exSz polyB = 2 := by
  unfold exSz polyB
  rw [Set.ncard_pair (by decide)]
  norm_num

open Classical in
/-- The tail of the example is `e^{-4}`: only `{0,1}` leaves `{0}`. -/
theorem exTail_eq : tailAt exU exE polyA 0 = ((Real.exp (-4) : ℝ) : ℂ) := by
  have hf : exU.filter (fun X => (0 : ZMod 5) ∈ X ∧ ¬ X ⊆ polyA) = {polyB} := by
    ext X
    simp only [exU, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hX | hX, h0, hn⟩
      · exact absurd (hX ▸ subset_rfl) hn
      · exact hX
    · rintro rfl
      refine ⟨Or.inr rfl, by simp [polyB], fun h => ?_⟩
      have : (1 : ZMod 5) ∈ polyA := h (by simp [polyB])
      simp [polyA] at this
      exact absurd this (by decide)
  unfold tailAt
  rw [hf, Finset.sum_singleton, exE, ncard_polyB]
  norm_num

open Classical in
/-- **T2 instance**: with `κ = 2`, `κ₀ = 1`, `E₀ = 1`, `K₀ = e^{-1} + e^{-2}`, `H = 2`, the abstract
tail lemma applies and the tail is nonzero (`e^{-4}`), below the bound `K₀ e^{-2}`. -/
theorem example_tail :
    ‖tailAt exU exE polyA 0‖ ≤ 1 * (Real.exp (-1) + Real.exp (-2)) * Real.exp (-(2 - 1) * 2) ∧
      tailAt exU exE polyA 0 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · refine tailAt_le_of_halo exU exE polyA 0 exSz (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro X hX _
      have : ‖exE 0 X‖ = Real.exp (-2 * exSz X) := by
        unfold exE; rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [this]; simp
    · intro X hX h0 hn
      simp only [exU, Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · exact absurd subset_rfl hn
      · rw [ncard_polyB]
    · have hsub : exU.filter (fun X => (0 : ZMod 5) ∈ X) = exU := by
        ext X
        simp only [exU, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl) <;> simp [polyA, polyB]
      rw [hsub]
      unfold exU
      rw [Finset.sum_pair polyA_ne_polyB, ncard_polyA, ncard_polyB]
      norm_num
  · rw [exTail_eq]
    exact_mod_cast (Real.exp_pos _).ne'

/-- The per-polymer coefficient `e^{-2|X|} / |X|` (spread uniformly over the sites of `X`). -/
noncomputable def exC (X : Set (ZMod 5)) (_y _x : ZMod 5) : ℂ :=
  ((Real.exp (-2 * exSz X) / exSz X : ℝ) : ℂ)

open Classical in
/-- The kernel at the centre `0`: the sum of the coefficients of the polymers through `0` and `x`. -/
noncomputable def exA (z : ZMod 5) : ℂ := ∑ X ∈ exU.filter (fun X => (0 : ZMod 5) ∈ X ∧ z ∈ X), exC X 0 z

open Classical in
theorem filter_mem_polyA : Finset.univ.filter (fun x : ZMod 5 => x ∈ polyA) = {0} := by
  ext x; simp [polyA]

open Classical in
theorem filter_mem_polyB : Finset.univ.filter (fun x : ZMod 5 => x ∈ polyB) = {0, 1} := by
  ext x; simp [polyB]

open Classical in
/-- **T3 instance**: the coefficient tail beyond the collar `{0}` is nonzero and below
`A₀ K₀ e^{-(κ-κ₀) H}` with `A₀ = 1`, `κ = 2`, `κ₀ = 1`, `H = 2`, `K₀ = e^{-1} + e^{-2}`. -/
theorem example_kernel_tail :
    0 < ∑ x ∈ ({0} : Finset (ZMod 5))ᶜ, ‖exA (x - 0)‖ ∧
    ∑ x ∈ ({0} : Finset (ZMod 5))ᶜ, ‖exA (x - 0)‖ ≤
      1 * (Real.exp (-1) + Real.exp (-2)) * Real.exp (-(2 - 1) * 2) := by
  have hmemU : ∀ X ∈ exU, X = polyA ∨ X = polyB := by
    intro X hX
    simpa [exU] using hX
  refine ⟨?_, ?_⟩
  · have h1 : exU.filter (fun X => (0 : ZMod 5) ∈ X ∧ (1 : ZMod 5) ∈ X) = {polyB} := by
      ext X
      simp only [exU, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h0, h1⟩
        · simp [polyA] at h1
          exact absurd h1 (by decide)
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, by simp [polyB]⟩
    have hpos : 0 < ‖exA ((1 : ZMod 5) - 0)‖ := by
      rw [sub_zero]
      unfold exA
      rw [h1, Finset.sum_singleton]
      unfold exC
      rw [ncard_polyB, Complex.norm_real]
      exact norm_pos_iff.2 (by positivity)
    refine lt_of_lt_of_le hpos ?_
    exact Finset.single_le_sum (f := fun x : ZMod 5 => ‖exA (x - 0)‖) (fun _ _ => norm_nonneg _)
      (by decide : (1 : ZMod 5) ∈ ({0} : Finset (ZMod 5))ᶜ)
  · refine kernel_tail_le_of_halo exU exC exA {0} 0 exSz (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
    · intro x; rw [sub_zero]; rfl
    · intro X hX h0
      rcases hmemU X hX with rfl | rfl
      · rw [filter_mem_polyA]
        rw [Finset.sum_singleton]
        simp only [exC, ncard_polyA, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity)]
        norm_num
      · rw [filter_mem_polyB]
        rw [Finset.sum_pair (by decide)]
        simp only [exC, ncard_polyB, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity)]
        norm_num
    · intro X hX h0 x hx hxB
      rcases hmemU X hX with rfl | rfl
      · simp [polyA] at hx
        exact absurd hx (by simpa using hxB)
      · rw [ncard_polyB]
    · have hsub : exU.filter (fun X => (0 : ZMod 5) ∈ X) = exU := by
        ext X
        simp only [exU, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl) <;> simp [polyA, polyB]
      rw [hsub]
      unfold exU
      rw [Finset.sum_pair polyA_ne_polyB, ncard_polyA, ncard_polyB]
      norm_num

end Example

end Balaban.LargeField.RegionalTails
