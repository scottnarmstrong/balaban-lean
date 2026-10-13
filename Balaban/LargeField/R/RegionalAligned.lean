/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalGroupedBound
public import Balaban.Fluctuation.SizeModG1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The grouped regional bound on the aligned lattice

## The two mismatches of `RegionalGroupedBound` and their repair

**(A) Collar versus alignment.**  The landed correction `corrSum` in `EresAt` runs over
`y ∈ alignedIn j Y` and `x ∈ Bc = alignedIn j (thickY R Y)`: aligned sites only.  The tail lemma
`farCrossing_polyUniv_le_of_halo_of_collar` needs every fine site of `Y^≈` in `Bc`.  The two
differ by the non-aligned fine sites over the halo.

*Decision (T1).*  The kernel of the landed dictionary is `a(x - y) = vc.v1 j (unlift j (x - y))`
(`RegionShrink.lean`, `EresAt` and `corrFn`, `hv1` of `RegionalGroupedBound`).  `unlift j z`
(`SmallField/Def6Terms.lean:171`) is the centred position of the `j`-block of `z`
(`jBlock = blockMap (L^j)`), hence **constant on each `j`-block**: a non-aligned `z` and the
corner of its block have the same `unlift`.  Therefore the landed kernel does *not* vanish off
aligned differences (it would force `vc.v1 j ≡ 0` on every block index): the premise "(A1): `a z = 0`
for non-aligned `z`" cannot be proved for `fun z => vc.v1 j (unlift j z)`, and it is false for
every `vc` with a nonzero `v1 j` (T6(a) below).  The correction in `EresAt` sums over aligned `x`
only, but `AtermRegion a s R` and `AtermCentre a s y` of `RegionalFlux.lean` sum over *all* fine
sites `x` of the torus.  So with `hv1` for all `x, y` the landed A-term is a sum over all fine sites
of a block-constant kernel.  The source A-term (P1 (3.104)) is a sum over the sites of the scale-`j`
lattice, i.e. over aligned `x`.  The repair is the alternative (A1'): the kernel that enters the
A-term is the **aligned kernel** `alignedKernel a' a z = if Aligned a' z then a z else 0` (zero off
aligned differences by definition), the remainder `I_j(y) = Efull - AtermCentre (alignedKernel ..)`,
and `hv1` is asked only for the pairs the correction uses (`y ∈ R'`, `x ∈ Bc`, both aligned).  No
alternative lattice (A2) is needed: `CTorus` stays the index type and the aligned sublattice enters
through the support of the kernel.

*Statements.*  `farCrossing_aligned`: if `a` vanishes off `P`-differences (`P` a predicate closed
as below, here alignment), `R ⊆ P` and `Bc, Bc'` agree on `P`, then `farCrossing a s R Bc =
farCrossing a s R Bc'`.  `farCrossing_polyUniv_le_power_aligned`: the landed power-form tail lemma
for the collar `Bc` with `∀ x, Aligned x → x ∈ sset(Y^≈) → x ∈ Bc` (true for `Bc = alignedIn j
(thickY R Y)`, `bc_collar_alignedIn`); no collar premise.

**(B) Per site versus row sum.**  `card_aligned_le_of_isDj`: a polymer `X ∈ 𝒟_j` contains at most
`q^d c_G (1 + d_j(X))` aligned sites, `q = L^(m₀+m₁)` the number of aligned sites per side of a
`π_j`-cell (cells have side `L^(j+m₀+m₁)`, aligned sites have spacing `L^j`), `c_G = (3 (2L-1))^d`
(`c1`, from `G1_cellCount`).  `rowSum_le_of_site`: a per-site bound `‖c X y x‖ ≤ A e^{-κ d_j(X)}` on
aligned `x ∈ X` gives the row sum `≤ A q^d c_G (1 + 1/η) e^{-(κ-η) d_j(X)}` for every `η > 0`,
using `(1 + t) e^{-η t} ≤ 1 + 1/η`.  The rate drops from `κ` to `κ - η`, the constant is multiplied
by `Γ_η = q^d c_G (1 + 1/η)`.

## Main declarations

* `GroupedBase`, `GroupedInputsAligned` (row-sum coefficients), `GroupedInputsSite` (per-site
  coefficients, rate `κ`, margin `η`), both inhabited (`groupedInputsAligned_nonempty`,
  `groupedInputsSite_nonempty`).
* `grouped_bound_power_aligned`, `omitted_tail_power_aligned`: the two halves of
  `‖Σ A_j - Corr_j‖` and the omitted tail, for the aligned kernel.
* `EresJ2_sub_remainder_le_aligned_of_radialCoeff`: the deliverable of T3.
* `EresJ2_sub_remainder_le_aligned_of_site`: the same with per-site coefficient bounds (T4).

## Findings (T6)

(a) **The landed identity is an identity, the landed bound is not available.**
`EresAt_eq_remainder_add_grouped_of_radialCoeff` is a tautology for any `a` (the remainder `I_j` is
defined by subtraction), correct as stated.  But the hypothesis `hv1 : ∀ x y, vc.v1 j (unlift j (x - y))
= a (x - y)` makes `a` constant on `j`-blocks, so `a` is nonzero at non-aligned differences, and
the term `AtermRegion a s R' - corrSum ..` then contains
`½ Σ_{y∈R'} Σ_{x non-aligned over the halo} a(x - y)(s x - s y)`, which the correction (aligned
`x` only) does not contain.  Minimal example: `R' = {y}`, `y` aligned, `x` a non-aligned fine site
in the block of `y`, `ψ` with `s x ≠ s y`, `v₂ = 0`.  The extra term is `½ a(x - y)(s x - s y)` with
`a(x - y) = a(0)` (same block), of order `(E₀ K_r/ε_j) σ² ε_q`, not of order `s^(d+α₃)` unless
`a(0) = 0`.  So `EresJ2_sub_remainder_le_of_radialCoeff` is either vacuous (its `collar` is
false for `Bc = alignedIn j (thickY R Y)`) or its conclusion fails; it is replaced here by the
aligned form.  The aligned form has an honest open input: the I6 decomposition has to be proved
for the aligned kernel, i.e. `I_j(y) = Efull - AtermCentre (alignedKernel ..)` is the remainder of
the source decomposition (the landed `RenormTorus` A-term, `Aterm_torus_sum`, sums over the
sites of `ℤ^d` seen through `unlift`, i.e. the block lattice; the identification with an aligned
sum on the fine torus is part of `regionalRadialCoefficient`).

(b) **Rate budget.**  The row-sum rate is `κ - η`, so `ρ = κ - κ₀ - η > 0` is needed, with
`κ₀ ≥ aEnt + 1`: `η` can be any number in `(0, κ - κ₀)`.  The constant `C_T` in `tailConst`
contains `ρ^{-p}` and `e^{2Lρ}`, and `Γ_η` contains `1/η`: choose `η = (κ - κ₀)/2`; then
the margin is `(κ - κ₀)/2` and all constants are explicit.  The input rate must satisfy
`κ ≥ aEnt + 1 + 2ρ`.

(c) **Other premises that the landed objects cannot satisfy.**  `v2_decomp` and `v2_coeff` of
`GroupedInputs` are asked for all `x` (including non-aligned `x`), but `v₂ = vc.v2 ∘ unlift` is
block-constant, so the per-polymer decomposition at non-aligned `x` is an extra (and unnatural)
premise; the aligned structure asks it for aligned `x` only (and sums only over aligned `x`).
`src_data` and `s_data` are pointwise data bounds and are fine.

## Still open for the grouped bound after this file

The identification of `T.dist X` with `sizeJ` and of `Site d` with `CTorus` in the per-site
coefficient bounds; `regionalRadialCoefficient` (`hv1` on aligned pairs and the aligned I6
decomposition above); `E_bound` (H4); `s_data`, `src_data`, `scale_rel` (small-field data and I6
spin bounds); the cube assignment `|R'| ≤ Γ_E s^{-d}`; `regionalEnergyIdentity`,
`regionalCommonTube`, `regionalTailAssignment`.
-/

@[expose] public section

open Finset Real Balaban.LargeField.RegionEnergyAlgebra Balaban.LargeField.RegionalFlux

namespace Balaban.LargeField.RegionalAligned

open Balaban Balaban.Localization

/-! ### Alignment is closed under differences -/

section TorusAligned

variable {d n : ℕ}

theorem aligned_iff_castHom {a : ℕ} [NeZero a] (ha : a ∣ n) [NeZero n] (x : Torus d n) :
    Aligned a x ↔ ∀ μ, ZMod.castHom ha (ZMod a) (x μ) = 0 := by
  refine forall_congr' fun μ => ?_
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

/-- If `y` and `x - y` are aligned, so is `x` (`a ∣ n`). -/
theorem aligned_of_sub {a : ℕ} [NeZero a] (ha : a ∣ n) [NeZero n] {x y : Torus d n}
    (hy : Aligned a y) (hxy : Aligned a (x - y)) : Aligned a x := by
  rw [aligned_iff_castHom ha] at hy hxy ⊢
  intro μ
  have h1 := hxy μ
  have h2 := hy μ
  have : x μ = (x - y) μ + y μ := by simp
  rw [this, map_add, h1, h2, add_zero]

/-- The difference of two aligned sites is aligned (`a ∣ n`). -/
theorem aligned_sub {a : ℕ} [NeZero a] (ha : a ∣ n) [NeZero n] {x y : Torus d n}
    (hx : Aligned a x) (hy : Aligned a y) : Aligned a (x - y) := by
  rw [aligned_iff_castHom ha] at hx hy ⊢
  intro μ
  simp [map_sub, hx μ, hy μ]

end TorusAligned

/-! ### (A) The far crossing sum only sees the aligned part of the collar -/

section Abstract

variable {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

/-- **`farCrossing_aligned`.**  Let `P` be a predicate on sites such that `P y` and `P (x - y)`
imply `P x` (alignment, for `a ∣ n`), let the kernel vanish off `P`-differences, the centres
satisfy `P`, and let `Bc`, `Bc'` agree on the sites satisfying `P`.  Then the far crossing sums
for `Bc` and `Bc'` coincide: the sites off `P` contribute nothing. -/
theorem farCrossing_aligned (P : ι → Prop) (hP : ∀ x y, P y → P (x - y) → P x) (a s : ι → ℂ)
    (R Bc Bc' : Finset ι) (hsupp : ∀ z, ¬ P z → a z = 0) (hR : ∀ y ∈ R, P y)
    (hB : ∀ x, P x → (x ∈ Bc ↔ x ∈ Bc')) :
    farCrossing a s R Bc = farCrossing a s R Bc' := by
  classical
  unfold farCrossing
  refine Finset.sum_congr rfl fun y hy => ?_
  have e : ∀ B : Finset ι, ∑ x ∈ Bᶜ, pairHalf a s y x =
      ∑ x, if x ∉ B then pairHalf a s y x else 0 := fun B => by
    rw [← Finset.sum_filter]
    congr 1
    ext x; simp
  rw [e, e]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : P x
  · simp [hB x hx]
  · have : pairHalf a s y x = 0 := by
      unfold pairHalf
      have hz : ¬ P (x - y) := fun h => hx (hP x y (hR y hy) h)
      rw [hsupp _ hz]; ring
    simp [this]

end Abstract

section Concrete

open Balaban.Fluctuation Balaban.SmallField Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.LargeField.RegionShrink Balaban.LargeField.RegionalTails
  Balaban.LargeField.RegionalSourceTerm Balaban.LargeField.RegionalArith
  Balaban.LargeField.RegionalGroupedBound Balaban.SmallField.Def6

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- `L^j` divides the side of the Def-6 torus for `j ≤ k`. -/
theorem pow_dvd_side {j : ℕ} (hj : j ≤ k) : S.L ^ j ∣ (C.N₁ * S.L ^ m₁) * S.L ^ k :=
  Dvd.dvd.mul_left (pow_dvd_pow _ hj) _

omit [NeZero S.L] in
theorem neZero_pow_L {j : ℕ} [NeZero S.L] : NeZero (S.L ^ j) :=
  ⟨pow_ne_zero _ (NeZero.ne _)⟩

open Classical in
/-- The aligned kernel: `a` on `L^j`-aligned arguments, `0` elsewhere. -/
noncomputable def alignedKernel (j : ℕ) (a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ) :
    Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ :=
  fun z => if Aligned (S.L ^ j) z then a z else 0

theorem alignedKernel_of_aligned {j : ℕ} (a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    {z : Localization.CTorus S.d S.L C.N₁ m₁ k} (hz : Aligned (S.L ^ j) z) :
    alignedKernel C j a z = a z := by
  classical
  simp [alignedKernel, hz]

theorem alignedKernel_of_not {j : ℕ} (a : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    {z : Localization.CTorus S.d S.L C.N₁ m₁ k} (hz : ¬ Aligned (S.L ^ j) z) :
    alignedKernel C j a z = 0 := by
  classical
  simp [alignedKernel, hz]

variable {C}

/-- Membership in the aligned collar of the landed correction: an aligned site of the fine set of
`Y^≈` lies in `alignedIn j (thickY R Y)`. -/
theorem bc_collar_alignedIn {j : ℕ} (Y : Set (Torus S.d (n k)))
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : Aligned (S.L ^ j) x)
    (hs : x ∈ C.sset (thickY R Y)) : x ∈ C.alignedIn j (thickY R Y) := by
  classical
  simp [SFCtx.alignedIn, hx, hs]

theorem aligned_of_mem_alignedIn {j : ℕ} {A : Set (Torus S.d (n k))}
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : x ∈ C.alignedIn j A) :
    Aligned (S.L ^ j) x := by
  classical
  simp only [SFCtx.alignedIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1

open Classical in
/-- **The tail lemma for the landed collar, no `collar` premise.**  For a kernel vanishing off
aligned differences and `Bc ⊇ (aligned sites of the fine set of Y^≈)` (e.g. `alignedIn j (thickY R Y)`),
the far crossing bound of `farCrossing_polyUniv_le_power` holds. -/
theorem farCrossing_polyUniv_le_power_aligned {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (c : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (a s : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ) (Y : Set (Torus S.d (n k)))
    (R' Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)) (hR' : R' ⊆ C.alignedIn j Y)
    (hBc : ∀ x, Aligned (S.L ^ j) x → x ∈ C.sset (thickY R Y) → x ∈ Bc)
    (hsupp : ∀ z, ¬ Aligned (S.L ^ j) z → a z = 0)
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
  have : NeZero (S.L ^ j) := neZero_pow_L
  set Bc' : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k) :=
    Bc ∪ Finset.univ.filter (fun x => ¬ Aligned (S.L ^ j) x) with hBc'
  have hdvd := pow_dvd_side C hj
  have hcol : ∀ x, x ∈ C.sset (thickY R Y) → x ∈ Bc' := by
    intro x hx
    by_cases hal : Aligned (S.L ^ j) x
    · exact Finset.mem_union_left _ (hBc x hal hx)
    · exact Finset.mem_union_right _ (by simp [hal])
  have hyal : ∀ y ∈ R', Aligned (S.L ^ j) y := fun y hy => aligned_of_mem_alignedIn (hR' hy)
  have hfa : farCrossing a s R' Bc' = farCrossing a s R' Bc := by
    refine farCrossing_aligned (fun z => Aligned (S.L ^ j) z)
      (fun x y hy hxy => aligned_of_sub hdvd hy hxy) a s R' Bc' Bc hsupp hyal ?_
    intro x hx
    simp [hBc', hx]
  rw [← hfa]
  exact farCrossing_polyUniv_le_power C hN hj c a s Y R' Bc' hR' hcol hA₀ hκ₀ hκ hRs hRq hM hp hs ha hc

end Concrete

end Balaban.LargeField.RegionalAligned
