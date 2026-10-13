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

/-! ### (B) Counting aligned sites of a polymer; per-site to row-sum -/

section Count

open Balaban.Fluctuation

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

open Classical in
/-- An aligned Localization.box `Localization.box b' (q a)` contains at most `q^d` points aligned to the grid of side `a`
(the proof of `card_aligned_in_cube` with a general cell ratio `q`). -/
theorem card_aligned_in_box {n a q : ℕ} [NeZero n] (ha : a ∣ n) (ha0 : 0 < a)
    {b' : Torus d n} (hb' : Aligned a b') :
    (Finset.univ.filter fun b : Torus d n => Aligned a b ∧ b ∈ Localization.box b' (q * a)).card ≤ q ^ d := by
  have hsub : (Finset.univ.filter fun b : Torus d n => Aligned a b ∧ b ∈ Localization.box b' (q * a)) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.range q).image
        (fun t : Fin d → ℕ => b' + natT (fun μ => a * t μ)) := by
    intro b hb
    obtain ⟨hal, w, hw, rfl⟩ := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_image]
    refine ⟨fun μ => w μ / a, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro μ
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul ha0]
      have := hw μ; linarith [mul_comm q a]
    · have hmod : ∀ μ, w μ % a = 0 := fun μ => by
        have := hal μ
        rwa [mod_of_aligned_add ha hb' μ] at this
      congr 2
      funext μ
      have := Nat.div_add_mod (w μ) a
      rw [hmod μ] at this
      omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range q).card := Finset.card_image_le
    _ = q ^ d := by simp

open Classical in
/-- **Aligned sites of a union of cells.**  A union of `π_j`-cells `X` contains at most
`q^d` aligned sites (spacing `L^j`) per cell, `q = L^(m₀+m₁)` (cells have side `L^(j+m₀+m₁)`). -/
theorem card_aligned_le_cellCount (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X : Set (Localization.CTorus d L N₁ m₁ K)} (hX : IsPiPrimeUnion m₀ j X) :
    ((Finset.univ.filter fun x : Localization.CTorus d L N₁ m₁ K => x ∈ X ∧ Aligned (L ^ j) x).card : ℝ) ≤
      (((L ^ (m₀ + m₁) : ℕ) : ℝ)) ^ d * cellCount (cellSide L m₀ m₁ j) X := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have hpos : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdj : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hj) _
  have haeq : a = L ^ (m₀ + m₁) * L ^ j := by
    rw [ha]; unfold cellSide; rw [← pow_add]; congr 1; omega
  have hja : L ^ j ∣ a := by rw [ha]; unfold cellSide; exact pow_dvd_pow L (by omega)
  set F := Finset.univ.filter (fun x : Localization.CTorus d L N₁ m₁ K => x ∈ X ∧ Aligned (L ^ j) x) with hF
  have hmap : ∀ x ∈ F, cbase a x ∈ Finset.univ.filter
      (fun b : Localization.CTorus d L N₁ m₁ K => Aligned a b ∧ Localization.box b a ⊆ X) := by
    intro x hx
    have hx' : x ∈ X := (Finset.mem_filter.1 hx).2.1
    obtain ⟨b, hb1, hb2, hb3⟩ := hX x hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨aligned_cbase x, (cell_subset_cube hdvd ha0 hb1 hb2).trans hb3⟩
  have hfib : ∀ t ∈ Finset.univ.filter (fun b : Localization.CTorus d L N₁ m₁ K => Aligned a b ∧ Localization.box b a ⊆ X),
      (F.filter fun x => cbase a x = t).card ≤ (L ^ (m₀ + m₁)) ^ d := by
    intro t ht
    have hta : Aligned a t := (Finset.mem_filter.1 ht).2.1
    have htj : Aligned (L ^ j) t := fun μ => by
      have := hta μ
      rw [← Nat.mod_mod_of_dvd _ hja, this]; simp
    have hsub : (F.filter fun x => cbase a x = t) ⊆
        Finset.univ.filter fun b : Localization.CTorus d L N₁ m₁ K =>
          Aligned (L ^ j) b ∧ b ∈ Localization.box t (L ^ (m₀ + m₁) * L ^ j) := by
      intro x hx
      obtain ⟨hxF, hxt⟩ := Finset.mem_filter.1 hx
      have hxA := (Finset.mem_filter.1 hxF).2.2
      have hbox : x ∈ Localization.box t a := hxt ▸ mem_box_cbase ha0 x
      rw [haeq] at hbox
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hxA, hbox⟩
    exact (Finset.card_le_card hsub).trans (card_aligned_in_box hdj hpos htj)
  have key := Finset.card_le_mul_card_image_of_maps_to hmap ((L ^ (m₀ + m₁)) ^ d) hfib
  have key' : F.card ≤ (L ^ (m₀ + m₁)) ^ d * cellCount a X := by
    unfold cellCount
    simpa using key
  exact_mod_cast key'

/-- **(B), site count.**  For `X ∈ 𝒟_j`: `#(aligned sites of X) ≤ q^d c_G (1 + d_j(X))`,
`q = L^(m₀+m₁)`, `c_G = (3 (2L-1))^d`. -/
theorem card_aligned_le_of_isDj (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ j X) :
    ((open Classical in Finset.univ.filter fun x : Localization.CTorus d L N₁ m₁ K => x ∈ X ∧ Aligned (L ^ j) x).card : ℝ) ≤
      (((L ^ (m₀ + m₁) : ℕ) : ℝ)) ^ d * c1 d L * (1 + treeLenCovOne m₀ j X) := by
  have h1 := card_aligned_le_cellCount hN hj hX.2.1
  have h2 := G1_cellCount hN hj (Ω := Set.univ) (X := X)
    ⟨hX, fun z hz => absurd (Set.mem_univ z) hz⟩
  rw [Set.inter_univ, dcovMod_of_subset (Set.subset_univ X)] at h2
  have hc : 0 ≤ c1 d L := by unfold c1; positivity
  calc _ ≤ _ := h1
    _ ≤ (((L ^ (m₀ + m₁) : ℕ) : ℝ)) ^ d * (c1 d L * (1 + treeLenCovOne m₀ j X)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end Count

/-- `(1 + t) e^{-η t} ≤ 1 + 1/η` for `t ≥ 0`, `η > 0`, in the form used for the row sums. -/
theorem exp_mul_one_add_le {κ η t : ℝ} (hη : 0 < η) (ht : 0 ≤ t) :
    exp (-κ * t) * (1 + t) ≤ (1 + 1 / η) * exp (-(κ - η) * t) := by
  have e1 : exp (-κ * t) = exp (-(κ - η) * t) * exp (-(η * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hu : 0 < exp (-(η * t)) := Real.exp_pos _
  have hu1 : exp (-(η * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hv : η * t ≤ exp (η * t) := by linarith [Real.add_one_le_exp (η * t)]
  have huv : exp (-(η * t)) * exp (η * t) = 1 := by rw [← Real.exp_add]; simp
  have h2 : η * (t * exp (-(η * t))) ≤ 1 := by
    calc η * (t * exp (-(η * t))) = (η * t) * exp (-(η * t)) := by ring
      _ ≤ exp (η * t) * exp (-(η * t)) := mul_le_mul_of_nonneg_right hv hu.le
      _ = 1 := by rw [mul_comm]; exact huv
  have h3 : t * exp (-(η * t)) ≤ 1 / η := by
    rw [le_div_iff₀ hη]; linarith
  have h4 : (1 + t) * exp (-(η * t)) ≤ 1 + 1 / η := by
    nlinarith
  rw [e1]
  have hw : 0 < exp (-(κ - η) * t) := Real.exp_pos _
  calc exp (-(κ - η) * t) * exp (-(η * t)) * (1 + t)
      = exp (-(κ - η) * t) * ((1 + t) * exp (-(η * t))) := by ring
    _ ≤ exp (-(κ - η) * t) * (1 + 1 / η) := mul_le_mul_of_nonneg_left h4 hw.le
    _ = _ := by ring

open Classical in
/-- **(B), `rowSum_le_of_site`.**  A per-site bound `‖c x‖ ≤ A e^{-κ d}` on the sites of `X`
satisfying `Pd`, and a site count `#{x ∈ X, Pd x} ≤ Γ₀ (1 + d)` (`d = d_j(X) ≥ 0`), give the row
sum `Σ_{x ∈ X, Pd x} ‖c x‖ ≤ A Γ₀ (1 + 1/η) e^{-(κ - η) d}` for every `η > 0`: the rate drops
from `κ` to `κ - η` and the constant is multiplied by `Γ₀ (1 + 1/η)`. -/
theorem rowSum_le_of_site {ι : Type*} [Fintype ι] (X : Set ι) (Pd : ι → Prop) (c : ι → ℂ)
    {A κ sz η Γ₀ : ℝ} (hA : 0 ≤ A) (hsz : 0 ≤ sz) (hη : 0 < η)
    (hsite : ∀ x ∈ X, Pd x → ‖c x‖ ≤ A * exp (-κ * sz))
    (hcount : ((Finset.univ.filter fun x => x ∈ X ∧ Pd x).card : ℝ) ≤ Γ₀ * (1 + sz)) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ X ∧ Pd x), ‖c x‖ ≤
      (A * Γ₀ * (1 + 1 / η)) * exp (-(κ - η) * sz) := by
  have h1 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ X ∧ Pd x), ‖c x‖ ≤
      (Finset.univ.filter fun x => x ∈ X ∧ Pd x).card * (A * exp (-κ * sz)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun x hx => hsite x (Finset.mem_filter.1 hx).2.1
      (Finset.mem_filter.1 hx).2.2
  have hAe : 0 ≤ A * exp (-κ * sz) := mul_nonneg hA (Real.exp_pos _).le
  have h2 := mul_le_mul_of_nonneg_right hcount hAe
  have h3 := exp_mul_one_add_le (κ := κ) hη hsz
  have hAΓ : 0 ≤ A := hA
  calc _ ≤ _ := h1
    _ ≤ Γ₀ * (1 + sz) * (A * exp (-κ * sz)) := h2
    _ = A * Γ₀ * (exp (-κ * sz) * (1 + sz)) := by ring
    _ ≤ A * Γ₀ * ((1 + 1 / η) * exp (-(κ - η) * sz)) := by
        refine mul_le_mul_of_nonneg_left h3 ?_
        have : 0 ≤ Γ₀ := by
          by_contra hneg
          push Not at hneg
          have : Γ₀ * (1 + sz) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
          linarith [hcount, (Nat.cast_nonneg (Finset.univ.filter fun x => x ∈ X ∧ Pd x).card : (0 : ℝ) ≤ _)]
        exact mul_nonneg hA this
    _ = _ := by ring

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


/-! ### Truncation of coefficients to aligned sites -/

open Classical in
/-- Truncating a coefficient to sites satisfying `Pd` does not change the row sum over the sites
of `X` satisfying `Pd`. -/
theorem sum_filter_trunc {ι : Type*} [Fintype ι] (X : Set ι) (Pd : ι → Prop) (f : ι → ℂ) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖if Pd x then f x else 0‖ =
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ X ∧ Pd x), ‖f x‖ := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : x ∈ X <;> by_cases h2 : Pd x <;> simp [h1, h2]

/-! ### The hypotheses of the aligned grouped bound -/

section Structs

variable (C)

open Classical in
/-- **The shared hypotheses** of the aligned grouped regional bound at the inherited level `j`:
numeric relations, typing data and the two data bounds, as in `GroupedInputs` (same fields and
names), without the geometric fields (`aligned`, `collar`), which are theorem hypotheses of the
aligned bound and hold for the landed objects.
* numeric: `E₀_nonneg`, `κ₀_ge` (entropy margin `κ₀ ≥ aEnt + 1`), `κ₀_lt` (rate `ρ = κ - κ₀ > 0`),
  `Rs_pos`, `Rs_le`, `M_pos`, `p_pos`, `dd_eq`, `α₁_nonneg`, `hrel` (`3 + 2α = d + α₃ + α₁`),
  `α_ge`, `C₀_nonneg`, `K_r_pos`, `B_nonneg`, `εj_pos`, `εq_nonneg`,
  `scale_rel` (`ε_q/ε_j ≤ K_R s^α`, the I6 spin bound).
* data bounds: `s_data` (`‖ψ·ψ - 1‖ ≤ σ² ε`), `src_data` (pointwise source bound on `x ∈ Bc`). -/
structure GroupedBase (j : ℕ) (R' Bc : Finset (SiteT C)) (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (h : Fin N → ℂ) (νj : ℝ)
    (E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ) : Prop where
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
  s_data : ∀ x, ‖dot (ψ x) (ψ x) - 1‖ ≤ (C₀ * scaleJ S.L k j) ^ 2 * εq
  src_data : ∀ y ∈ R', ∀ x ∈ Bc,
    ‖(νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y)))‖ ≤
      sourceConstC B * (distWeight C j y x ^ 2 + distWeight C j y x) *
        (C₀ * scaleJ S.L k j) ^ 3 * εq ^ 2

open Classical in
/-- **The hypotheses of the aligned grouped bound, row-sum coefficients.**  `GroupedBase` plus the
class inputs: the kernel `a` vanishes off aligned differences (`a_supp`, true by construction for
`alignedKernel`), is on aligned `x` the sum of per-polymer coefficients `c` over `polyUniv`
(`a_decomp`), with row sum over the *aligned* sites of the polymer at most
`(E₀ K_r / ε_j) e^{-κ d_j(X)}` (`a_coeff`); the same for `v₂` with `4 E₀ K_r² / ε_j²`
(`v2_decomp`, `v2_coeff`); polymer decay of the activity (`E_bound`, H4). -/
structure GroupedInputsAligned (j : ℕ) (Y : Set (Torus S.d (n k))) (R' Bc : Finset (SiteT C))
    (ψ : Fld S.d S.L C.N₁ m₁ k N) (h : Fin N → ℂ) (νj : ℝ) (a : SiteT C → ℂ)
    (v₂ : SiteT C → SiteT C → ℂ) (c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ)
    (E : SiteT C → Set (SiteT C) → ℂ)
    (E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ) : Prop
    extends GroupedBase C j R' Bc ψ h νj E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq where
  a_supp : ∀ z, ¬ Aligned (S.L ^ j) z → a z = 0
  a_decomp : ∀ y ∈ R', ∀ x, Aligned (S.L ^ j) x → a (x - y) =
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), c X y x
  a_coeff : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ X ∧ Aligned (S.L ^ j) x), ‖c X y x‖ ≤
      (E₀ / (εj / K_r)) * exp (-κ * Def6.sizeJ C.m₀ j X)
  v2_decomp : ∀ y ∈ R', ∀ x, Aligned (S.L ^ j) x → v₂ y x =
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), cv X y x
  v2_coeff : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ X ∧ Aligned (S.L ^ j) x), ‖cv X y x‖ ≤
      (4 * E₀ / (εj / K_r) ^ 2) * exp (-κ * Def6.sizeJ C.m₀ j X)
  E_bound : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ‖E y X‖ ≤ E₀ * exp (-κ * Def6.sizeJ C.m₀ j X)

end Structs

theorem GroupedBase.tailConst_nonneg {j : ℕ} {R' Bc : Finset (SiteT C)}
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {h : Fin N → ℂ} {νj : ℝ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedBase C j R' Bc ψ h νj E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    0 ≤ RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃ := by
  have hK0 := K0_nonneg S.d S.L κ₀
  unfold RegionalGroupedBound.tailConst
  have hρ : 0 < κ - κ₀ := sub_pos.2 g.κ₀_lt
  have hM : (0 : ℝ) < M := by exact_mod_cast g.M_pos
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hRs := g.Rs_pos
  have hp := g.p_pos
  have hc : (0 : ℝ) < (M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁) := by positivity
  have hden : 0 < exp 1 * ((κ - κ₀) * ((M : ℝ) / (S.L : ℝ) ^ (C.m₀ + m₁)) * Rs) := by positivity
  exact mul_nonneg (mul_nonneg hK0 (Real.exp_pos _).le)
    (Real.rpow_nonneg (div_nonneg hp.le hden.le) _)

open Classical in
/-- **The grouped regional correction in power form, aligned lattice.**
`‖Σ_{y∈R'} A_j(y) - Corr_j(R', Bc)‖ ≤ |R'| (C₁ + C₂) E₀ s^(d+α₃)` for the kernel `a` (vanishing
off aligned differences) and `v₁(y, x) = a(x - y)`.  Geometry: `R'` aligned centres in
`alignedIn j Y`, `Bc` aligned sites containing the aligned sites of the fine set of `Y^≈`. -/
theorem grouped_bound_power_aligned {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    {Y : Set (Torus S.d (n k))} {R' Bc : Finset (SiteT C)}
    (hR' : R' ⊆ C.alignedIn j Y) (hBal : ∀ x ∈ Bc, Aligned (S.L ^ j) x)
    (hBcol : ∀ x, Aligned (S.L ^ j) x → x ∈ C.sset (thickY R Y) → x ∈ Bc)
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {h : Fin N → ℂ} {νj : ℝ} {a : SiteT C → ℂ}
    {v₂ : SiteT C → SiteT C → ℂ} {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E : SiteT C → Set (SiteT C) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputsAligned C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B
      εj εq) :
    ‖AtermRegion a (fun x => dot (ψ x) (ψ x)) R' -
        corrSum (fun y x => a (x - y)) v₂ νj R' Bc ψ h‖ ≤
      R'.card * ((farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R + v2Const (S := S) κ κ₀ B C₀ K_r K_R) *
        E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
  have : NeZero (S.L ^ j) := neZero_pow_L
  have hdvd := pow_dvd_side C hj
  have hyal : ∀ y ∈ R', Aligned (S.L ^ j) y := fun y hy => aligned_of_mem_alignedIn (hR' hy)
  have hs0 := scaleJ_pos S.L k j
  have hs1 := scaleJ_le_one S.L k j
  have hK0 := K0_nonneg S.d S.L κ₀
  have hCT : 0 ≤ RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃ := g.toGroupedBase.tailConst_nonneg
  have hA₀ : 0 ≤ E₀ / (εj / K_r) := by
    have := g.E₀_nonneg; have := g.εj_pos; have := g.K_r_pos; positivity
  -- far crossing
  set c'' : Set (SiteT C) → SiteT C → SiteT C → ℂ :=
    fun X y x => if Aligned (S.L ^ j) x then c X y x else 0 with hc''
  have hfar := farCrossing_polyUniv_le_power_aligned hN hj c'' a
    (fun x => dot (ψ x) (ψ x) - 1) Y R' Bc hR' hBcol g.a_supp
    (A₀ := E₀ / (εj / K_r)) (κ := κ) (κ₀ := κ₀)
    (Bs := (C₀ * scaleJ S.L k j) ^ 2 * εq) (Rs := Rs) (d := dd) (α₃ := α₃) hA₀ g.κ₀_ge g.κ₀_lt
    g.Rs_pos g.Rs_le g.M_pos g.p_pos g.s_data
    (fun y hy x => by
      by_cases hx : Aligned (S.L ^ j) x
      · rw [g.a_decomp y hy x hx]
        exact Finset.sum_congr rfl fun X _ => by simp [hc'', hx]
      · have hz : ¬ Aligned (S.L ^ j) (x - y) := fun h' => hx (aligned_of_sub hdvd (hyal y hy) h')
        rw [g.a_supp _ hz]
        exact (Finset.sum_eq_zero fun X _ => by simp [hc'', hx]).symm)
    (fun y hy X hX hyX => by
      have := g.a_coeff y hy X hX hyX
      rw [← sum_filter_trunc X (fun x => Aligned (S.L ^ j) x) (c X y)] at this
      exact this)
  rw [farCrossing_sub_const] at hfar
  have hfar2 : ‖farCrossing a (fun x => dot (ψ x) (ψ x)) R' Bc‖ ≤
      R'.card * (farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
    refine hfar.trans ?_
    rw [mul_comm _ (R'.card : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have := far_scalar (C₀ := C₀) (K_r := K_r) (K_R := K_R) (CT := RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃)
      (E₀ := E₀) (εj := εj) (εq := εq) (s := scaleJ S.L k j) (α := α) (p := dd + α₃) hCT
      g.E₀_nonneg g.K_r_pos g.εj_pos g.εq_nonneg hs0 hs1 g.α_ge g.scale_rel
    unfold farConst
    exact this
  -- near source term
  obtain ⟨hsz, hD⟩ := polyUniv_weights C hN hj
  set v₂'' : SiteT C → SiteT C → ℂ := fun y x => if Aligned (S.L ^ j) x then v₂ y x else 0
    with hv₂''
  set cv'' : Set (SiteT C) → SiteT C → SiteT C → ℂ :=
    fun X y x => if Aligned (S.L ^ j) x then cv X y x else 0 with hcv''
  have hv2e : v2Part v₂'' νj R' Bc ψ h = v2Part v₂ νj R' Bc ψ h := by
    unfold v2Part
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
    simp [hv₂'', hBal x hx]
  have hv2 := v2Part_le_power (polyUniv C j) cv'' v₂'' νj R' Bc ψ h (Def6.sizeJ C.m₀ j)
    (distWeight C j) (E₀ := E₀) (K₀ := K0 S.d S.L κ₀) (κ := κ) (κ₀ := κ₀) (c₀ := 2 * S.L)
    (Cs := sourceConstC B) (C₀ := C₀) (K_r := K_r) (K_R := K_R) (s := scaleJ S.L k j) (α := α)
    (εj := εj) (εq := εq) (r := εj / K_r) (dd := dd) (α₁ := α₁) (α₃ := α₃) g.E₀_nonneg hK0
    (by positivity) g.κ₀_lt (by unfold sourceConstC; have := g.B_nonneg; positivity) g.C₀_nonneg
    g.K_r_pos hs0 hs1 g.εj_pos g.εq_nonneg rfl g.scale_rel g.hrel g.α₁_nonneg
    (fun y hy x => by
      by_cases hx : Aligned (S.L ^ j) x
      · simp only [hv₂'', hx, ite_true]
        rw [g.v2_decomp y hy x hx]
        exact Finset.sum_congr rfl fun X _ => by simp [hcv'', hx]
      · simp only [hv₂'', hx, ite_false]
        exact (Finset.sum_eq_zero fun X _ => by simp [hcv'', hx]).symm)
    (fun y hy X hX hyX => by
      have := g.v2_coeff y hy X ((mem_polyUniv C).1 hX) hyX
      rw [← sum_filter_trunc X (fun x => Aligned (S.L ^ j) x) (cv X y)] at this
      exact this)
    (fun y _ X hX _ => hsz X hX)
    (fun y _ x => distWeight_nonneg C j y x)
    (fun y _ X hX hyX x hxX => hD X hX y hyX x hxX)
    (fun y _ => entropy_polyUniv C hN hj y g.κ₀_ge) g.src_data
  rw [hv2e] at hv2
  have hv2' : ‖v2Part v₂ νj R' Bc ψ h‖ ≤
      R'.card * (v2Const (S := S) κ κ₀ B C₀ K_r K_R * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
    unfold v2Const; exact hv2
  have := grouped_le_of_far a v₂ νj R' Bc ψ h hfar2 hv2'
  refine this.trans (le_of_eq ?_)
  ring

open Classical in
/-- **The omitted tail in power form** (the aligned structure; only the centres and the polymer
decay are used). -/
theorem omitted_tail_power_aligned {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    {Y : Set (Torus S.d (n k))} {R' Bc : Finset (SiteT C)} (hR' : R' ⊆ C.alignedIn j Y)
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {h : Fin N → ℂ} {νj : ℝ} {a : SiteT C → ℂ}
    {v₂ : SiteT C → SiteT C → ℂ} {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E : SiteT C → Set (SiteT C) → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputsAligned C j Y R' Bc ψ h νj a v₂ c cv E E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B
      εj εq) :
    ‖∑ y ∈ R', tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖ ≤
      R'.card * (RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃ * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y ∈ R', ‖tailAt (polyUniv C j) E (C.sset (thickY R Y)) y‖
      ≤ ∑ _y ∈ R', RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃ * E₀ * scaleJ S.L k j ^ (dd + α₃) :=
        Finset.sum_le_sum fun y hy =>
          tailAt_polyUniv_le_power C hN hj E Y (hR' hy) g.E₀_nonneg g.κ₀_ge g.κ₀_lt g.Rs_pos
            g.Rs_le g.M_pos g.p_pos (g.E_bound y hy)
    _ = _ := by simp

/-! ### (B) Per-site coefficients: the structure and the conversion to row sums -/

/-- The factor `Γ_η = q^d c_G (1 + 1/η)` of the row-sum bound: `q = L^(m₀+m₁)` aligned sites per
side of a `π_j`-cell, `c_G = (3 (2L-1))^d`, and `1 + 1/η` from `(1 + t) e^{-η t}`. -/
noncomputable def rowFactor (S : Setting) (m₀ m₁ : ℕ) (η : ℝ) : ℝ :=
  (((S.L : ℝ) ^ (m₀ + m₁)) ^ S.d) * c1 S.d S.L * (1 + 1 / η)

theorem one_le_c1 (d L : ℕ) [NeZero L] : 1 ≤ c1 d L := by
  unfold c1
  have : (1 : ℝ) ≤ ((3 * (2 * L - 1) : ℕ) : ℝ) := by
    have : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact_mod_cast (by omega : 1 ≤ 3 * (2 * L - 1))
  exact one_le_pow₀ this

theorem one_le_rowFactor (S : Setting) [NeZero S.L] (m₀ m₁ : ℕ) {η : ℝ} (hη : 0 < η) :
    1 ≤ rowFactor S m₀ m₁ η := by
  unfold rowFactor
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  have h1 : (1 : ℝ) ≤ ((S.L : ℝ) ^ (m₀ + m₁)) ^ S.d := one_le_pow₀ (one_le_pow₀ hL)
  have h2 := one_le_c1 S.d S.L
  have h3 : (1 : ℝ) ≤ 1 + 1 / η := by have : 0 ≤ 1 / η := by positivity
                                      linarith
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ _ := mul_le_mul (mul_le_mul h1 h2 zero_le_one (by linarith)) h3 zero_le_one (by positivity)

section Structs2

variable (C)

open Classical in
/-- **The hypotheses of the aligned grouped bound, per-site coefficients** (the form of
`PinJetTerm.tensA_le`, `tensB_le`).  As `GroupedInputsAligned`, but the coefficient bounds are per
site (resp. per pair) on the aligned sites `x` of the polymer: `‖c X y x‖ ≤ (E₀ K_r/ε_j)
e^{-κ d_j(X)}`, `‖cv X y x‖ ≤ (4 E₀ K_r²/ε_j²) e^{-κ d_j(X)}`, with the activity bound at the same
rate.  The shared hypotheses `GroupedBase` are at the reduced rate `κ - η` (`η > 0`, `κ₀ < κ - η`):
the number of aligned sites of a polymer is at most `q^d c_G (1 + d_j(X))`, absorbed by lowering the
rate by `η` (`rowSum_le_of_site`). -/
structure GroupedInputsSite (j : ℕ) (R' Bc : Finset (SiteT C))
    (ψ : Fld S.d S.L C.N₁ m₁ k N) (h : Fin N → ℂ) (νj : ℝ) (a : SiteT C → ℂ)
    (v₂ : SiteT C → SiteT C → ℂ) (c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ)
    (E : SiteT C → Set (SiteT C) → ℂ)
    (E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ) : Prop
    extends GroupedBase C j R' Bc ψ h νj E₀ (κ - η) κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq where
  η_pos : 0 < η
  a_supp : ∀ z, ¬ Aligned (S.L ^ j) z → a z = 0
  a_decomp : ∀ y ∈ R', ∀ x, Aligned (S.L ^ j) x → a (x - y) =
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), c X y x
  a_site : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X → ∀ x ∈ X, Aligned (S.L ^ j) x →
    ‖c X y x‖ ≤ (E₀ / (εj / K_r)) * exp (-κ * Def6.sizeJ C.m₀ j X)
  v2_decomp : ∀ y ∈ R', ∀ x, Aligned (S.L ^ j) x → v₂ y x =
    ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), cv X y x
  v2_site : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X → ∀ x ∈ X, Aligned (S.L ^ j) x →
    ‖cv X y x‖ ≤ (4 * E₀ / (εj / K_r) ^ 2) * exp (-κ * Def6.sizeJ C.m₀ j X)
  E_bound : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
    ‖E y X‖ ≤ E₀ * exp (-κ * Def6.sizeJ C.m₀ j X)

end Structs2

open Classical in
/-- **From per-site to row-sum coefficients** (`rowSum_le_of_site` and `card_aligned_le_of_isDj`):
`GroupedInputsSite` at rate `κ` with margin `η` gives `GroupedInputsAligned` at the rate `κ - η`
and the constant `Γ_η E₀`.  Typing data `L^m₀ ∣ N₁`, `j ≤ k`. -/
theorem GroupedInputsSite.toAligned {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    {Y : Set (Torus S.d (n k))} {R' Bc : Finset (SiteT C)}
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {h : Fin N → ℂ} {νj : ℝ} {a : SiteT C → ℂ}
    {v₂ : SiteT C → SiteT C → ℂ} {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E : SiteT C → Set (SiteT C) → ℂ}
    {E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputsSite C j R' Bc ψ h νj a v₂ c cv E E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B
      εj εq) :
    GroupedInputsAligned C j Y R' Bc ψ h νj a v₂ c cv E (rowFactor S C.m₀ m₁ η * E₀) (κ - η) κ₀
      Rs dd α₃ α₁ α C₀ K_r K_R B εj εq := by
  have hη := g.η_pos
  have hΓ1 := one_le_rowFactor S C.m₀ m₁ hη
  have hE0 := g.E₀_nonneg
  have hr : 0 ≤ εj / K_r := (div_pos g.εj_pos g.K_r_pos).le
  have hcnt : ∀ X, Def6.IsPolyDom C.m₀ j X →
      ((Finset.univ.filter fun x : SiteT C => x ∈ X ∧ Aligned (S.L ^ j) x).card : ℝ) ≤
        ((((S.L : ℝ) ^ (C.m₀ + m₁)) ^ S.d) * c1 S.d S.L) * (1 + Def6.sizeJ C.m₀ j X) := by
    intro X hX
    have := card_aligned_le_of_isDj (m₁ := m₁) (K := k) hN hj (Def6.isDj_of_isPolyDom hX)
    have e : (((S.L ^ (C.m₀ + m₁) : ℕ) : ℝ)) = (S.L : ℝ) ^ (C.m₀ + m₁) := by push_cast; rfl
    rw [e] at this
    exact this.trans (le_of_eq (by unfold Def6.sizeJ; ring))
  have hsz : ∀ X, Def6.IsPolyDom C.m₀ j X → 0 ≤ Def6.sizeJ C.m₀ j X :=
    fun X hX => (polyUniv_weights C hN hj).1 X ((mem_polyUniv C).2 hX)
  refine
  { toGroupedBase := { g.toGroupedBase with E₀_nonneg := by positivity }
    a_supp := g.a_supp
    a_decomp := g.a_decomp
    a_coeff := ?_
    v2_decomp := g.v2_decomp
    v2_coeff := ?_
    E_bound := ?_ }
  · intro y hy X hX hyX
    have := rowSum_le_of_site X (fun x => Aligned (S.L ^ j) x) (c X y) (A := E₀ / (εj / K_r))
      (κ := κ) (sz := Def6.sizeJ C.m₀ j X) (η := η)
      (Γ₀ := (((S.L : ℝ) ^ (C.m₀ + m₁)) ^ S.d) * c1 S.d S.L) (by positivity) (hsz X hX) hη
      (fun x hx hal => g.a_site y hy X hX hyX x hx hal) (hcnt X hX)
    refine this.trans (le_of_eq ?_)
    unfold rowFactor; ring
  · intro y hy X hX hyX
    have := rowSum_le_of_site X (fun x => Aligned (S.L ^ j) x) (cv X y)
      (A := 4 * E₀ / (εj / K_r) ^ 2)
      (κ := κ) (sz := Def6.sizeJ C.m₀ j X) (η := η)
      (Γ₀ := (((S.L : ℝ) ^ (C.m₀ + m₁)) ^ S.d) * c1 S.d S.L) (by positivity) (hsz X hX) hη
      (fun x hx hal => g.v2_site y hy X hX hyX x hx hal) (hcnt X hX)
    refine this.trans (le_of_eq ?_)
    unfold rowFactor; ring
  · intro y hy X hX hyX
    refine (g.E_bound y hy X hX hyX).trans ?_
    have h1 : exp (-κ * Def6.sizeJ C.m₀ j X) ≤ exp (-(κ - η) * Def6.sizeJ C.m₀ j X) :=
      Real.exp_le_exp.2 (by nlinarith [hsz X hX])
    calc E₀ * exp (-κ * Def6.sizeJ C.m₀ j X) ≤ E₀ * exp (-(κ - η) * Def6.sizeJ C.m₀ j X) :=
          mul_le_mul_of_nonneg_left h1 hE0
      _ ≤ rowFactor S C.m₀ m₁ η * E₀ * exp (-(κ - η) * Def6.sizeJ C.m₀ j X) := by
          have := (Real.exp_pos (-(κ - η) * Def6.sizeJ C.m₀ j X)).le
          nlinarith [mul_nonneg hE0 this]

/-! ### (T3) The landed regional energy on the aligned lattice -/

section Energy

variable (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N))

open Classical in
/-- **The decomposition of the landed regional energy, aligned form.**  The correction
coefficient is the marginal kernel `a` on the pairs the correction uses (`y ∈ R'`, `x ∈ Bc`):
`EresAt = Σ_{y∈R'} I_j(y) + (Σ_{y∈R'} A_j(y) - Corr_j) - (omitted tail)`, with
`I_j(y) = Efull - AtermCentre a ..` for the given kernel `a`. -/
theorem EresAt_eq_remainder_add_grouped_aligned (j : ℕ) (R' Bc : Finset (SiteT C))
    (Bp : Set (SiteT C)) (ψ : Fld S.d S.L C.N₁ m₁ k N) (a : SiteT C → ℂ)
    (hv1 : ∀ y ∈ R', ∀ x ∈ Bc, vc.v1 j (unlift j (x - y)) = a (x - y)) :
    EresAt C vc hv j R' Bc Bp ψ =
      ∑ y ∈ R', (Efull (polyUniv C j) (polyTerm C hv j ψ) y -
          AtermCentre a (fun x => dot (ψ x) (ψ x)) y) +
        (AtermRegion a (fun x => dot (ψ x) (ψ x)) R' -
          corrSum (fun y x => a (x - y)) (fun y x => vc.v2 j (unlift j (x - y)))
            (nuIdeal S.L k (C.sf.ν k) j) R' Bc ψ (hC hv)) -
        ∑ y ∈ R', tailAt (polyUniv C j) (polyTerm C hv j ψ) Bp y := by
  rw [EresAt_eq_energyAt, energyAt_decomposition (a := a) (s := fun x => dot (ψ x) (ψ x))]
  have h2 : RegionShrink.pairSum (corrFn C vc hv j ψ) R' Bc =
      corrSum (fun y x => a (x - y)) (fun y x => vc.v2 j (unlift j (x - y)))
        (nuIdeal S.L k (C.sf.ν k) j) R' Bc ψ (hC hv) := by
    unfold RegionShrink.pairSum corrSum corrFn
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    rw [hv1 y hy x hx]
  rw [h2]

open Classical in
/-- **The bound for `EresAt`, aligned form.**  Under `GroupedInputsAligned` (for `ν_j = nuIdeal`,
`v₂ = vc.v2 ∘ unlift`, the activity `polyTerm`) and `hv1` on the pairs used by the correction:
`‖EresAt - Σ_{y∈R'} I_j(y)‖ ≤ |R'| (C₁ + C₂ + C_T) E₀ s^(d+α₃)`, `Bp = sset(Y^≈)`. -/
theorem EresAt_sub_remainder_le_aligned_of_radialCoeff {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁)
    (hj : j ≤ k) {Y : Set (Torus S.d (n k))} {R' Bc : Finset (SiteT C)}
    (hR' : R' ⊆ C.alignedIn j Y) (hBal : ∀ x ∈ Bc, Aligned (S.L ^ j) x)
    (hBcol : ∀ x, Aligned (S.L ^ j) x → x ∈ C.sset (thickY R Y) → x ∈ Bc)
    {ψ : Fld S.d S.L C.N₁ m₁ k N} {a : SiteT C → ℂ}
    {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv1 : ∀ y ∈ R', ∀ x ∈ Bc, vc.v1 j (unlift j (x - y)) = a (x - y))
    (g : GroupedInputsAligned C j Y R' Bc ψ (hC hv) (nuIdeal S.L k (C.sf.ν k) j) a
      (fun y x => vc.v2 j (unlift j (x - y))) c cv (polyTerm C hv j ψ)
      E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresAt C vc hv j R' Bc (C.sset (thickY R Y)) ψ -
        ∑ y ∈ R', (Efull (polyUniv C j) (polyTerm C hv j ψ) y -
          AtermCentre a (fun x => dot (ψ x) (ψ x)) y)‖ ≤
      R'.card * ((RegionalGroupedBound.farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R +
        RegionalGroupedBound.v2Const (S := S) κ κ₀ B C₀ K_r K_R +
        RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃) * E₀ * scaleJ S.L k j ^ (dd + α₃)) := by
  rw [EresAt_eq_remainder_add_grouped_aligned vc hv j R' Bc _ ψ a hv1]
  have e : ∀ I G T : ℂ, I + G - T - I = G - T := fun I G T => by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := grouped_bound_power_aligned hN hj hR' hBal hBcol g
  have h2 := omitted_tail_power_aligned hN hj hR' g
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  ring

open Classical in
/-- **(T3) The deliverable.  `EresJ2` at the regions of `Y`, aligned form**: `R' = alignedIn j Y`,
`Bc = alignedIn j (thickY R Y)`, the composed field `psiJ`.  Every geometric premise holds for the
landed objects (the collar premise of `EresJ2_sub_remainder_le_of_radialCoeff` is replaced by the
support of the kernel on aligned differences, a field of `GroupedInputsAligned`); `hv1` is asked
for the pairs of the correction only.  The remainder is `I_j(y) = Efull - AtermCentre a ..` with
the aligned kernel `a`. -/
theorem EresJ2_sub_remainder_le_aligned_of_radialCoeff {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁)
    (hj : j ≤ k) (Y : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    {a : SiteT C → ℂ} {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv1 : ∀ y ∈ C.alignedIn j Y, ∀ x ∈ C.alignedIn j (thickY R Y),
      vc.v1 j (unlift j (x - y)) = a (x - y))
    (g : GroupedInputsAligned C j Y (C.alignedIn j Y) (C.alignedIn j (thickY R Y))
      (C.psiJ Y ψk hv j) (hC hv) (nuIdeal S.L k (C.sf.ν k) j) a
      (fun y x => vc.v2 j (unlift j (x - y))) c cv (polyTerm C hv j (C.psiJ Y ψk hv j))
      E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresJ2 C vc Y ψk hv j -
        ∑ y ∈ C.alignedIn j Y, (Efull (polyUniv C j) (polyTerm C hv j (C.psiJ Y ψk hv j)) y -
          AtermCentre a (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) y)‖ ≤
      (C.alignedIn j Y).card * ((RegionalGroupedBound.farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R +
        RegionalGroupedBound.v2Const (S := S) κ κ₀ B C₀ K_r K_R +
        RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃) * E₀ *
          scaleJ S.L k j ^ (dd + α₃)) := by
  rw [EresJ2_eq_EresAt]
  exact EresAt_sub_remainder_le_aligned_of_radialCoeff vc hv hN hj subset_rfl
    (fun x hx => aligned_of_mem_alignedIn hx)
    (fun x hal hs => bc_collar_alignedIn Y hal hs) hv1 g

open Classical in
/-- **(T4) The same with per-site coefficient bounds** (`GroupedInputsSite`, the form of
`PinJetTerm.tensA_le`, `tensB_le`): the rate is `κ - η` and the constant is `Γ_η E₀`,
`Γ_η = rowFactor S m₀ m₁ η = q^d c_G (1 + 1/η)`, `q = L^(m₀+m₁)`. -/
theorem EresJ2_sub_remainder_le_aligned_of_site {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁)
    (hj : j ≤ k) (Y : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    {a : SiteT C → ℂ} {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv1 : ∀ y ∈ C.alignedIn j Y, ∀ x ∈ C.alignedIn j (thickY R Y),
      vc.v1 j (unlift j (x - y)) = a (x - y))
    (g : GroupedInputsSite C j (C.alignedIn j Y) (C.alignedIn j (thickY R Y))
      (C.psiJ Y ψk hv j) (hC hv) (nuIdeal S.L k (C.sf.ν k) j) a
      (fun y x => vc.v2 j (unlift j (x - y))) c cv (polyTerm C hv j (C.psiJ Y ψk hv j))
      E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresJ2 C vc Y ψk hv j -
        ∑ y ∈ C.alignedIn j Y, (Efull (polyUniv C j) (polyTerm C hv j (C.psiJ Y ψk hv j)) y -
          AtermCentre a (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) y)‖ ≤
      (C.alignedIn j Y).card * ((RegionalGroupedBound.farConst C (κ - η) κ₀ Rs dd α₃ C₀ K_r K_R +
        RegionalGroupedBound.v2Const (S := S) (κ - η) κ₀ B C₀ K_r K_R +
        RegionalGroupedBound.tailConst C (κ - η) κ₀ Rs dd α₃) *
          (rowFactor S C.m₀ m₁ η * E₀) * scaleJ S.L k j ^ (dd + α₃)) :=
  EresJ2_sub_remainder_le_aligned_of_radialCoeff vc hv hN hj Y ψk hv1 (g.toAligned hN hj)

end Energy

/-! ### Non-vacuity (rule 10) -/

section Inhabited

open Classical in
/-- The shared hypotheses are inhabited for any context with `R_{k-1} > 0`, `M > 0`, any field
`ψ`, source `h`, centres and collar, with `ν_j = 0`: `E₀ = ε_j = ε_q = K_r = 1`, `α₁ = B = 0`,
`α₃ = 1`, `d = S.d`, `κ₀ = aEnt + 1`, any rate `κ > κ₀`, `R_* = R_{k-1}`, `α = (d - 2)/2`,
`C₀` large enough to cover the data `ψ·ψ - 1`. -/
theorem groupedBase_nonempty (j : ℕ) (hRpos : 0 < R (k - 1)) (hM : 0 < M) {κ : ℝ}
    (hκ : aEnt S.d S.L + 1 < κ) (R' Bc : Finset (SiteT C))
    (ψ : Fld S.d S.L C.N₁ m₁ k N) (h : Fin N → ℂ) :
    ∃ E₀ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ,
      Nonempty (GroupedBase C j R' Bc ψ h 0 E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) := by
  have hs := scaleJ_pos S.L k j
  set s := scaleJ S.L k j with hsdef
  set T : ℝ := ∑ x, ‖dot (ψ x) (ψ x) - 1‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => norm_nonneg _
  have hsα : 0 < s ^ ((S.d - 2 : ℝ) / 2) := Real.rpow_pos_of_pos hs _
  have hC0 : 0 ≤ (T + 1) / s := by positivity
  have hCs : 0 ≤ sourceConstC 0 := by unfold sourceConstC; norm_num
  refine ⟨1, aEnt S.d S.L + 1, R (k - 1), (S.d : ℝ), 1, 0, ((S.d : ℝ) - 2) / 2,
    (T + 1) / s, 1, (s ^ (((S.d : ℝ) - 2) / 2))⁻¹, 0, 1, 1, ⟨?_⟩⟩
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  exact
  { E₀_nonneg := zero_le_one
    κ₀_ge := le_rfl
    κ₀_lt := hκ
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

open Classical in
/-- **`GroupedInputsAligned` is inhabited** (zero kernel, zero coefficients and activity). -/
theorem groupedInputsAligned_nonempty (j : ℕ) (hRpos : 0 < R (k - 1)) (hM : 0 < M)
    (Y : Set (Torus S.d (n k))) (Bc : Finset (SiteT C)) (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (h : Fin N → ℂ) :
    ∃ E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ,
      Nonempty (GroupedInputsAligned C j Y (C.alignedIn j Y) Bc ψ h 0 (fun _ => 0)
        (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
        E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) := by
  obtain ⟨E₀, κ₀, Rs, dd, α₃, α₁, α, C₀, K_r, K_R, B, εj, εq, ⟨b⟩⟩ :=
    groupedBase_nonempty (C := C) j hRpos hM (κ := aEnt S.d S.L + 2) (by linarith)
      (C.alignedIn j Y) Bc ψ h
  refine ⟨E₀, aEnt S.d S.L + 2, κ₀, Rs, dd, α₃, α₁, α, C₀, K_r, K_R, B, εj, εq, ⟨?_⟩⟩
  exact
  { toGroupedBase := b
    a_supp := fun z _ => rfl
    a_decomp := fun y _ x _ => by simp
    a_coeff := fun y _ X _ _ => by
      simp only [norm_zero, Finset.sum_const_zero]; have := b.E₀_nonneg; have := b.εj_pos
      have := b.K_r_pos; positivity
    v2_decomp := fun y _ x _ => by simp
    v2_coeff := fun y _ X _ _ => by
      simp only [norm_zero, Finset.sum_const_zero]; have := b.E₀_nonneg; have := b.εj_pos
      have := b.K_r_pos; positivity
    E_bound := fun y _ X _ _ => by
      simp only [norm_zero]; have := b.E₀_nonneg; positivity }

open Classical in
/-- **`GroupedInputsSite` is inhabited** (zero kernel, margin `η = 1`). -/
theorem groupedInputsSite_nonempty (j : ℕ) (hRpos : 0 < R (k - 1)) (hM : 0 < M)
    (Bc : Finset (SiteT C)) (Y : Set (Torus S.d (n k))) (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (h : Fin N → ℂ) :
    ∃ E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ,
      Nonempty (GroupedInputsSite C j (C.alignedIn j Y) Bc ψ h 0 (fun _ => 0)
        (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
        E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) := by
  obtain ⟨E₀, κ₀, Rs, dd, α₃, α₁, α, C₀, K_r, K_R, B, εj, εq, ⟨b⟩⟩ :=
    groupedBase_nonempty (C := C) j hRpos hM (κ := aEnt S.d S.L + 3 - 1) (by linarith)
      (C.alignedIn j Y) Bc ψ h
  refine ⟨E₀, aEnt S.d S.L + 3, 1, κ₀, Rs, dd, α₃, α₁, α, C₀, K_r, K_R, B, εj, εq, ⟨?_⟩⟩
  exact
  { toGroupedBase := b
    η_pos := one_pos
    a_supp := fun z _ => rfl
    a_decomp := fun y _ x _ => by simp
    a_site := fun y _ X _ _ x _ _ => by
      simp only [norm_zero]; have := b.E₀_nonneg; have := b.εj_pos
      have := b.K_r_pos; positivity
    v2_decomp := fun y _ x _ => by simp
    v2_site := fun y _ X _ _ x _ _ => by
      simp only [norm_zero]; have := b.E₀_nonneg; have := b.εj_pos
      have := b.K_r_pos; positivity
    E_bound := fun y _ X _ _ => by
      simp only [norm_zero]; have := b.E₀_nonneg; positivity }

end Inhabited

end Concrete

end Balaban.LargeField.RegionalAligned
