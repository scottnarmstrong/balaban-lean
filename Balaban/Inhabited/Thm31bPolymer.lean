/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsUnconditional
public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.RootActiveSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable coefficients regrouped onto localization domains

`thm31b_zeroClass_fromTower` expands the observable as `√b · ∑_T E T` over finite sets `T` of
block cubes, with `E T = 0` unless the root cube lies in `T` and `‖E T‖ ≤ c e^{-λ dExt T}`.  Here
the coefficients are regrouped on the collar hulls of the sets `T` (`detCollarGrouped`).

## Support (the verdict on the polymer condition)

`IsPolyDom m₀ K (sitesOf T)` holds iff `T` is nonempty and `dOmega m₀ K univ (sitesOf T) ≠ ⊤`
(`isPolyDom_iff_dOmega_ne_top`); it is not automatic (it needs nearest-neighbour connectedness).
The landed coefficients carry only the bound in `dExt T`, which equals the constant `Mbig` when
`dOmega = ⊤`; they are not known to vanish there.  So the regrouping is applied to the part of
the coefficients on polymers, and the part on the other sets `T` is a separate remainder `R`,
with `‖R‖ ≤ c e^{-λ}` (it is not localized, and it is exponentially small in the square of the
number of sites of the torus).

* `rooted_regroup_of_supp`: the regrouping when the coefficients vanish off polymers (no
  remainder).
* `rooted_regroup`: the regrouping with the remainder, for coefficients with the root clause and
  the `dExt` bound only.
* `thm31b_zeroClass_polymer_fromTower`: the observable at the shared tower.

## What is not proved

Clause (b) of `notes/phase1/FLUCTUATION.md` Theorem 3.1 is not obtained: there is no termwise
locality in the datum and the source (it needs the coefficient family of the observable family
program), no analyticity in the source `g` (the coefficients are chosen after `g`), no reality or
symmetry clause, the prefactor is `obsPrefactor` and not the paper's power of `β`, and the
unlocalized remainder `R` is extra.  The output rate `hullRate 3 3 (3/2 κ_dec)` is positive only
under a numerical condition on `κ_dec` (`hullRate_three_pos_iff`); it is not claimed.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Metric

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- **Rooted regrouping when the coefficients vanish off polymers.**  For `e` with the root clause
at the cube `bx`, vanishing unless `sitesOf T` is a polymer, and `‖e T‖ ≤ c e^{-λ dExt T}`, the
grouped family `X ↦ detCollarGrouped e X` has the same total sum, is nonzero only on domains of
`𝒟_K` containing the box of `bx`, and is bounded by `C_hull e^{-λ_hull sizeJ X}`. -/
theorem rooted_regroup_of_supp (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) {c lam : ℝ} (hc : 0 ≤ c)
    (hlam : 0 ≤ lam) (bx : 𝔅) (e : Finset 𝔅 → ℂ) (hroot : ∀ T, bx ∉ T → e T = 0)
    (hsupp : ∀ T, e T ≠ 0 → IsPolyDom m₀ K (sitesOf T))
    (hb : ∀ T, ‖e T‖ ≤ c * Real.exp (-lam * dExt T)) :
    ∑ X ∈ (Finset.univ : Finset (Finset 𝔅)).image detCollarHull, detCollarGrouped e X =
        ∑ T, e T ∧
      (∀ X : Set (CTorus d L N₁ m₁ K), detCollarGrouped e X ≠ 0 →
        IsDj m₀ K X ∧ box bx.1 (cellSide L m₀ m₁ K) ⊆ X) ∧
      ∀ X : Set (CTorus d L N₁ m₁ K), ‖detCollarGrouped e X‖ ≤
        hullConst d L lam c * Real.exp (-hullRate d L lam * sizeJ m₀ K X) := by
  refine ⟨sum_detCollarGrouped e, fun X hX => ?_, detCollarGrouped_bound hL hN hc hlam e hsupp hb⟩
  obtain ⟨T, hT, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX
  have hTX := mem_detCollarFibre.1 hT
  have hbx : bx ∈ T := by
    by_contra h
    exact hne (hroot T h)
  subst hTX
  exact ⟨(detCollarHull_isDj hL hN (hsupp T hne)).1, box_subset_detCollarHull hbx⟩

theorem card_finset_cubeB_le :
    Fintype.card (Finset 𝔅) ≤ 2 ^ Fintype.card (CTorus d L N₁ m₁ K) := by
  rw [Fintype.card_finset]
  exact Nat.pow_le_pow_right (by norm_num)
    (Fintype.card_le_of_injective (Subtype.val : 𝔅 → CTorus d L N₁ m₁ K) Subtype.val_injective)

open Classical in
/-- **Rooted regrouping with the remainder.**  For `e` with the root clause at `bx` and
`‖e T‖ ≤ c e^{-λ dExt T}` only, `log 2 ≤ λ`: with `e⁺ T = e T` if `sitesOf T` is a polymer and `0`
otherwise, the grouped family `X ↦ detCollarGrouped e⁺ X` and a number `R` satisfy
`∑_X grouped + R = ∑_T e T`, `‖R‖ ≤ c e^{-λ}`, the anchor and the hull bound. -/
theorem rooted_regroup (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) {c lam : ℝ} (hc : 0 ≤ c)
    (hlam : Real.log 2 ≤ lam) (bx : 𝔅) (e : Finset 𝔅 → ℂ) (hroot : ∀ T, bx ∉ T → e T = 0)
    (hb : ∀ T, ‖e T‖ ≤ c * Real.exp (-lam * dExt T)) :
    ∃ R : ℂ,
      ∑ X ∈ (Finset.univ : Finset (Finset 𝔅)).image detCollarHull,
        detCollarGrouped (fun T => if IsPolyDom m₀ K (sitesOf T) then e T else 0) X + R =
          ∑ T, e T ∧
      ‖R‖ ≤ c * Real.exp (-lam) ∧
      (∀ X : Set (CTorus d L N₁ m₁ K),
        detCollarGrouped (fun T => if IsPolyDom m₀ K (sitesOf T) then e T else 0) X ≠ 0 →
        IsDj m₀ K X ∧ box bx.1 (cellSide L m₀ m₁ K) ⊆ X) ∧
      ∀ X : Set (CTorus d L N₁ m₁ K),
        ‖detCollarGrouped (fun T => if IsPolyDom m₀ K (sitesOf T) then e T else 0) X‖ ≤
          hullConst d L lam c * Real.exp (-hullRate d L lam * sizeJ m₀ K X) := by
  have hlam0 : 0 ≤ lam := le_trans (Real.log_nonneg (by norm_num)) hlam
  have hmain := rooted_regroup_of_supp hL hN hc hlam0 bx
    (fun T => if IsPolyDom m₀ K (sitesOf T) then e T else 0)
    (fun T hT => by simp [hroot T hT])
    (fun T hT => by
      by_contra h
      exact hT (by simp [h]))
    (fun T => by
      by_cases h : IsPolyDom m₀ K (sitesOf T)
      · simp only [h, ↓reduceIte]; exact hb T
      · simp only [h, ↓reduceIte, norm_zero]
        have := Real.exp_nonneg (-lam * dExt T)
        positivity)
  obtain ⟨h1, h2, h3⟩ := hmain
  refine ⟨∑ T, (if IsPolyDom m₀ K (sitesOf T) then 0 else e T), ?_, ?_, h2, h3⟩
  · rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : IsPolyDom m₀ K (sitesOf T) <;> simp [h]
  · -- the non-polymer terms with the root clause have `dExt = Mbig`
    set n := Fintype.card (CTorus d L N₁ m₁ K) with hn
    have hterm : ∀ T : Finset 𝔅,
        ‖(if IsPolyDom m₀ K (sitesOf T) then 0 else e T)‖ ≤
          c * Real.exp (-lam * Mbig d L N₁ m₁ K) := by
      intro T
      by_cases h : IsPolyDom m₀ K (sitesOf T)
      · simp only [h, ↓reduceIte, norm_zero]; positivity
      · simp only [h, ↓reduceIte]
        by_cases h0 : e T = 0
        · rw [h0, norm_zero]; positivity
        · have hbx : bx ∈ T := by
            by_contra hh
            exact h0 (hroot T hh)
          have hdo : dOmega m₀ K Set.univ (sitesOf T) = ⊤ := by
            by_contra hh
            exact h (isPolyDom_iff_dOmega_ne_top.2 ⟨⟨bx, hbx⟩, hh⟩)
          rw [← dExt_eq_Mbig hdo]
          exact hb T
    calc ‖∑ T, (if IsPolyDom m₀ K (sitesOf T) then 0 else e T)‖
        ≤ ∑ T : Finset 𝔅, ‖(if IsPolyDom m₀ K (sitesOf T) then 0 else e T)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _T : Finset 𝔅, c * Real.exp (-lam * Mbig d L N₁ m₁ K) :=
          Finset.sum_le_sum fun T _ => hterm T
      _ = (Fintype.card (Finset 𝔅) : ℝ) * (c * Real.exp (-lam * Mbig d L N₁ m₁ K)) := by
          simp
      _ ≤ ((2 : ℝ) ^ n) * (c * Real.exp (-lam * Mbig d L N₁ m₁ K)) := by
          have : (Fintype.card (Finset 𝔅) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast card_finset_cubeB_le
          have h0 : 0 ≤ c * Real.exp (-lam * Mbig d L N₁ m₁ K) := by positivity
          exact mul_le_mul_of_nonneg_right this h0
      _ ≤ c * Real.exp (-lam) := by
          have h2n : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
          have hn1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
            have : n ≤ n ^ 2 := by nlinarith [Nat.zero_le n]
            exact_mod_cast this
          have hM : Mbig d L N₁ m₁ K = (n : ℝ) ^ 2 + 1 := rfl
          have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hexp : Real.exp (n * Real.log 2) * Real.exp (-lam * Mbig d L N₁ m₁ K) ≤
              Real.exp (-lam) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            rw [hM]
            nlinarith [mul_le_mul_of_nonneg_left hlam hnn, mul_le_mul_of_nonneg_left hn1
              (le_trans (Real.log_nonneg (by norm_num)) hlam)]
          rw [h2n]
          calc Real.exp (n * Real.log 2) * (c * Real.exp (-lam * Mbig d L N₁ m₁ K))
              = c * (Real.exp (n * Real.log 2) * Real.exp (-lam * Mbig d L N₁ m₁ K)) := by ring
            _ ≤ c * Real.exp (-lam) := mul_le_mul_of_nonneg_left hexp hc

end Generic

/-- **When the hull rate is positive.**  `hullRate 3 3 lam = lam / 60751 - 3375 log 2`, which is
positive iff `60751 · 3375 · log 2 < lam`. -/
theorem hullRate_three_pos_iff (lam : ℝ) :
    0 < hullRate 3 3 lam ↔ 60751 * (3375 * Real.log 2) < lam := by
  unfold hullRate
  rw [collarB_three, c1_three]
  constructor
  · intro h
    have : 3375 * Real.log 2 < lam / (1 + 60750) := by linarith
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  · intro h
    have : 3375 * Real.log 2 < lam / (1 + 60750) := by
      rw [lt_div_iff₀ (by norm_num)]; linarith
    linarith

open Classical in
/-- **Theorem 3.1 (b) for the zero-class step on localization domains, at the shared tower.**
Under the hypotheses of `thm31b_zeroClass_fromTower` (and nothing else) the observable is
`√b (∑_X E' X + R)`, the sum over the image of the collar hull map, where `E' X` is the sum of the
coefficients `E T` over the sets `T` with polymer sites and hull `X`; `E' X ≠ 0` only for `X` in
`𝒟_{k+1}` containing the box of the root cube of `y`; `‖E' X‖ ≤ C_hull e^{-λ_hull sizeJ X}` with
`λ = (3/2) κ_dec`, constant `c = C · obsPrefactor`, and `R` collects the sets `T` that are not
polymers, `‖R‖ ≤ c e^{-(3/2) κ_dec}` (not localized).  The rate is `hullRate 3 3 ((3/2) κ_dec)`,
positive iff `60751 · 3375 · log 2 < (3/2) κ_dec` (`hullRate_three_pos_iff`); the loss against the
input rate is the factor `1 / 60751` and the shift `3375 log 2`.

Still lacking against clause (b): termwise locality in the datum and the source (needs the
coefficient family of the observable family program), analyticity in `g`, reality and symmetry,
the paper's prefactor, and a localized treatment of the remainder `R` (it is one scalar with the
bound above, with no domain index, locality or analyticity).  The fixed `thm31b_zeroClass_polymer_fromTower` is its corollary. -/
theorem thm31b_zeroClass_polymer_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C : ℝ, 2 ≤ β₀ ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
  StepScaleDataG T k hk N₁ ν β p₁ →
  ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    g ∈ l1Ball d L N₁ T.m₁ (k + 1) N →
  ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
    ∃ (E' : Set (CTorus d L N₁ T.m₁ (k + 1)) → ℂ) (R : ℂ),
      (T.step k hk N₁ ν β p₁).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
        (((T.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁)
            (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ))).image detCollarHull, E' X + R) ∧
      ‖R‖ ≤ C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) * Real.exp (-(3 / 2 * T.κdec)) ∧
      (∀ X, E' X ≠ 0 → IsDj T.m₀ (k + 1) X ∧
        box (rootCube (m₀ := T.m₀) (K := k + 1) (blockIndex y)).1 (cellSide L T.m₀ T.m₁ (k + 1)) ⊆ X) ∧
      ∀ X, ‖E' X‖ ≤ hullConst d L (3 / 2 * T.κdec) (C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2)))) *
        Real.exp (-hullRate d L (3 / 2 * T.κdec) * sizeJ T.m₀ (k + 1) X) := by
  obtain ⟨β₀, C, hβ₀, -, hC, hmain⟩ := thm31b_zeroClass_fromTowerG_rho T hA p hCR hs0 hs 1 one_pos
  refine ⟨β₀, C, hβ₀, hC, ?_⟩
  intro k hk N₁ _ hLN h5 ν hν hνk β hβ p₁ hp hp₁ hsc g hg y i
  obtain ⟨E, h1, h2, h3'⟩ := hmain k hk N₁ hLN h5 ν hν hνk β hβ p₁ hp hp₁ hsc g hg y i
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  have hβ1 : (1 : ℝ) ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    have : (1 : ℝ) ≤ β := by linarith
    nlinarith
  have hc : 0 ≤ C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) :=
    mul_nonneg hC (obsPrefactor_nonneg p s hβ1)
  have hκ : 3 ≤ T.κdec := by have := T.κdec_lower; have := T.κ0_nonneg; linarith
  have hlam : Real.log 2 ≤ 3 / 2 * T.κdec := by
    have := Real.log_two_lt_d9; linarith
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := rooted_regroup (m₀ := T.m₀) (K := k + 1) T.hL hLN hc hlam
    (rootCube (m₀ := T.m₀) (K := k + 1) (blockIndex y)) E h2 h3'
  refine ⟨_, R, ?_, hR2, hR3, hR4⟩
  rw [h1, ← hR1]

open Classical in
/-- **Theorem 3.1 (b) for the zero-class step on localization domains, at the shared tower.**
Under the hypotheses of `thm31b_zeroClass_fromTower` (and nothing else) the observable is
`√b (∑_X E' X + R)`, the sum over the image of the collar hull map, where `E' X` is the sum of the
coefficients `E T` over the sets `T` with polymer sites and hull `X`; `E' X ≠ 0` only for `X` in
`𝒟_{k+1}` containing the box of the root cube of `y`; `‖E' X‖ ≤ C_hull e^{-λ_hull sizeJ X}` with
`λ = (3/2) κ_dec`, constant `c = C · obsPrefactor`, and `R` collects the sets `T` that are not
polymers, `‖R‖ ≤ c e^{-(3/2) κ_dec}` (not localized).  The rate is `hullRate 3 3 ((3/2) κ_dec)`,
positive iff `60751 · 3375 · log 2 < (3/2) κ_dec` (`hullRate_three_pos_iff`); the loss against the
input rate is the factor `1 / 60751` and the shift `3375 log 2`.

Still lacking against clause (b): termwise locality in the datum and the source (needs the
coefficient family of the observable family program), analyticity in `g`, reality and symmetry,
the paper's prefactor, and a localized treatment of the remainder `R` (it is one scalar with the
bound above, with no domain index, locality or analyticity). -/
theorem thm31b_zeroClass_polymer_fromTower {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C : ℝ, 2 ≤ β₀ ∧ 0 ≤ C ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ), 0 < p₁ →
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    ∃ (E' : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ℂ) (R : ℂ),
      (T.step k hk N₁ ν β p₁).M0C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
        (((T.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
            (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull, E' X + R) ∧
      ‖R‖ ≤ C * obsPrefactor p s (β * 3 ^ k) * Real.exp (-(3 / 2 * T.κdec)) ∧
      (∀ X, E' X ≠ 0 → IsDj 1 (k + 1) X ∧
        box (rootCube (m₀ := 1) (K := k + 1) (blockIndex y)).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ X) ∧
      ∀ X, ‖E' X‖ ≤ hullConst 3 3 (3 / 2 * T.κdec) (C * obsPrefactor p s (β * 3 ^ k)) *
        Real.exp (-hullRate 3 3 (3 / 2 * T.κdec) * sizeJ 1 (k + 1) X) := by
  obtain ⟨β₀, C, hβ₀, hC, H⟩ := thm31b_zeroClass_polymer_fromTowerG T.toG hA p hCR hs0 hs
  refine ⟨β₀, C, hβ₀, hC, ?_⟩
  intro k hk N₁ _ h3 h5 ν hν hνk β hβ p₁ hp hp₁ hsc g hg y i
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3) h5 ν hν (by simpa using hνk) β hβ p₁ hp
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T hsc) g hg y i
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

end Balaban.Inhabited
