/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairBase
public import Balaban.Localization.I5FluctGeom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The stencil `RowInHat` and the old `CoverLocal` of the P6 mixed pair (VMOD-11 §3, row 7)

* `p6_rowInHat_of_pair`: for any pair `H ≺ F` (`F` cube aligned and sup-separated), the rows of
  `H_D(α)` at the sites of `□_z` lie in `□̂_z` (`n_H(x) ≤ z.1 + 1`, hat radius `3 L² ℓ_m`);
* `p6_rowInHat_old`, `p6_rowInHat_boundary`: `RowInHat (coverOf F♯) H a ν` for `H = H⁻, H^∂`;
* `p6_old_coverLocal`: `Dec2.CoverLocal (coverOf F♯) H⁻` (for `k ≥ 1`; `Ω₁(H⁻) = Ω₁(F♯)`).

There is no boundary `CoverLocal` (VMOD-11 §1.3).
-/

@[expose] public section

namespace Balaban.Multiscale.GeneratingSet

variable {d L K : ℕ} [NeZero L] {ϱ : ℝ}

/-- Domains agree after transport along an equality of base sides. -/
theorem castN_Ω_eq {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀') {ϱ' : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {n : ℕ}
    (hΩ : G.Ω n = G'.Ω n) : (castN h G).Ω n = (castN h G').Ω n := by
  subst h; exact hΩ

end Balaban.Multiscale.GeneratingSet

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d L : ℕ} [NeZero L]

/-- **The stencil of `H_D(α)` at the sites of a cover cube** (`row_mem_hat`), for any pair
`H ≺ F` with `F` sup-separated: `H_D(α) x y ≠ 0`, `x ∈ □_z` give `y ∈ □̂_z`. -/
theorem p6_rowInHat_of_pair {N₁' m₁' K' : ℕ} [NeZero N₁'] {ϱF ϱH : ℝ}
    {F : GeneratingSet d L (N₁' * L ^ m₁') K' ϱF} {H : GeneratingSet d L (N₁' * L ^ m₁') K' ϱH}
    (hSS : SupSep F m₁') (hHF : Background.Precedes H F) (hL3 : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} :
    RowInHat (coverOf F) H a ν := by
  classical
  intro z hz α x hx y h
  have hz' : z ∈ cubeIdx F := (mem_cubeIdx F).2 ((mem_cubeIdx F).1 hz)
  have hL3r : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hLr : (1 : ℝ) ≤ L := by linarith
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ hLr
  have hbig : (1 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 := by nlinarith
  by_contra hyH
  apply h
  apply dirichlet_entry_eq_zero (G := H) α
  · intro hyx
    exact hyH (hyx ▸ box_subset_hatBox z hx)
  · intro μ
    constructor
    · intro hyx
      have hw : ((x : Localization.CTorus d L N₁' m₁' K') + Pi.single μ 1) =
          (x : Localization.CTorus d L N₁' m₁' K') + (intTorus (Pi.single μ (1 : ℤ)) : Localization.CTorus d L N₁' m₁' K') := by
        congr 1
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
    · intro hyx
      have hw : ((x : Localization.CTorus d L N₁' m₁' K') - Pi.single μ 1) =
          (x : Localization.CTorus d L N₁' m₁' K') + (intTorus (Pi.single μ (-1 : ℤ)) : Localization.CTorus d L N₁' m₁' K') := by
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h', sub_eq_add_neg]
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
  · intro hy
    have hy' := H.mem_blk.1 hy
    obtain ⟨hn1, hnK, hxl⟩ := H.layerIndex_spec x.2
    have hnle := (p6_cover_scale_near hSS hHF (by omega) hz' x.2 hx)
    have hnle' : H.layerIndex (x : Localization.CTorus d L N₁' m₁' K') ≤ z.1 + 1 := hnle.1.trans hnle.2
    have hcell : SameCell (L ^ H.layerIndex (x : Localization.CTorus d L N₁' m₁' K'))
        (y : Localization.CTorus d L N₁' m₁' K') x := sameCell_of_jBlock_eq hnK hy'
    have hlpos : 0 < L ^ H.layerIndex (x : Localization.CTorus d L N₁' m₁' K') :=
      pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    obtain ⟨w, hw, hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine hyH ?_
    rw [hw]
    refine inBox_hat_of_add_int hx w (B := (L : ℝ) ^ (z.1 + 1)) (fun ν' => ?_) ?_
    · have h1 := hwb ν'
      have h3 : (((L ^ H.layerIndex (x : Localization.CTorus d L N₁' m₁' K') : ℕ)) : ℝ) =
          (L : ℝ) ^ H.layerIndex (x : Localization.CTorus d L N₁' m₁' K') := by push_cast; rfl
      rw [h3] at h1
      exact h1.le.trans (pow_le_pow_right₀ hLr hnle')
    · have : (L : ℝ) ^ (z.1 + 1) = L * (L : ℝ) ^ z.1 := by ring
      rw [this]
      nlinarith

variable {M1 c n1 k n0 m₁ : ℕ} [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- **`p6_rowInHat_old`**: `RowInHat (coverOf F♯) H⁻ a ν`. -/
theorem p6_rowInHat_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} :
    RowInHat (coverOf (p6FsharpC hn hρ hc Z hM1))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν :=
  p6_rowInHat_of_pair (castN_supSep _ (p6_fsharp_supSep hn hρ hc Z hM1))
    (castN_precedes _ (p6_old_precedes hn hρ hc Z)) hL

variable {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **`p6_rowInHat_boundary`**: `RowInHat (coverOf F♯) H^∂ a ν`. -/
theorem p6_rowInHat_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hL3 : 3 ≤ L)
    {a : ℕ → ℝ} {ν : ℝ} :
    RowInHat (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν :=
  p6_rowInHat_of_pair
    (castN_supSep _ (p6_fsharp_supSep hn hρ (by omega : 5 ≤ c) st.Z hM1))
    (castN_precedes _ (p6_boundary_embedded st hc hn hL hρ hZ)) hL3

/-- **`p6_old_coverLocal`**: `Dec2.CoverLocal (coverOf F♯) H⁻ a ν (mixedKc d L) (Cchi d L)` for
`k ≥ 1` (`Ω₁(H⁻) = Ω₁(F♯)`, VMOD-11 (1.5)). -/
theorem p6_old_coverLocal (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hN : 5 < c * n1) (hk : 1 ≤ k)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverLocal (coverOf (p6FsharpC hn hρ hc Z hM1))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (Dec2.mixedKc d L) (Cchi d L) := by
  have hΩ : (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z).Ω 1 =
      (p6FsharpC hn hρ hc Z hM1).Ω 1 :=
    castN_Ω_eq (p6_side hM1) (p6_old_Ω1 (M1 := M1) (c := c) (k := k) hn hρ hc Z hk)
  have hF := castN_cubeAligned (p6_side hM1) (p6_fsharp_cubeAligned (k := k) hn hρ hc Z hM1 hm₁)
  refine
    { toCoverBase := p6_coverBase_old hn hρ hc hN Z hM1 hm₁ hM hd hL hν hνL ha hsep
      idx_range := fun q hq => ((mem_cubeIdx _).1 hq).1
      idx_base := fun q hq => ((mem_cubeIdx _).1 hq).2.2
      chi_supp := fun _ _ _ h => inBox_of_chi_ne_zero h
      cubeP_sub := ?_
      own_cover := ?_
      row_mem_hat := fun z hz α x hx y h =>
        p6_rowInHat_old hn hρ hc Z hM1 hL z hz α hx h }
  · intro q hq x hx
    obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx _).1 hq
    have hxl : x ∈ (p6FsharpC hn hρ hc Z hM1).layer q.1 :=
      ((hF.mem_layer_iff hm1 hmK (mem_cubeP.1 hx |>.mono
        (pow_dvd_pow L (by omega : q.1 + m₁ ≤ q.1 + m₁)))).2 hl)
    rw [hΩ]
    exact (p6FsharpC hn hρ hc Z hM1).layer_subset hm1 hmK hxl
  · intro x hx
    rw [hΩ] at hx
    obtain ⟨hn1', hnK, hxl⟩ := (p6FsharpC hn hρ hc Z hM1).layerIndex_spec hx
    exact ⟨_, own_mem_cubeIdx hF hn1' hnK hxl, mem_cubeP.2 (ownBase_sameCell x)⟩

end Balaban.LargeField
