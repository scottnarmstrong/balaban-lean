/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedMargin
import Mathlib

/-!
# The margin of the oscillation bound without the cap `ϱ - 1` (blocker 4, question A)

`margin_of_torusDist` (`CoreResponseOsc.lean`) gives the path-distance margin
`min ((T - 1) / L^{k+1}, ϱ - 1)` from a torus distance `T`.  The cap `ϱ - 1` is not a property of the
path metric: every bond of `Ω₁` costs at least `1 / L^k` (the spacing is at most `L^k`), so the path
distance dominates the torus distance divided by `L^k`.

* `pathDist_ge_torusDist_top`: `d(x, p) ≥ |x - p|_torus / L^k`, with no hypothesis on `x`, `p`;
* `margin_of_torusDist_top`: the hypothesis of `margin_of_torusDist` gives the margin `(T - 1) / L^k`;
* `hmargin_removed_uncapped`: `hmargin_removed` for every `Rm ≤ M ⌊R_{k-1}⌋ / L`, with no condition
  `Rm ≤ ϱ - 1`.

## The energy `E_k` of P7 (3.7)-(3.10) (question B)

`hEZ_of_vacuum_bound`: from the vacuum bound `|E_k| ≤ C'_E λ_k + C'_E` (P7 p. 520, a source premise: the
vacuum constant `Ek` of the small-field class, `IsSF … Ek`, `StepClass.Ek`, has no landed bound) and the
volume bound `|Z|_k ≤ (M crit_k)^d` (`removed_cubeVol_le`), the hypothesis `hEZ` of
`removedKernel_kerBound_of_window_inst` for `EZ = E_k |Z|_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization

section Top

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The path distance dominates the torus distance divided by `L^k`.** -/
theorem pathDist_ge_torusDist_top (G : GeneratingSet d L N₀ k ϱ) (x p : Torus d (N₀ * L ^ k)) :
    ENNReal.ofReal (Green.torusDist d (N₀ * L ^ k) x p / (L : ℝ) ^ k) ≤ G.pathDist x p := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hc0 : 0 < (L : ℝ) ^ k := by positivity
  set F : Torus d (N₀ * L ^ k) → ℝ := fun q => Green.torusDist d (N₀ * L ^ k) x q / (L : ℝ) ^ k with hF
  have hFx : F x = 0 := by
    show Green.torusDist d (N₀ * L ^ k) x x / (L : ℝ) ^ k = 0
    rw [Balaban.Multiscale.torusDist_self', zero_div]
  have hlip : ∀ a b, a ∈ G.Ω 1 → b ∈ G.Ω 1 → Adj a b → |F a - F b| ≤ G.bondCost a b := by
    intro a b ha hb hadj
    have hab := hadj.torusDist_le
    have t1 := Green.torusDist_triangle_gen (d := d) (m := N₀ * L ^ k) x a b
    have t2 := Green.torusDist_triangle_gen (d := d) (m := N₀ * L ^ k) x b a
    have t3 : Green.torusDist d (N₀ * L ^ k) b a = Green.torusDist d (N₀ * L ^ k) a b :=
      Green.torusDist_comm_gen _ _
    have hdiff : |Green.torusDist d (N₀ * L ^ k) x a - Green.torusDist d (N₀ * L ^ k) x b| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hsa : G.spacing a ≤ (L : ℝ) ^ k :=
      pow_le_pow_right₀ hL1 (G.layerIndex_spec ha).2.1
    have hsb : G.spacing b ≤ (L : ℝ) ^ k :=
      pow_le_pow_right₀ hL1 (G.layerIndex_spec hb).2.1
    have hmpos : 0 < max (G.spacing a) (G.spacing b) := lt_of_lt_of_le (spacing_pos G) (le_max_left _ _)
    have hbc : 1 / (L : ℝ) ^ k ≤ G.bondCost a b := by
      unfold GeneratingSet.bondCost
      exact one_div_le_one_div_of_le hmpos (max_le hsa hsb)
    calc |F a - F b|
        = |Green.torusDist d (N₀ * L ^ k) x a - Green.torusDist d (N₀ * L ^ k) x b| / (L : ℝ) ^ k := by
          show |_ / (L : ℝ) ^ k - _ / (L : ℝ) ^ k| = _
          rw [← sub_div, abs_div, abs_of_pos hc0]
      _ ≤ 1 / (L : ℝ) ^ k := div_le_div_of_nonneg_right hdiff hc0.le
      _ ≤ _ := hbc
  have := G.ofReal_sub_le_pathDist F hlip x p
  rw [hFx, sub_zero] at this
  exact this

end Top

section Margin

variable {d L : ℕ} [NeZero L] {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}

/-- **The geometric margin from the torus distance, without the cap `ϱ - 1`**: under the hypothesis of
`margin_of_torusDist`, the margin hypothesis of `effAction_sub_actionZ_osc_le_of_weighted` holds with
`R = (T - 1) / L^k`. -/
theorem margin_of_torusDist_top (Zr : ActionConv.Region G)
    (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) {T : ℝ}
    (hfar : ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin d, y + Pi.single μ 1 ∉ Zr.sites ∨
        y - Pi.single μ 1 ∉ Zr.sites) →
      ∀ w ∈ Zf.biUnion (fib d L (N₁ * L ^ m₁) k k), T ≤ Green.torusDist d (N₁ * L ^ m₁ * L ^ k) y w) :
    ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin d, y + Pi.single μ 1 ∉ Zr.sites ∨ y - Pi.single μ 1 ∉ Zr.sites) →
      ENNReal.ofReal ((T - 1) / (L : ℝ) ^ k) ≤
        siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) y := by
  classical
  intro y hy hOy
  unfold siteSetDist
  refine le_iInf₂ fun w hw => ?_
  have hc0 : 0 < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hdist : T - 1 ≤ Green.torusDist d (N₁ * L ^ m₁ * L ^ k) y w := by
    obtain ⟨-, hw1⟩ := Finset.mem_filter.1 hw
    rcases hw1.2 with hwW | ⟨w', hw'W, hadj⟩
    · have := hfar y hy hOy w hwW; linarith
    · have h1 := hfar y hy hOy w' hw'W
      have h2 := Green.torusDist_triangle_gen (d := d) (m := N₁ * L ^ m₁ * L ^ k) y w w'
      have h3 : Green.torusDist d (N₁ * L ^ m₁ * L ^ k) w w' ≤ 1 := hadj.torusDist_le
      linarith
  exact le_trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hdist hc0.le))
    (pathDist_ge_torusDist_top G y w)

end Margin

section Removed

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]
  {k' : ℕ} (hkK : k' + 1 ≤ K) (Z : H.Comp (k' + 1)) {N₁ m₁ : ℕ} [NeZero N₁]
  (hq : N₁ * S.L ^ m₁ = S.M * n (k' + 1)) {ϱ : ℝ}
  (G : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k' + 1) ϱ) (Zr : ActionConv.Region G)
  (b0 : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1 - (k' + 1)))) (w : Fin S.d → ℕ)
  (hbx : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
    jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w ↔
      blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1))
        (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ H.Zzero (k' + 1) Z)
  (hZrsites : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
    x ∈ Zr.sites ↔ cubeMap n S.L S.M (k' + 1) (k' + 1)
      (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ (Z.1 : Set (Torus S.d (n (k' + 1)))))

include hkK hbx hZrsites in
/-- **Premise `hmargin` without the cap**: as `hmargin_removed`, for every `Rm ≤ M ⌊R_{k-1}⌋ / L`
(`k = k' + 1`), with no condition `Rm ≤ ϱ - 1`. -/
theorem hmargin_removed_uncapped {Rm : ℝ} (hR1 : Rm ≤ (S.M : ℝ) * ⌊R k'⌋₊ / S.L) :
    ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin S.d, y + Pi.single μ 1 ∉ Zr.sites ∨
        y - Pi.single μ 1 ∉ Zr.sites) →
      ENNReal.ofReal Rm ≤ siteSetDist G (shadow G
        ((boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w).biUnion
          (fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1)))) y := by
  intro y hy hOy
  have hL : (0 : ℝ) < S.L := by exact_mod_cast NeZero.pos S.L
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast NeZero.pos S.L
  have hM : (0 : ℝ) < S.M := by exact_mod_cast NeZero.pos S.M
  have hfar := hfar_removed H hkK Z hq G Zr b0 w hbx hZrsites
  have hm := margin_of_torusDist_top Zr
    (boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w)
    (T := ((S.L ^ k' * S.M : ℕ) : ℝ) * ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ))
    (fun y' _ h w' hw' => hfar y' h w' hw') y hy hOy
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hm
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (k' + 1) := pow_pos hL _
  rw [le_div_iff₀ hp]
  have hX : (1 : ℝ) ≤ ((S.L ^ k' * S.M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (NeZero.pos S.L) _) (NeZero.pos S.M)
  have hg : (1 : ℝ) ≤ ((3 * S.L + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have h2 : ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) =
      S.L * ⌊R k'⌋₊ + ((3 * S.L + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h2]
  have h3 : Rm * (S.L : ℝ) ≤ (S.M : ℝ) * ⌊R k'⌋₊ := by
    rw [le_div_iff₀ hL] at hR1; exact hR1
  have h4 : Rm * (S.L : ℝ) ^ (k' + 1) = Rm * S.L * (S.L : ℝ) ^ k' := by ring
  have h5 : ((S.L ^ k' * S.M : ℕ) : ℝ) = (S.L : ℝ) ^ k' * S.M := by push_cast; ring
  have hLk : (0 : ℝ) < (S.L : ℝ) ^ k' := pow_pos hL _
  have hf : (0 : ℝ) ≤ ⌊R k'⌋₊ := Nat.cast_nonneg _
  rw [h4]
  have h6 : Rm * S.L * (S.L : ℝ) ^ k' ≤ (S.M : ℝ) * ⌊R k'⌋₊ * (S.L : ℝ) ^ k' :=
    mul_le_mul_of_nonneg_right h3 hLk.le
  have h7 : (S.M : ℝ) * ⌊R k'⌋₊ * (S.L : ℝ) ^ k' ≤
      ((S.L ^ k' * S.M : ℕ) : ℝ) * (S.L * ⌊R k'⌋₊) := by
    rw [h5]
    have : (S.M : ℝ) * ⌊R k'⌋₊ * (S.L : ℝ) ^ k' * 1 ≤ (S.M : ℝ) * ⌊R k'⌋₊ * (S.L : ℝ) ^ k' * S.L :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    nlinarith
  have h8 : (1 : ℝ) ≤ ((S.L ^ k' * S.M : ℕ) : ℝ) * ((3 * S.L + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) := by
    nlinarith
  nlinarith

end Removed

section Energy

/-- **`hEZ` for `EZ = E_k |Z|_k`** from the vacuum bound `|E_k| ≤ C'_E λ + C'_E` and `|Z|_k ≤ V`. -/
theorem hEZ_of_vacuum_bound {Ek CE' lam cnt vol : ℝ} (hE : |Ek| ≤ CE' * lam + CE') (hcnt : 0 ≤ cnt)
    (hcv : cnt ≤ vol) : Ek * cnt ≤ (CE' * lam + CE') * vol := by
  have h0 : 0 ≤ CE' * lam + CE' := (abs_nonneg _).trans hE
  calc Ek * cnt ≤ |Ek| * cnt := mul_le_mul_of_nonneg_right (le_abs_self _) hcnt
    _ ≤ (CE' * lam + CE') * cnt := mul_le_mul_of_nonneg_right hE hcnt
    _ ≤ _ := mul_le_mul_of_nonneg_left hcv h0

end Energy

end Balaban.LargeField
