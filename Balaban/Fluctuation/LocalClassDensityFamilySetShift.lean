/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
public import Balaban.Fluctuation.LevelLocalCover
public import Balaban.Fluctuation.CriticalPoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Shifts of a point of a chosen cube stay in `X₁` (`LocalClassDensityFamilySetShift`)

For a chosen cube `q ∈ 𝒦_X` (side `L a_j`, `j < K`) a point `w` of `q` moved by an integer vector of
sup norm at most `(L - 2) a_K` stays in `X₁ = ⋃ 𝒬₀`.  The cube `q` may straddle two `π_K`-cells, so
the margin is `L - 2` cells and not the `L - 1` cells of a cube inside one cell.

* `exists_shift_index`: the arithmetic of one coordinate;
* `shift_mem_X1`: the statement above, for a level generating set `G` of the top level `K`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Arith

/-- **One coordinate.**  For `t < 2 a` and `|v| ≤ (L - 2) a` there is `σ ≤ L - 2` with
`0 ≤ σ a + t + v < L a`. -/
theorem exists_shift_index {L a t : ℕ} (hL : 2 ≤ L) (ha : 0 < a) (ht : t < 2 * a) {v : ℤ}
    (hv : |v| ≤ (((L - 2) * a : ℕ) : ℤ)) :
    ∃ σ : ℕ, σ ≤ L - 2 ∧ 0 ≤ ((σ * a : ℕ) : ℤ) + t + v ∧
      ((σ * a : ℕ) : ℤ) + t + v < ((L * a : ℕ) : ℤ) := by
  have hLa : (((L - 2) * a : ℕ) : ℤ) + 2 * a = ((L * a : ℕ) : ℤ) := by
    have : (L - 2) * a + 2 * a = L * a := by
      rw [← Nat.add_mul]; congr 1; omega
    exact_mod_cast this
  obtain ⟨hv1, hv2⟩ := abs_le.1 hv
  by_cases hs : 0 ≤ (t : ℤ) + v
  · refine ⟨0, Nat.zero_le _, by simpa using hs, ?_⟩
    simp only [zero_mul, Nat.cast_zero, zero_add]
    have : (t : ℤ) < 2 * a := by exact_mod_cast ht
    linarith
  · push Not at hs
    set e : ℕ := (-((t : ℤ) + v)).toNat with he
    have he1 : (e : ℤ) = -((t : ℤ) + v) := by rw [he]; omega
    have hepos : 0 < e := by omega
    have he2 : (e : ℤ) ≤ (((L - 2) * a : ℕ) : ℤ) := by
      have : (t : ℤ) ≥ 0 := by positivity
      omega
    set σ : ℕ := (e + a - 1) / a with hσ
    have hdm := Nat.div_add_mod (e + a - 1) a
    have hmod := Nat.mod_lt (e + a - 1) ha
    have h1 : a * σ ≤ e + a - 1 := by rw [hσ]; omega
    have h2 : e ≤ a * σ := by rw [hσ]; omega
    have he2' : e ≤ (L - 2) * a := by exact_mod_cast he2
    have hσle : σ ≤ L - 2 := by
      by_contra hcon
      push Not at hcon
      have : (L - 2 + 1) * a ≤ σ * a := Nat.mul_le_mul_right a hcon
      rw [Nat.add_mul, one_mul] at this
      rw [mul_comm] at h1
      omega
    refine ⟨σ, hσle, ?_, ?_⟩
    · have : ((σ * a : ℕ) : ℤ) ≥ e := by
        have : e ≤ σ * a := by rw [mul_comm]; exact h2
        exact_mod_cast this
      linarith
    · have h1' : σ * a ≤ e + a - 1 := by rw [mul_comm]; exact h1
      have : ((σ * a : ℕ) : ℤ) < e + a := by
        have : σ * a < e + a := by omega
        exact_mod_cast this
      have hLa' : (0 : ℤ) < ((L * a : ℕ) : ℤ) - 2 * a - (((L - 2) * a : ℕ) : ℤ) + 1 := by
        linarith
      have : (a : ℤ) ≤ ((L * a : ℕ) : ℤ) := by
        have : a ≤ L * a := Nat.le_mul_of_pos_left a (by omega)
        exact_mod_cast this
      linarith

end Arith

section Shift

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {m₀ : ℕ}

/-- **A shifted point of a chosen cube lies in `X₁`.**  Let `G` be a level generating set of the top
level `K`, `L ≥ 2`, `L^{m₀} ∣ N₁`, `j + 1 ≤ K` and `q ∈ 𝒦_X`.  If `w ∈ q` (the cube of side
`L a_j`) and `v` is an integer vector with `|v_μ| ≤ (L - 2) a_K`, then `w + v ∈ X₁`. -/
theorem shift_mem_X1 {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hlev : IsLevel G K)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {j : ℕ} (hjK : j + 1 ≤ K)
    {𝒦X : Set (CTorus d L N₁ m₁ K)} {q w : CTorus d L N₁ m₁ K} (hq : q ∈ 𝒦X)
    (hw : w ∈ box q (L * cellSide L m₀ m₁ j)) (v : Fin d → ℤ)
    (hv : ∀ μ, |v μ| ≤ (((L - 2) * cellSide L m₀ m₁ K : ℕ) : ℤ)) :
    w + (intTorus v : CTorus d L N₁ m₁ K) ∈ X1 G m₀ j 𝒦X := by
  classical
  set a := cellSide L m₀ m₁ K with ha
  have hc : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN le_rfl
  have ha0 : 0 < a := cellSide_pos m₀ m₁ K
  have hLa : L * cellSide L m₀ m₁ j ≤ a :=
    cellSide_succ_le (Nat.pos_of_ne_zero (NeZero.ne L)) hjK m₀ m₁
  set c0 : CTorus d L N₁ m₁ K := cbase a q with hc0
  obtain ⟨r, hr, hqr⟩ := mem_box_cbase (a := a) ha0 q
  obtain ⟨u, hu, rfl⟩ := hw
  -- the coordinates of `w` relative to `c0`
  set t : Fin d → ℕ := r + u with ht
  have htl : ∀ μ, t μ < 2 * a := fun μ => by
    have := hr μ; have := hu μ; simp only [ht, Pi.add_apply]; omega
  have hwt : q + natT u = c0 + natT t := by
    rw [hqr, natT_add, add_assoc]
  choose σ hσle hσ0 hσ1 using fun μ =>
    exists_shift_index (L := L) (a := a) (t := t μ) hL ha0 (htl μ) (hv μ)
  set b : CTorus d L N₁ m₁ K := c0 - natT fun μ => σ μ * a with hb
  have hbal : Aligned a b :=
    aligned_sub_natT hc (aligned_cbase q) (fun μ => by simp)
  have hlay : box b (L * a) ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)) := by
    intro z _
    have := (G.layerIndex_spec (hlev z).1).2.2
    rw [(hlev z).2] at this
    exact_mod_cast this
  have hbox : box q (L * cellSide L m₀ m₁ j) ⊆ box b (L * a) := by
    rintro x ⟨u', hu', rfl⟩
    refine ⟨(fun μ => σ μ * a) + (r + u'), fun μ => ?_, ?_⟩
    · have h1 := hσle μ
      have h2 := hr μ
      have h3 := hu' μ
      have h4 : σ μ * a ≤ (L - 2) * a := Nat.mul_le_mul_right a h1
      have h5 : u' μ < a := lt_of_lt_of_le h3 hLa
      have h6 : (L - 2) * a + 2 * a = L * a := by rw [← Nat.add_mul]; congr 1; omega
      simp only [Pi.add_apply]
      omega
    · have hq' : q = c0 + natT r := hqr
      have e1 : q + natT u' = c0 + natT r + natT u' := by rw [← hq']
      rw [e1, hb, natT_add, natT_add]
      abel
  have hQ : b ∈ Q0 G m₀ j 𝒦X := ⟨hbal, hlay, q, hq, hbox⟩
  refine Set.mem_iUnion₂.2 ⟨b, hQ, ?_⟩
  rw [hwt]
  refine ⟨fun μ => (((σ μ * a : ℕ) : ℤ) + t μ + v μ).toNat, fun μ => ?_, ?_⟩
  · have h1 := hσ0 μ
    have h2 := hσ1 μ
    show (((σ μ * a : ℕ) : ℤ) + t μ + v μ).toNat < L * a
    omega
  · funext μ
    have h0 := hσ0 μ
    have e : ((((((σ μ * a : ℕ) : ℤ) + t μ + v μ).toNat : ℕ)) : ZMod ((N₁ * L ^ m₁) * L ^ K)) =
        ((((σ μ * a : ℕ) : ℤ) + t μ + v μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    simp only [hb, Pi.add_apply, Pi.sub_apply, natT_apply, intTorus_apply, e]
    push_cast
    ring

end Shift

end Balaban.Localization
