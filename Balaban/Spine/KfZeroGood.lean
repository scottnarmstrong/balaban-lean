/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KfZero

/-!
# The all-good sector input needs a positive block threshold

`KF0GoodSectorInput d N δ T thr` (`Spine/KfZero.lean`) takes the block threshold `thr` as a
parameter. The all-good sector is the set of spin configurations within `r = thr κ c₉ β ν` of `h`
at every site. For `r ≤ 0` no configuration is within `r` of `h`, the sector integral vanishes, and
the claimed identity `Z_∅(g) = exp(E + ⟨g, h⟩ + ∑ a)` is false, since an exponential is non-zero.
So the input cannot hold for an arbitrary `thr`, and the provider of `KfZeroInput` must supply a
threshold function with `thr > 0` (the notes take `r = A log(β a)/√(β ν)`, positive and at most `√2`
for large `β`). The positive-threshold case is the content of `KF0GoodSectorInput` proper; see the
section "KfZeroInput sub-inputs" of `notes/phase1/SPINE.md` for the unproved clauses.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

/-- For a non-positive threshold the all-good sector vanishes: no site is within `r ≤ 0` of `h`. -/
theorem kf0Sector_empty_eq_zero_of_nonpos {d N ℓ : ℕ} [NeZero ℓ] (s m : ℕ) [NeZero m] {r : ℝ}
    (hr : r ≤ 0) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (hℓ : ℓ = s * m)
    (g : Torus d ℓ → Fin N → ℂ) :
    kf0Sector s m r β ν h ∅ g = 0 := by
  obtain ⟨Q⟩ : Nonempty (Torus d m) := ⟨0⟩
  obtain ⟨x, hx⟩ := exists_site (d := d) (ℓ := ℓ) s m hℓ Q
  have hw : ∀ φ : Cfg d N ℓ, sectorWeight s m r h ∅ φ = 0 := fun φ => by
    unfold sectorWeight
    have hc : chi s m r h Q φ = 0 := by
      have : ¬ goodBlock s m r h Q φ := fun hg =>
        absurd (hg x hx) (not_lt.2 (le_trans hr (norm_nonneg _)))
      simp [chi, this]
    rw [Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ Q, by simp⟩) hc, mul_zero]
  unfold kf0Sector sourceIntegral sourceIntegrand
  simp [hw]

/-- **`KF0GoodSectorInput` is false for a non-positive block threshold** (when the typing has
`L ≥ 2`, `M ≥ 1` and the spin space is non-trivial): the all-good sector is zero, while the claimed
value is an exponential. -/
theorem not_kf0GoodSectorInput_of_thr_nonpos {d N : ℕ} (δ : ℝ) (T : ℝ → ℝ → Typing)
    (thr : ℝ → ℝ → ℝ → ℝ → ℝ) (hN : 0 < N) (hL : ∀ κ c₉, 2 ≤ (T κ c₉).L)
    (hM : ∀ κ c₉, 1 ≤ (T κ c₉).M) (hthr : ∀ κ c₉ β ν, thr κ c₉ β ν ≤ 0) :
    ¬ KF0GoodSectorInput d N δ T thr := by
  intro H
  obtain ⟨β₀, hβ⟩ := H 1 one_pos 1 one_pos
  have hL1 : (2 : ℝ) ≤ ((T 1 1).L : ℝ) := by exact_mod_cast hL 1 1
  have hν : 7 / 8 < (1 : ℝ) * ((T 1 1).L : ℝ) ^ 2 := by nlinarith
  have hh : ‖(EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ))‖ = 1 := by simp
  have hhor : IsHorizon (T 1 1).L 1 0 := by
    refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    have : (1 : ℝ) ≤ ((T 1 1).L : ℝ) ^ (2 * 0 + 2) := one_le_pow₀ (by linarith)
    simpa using this
  obtain ⟨a, E, -, hid⟩ := hβ (max β₀ 0) (le_max_left _ _) 1 hν le_rfl _ hh 0 hhor
  have hMpos : 0 < (T 1 1).M := hM 1 1
  have hLpos : 0 < (T 1 1).L := by have := hL 1 1; omega
  have : NeZero ((T 1 1).M * (T 1 1).L) := ⟨by positivity⟩
  have : NeZero 1 := ⟨one_ne_zero⟩
  have h0 := hid ((T 1 1).M * (T 1 1).L) (by simp) 1 (by simp) 0 (by simp)
  rw [kf0Sector_empty_eq_zero_of_nonpos _ 1 (hthr 1 1 _ _) _ _ _ (by simp)] at h0
  exact Complex.exp_ne_zero _ h0.symm

end Balaban.RootFSpine
