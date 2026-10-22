/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LevelLocalCover

/-!
# The region `X₁` of a chosen family contains a neighbourhood of every polymer site

`box_hull_subset_iUnion`: the aligned `L c`-cubes containing a set that lies in a box of `m` cells
(`m + e ≤ L`) cover the box of `e` cells around it.  `X1_far`: for a chosen family `𝒦` of the polymer
`X` at the scale `j < K`, every point of `X` moved by an integer vector of sup norm at most
`(L - 2) a_K` lies in `X₁ = ⋃𝒬₀` (the hull of a cube of `𝒦` is two cells wide).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation

section Hull

variable {d n : ℕ}

/-- **The aligned cubes containing a set in a box of `m` cells cover `e` cells around it.** -/
theorem box_hull_subset_iUnion [NeZero n] {L c s m e : ℕ} (hc : c ∣ n) (hc0 : 0 < c) (hL : 1 ≤ L)
    (hmeL : m + e ≤ L) {B q : Torus d n} (hB : Aligned c B) (hq : box q s ⊆ box B (m * c))
    {y : Torus d n} (hy : y ∈ box (B - natT fun _ => e * c) (e * c + L * c)) :
    ∃ b : Torus d n, Aligned c b ∧ box q s ⊆ box b (L * c) ∧ y ∈ box b (L * c) := by
  obtain ⟨t, ht, rfl⟩ := hy
  set B' : Torus d n := B - natT fun _ => e * c with hB'def
  have hB' : Aligned c B' := aligned_sub_natT hc hB (fun _ => Nat.mul_mod_left _ _)
  set σ : Fin d → ℕ := fun μ => min (t μ / c) e with hσ
  have hσle : ∀ μ, σ μ ≤ e := fun μ => min_le_right _ _
  have hσt : ∀ μ, σ μ * c ≤ t μ := fun μ =>
    (Nat.mul_le_mul_right c (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  set b : Torus d n := B' + natT fun μ => σ μ * c with hbdef
  have hb : Aligned c b := aligned_add_natT hc hB' (fun μ => Nat.mul_mod_left _ _)
  have hBb : B = b + natT fun μ => (e - σ μ) * c := by
    funext μ
    have h1 : e * c = σ μ * c + (e - σ μ) * c := by
      rw [← Nat.add_mul]; congr 1; have := hσle μ; omega
    have h2 : ((e * c : ℕ) : ZMod n) =
        ((σ μ * c : ℕ) : ZMod n) + (((e - σ μ) * c : ℕ) : ZMod n) := by
      rw [← Nat.cast_add, ← h1]
    simp only [hbdef, hB'def, Pi.add_apply, Pi.sub_apply, natT_apply, h2]
    ring
  refine ⟨b, hb, ?_, ?_⟩
  · refine hq.trans ?_
    rw [hBb]
    refine box_add_subset b _ (fun μ => ?_)
    calc (e - σ μ) * c + m * c = (e - σ μ + m) * c := by rw [Nat.add_mul]
      _ ≤ L * c := Nat.mul_le_mul_right _ (by have := hσle μ; omega)
  · refine ⟨fun μ => t μ - σ μ * c, fun μ => ?_, ?_⟩
    · have h1 := ht μ
      have h2 := hσt μ
      have h6 : c ≤ L * c := Nat.le_mul_of_pos_left c (by omega)
      by_cases h : t μ / c ≤ e
      · have eq : σ μ = t μ / c := min_eq_left h
        have h3 : t μ - σ μ * c = t μ % c := by
          rw [eq]; have := Nat.div_add_mod (t μ) c
          have h4 : t μ / c * c = c * (t μ / c) := Nat.mul_comm _ _
          omega
        have h5 : t μ % c < c := Nat.mod_lt _ hc0
        show t μ - σ μ * c < L * c
        omega
      · have eq : σ μ = e := min_eq_right (by omega)
        show t μ - σ μ * c < L * c
        rw [eq]; omega
    · funext μ
      simp only [hbdef, Pi.add_apply, natT_apply]
      rw [Nat.cast_sub (hσt μ)]
      ring

end Hull

section Far

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **`X₁` of a chosen family contains the `(L-2)`-cell neighbourhood of every site of the polymer.** -/
theorem X1_far {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K) {m₀ j : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hjK : j + 1 ≤ K) (hL : 2 ≤ L)
    {X 𝒦 : Set (CTorus d L N₁ m₁ K)} (hch : ChosenOne m₀ j X 𝒦) {p : CTorus d L N₁ m₁ K}
    (hp : p ∈ X) (v : Fin d → ℤ)
    (hv : ∀ μ, |v μ| ≤ (((L - 2) * cellSide L m₀ m₁ K : ℕ) : ℤ)) :
    p + (intTorus v : CTorus d L N₁ m₁ K) ∈ X1 G m₀ j 𝒦 := by
  obtain ⟨b0, hb0, hpb⟩ := hch.2 p hp
  obtain ⟨hal, -⟩ := hch.1 b0 hb0
  set a := cellSide L m₀ m₁ K with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ K
  have hLa : L * cellSide L m₀ m₁ j ≤ a := cellSide_succ_le (by omega) hjK m₀ m₁
  have hdv : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN le_rfl
  set c0 : CTorus d L N₁ m₁ K := cbase a b0 with hc0
  have hc0al : Aligned a c0 := aligned_cbase b0
  -- the cube of `𝒦` lies in the two-cell hull of `c0`
  have hhull : box b0 (L * cellSide L m₀ m₁ j) ⊆ box c0 (2 * a) := by
    have hb0eq : b0 = c0 + natT (fun μ => (b0 μ).val % a) := by
      rw [hc0, cbase_eq_sub]; funext μ; simp
    rw [hb0eq]
    refine box_add_subset c0 _ (fun μ => ?_)
    have := Nat.mod_lt (b0 μ).val ha0
    omega
  obtain ⟨w, hw, hpw⟩ := hpb
  obtain ⟨u, hu, hb0u⟩ := (hhull ⟨w, hw, rfl⟩ : b0 + natT w ∈ box c0 (2 * a))
  have hpu : p = c0 + natT u := hpw.trans hb0u
  set e := L - 2 with he
  let t : Fin d → ℕ := fun μ => ((u μ : ℤ) + v μ + ((e * a : ℕ) : ℤ)).toNat
  have hvμ : ∀ μ, -((e * a : ℕ) : ℤ) ≤ v μ ∧ v μ ≤ ((e * a : ℕ) : ℤ) := fun μ => by
    have := abs_le.1 (hv μ)
    have h2 : (L - 2) * a = e * a := rfl
    rw [h2] at this
    exact this
  have ht0 : ∀ μ, 0 ≤ (u μ : ℤ) + v μ + ((e * a : ℕ) : ℤ) := fun μ => by
    have := (hvμ μ).1; have : (0 : ℤ) ≤ u μ := by positivity
    omega
  have hty : p + (intTorus v : CTorus d L N₁ m₁ K) =
      (c0 - natT fun _ => e * a) + natT t := by
    funext μ
    rw [hpu]
    simp only [Pi.add_apply, Pi.sub_apply, natT_apply, intTorus_apply]
    have : ((t μ : ℕ) : ℤ) = (u μ : ℤ) + v μ + ((e * a : ℕ) : ℤ) := Int.toNat_of_nonneg (ht0 μ)
    have h2 : ((t μ : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) =
        (((t μ : ℕ) : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by simp
    rw [h2, this]
    push_cast
    ring
  have hLe : 2 + e ≤ L := by omega
  have hmem : p + (intTorus v : CTorus d L N₁ m₁ K) ∈
      box (c0 - natT fun _ => e * a) (e * a + L * a) := by
    rw [hty]
    refine ⟨t, fun μ => ?_, rfl⟩
    have h1 := hvμ μ
    have h2 := hu μ
    have h3 : ((t μ : ℕ) : ℤ) = (u μ : ℤ) + v μ + ((e * a : ℕ) : ℤ) := Int.toNat_of_nonneg (ht0 μ)
    have h4 : (L * a : ℕ) = (e + 2) * a := by rw [he]; congr 1; omega
    have h5 : ((e + 2) * a : ℕ) = e * a + 2 * a := by ring
    zify at h2 ⊢
    rw [h4] at *
    push_cast at *
    nlinarith
  obtain ⟨b, hbal, hbq, hyb⟩ := box_hull_subset_iUnion (L := L) (m := 2) (e := e) hdv ha0
    (by omega) hLe hc0al hhull hmem
  refine Set.mem_iUnion₂.2 ⟨b, ⟨hbal, fun z _ => Finset.mem_coe.2 (hG.mem_layer z),
    b0, hb0, hbq⟩, hyb⟩

end Far

end Balaban.Localization
