module

public import Balaban.LargeField.Geometry.Continuous
public import Balaban.LargeField.Geometry.Coarsen
public import Balaban.LargeField.Counter.Params
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Covers by boxes under a pure shadow (Part I, proof of Lemma I.4.10 (a), (T1))

A set covered by boxes of side `≤ b` has its neighbourhood `X^{∼m}` covered by the boxes enlarged
by `m` on each side (`nbhd_box_subset`), and its coarsening covered by the coarsened boxes
(`blockMap_box_subset`, of side `≤ ⌈(b-1)/L⌉ + 1`).  Together (`shadow_box_side`) a box of side
`≤ crit_k = 2ρ_k + 10` becomes a box of side `≤ crit_{k+1}` under a pure shadow with attribution
radius `s_* r_k`, by the conditions (K) of §I.5.2.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Boxes

variable {d n : ℕ} [NeZero n]

/-- The `m`-neighbourhood of a box is the box enlarged by `m` on each side. -/
theorem nbhd_box_subset (m : ℕ) (a : Torus d n) (s : Fin d → ℕ) :
    nbhd m (box a s) ⊆ box (fun i => a i - (m : ZMod n)) (fun i => s i + 2 * m) := by
  intro y hy i
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.mp hy
  obtain ⟨j, hj, hxj⟩ := hx i
  have h1 := cycNorm_le_supDist y x i
  obtain ⟨u, hu, hue⟩ := (cycNorm_le_iff (n := n) (y i - x i) m).mp (h1.trans hxy)
  have hu' := abs_le.mp hu
  refine ⟨(j : ℤ) + u + m |>.toNat, ?_, ?_⟩
  · dsimp only; omega
  have e : ((((j : ℤ) + u + m).toNat : ℕ) : ZMod n) = (((j : ℤ) + u + m : ℤ) : ZMod n) := by
    have : (((j : ℤ) + u + m).toNat : ℤ) = (j : ℤ) + u + m := by omega
    rw [← Int.cast_natCast, this]
  rw [e]
  push_cast
  have : y i = x i + (u : ZMod n) := by rw [hue]; ring
  rw [this, hxj]
  ring

end Boxes

section Coarse

variable {d n m L : ℕ} [NeZero n] [NeZero m]

/-- The coarsening of a box lies in a box of side `⌊(s + L - 2)/L⌋ + 1`. -/
theorem blockMap_box_subset (hn : n = L * m) (a : Torus d n) (s : Fin d → ℕ) :
    blockMap L m '' (box a s) ⊆ box (blockMap L m a) (fun i => (s i + L - 2) / L + 1) := by
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · exact absurd (by simpa [h] using hn) (NeZero.ne n)
    · exact h
  rintro _ ⟨x, hx, rfl⟩ i
  obtain ⟨j, hj, hxj⟩ := hx i
  refine ⟨((a i).val % L + j) / L, ?_, ?_⟩
  · have : ((a i).val % L + j) / L ≤ (s i + L - 2) / L := by
      apply Nat.div_le_div_right
      have := Nat.mod_lt (a i).val hL
      omega
    dsimp only; omega
  · have hz : (((a i).val + j : ℕ) : ℤ) = (a i).val + j := by push_cast; ring
    have hzm : ((((a i).val + j : ℕ) : ℤ) : ZMod n) = x i := by
      rw [hxj]; push_cast; simp
    rw [blockMap_apply, blockCoord_intCast hn (x i) _ hzm]
    rw [blockMap_apply, blockCoord]
    have hdiv : (((a i).val + j : ℕ) : ℤ) / L = (((a i).val / L + ((a i).val % L + j) / L : ℕ) : ℤ) := by
      have h1 : (a i).val + j = L * ((a i).val / L) + ((a i).val % L + j) := by
        have := Nat.div_add_mod (a i).val L
        omega
      have h2 : ((a i).val + j) / L = (a i).val / L + ((a i).val % L + j) / L := by
        rw [h1, Nat.mul_add_div hL]
      exact_mod_cast h2
    rw [hdiv, Int.cast_natCast, Nat.cast_add]

/-- Pure-shadow cover: if `Z ⊆ ⋃_i box (a i) (s i)` and `Z' ⊆ (Z^↑)^{∼m}` then `Z'` lies in the union
of the boxes `box (a_i^↑ - m) (⌊(s_i+L-2)/L⌋ + 1 + 2m)`. -/
theorem shadow_cover (hn : n = L * m) {ι : Type*} (I : Finset ι) (a : ι → Torus d n)
    (s : ι → Fin d → ℕ) {Z : Set (Torus d n)} (hZ : Z ⊆ ⋃ i ∈ I, box (a i) (s i)) (r : ℕ)
    {Z' : Set (Torus d m)} (hZ' : Z' ⊆ nbhd r (blockMap L m '' Z)) :
    Z' ⊆ ⋃ i ∈ I, box (fun k => blockMap L m (a i) k - (r : ZMod m))
      (fun k => (s i k + L - 2) / L + 1 + 2 * r) := by
  intro y hy
  obtain ⟨x, ⟨z, hz, rfl⟩, hxy⟩ := mem_nbhd.mp (hZ' hy)
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hZ hz)
  refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  have h1 := blockMap_box_subset hn (a i) (s i) ⟨z, hzi, rfl⟩
  have h2 : y ∈ nbhd r (box (blockMap L m (a i)) (fun k => (s i k + L - 2) / L + 1)) :=
    mem_nbhd.mpr ⟨_, h1, hxy⟩
  exact nbhd_box_subset r _ _ h2

end Coarse

/-- The side bound: `⌊(crit_k + L - 2)/L⌋ + 1 + 2 s_* r_k ≤ crit_{k+1}`, with `crit_j = 2 c₀ r_j + 10`,
by `c₀ (1 - L⁻¹) ≥ s_* + 1`, `r_k ≥ 2`, `r_k ≤ r_{k+1}`. -/
theorem shadow_box_side {L c0 sS r r' : ℕ} (hL : 2 ≤ L)
    (hc : (sS : ℝ) + 1 ≤ c0 * (1 - 1 / (L : ℝ))) (hr : 2 ≤ r) (hrr : r ≤ r') (hs : 1 ≤ sS) :
    (2 * (c0 * r) + 10 + L - 2) / L + 1 + 2 * (sS * r) ≤ 2 * (c0 * r') + 10 := by
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hdiv : (((2 * (c0 * r) + 10 + L - 2) / L : ℕ) : ℝ) ≤ ((2 * (c0 * r) + 10 + L - 2 : ℕ) : ℝ) / L :=
    Nat.cast_div_le
  have hsum : ((2 * (c0 * r) + 10 + L - 2 : ℕ) : ℝ) = 2 * c0 * r + 8 + L := by
    have : 2 * (c0 * r) + 10 + L - 2 = 2 * (c0 * r) + 8 + L := by omega
    rw [this]; push_cast; ring
  rw [hsum] at hdiv
  have hx : (L : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hLr
  have hc' : (c0 : ℝ) * (L : ℝ)⁻¹ ≤ c0 - sS - 1 := by
    have : (1 : ℝ) / L = (L : ℝ)⁻¹ := one_div _
    rw [this] at hc; nlinarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrr' : (r : ℝ) ≤ r' := by exact_mod_cast hrr
  have hsR : (1 : ℝ) ≤ sS := by exact_mod_cast hs
  have hc0 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg _
  have key : (((2 * (c0 * r) + 10 + L - 2) / L : ℕ) : ℝ) + 1 + 2 * (sS * r) ≤ 2 * (c0 * r') + 10 := by
    have e1 : ((2 * (c0 : ℝ) * r + 8 + L) / L) = (2 * c0 * r + 8) * (L : ℝ)⁻¹ + 1 := by
      field_simp
    rw [e1] at hdiv
    have e2 : (2 * (c0 : ℝ) * r + 8) * (L : ℝ)⁻¹ = 2 * ((c0 : ℝ) * (L : ℝ)⁻¹) * r + 8 * (L : ℝ)⁻¹ := by ring
    rw [e2] at hdiv
    have e3 : 2 * ((c0 : ℝ) * (L : ℝ)⁻¹) * r ≤ 2 * (c0 - sS - 1) * r := by
      have := mul_le_mul_of_nonneg_right hc' (by linarith : (0 : ℝ) ≤ 2 * r)
      nlinarith
    have e4 : (c0 : ℝ) * r ≤ c0 * r' := mul_le_mul_of_nonneg_left hrr' hc0
    nlinarith
  exact_mod_cast key

end Balaban.LargeField
