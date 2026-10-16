/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTorusCloseUnif
public import Balaban.Green.FinalTaggedTorusClose
public import Balaban.Green.FinalPathDefect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Distance-weighted closeness on two tori, and the weighted tag bound (blocker 7)

The size cap of the two-torus closeness of the tagged matrices comes from bounding the tag
monomial by `e^{κ |C|}` (`taggedMat_close_twoTorus`).  Here the tag monomial of the pair `(x, y)`
is bounded by `e^{H κ} e^{κ 7^d dist(x,y) / M}` (`norm_tagMon_macTags_le`), the entries of the
final operators on two tori are shown to be close with an extra factor `e^{-σ dist(x,y)/2}`
(`final_region_entry_close_weighted`), and the tagged-matrix difference is bounded by
`|C| e^{H κ} δ_w` with no factor `e^{κ |C|}` (`taggedMat_close_twoTorus_weighted`).

* `dist_map_eq_of_mem_macRegion`: `dist (f x) (f y) = dist x y` for `x, y ∈ Y(C)`.
* `min_le_sqrt_mul_exp`: `min ε (B e^{-σ t}) ≤ √(ε B) e^{-σ t / 2}`.
* `final_region_entry_close_weighted`: constants uniform in `k`, the torus sizes and the box.
-/

@[expose] public section

open Finset Matrix Balaban.Localization

namespace Balaban.Green

/-- Interpolation: `min ε (B e^{-σ t}) ≤ √(ε B) e^{-σ t / 2}` for `ε, B ≥ 0`. -/
theorem min_le_sqrt_mul_exp {ε B σ t : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) :
    min ε (B * Real.exp (-σ * t)) ≤ Real.sqrt (ε * B) * Real.exp (-σ * t / 2) := by
  set m := min ε (B * Real.exp (-σ * t)) with hm
  have hm0 : 0 ≤ m := le_min hε (by positivity)
  have h1 : m ≤ ε := min_le_left _ _
  have h2 : m ≤ B * Real.exp (-σ * t) := min_le_right _ _
  have hsq : m * m ≤ ε * (B * Real.exp (-σ * t)) := mul_le_mul h1 h2 hm0 hε
  set r := Real.sqrt (ε * B) * Real.exp (-σ * t / 2) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrr : r * r = ε * (B * Real.exp (-σ * t)) := by
    have e1 : Real.sqrt (ε * B) * Real.sqrt (ε * B) = ε * B :=
      Real.mul_self_sqrt (by positivity)
    have e2 : Real.exp (-σ * t / 2) * Real.exp (-σ * t / 2) = Real.exp (-σ * t) := by
      rw [← Real.exp_add]; ring_nf
    calc r * r = (Real.sqrt (ε * B) * Real.sqrt (ε * B)) *
          (Real.exp (-σ * t / 2) * Real.exp (-σ * t / 2)) := by rw [hr]; ring
      _ = _ := by rw [e1, e2]; ring
  by_contra h
  have h := not_le.1 h
  nlinarith [mul_self_lt_mul_self hr0 h]

section TwoTorus

variable {d M J N N' L : ℕ} [NeZero N] [NeZero N'] [NeZero L]

/-- On `Y(C)` the map `f` preserves the `ℓ¹` distance of the two tori. -/
theorem dist_map_eq_of_mem_macRegion (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    dist (f x) (f y) = dist x y := by
  have hxm := mid_of_mem_macRegion hM hN hC hx
  have hym := mid_of_mem_macRegion hM hN hC hy
  rw [dist_L1Torus, dist_L1Torus]
  unfold torusDist
  refine Finset.sum_congr rfl fun i _ => ?_
  have hv : ∀ u : L1Torus d N, (∀ i, (u i).val < (J + 3) * M) →
      ((f u i).val) = (u i).val := by
    intro u hu
    rw [hf, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by nlinarith [hu i, hN'])
  have h1 := hv x (fun i => (hxm i).2)
  have h2 := hv y (fun i => (hym i).2)
  have hx1 := hxm i
  have hy1 := hym i
  have hJ : 2 * ((J + 3) * M) ≤ N := by nlinarith
  have hJ' : 2 * ((J + 3) * M) ≤ N' := by nlinarith
  rw [natAbs_cycRep_sub_eq, natAbs_cycRep_sub_eq, h1, h2]
  have e1 : min ((((x i).val : ℤ) - (y i).val).natAbs) (N' - (((x i).val : ℤ) - (y i).val).natAbs)
      = min ((((x i).val : ℤ) - (y i).val).natAbs) (N - (((x i).val : ℤ) - (y i).val).natAbs) := by
    omega
  rw [e1]

/-- **Weighted entry closeness of the final operators on two tori.**  The constants `C₀`, `c₀` are
those of `final_region_entry_close_unif` (uniform in `k`, `v`, `a`, the tori and the box); for
`x, y ∈ Y(C)` the entries differ by at most
`√(2 D C₀ e^{-c₀ (min N N' / 2 - (J+3) M)}) e^{-σ dist(x,y) / 2}`, `D = finalDecayC d L`,
`σ = blockDecayRate d`. -/
theorem final_region_entry_close_weighted (hd : 0 < d) :
    ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a →
      a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {M J N N' : ℕ} [NeZero N] [NeZero N'], 0 < M → 2 * (J + 6) * M ≤ N →
      2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {C : Finset (MacIdx d N M)}, (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤
        Real.sqrt (2 * finalDecayC d L *
            (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))))) *
          Real.exp (-blockDecayRate d * dist x y / 2) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hent⟩ := final_region_entry_close_unif (d := d) (L := L) hd
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro k hk v a hv0 hv1 ha1 ha2 hmass M J N N' _ _ hM hN hN' f hf C' hC' x hx y hy
  have h1 := hent hk hv0 hv1 ha1 ha2 hmass hM hN hN' hf hC' x hx y hy
  have hD := finalDecayC_pos (d := d) (L := L) hd
  have hdist := dist_map_eq_of_mem_macRegion hM hN hN' hf hC' hx hy
  have dx := finalMass_entry_decay (d := d) (L := L) (N₀ := N) (k := k) hd hk hv0 ha1 ha2 x y
  have dy := finalMass_entry_decay (d := d) (L := L) (N₀ := N') (k := k) hd hk hv0 ha1 ha2
    (f x) (f y)
  rw [hdist] at dy
  have h2 : ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤
      (2 * finalDecayC d L) * Real.exp (-blockDecayRate d * dist x y) := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have h3 := min_le_sqrt_mul_exp (σ := blockDecayRate d) (t := dist x y)
    (ε := C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))))
    (B := 2 * finalDecayC d L) (by positivity) (by positivity)
  have h4 := le_min h1 h2
  rw [mul_comm (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))))
    (2 * finalDecayC d L)] at h3
  exact h4.trans h3

/-- **The weighted tag bound.**  On the polydisc `‖s p‖ ≤ e^κ`, the tag monomial of the pair
`(x, y)` is at most `e^{H κ} e^{κ 7^d dist(x,y) / M}`, with `H = pdH d`; no dependence on the
size of the polymer. -/
theorem norm_tagMon_macTags_le {m : ℕ} [NeZero m] (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    {s : MacIdx d m M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (z : MacIdx d m M)
    (x y : L1Torus d m) :
    ‖tagMon (macTags d m M z x y) s‖ ≤
      Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) := by
  refine (norm_tagMon_le _ hs).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := macTags_card_le hM z x y
  unfold pdH
  nlinarith

end TwoTorus

end Balaban.Green
