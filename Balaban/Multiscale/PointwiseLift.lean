/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ScaleMismatch
public import Balaban.Multiscale.Locality
public import Balaban.Green.Lattice.Loc
public import Balaban.Green.Lattice.LocSums

/-!
# Lifting lattice balls to the fine torus (GREEN.md Lemma P, geometry)

For a centre `c` of the fine torus `Torus d (N₀ * L ^ k)` and `z ∈ ℤ^d`, `liftPt c z = c + z`.

* `negLap_liftPt`: the unit-spacing Laplacian of a lifted field is the torus Laplacian;
* `torusDist_liftPt_le`: `torusDist c (c + z) ≤ d ‖z‖_∞`;
* `liftPt_injOn`: the lift is injective on balls of radius `< N₀ L^k / 2`;
* `exists_pathCost_lift`: a path from `c + z` to `c` inside a region of spacing `≥ m` of cost
  `≤ ‖z‖₁ / m`;
* `lift_mem_layers`: Lemma 4.3 (d): the lifted ball of `ℓ¹` radius `≤ L^{j-1}` around a layer-`j`
  point lies in `Ω₁` with spacing in `[L^{j-1}, L^{j+1}]`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Balaban Balaban.LatticeGreen Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The lift of `z ∈ ℤ^d` to the fine torus, centred at `c`. -/
def liftPt (c : Torus d (N₀ * L ^ k)) (z : Fin d → ℤ) : Torus d (N₀ * L ^ k) :=
  c + fun i => ((z i : ℤ) : ZMod (N₀ * L ^ k))

omit [NeZero N₀] [NeZero L] in
theorem liftPt_zero (c : Torus d (N₀ * L ^ k)) : liftPt c 0 = c := by
  funext i
  simp [liftPt]

omit [NeZero N₀] [NeZero L] in
theorem liftPt_add_single (c : Torus d (N₀ * L ^ k)) (z : Fin d → ℤ) (μ : Fin d) :
    liftPt c (z + Pi.single μ 1) = liftPt c z + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [liftPt]; ring
  · simp [liftPt, h]

omit [NeZero N₀] [NeZero L] in
theorem liftPt_sub_single (c : Torus d (N₀ * L ^ k)) (z : Fin d → ℤ) (μ : Fin d) :
    liftPt c (z - Pi.single μ 1) = liftPt c z - Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [liftPt]; ring
  · simp [liftPt, h]

omit [NeZero N₀] [NeZero L] in
theorem negLap_liftPt (c : Torus d (N₀ * L ^ k)) (v : Torus d (N₀ * L ^ k) → ℂ)
    (z : Fin d → ℤ) :
    negLap (fun w => v (liftPt c w)) z =
      ∑ μ : Fin d, (2 * v (liftPt c z) - v (liftPt c z + Pi.single μ 1) -
        v (liftPt c z - Pi.single μ 1)) := by
  unfold negLap
  refine Finset.sum_congr rfl fun μ _ => ?_
  dsimp only
  rw [liftPt_add_single, liftPt_sub_single]

theorem torusDist_liftPt_le (c : Torus d (N₀ * L ^ k)) (z : Fin d → ℤ) :
    Green.torusDist d (N₀ * L ^ k) c (liftPt c z) ≤ d * ‖z‖ := by
  unfold Green.torusDist
  calc _ ≤ ∑ _i : Fin d, ‖z‖ := Finset.sum_le_sum fun i _ => ?_
    _ = d * ‖z‖ := by simp
  have h1 := Green.natAbs_cycRep_le_of_cast (m := N₀ * L ^ k) (c i - liftPt c z i) (-(z i))
    (by simp [liftPt])
  have h2 : ((z i).natAbs : ℝ) ≤ ‖z‖ := by
    have := norm_le_pi_norm z i
    rw [Int.norm_eq_abs] at this
    rwa [Nat.cast_natAbs, Int.cast_abs]
  rw [Int.natAbs_neg] at h1
  exact (Nat.cast_le.2 h1).trans h2

omit [NeZero N₀] [NeZero L] in
theorem liftPt_injOn (c : Torus d (N₀ * L ^ k)) {z z' : Fin d → ℤ} {R : ℝ}
    (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R) (hR : 2 * R < (N₀ * L ^ k : ℕ))
    (h : liftPt c z = liftPt c z') : z = z' := by
  funext i
  have h1 := congrFun h i
  simp only [liftPt, Pi.add_apply, add_right_inj] at h1
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (z i) (z' i) (N₀ * L ^ k)).1 h1
  have h3 : |((z' i - z i : ℤ) : ℝ)| < ((N₀ * L ^ k : ℕ) : ℝ) := by
    have a := norm_le_pi_norm z i
    have b := norm_le_pi_norm z' i
    rw [Int.norm_eq_abs] at a b
    rw [Int.cast_sub]
    calc |((z' i : ℤ) : ℝ) - (z i : ℝ)| ≤ |(z' i : ℝ)| + |(z i : ℝ)| := abs_sub _ _
      _ < _ := by linarith
  have h4 : |z' i - z i| < ((N₀ * L ^ k : ℕ) : ℤ) := by
    rw [← Int.cast_abs] at h3
    exact_mod_cast h3
  have h5 := Int.eq_zero_of_abs_lt_dvd h2 h4
  omega

theorem abs_cast_le_of_natAbs_le {a b : ℤ} (h : a.natAbs ≤ b.natAbs) :
    |(a : ℝ)| ≤ |(b : ℝ)| := by
  have := (Nat.cast_le (α := ℝ)).2 h
  rwa [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at this

theorem exists_descent (z : Fin d → ℤ) (μ : Fin d) (hz : z μ ≠ 0) :
    ∃ z' : Fin d → ℤ, ∑ i, (z' i).natAbs + 1 = ∑ i, (z i).natAbs ∧ ‖z'‖ ≤ ‖z‖ ∧
      (z' = z - Pi.single μ 1 ∨ z' = z + Pi.single μ 1) := by
  have key : ∀ (ε : ℤ), (z μ + ε).natAbs + 1 = (z μ).natAbs →
      (∑ i, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs + 1 = ∑ i, (z i).natAbs ∧
        ‖z + (Pi.single μ ε : Fin d → ℤ)‖ ≤ ‖z‖) := by
    intro ε hε
    constructor
    · have e1 : ∑ i, (z i).natAbs = (z μ).natAbs + ∑ i ∈ Finset.univ.erase μ, (z i).natAbs :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
      have e2 : ∑ i, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs = ((z + (Pi.single μ ε : Fin d → ℤ)) μ).natAbs +
          ∑ i ∈ Finset.univ.erase μ, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
      have e3 : ∑ i ∈ Finset.univ.erase μ, ((z + (Pi.single μ ε : Fin d → ℤ)) i).natAbs =
          ∑ i ∈ Finset.univ.erase μ, (z i).natAbs :=
        Finset.sum_congr rfl fun i hi => by
          simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
      have e4 : ((z + (Pi.single μ ε : Fin d → ℤ)) μ).natAbs = (z μ + ε).natAbs := by simp
      omega
    · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      by_cases hi : i = μ
      · subst hi
        simp only [Pi.add_apply, Pi.single_eq_same, Int.norm_eq_abs]
        have h1 : (z i + ε).natAbs ≤ (z i).natAbs := by omega
        have h2 := norm_le_pi_norm z i
        rw [Int.norm_eq_abs] at h2
        exact (abs_cast_le_of_natAbs_le h1).trans h2
      · simpa [Pi.single_eq_of_ne hi] using norm_le_pi_norm z i
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · obtain ⟨h1, h2⟩ := key 1 (by omega)
    exact ⟨z + Pi.single μ 1, h1, h2, Or.inr rfl⟩
  · obtain ⟨h1, h2⟩ := key (-1) (by omega)
    refine ⟨z + Pi.single μ (-1), h1, h2, Or.inl ?_⟩
    rw [Pi.single_neg, sub_eq_add_neg]

theorem exists_pathCost_lift (G : GeneratingSet d L N₀ k ϱ) (c : Torus d (N₀ * L ^ k))
    {R m : ℝ} (hm : 0 < m)
    (hΩ : ∀ z : Fin d → ℤ, ‖z‖ ≤ R → liftPt c z ∈ G.Ω 1)
    (hsp : ∀ z : Fin d → ℤ, ‖z‖ ≤ R → m ≤ G.spacing (liftPt c z)) :
    ∀ (N : ℕ) (z : Fin d → ℤ), ∑ i, (z i).natAbs = N → ‖z‖ ≤ R →
      ∃ t : ℝ, t ≤ N / m ∧ G.PathCost (liftPt c z) c t := by
  intro N
  induction N with
  | zero =>
      intro z hz hzR
      have h0 : z = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff.1 hz) i (Finset.mem_univ i)
        simpa using this
      subst h0
      refine ⟨0, by simp, ?_⟩
      rw [liftPt_zero]
      refine GeneratingSet.PathCost.refl c ?_
      have := hΩ 0 (by simpa using hzR)
      rwa [liftPt_zero] at this
  | succ N ih =>
      intro z hz hzR
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => (z i).natAbs) (by rw [hz]; omega)
      have hzμ : z μ ≠ 0 := by
        intro h; apply hμ; simp [h]
      obtain ⟨z', hsum, hnorm, hz'⟩ := exists_descent z μ hzμ
      obtain ⟨t, ht, hp⟩ := ih z' (by omega) (hnorm.trans hzR)
      have hadj : Adj (liftPt c z) (liftPt c z') := by
        rcases hz' with rfl | rfl
        · exact ⟨μ, Or.inr (by rw [liftPt_sub_single]; abel)⟩
        · exact ⟨μ, Or.inl (liftPt_add_single c z μ)⟩
      refine ⟨G.bondCost (liftPt c z) (liftPt c z') + t, ?_,
        GeneratingSet.PathCost.step _ _ _ _ (hΩ z hzR) hadj hp⟩
      have hb : G.bondCost (liftPt c z) (liftPt c z') ≤ 1 / m :=
        (G.bondCost_le_inv_left _ _).trans
          (one_div_le_one_div_of_le hm (hsp z hzR))
      push_cast
      calc _ ≤ 1 / m + N / m := add_le_add hb ht
        _ = _ := by ring

/-- **Lemma 4.3 (d).**  The lifted ball of `ℓ¹` radius `≤ L^{j-1}` around a layer-`j` point
(`j ≥ 2`) lies in `Ω₁` and its sites have spacing between `L^{j-1}` and `L^{j+1}`. -/
theorem lift_mem_layers (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {j : ℕ} (hj2 : 2 ≤ j)
    (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {z : Fin d → ℤ}
    (hz : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (j - 1)) :
    liftPt x z ∈ G.Ω 1 ∧ (L : ℝ) ^ (j - 1) ≤ G.spacing (liftPt x z) ∧
      G.spacing (liftPt x z) ≤ (L : ℝ) ^ (j + 1) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hdist := torusDist_liftPt_le x z
  set p := liftPt x z with hp
  have hxΩ : x ∈ G.Ω j := (G.mem_layer.1 hx).1
  have hxn : x ∉ G.Ω (j + 1) := (G.mem_layer.1 hx).2
  -- p ∈ Ω_{j-1}
  have hpA : p ∈ G.Ω (j - 1) := by
    by_contra hnp
    have hs := G.separation (j - 1) (by omega) (by omega) p hnp x (by
      have : j - 1 + 1 = j := by omega
      rw [this]; exact hxΩ)
    rw [torusDist_comm'] at hs
    have h1 : (L : ℝ) ^ (j - 1) ≤ ϱ * (L : ℝ) ^ (j - 1) :=
      le_mul_of_one_le_left (by positivity) hϱ
    linarith
  have hpΩ : p ∈ G.Ω 1 := G.Ω_antitone le_rfl (by omega) (by omega) hpA
  obtain ⟨hm1, hmk, hpl⟩ := G.layerIndex_spec hpΩ
  set m := G.layerIndex p with hm
  have hmlo : j - 1 ≤ m := by
    by_contra hlt
    have hpl' := G.mem_layer.1 hpl
    exact hpl'.2 (G.Ω_antitone (by omega) (by omega) (by omega) hpA)
  have hmhi : m ≤ j + 1 := by
    by_contra hgt
    have hpl' := G.mem_layer.1 hpl
    have hpA2 : p ∈ G.Ω (j + 2) := G.Ω_antitone (by omega) (by omega) (by omega) hpl'.1
    have hs := G.separation (j + 1) (by omega) (by omega) x hxn p hpA2
    have h1 : (L : ℝ) ^ (j - 1) ≤ (L : ℝ) ^ (j + 1) := pow_le_pow_right₀ hL (by omega)
    have h2 : (L : ℝ) ^ (j + 1) ≤ ϱ * (L : ℝ) ^ (j + 1) :=
      le_mul_of_one_le_left (by positivity) hϱ
    linarith
  refine ⟨hpΩ, ?_, ?_⟩
  · rw [G.spacing_eq hm1 hmk hpl]
    exact pow_le_pow_right₀ hL hmlo
  · rw [G.spacing_eq hm1 hmk hpl]
    exact pow_le_pow_right₀ hL hmhi

end Balaban.Multiscale
