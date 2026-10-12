/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.BoxCube
public import Balaban.Localization.ReflectionOperator
public import Balaban.Multiscale.PointwiseLift
public import Balaban.Multiscale.CutOperator

/-!
# Local geometry of the fold of a cube (VMOD-9, Lemma 2.1)

For the coordinate cube `Λ = cubeSet ℓ S c` (`ℓ = N₀ L^k`) of the torus and a preimage `p₀` of a point
`x ∈ Λ` under the fold `foldMap` of the doubled torus `(ℤ/2Sℤ)^d`, the local fold is
`P(z) = foldMap (p₀ + z)`, `z ∈ ℤ^d` (`cubeFoldPt`).

* `cubeFoldPt_disp`: `P(z)` is the lift of `x = P(0)` by a displacement `h` with `‖h‖ ≤ ‖z‖`;
* `side_ge_of_blockAligned`: a block-aligned cube meeting the layer `j` has side `S ≥ L^j`;
* `dblPt_injOn`, `card_fibre_cubeFoldPt_le`, `sum_cubeFoldPt_le`: `P` has multiplicity at most `2^d`
  on a ball of radius `< S`;
* `exists_lowerHalf`: a preimage `p₀` of `x` in the lower half, so that the forward folded neighbours
  of `x` are the retained neighbours (`cubeFoldPt_single_up`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Reflection Balaban.LatticeGreen Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The point `p₀ + z` of the doubled torus `(ℤ/2Sℤ)^d`. -/
def dblPt (S : ℕ) (p0 : Torus d (2 * S)) (z : Fin d → ℤ) : Torus d (2 * S) :=
  p0 + fun i => ((z i : ℤ) : ZMod (2 * S))

/-- **The local fold** `P(z) = foldMap (p₀ + z)` of a cube `{c + t : t < S}^d`. -/
def cubeFoldPt (N₀ L k S : ℕ) (c : Fin d → ℕ) (p0 : Torus d (2 * S)) (z : Fin d → ℤ) :
    Torus d (N₀ * L ^ k) :=
  foldMap (N₀ * L ^ k) S (2 * S) c (dblPt S p0 z)

theorem dblPt_zero (S : ℕ) (p0 : Torus d (2 * S)) : dblPt S p0 0 = p0 := by
  funext i
  simp [dblPt]

theorem dblPt_add_single (S : ℕ) (p0 : Torus d (2 * S)) (z : Fin d → ℤ) (μ : Fin d) :
    dblPt S p0 (z + Pi.single μ 1) = dblPt S p0 z + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [dblPt]; ring
  · simp [dblPt, h]

theorem dblPt_sub_single (S : ℕ) (p0 : Torus d (2 * S)) (z : Fin d → ℤ) (μ : Fin d) :
    dblPt S p0 (z - Pi.single μ 1) = dblPt S p0 z - Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [dblPt]; ring
  · simp [dblPt, h]

omit [NeZero N₀] [NeZero L] in
theorem cubeFoldPt_zero (S : ℕ) (c : Fin d → ℕ) (p0 : Torus d (2 * S)) :
    cubeFoldPt N₀ L k S c p0 0 = foldMap (N₀ * L ^ k) S (2 * S) c p0 := by
  unfold cubeFoldPt
  rw [dblPt_zero]

theorem cubeFoldPt_mem (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (z : Fin d → ℤ) : cubeFoldPt N₀ L k S c p0 z ∈ cubeSet (N₀ * L ^ k) S c :=
  foldMap_mem_cubeSet (m := 2 * S) rfl _

/-- **Displacement.** The local fold moves a point by at most the displacement of `z`:
`P(z)` is the lift of `x = P(0)` by some `h` with `‖h‖ ≤ ‖z‖`. -/
theorem cubeFoldPt_disp (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (z : Fin d → ℤ) :
    ∃ h : Fin d → ℤ, ‖h‖ ≤ ‖z‖ ∧
      cubeFoldPt N₀ L k S c p0 z = liftPt (cubeFoldPt N₀ L k S c p0 0) h := by
  classical
  have hS : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  refine ⟨fun i => Green.cycRep (fold1 (N₀ * L ^ k) S (c i) (2 * S) (dblPt S p0 z i) -
    fold1 (N₀ * L ^ k) S (c i) (2 * S) (dblPt S p0 0 i)), ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have h1 := natAbs_cycRep_fold1_le (ℓ := N₀ * L ^ k) (c := c i) (m := 2 * S) rfl hS
      (dblPt S p0 z i) (dblPt S p0 0 i)
    have h2 : (Green.cycRep (dblPt S p0 z i - dblPt S p0 0 i)).natAbs ≤ (z i).natAbs :=
      Green.natAbs_cycRep_le_of_cast _ _ (by simp [dblPt])
    have h3 : ((z i).natAbs : ℝ) ≤ ‖z‖ := by
      have := norm_le_pi_norm z i
      rw [Int.norm_eq_abs] at this
      rwa [Nat.cast_natAbs, Int.cast_abs]
    have h4 := (h1.trans h2)
    have h5 : (((Green.cycRep (fold1 (N₀ * L ^ k) S (c i) (2 * S) (dblPt S p0 z i) -
        fold1 (N₀ * L ^ k) S (c i) (2 * S) (dblPt S p0 0 i))).natAbs : ℕ) : ℝ) ≤ ‖z‖ :=
      (Nat.cast_le.2 h4).trans h3
    rw [Int.norm_eq_abs]
    rwa [Nat.cast_natAbs, Int.cast_abs] at h5
  · funext i
    simp only [liftPt, Pi.add_apply, Green.cast_cycRep]
    change fold1 (N₀ * L ^ k) S (c i) (2 * S) (dblPt S p0 z i) = fold1 (N₀ * L ^ k) S (c i) (2 * S)
      (dblPt S p0 0 i) + _
    ring

/-- A cube is contained in an image of `S^d` points. -/
theorem card_cubeSet_le (ℓ S : ℕ) [NeZero ℓ] (c : Fin d → ℕ) :
    (cubeSet ℓ S c).card ≤ S ^ d := by
  classical
  have hsub : cubeSet ℓ S c ⊆ (Finset.univ : Finset (Fin d → Fin S)).image
      (fun t : Fin d → Fin S => fun i => (((c i + (t i : ℕ) : ℕ)) : ZMod ℓ)) := by
    intro x hx
    have h := mem_cubeSet.1 hx
    choose t ht hxt using h
    refine Finset.mem_image.2 ⟨fun i => ⟨t i, ht i⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact (hxt i).symm
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp

/-- **Lemma 2.1 (side).** A block-aligned cube that meets the layer `j` has side `S ≥ L^j`. -/
theorem side_ge_of_blockAligned (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {S : ℕ}
    {c : Fin d → ℕ} (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c)) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c) : L ^ j ≤ S := by
  have hsub : G.blk j x ⊆ cubeSet (N₀ * L ^ k) S c := by
    intro x' hx'
    exact (hΛ j hj1 hjk x x' hx (GeneratingSet.mem_blk.1 hx')).1 hxΛ
  have h1 := Finset.card_le_card hsub
  rw [card_blk G j hjk x] at h1
  have h2 := h1.trans (card_cubeSet_le (N₀ * L ^ k) S c)
  exact (Nat.pow_le_pow_iff_left hd.ne').1 h2

theorem dblPt_injOn (S : ℕ) (p0 : Torus d (2 * S)) {z z' : Fin d → ℤ} {R : ℝ} (hz : ‖z‖ ≤ R)
    (hz' : ‖z'‖ ≤ R) (hR : 2 * R < ((2 * S : ℕ) : ℝ)) (h : dblPt S p0 z = dblPt S p0 z') :
    z = z' := by
  funext i
  have h1 := congrFun h i
  simp only [dblPt, Pi.add_apply, add_right_inj] at h1
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (z i) (z' i) (2 * S)).1 h1
  have h3 : |((z' i - z i : ℤ) : ℝ)| < ((2 * S : ℕ) : ℝ) := by
    have a := norm_le_pi_norm z i
    have b := norm_le_pi_norm z' i
    rw [Int.norm_eq_abs] at a b
    rw [Int.cast_sub]
    calc |((z' i : ℤ) : ℝ) - (z i : ℝ)| ≤ |(z' i : ℝ)| + |(z i : ℝ)| := abs_sub _ _
      _ < _ := by linarith
  have h4 : |z' i - z i| < ((2 * S : ℕ) : ℤ) := by
    rw [← Int.cast_abs] at h3
    exact_mod_cast h3
  have h5 := Int.eq_zero_of_abs_lt_dvd h2 h4
  omega

/-- The fibre of the fold of the doubled torus has at most `2^d` points. -/
theorem card_foldMap_fibre_le (S : ℕ) [NeZero S] {ℓ : ℕ} [NeZero ℓ] (hSℓ : S < ℓ)
    (c : Fin d → ℕ) (p1 : Torus d (2 * S)) :
    (Finset.univ.filter fun p : Torus d (2 * S) =>
      foldMap ℓ S (2 * S) c p = foldMap ℓ S (2 * S) c p1).card ≤ 2 ^ d := by
  classical
  have hsub : (Finset.univ.filter fun p : Torus d (2 * S) =>
      foldMap ℓ S (2 * S) c p = foldMap ℓ S (2 * S) c p1) ⊆
      Fintype.piFinset (fun i => ({p1 i, -1 - p1 i} : Finset (ZMod (2 * S)))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Fintype.mem_piFinset]
    intro i
    have := fold1_fibre (c := c i) (m := 2 * S) (ℓ := ℓ) rfl hSℓ (a := p1 i) (b := p i)
      (congrFun hp.2.symm i)
    rcases this with h | h
    · simp [h]
    · simp [h]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc _ ≤ ∏ _i : Fin d, 2 := Finset.prod_le_prod fun i _ => Finset.card_le_two
    _ = 2 ^ d := by simp

/-- **Multiplicity.** The local fold has at most `2^d` preimages in a ball of radius `R < S`. -/
theorem card_fibre_cubeFoldPt_le (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hSℓ : S < N₀ * L ^ k) {R : ℝ} (hR0 : 0 ≤ R) (hRS : R < S) (y : Torus d (N₀ * L ^ k)) :
    ((latticeBall (0 : Fin d → ℤ) R).filter
      fun z => cubeFoldPt N₀ L k S c p0 z = y).card ≤ 2 ^ d := by
  classical
  by_cases hne : ((latticeBall (0 : Fin d → ℤ) R).filter
      fun z => cubeFoldPt N₀ L k S c p0 z = y).Nonempty
  · obtain ⟨z₁, hz₁⟩ := hne
    rw [Finset.mem_filter] at hz₁
    refine le_trans ?_ (card_foldMap_fibre_le S hSℓ c (dblPt S p0 z₁))
    refine Finset.card_le_card_of_injOn (dblPt S p0) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        have h1 : foldMap (N₀ * L ^ k) S (2 * S) c (dblPt S p0 z) = y := hz.2
        have h2 : foldMap (N₀ * L ^ k) S (2 * S) c (dblPt S p0 z₁) = y := hz₁.2
        rw [h1, h2]⟩
    · intro z hz z' hz' h
      rw [Finset.mem_coe, Finset.mem_filter, mem_latticeBall hR0, sub_zero] at hz hz'
      exact dblPt_injOn S p0 hz.1 hz'.1 (by push_cast; linarith) h
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp

/-- **Multiplicity, sum form.** -/
theorem sum_cubeFoldPt_le (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hSℓ : S < N₀ * L ^ k) {R : ℝ} (hR0 : 0 ≤ R) (hRS : R < S)
    (g : Torus d (N₀ * L ^ k) → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ z ∈ latticeBall (0 : Fin d → ℤ) R, g (cubeFoldPt N₀ L k S c p0 z) ≤
      2 ^ d * ∑ y ∈ (latticeBall (0 : Fin d → ℤ) R).image (cubeFoldPt N₀ L k S c p0), g y := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := latticeBall (0 : Fin d → ℤ) R)
    (t := (latticeBall (0 : Fin d → ℤ) R).image (cubeFoldPt N₀ L k S c p0))
    (g := cubeFoldPt N₀ L k S c p0) (fun z hz => Finset.mem_image_of_mem _ hz), Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.1 hz).2]), Finset.sum_const,
    nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_fibre_cubeFoldPt_le S c p0 hSℓ hR0 hRS y)
    (hg y)

/-- A preimage of `x` under the fold in the lower half of the doubled torus. -/
theorem exists_lowerHalf {ℓ S : ℕ} [NeZero ℓ] [NeZero S] {c : Fin d → ℕ} {x : Torus d ℓ}
    (hx : x ∈ cubeSet ℓ S c) :
    ∃ p0 : Torus d (2 * S), foldMap ℓ S (2 * S) c p0 = x ∧ ∀ i, (p0 i).val < S := by
  classical
  have h := mem_cubeSet.1 hx
  choose t ht hxt using h
  have hv : ∀ i, (((t i : ℕ) : ZMod (2 * S))).val = t i := fun i => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ht i; omega)]
  refine ⟨fun i => ((t i : ℕ) : ZMod (2 * S)), ?_, fun i => by rw [hv i]; exact ht i⟩
  funext i
  show fold1 ℓ S (c i) (2 * S) _ = x i
  rw [fold1_eq, hv i, hxt i]
  simp [foldNat, ht i]

/-- With `p₀` in the lower half, the forward folded neighbour of `x = P(0)` is the retained
neighbour `x + e_μ` when it stays in the cube, and `x` itself at an upper face. -/
theorem cubeFoldPt_single_up (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hSℓ : S < N₀ * L ^ k) (hp0 : ∀ i, (p0 i).val < S) (μ : Fin d) :
    cubeFoldPt N₀ L k S c p0 (Pi.single μ 1) =
      stepUpT (cubeSet (N₀ * L ^ k) S c) (cubeFoldPt N₀ L k S c p0 0) μ := by
  have hS : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  have h1 := (foldMap_nbr_low (ℓ := N₀ * L ^ k) (c := c) (m := 2 * S) rfl hS hSℓ p0 μ (hp0 μ)).1
  have e : dblPt S p0 (Pi.single μ 1) = p0 + Pi.single μ 1 := by
    have := dblPt_add_single S p0 0 μ
    rwa [zero_add, dblPt_zero] at this
  unfold cubeFoldPt
  rw [e, dblPt_zero]
  exact h1

end Balaban.Localization
