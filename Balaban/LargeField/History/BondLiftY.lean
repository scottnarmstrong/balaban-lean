/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.TopBlockTransport
import Balaban.Multiscale.Coercivity
import Balaban.Multiscale.ConstraintComm
import Balaban.Multiscale.Locality
import Balaban.LargeField.Background.CubeUnion
import Mathlib.Tactic.Linarith

/-!
# The bond lift over the small-field region (Q13-COVER, `FactorBondLift` over `Y`)

Setting: scale `k = j + 1`, `Y = Z_kᶜ`, the small-field context `Cx : SFCtx` at scale `k`, the
generating set `G_k = Cx.genW Y = 𝔹_k(W₂(Y))`, and the datum `Cx.liftData ψ_k` (the value of the
datum at a site is the field `ψ_k` at the `k`-block of the site).  The domain of the background
solver asks for the interface condition (R1) at every `IsInterfacePair` of `G_k` and the sphere
condition (R2) at every datum site.  `TopBlockTransport` gives them, with tolerance `3dLδ_{k-1}`,
for the pairs with a site over a retained component of `Z^pre_k`.  This file treats the pairs with
a site over a cube of `Y`, from the characteristic function `χ_k(Y) = chiY ≠ 0`.

## What is proved

* **Classification (T1).**  Let `y₁ ∈ Y` and let `s` be a site over the cube `y₁`.  Since
  `W₂(Y) = nbhd_{2⌊R_{k-1}⌋+2}(Y) ⊇ nbhd_2 {y₁}` and the top layer of `𝔹_k(W₂(Y))` is the fine
  set of the cubes of `W₂(Y)` (`genSF_top_mem`), the site `s` lies in `Ω_k`, hence in the top layer
  `k`, and not in the collar.  For an interface pair `(s, s')` of `G_k` (`interfacePair_over_Y`):
  the partner `s'` lies over a cube within one cube of `y₁`, hence also in the top layer `k`;
  neither site is a collar site; and the pair condition is exactly "the `k`-blocks of `s` and `s'`
  contain adjacent sites" (`isInterfacePair_top_iff`).  There are no pairs of two different layers
  and no collar pairs with a site over `Y`.  Two sites of the same `k`-block form a pair, and so
  do two sites of adjacent `k`-blocks: the pairs `(s, s + e_μ)` exist (`interfacePair_succ_over_Y`,
  `exists_pair_over_Y`).  If the second site is over `Y`, the pair condition is symmetric
  (`isInterfacePair_symm_of_top`).
* **R1 over `Y` (T2).**  Under `chiY ≠ 0`, for an interface pair `(s, s')` with `s` or `s'` over a
  cube `y₁ ∈ Y` (`pair_bound_over_Y_either`, `psi_close_over_Y`)
  `‖Ψ(s) - Ψ(s')‖ < 3 δ_k`, `Ψ` the datum of `G_k` (`ψ_k` at the two top blocks).  The proof takes
  the single-cube background `φ` of `genCube y₁` and splits
  `Ψ(s) - Ψ(s') = (Ψ(s) - Qφ(s)) + (Qφ(s) - Qφ(s')) + (Qφ(s') - Ψ(s'))`.  The outer terms are
  `BlockClose` (`blockDev_lt_of_chiY_ne_zero`, tolerance `δ_k`; the sites `s, s'` lie over
  `nbhd_1 {y₁}`).  For the middle term, two `k`-blocks `B, B'` containing adjacent sites are equal
  or `B' = B + L^k e_μ` (`blocks_of_adj`); in the second case `Qφ(s') - Qφ(s)` is the mean over
  `z ∈ B` of `φ(z + L^k e_μ) - φ(z)`, a sum of `L^k` steps of `φ̄` along the segment from `z` in
  the direction `e_μ`, each of size `< δ_k / L^k` by `GradClose` (`blockAvg_sub_lt`).  The segment
  runs over the cubes of `nbhd_1 {y₁}`: the cube index of `z + t e_μ`, `0 ≤ t ≤ L^k`, equals that
  of `z` or that of `z + L^k e_μ` (`cube_seg`), so all its sites are over `nbhd_1 {y₁}`, in the top
  layer of `genCube y₁`, in the stencil `cubeNbhd 1 y₁` of `BlockClose`/`GradClose`.  No premise on
  the geometry is needed beyond `y₁ ∈ Y`.  The datum of the cube and that of `G_k` agree at the
  sites (`cubeData_Ψ_eq_liftSingle_Ψ`).  **The constant is `C = 3`, independent of `d` and `L`.**
* **R2 over `Y` (T4).**  Under `chiY ≠ 0` and the landed numeric premise `BgHyp` of the background
  solver (weights, `0 ≤ ν`, `ν L^{2k} ≤ 1`, `ϱ ≥ bgR0`), for `s` over `y₁ ∈ Y`:
  `| ‖ψ_k(b(s))‖ - 1 | < (d + 1) δ_k` (`sphere_over_Y`) and
  `| ‖ψ_k(b(s))‖² - 1 | < (d + 1) δ_k (2 + (d + 1) δ_k)` (`sphere_sq_over_Y`; this is
  `< 3 (d + 1) δ_k` when `(d + 1) δ_k ≤ 1`).  The proof uses the `InUnionDomainR` conjunct of the
  `Reg` of the cube, only through Theorem 7.1/7.2 of the background (real unit field, `bgFieldC =
  bgField`): the background is a field of unit vectors; the block average `Qφ(s)` is within `d δ_k`
  of the unit vector `φ(c)` at the corner `c` of the block of `s` (`blockAvg_near_corner`: each of
  the at most `d L^k` unit steps from a site of the block to its corner costs `< δ_k / L^k`,
  `corner_close`), and `‖Ψ(s) - Qφ(s)‖ < δ_k` by `BlockClose`.  The constant is `C' = d + 1`.
* **Non-vacuity (T5, partial).**  `exists_pair_over_Y` gives, for any `Cx`, a set `Y = {0}`, the site
  `s = 0` over `y₁ = 0`, and the pair `(0, e_μ)`, with all the properties of the classification;
  `multi_pair_over_Y_instance` is this statement on the landed multi-cube context `ctxMulti`.
  `chiY ≠ 0` is not exhibited on `ctxMulti`; see below.

## Which pairs are covered

Every datum site of `G_k` lies over a cube of `Y` or over a cube of `Z_k`.  A site over a cube of
`Y` is never a collar site.  (a) Pairs with a site over `Y`: covered by `pair_bound_over_Y_either`
(`3 δ_k`).  (b) Pairs with a site over a retained component: `chiDomAt_pair_bounds`
(`3 d L δ_{k-1}`).  (c) Pairs with both sites over `Z_k` and no site over a retained component, if
there are any (this holds when every cube of `Z_k` lies in a retained component of `Z^pre_k`; a
removed component belongs to `Y`, `Q13-COVER` §1; this inclusion is not proved here): not covered.
Nothing in this file covers collar pairs with both sites over `Z_k`.  What was expected to be
uncovered over `Y` (bonds leaving `Ω₁` of the single-cube background, blocks in the stencils of two
different cubes) does not occur: the partner of a site over `y₁ ∈ Y` is in the stencil `nbhd_1
{y₁}`, in the top layer of both `G_k` and `genCube y₁`.

## What is not proved

* The pairs of class (c) above, the `ActiveFactor` statement (that the datum of the small-field
  factor in the integrand is `Cx.liftData (outField o)`), and the transfer to the composed
  inherited fields `ψ^{(j)}_k` (`psiJ`) of older scales: the bounds here concern the `k`-block
  field `ψ_k`.
* The strict-margin statements: comparison of the background of `G_k` with the cube backgrounds
  (the eight `StrictData` tests); the numbers `3 d L δ_{k-1}` (from the history, in
  `chiDomAt_pair_bounds`) and `3 δ_k`, `(d+1) δ_k` (from `chiY`, here) are different tolerances and
  are only recorded.  Both are bounds on `Ψ`; neither is a bound on the background of `G_k`.
* The non-vacuity of `chiY ≠ 0`.  On `ctxMulti` the small-field data and the weights are those of
  the landed witness; `chiY ≠ 0` for the constant field `ψ_k ≡ e₀` (with `hv = e₀`) needs that the
  background `bgFieldC` of the cube `genCube y₁` with constant unit data is the constant field with
  multiplier `0` (the constant is a small solution of (EL) for data equal to it: the Dirichlet part
  of the operator on a constant field cancels the boundary term, `Q* a Q` fixes constants), and
  the `BgHyp` premises for `ctxMulti` (admissible weights, `ϱ = bgR0`, `ν L^{2k} ≤ 1`).  Neither
  is landed for the cube generating sets (`StepActivityWitnessMin` treats whole-lattice sets).
  This ingredient is missing; the quantities `BlockClose`/`GradClose` would then vanish.
* The theorems hold with the stencil/mass conventions of the landed `Reg`.  The pair bound `C = 3`
  and the classification use only `BlockClose`, `GradClose` and the top-layer structure of
  `𝔹_k`; nothing depends on the mass convention of the backgrounds.  The sphere bound uses the
  mass only through the landed numeric premise `BgHyp` of Theorem 7.1.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section Coord
variable {ℓ N m : ℕ} [NeZero ℓ]

/-- Moving a coordinate by one block side `N` raises the block coordinate by one. -/
theorem blockCoord_add_block (hℓ : ℓ = N * m) (hN : 0 < N) (a : ZMod ℓ) :
    blockCoord N m (a + (N : ZMod ℓ)) = blockCoord N m a + 1 := by
  have key : ∀ x : ℕ, x % ℓ / N = x / N % m := fun x => by
    subst hℓ; exact Nat.mod_mul_right_div_self _ _ _
  have e : a + (N : ZMod ℓ) = ((a.val + N : ℕ) : ZMod ℓ) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have hv : (a + (N : ZMod ℓ)).val = (a.val + N) % ℓ := by
    rw [e, ZMod.val_natCast]
  unfold blockCoord
  rw [hv, key, Nat.add_div_right _ hN, ZMod.natCast_mod]
  push_cast; rfl

/-- Moving a coordinate on the last site of its block by one step raises the block coordinate by one. -/
theorem blockCoord_add_one_top (hℓ : ℓ = N * m) (hN : 0 < N) (a : ZMod ℓ)
    (h : a.val % N + 1 = N) :
    blockCoord N m (a + 1) = blockCoord N m a + 1 := by
  have key : ∀ x : ℕ, x % ℓ / N = x / N % m := fun x => by
    subst hℓ; exact Nat.mod_mul_right_div_self _ _ _
  have e : a + 1 = ((a.val + 1 : ℕ) : ZMod ℓ) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have hv : (a + 1).val = (a.val + 1) % ℓ := by
    rw [e, ZMod.val_natCast]
  have h2 : (a.val + 1) / N = a.val / N + 1 := by
    have h3 := Nat.div_add_mod a.val N
    have : a.val + 1 = N * (a.val / N + 1) := by
      rw [mul_add, mul_one]; omega
    rw [this, Nat.mul_div_cancel_left _ hN]
  unfold blockCoord
  rw [hv, key, h2, ZMod.natCast_mod]
  push_cast; rfl

end Coord

section Generic
variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The shift by one side `L^k` of a `k`-block in the direction `e_μ`. -/
def blockShift (d L N₀ k : ℕ) (μ : Fin d) : Torus d (N₀ * L ^ k) :=
  (L ^ k) • Pi.single μ (1 : ZMod (N₀ * L ^ k))

/-- Shifting a site by `L^k e_μ` moves its `k`-block to the neighbouring `k`-block in the direction `e_μ`. -/
theorem jBlock_top_add_shift (μ : Fin d) (z : Torus d (N₀ * L ^ k)) :
    jBlock d L N₀ k k (z + blockShift d L N₀ k μ) = jBlock d L N₀ k k z + Pi.single μ 1 := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L))
  funext i
  unfold jBlock
  simp only [blockMap_apply, Pi.add_apply]
  by_cases hi : i = μ
  · subst hi
    have : blockShift d L N₀ k i i = ((L ^ k : ℕ) : ZMod (N₀ * L ^ k)) := by
      simp [blockShift]
    rw [this]
    simpa using blockCoord_add_block (side_eq (N₀ := N₀) (L := L) (k := k) (j := k) le_rfl) hN (z i)
  · simp [blockShift, hi]

/-- A step `e_μ` from a site on the last layer of its `k`-block in the direction `e_μ` goes to the neighbouring `k`-block. -/
theorem jBlock_add_one_top (μ : Fin d) (y : Torus d (N₀ * L ^ k))
    (h : (y μ).val % L ^ k + 1 = L ^ k) :
    jBlock d L N₀ k k (y + Pi.single μ 1) = jBlock d L N₀ k k y + Pi.single μ 1 := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L))
  funext i
  unfold jBlock
  simp only [blockMap_apply, Pi.add_apply]
  by_cases hi : i = μ
  · subst hi
    simpa using blockCoord_add_one_top (side_eq (N₀ := N₀) (L := L) (k := k) (j := k) le_rfl) hN (y i) h
  · simp [hi]

end Generic

section Avg
open Finset
variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The norm of a constant times a finite sum of vectors is at most the modulus of the constant times the sum of the norms. -/
theorem vn_smul_sum_le {ι : Type*} (c : ℂ) (B : Finset ι) (W : ι → Fin N → ℂ) :
    vn (fun i => c * ∑ z ∈ B, W z i) ≤ ‖c‖ * ∑ z ∈ B, vn (W z) := by
  have e : (WithLp.toLp 2 (fun i => c * ∑ z ∈ B, W z i) : EuclideanSpace ℂ (Fin N)) =
      c • ∑ z ∈ B, (WithLp.toLp 2 (W z) : EuclideanSpace ℂ (Fin N)) := by
    ext i
    simp [Finset.sum_apply]
  unfold vn
  rw [e, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)

/-- Telescoping bound: the norm of `F n - F 0` is at most the sum of the norms of the increments. -/
theorem vn_telescope (F : ℕ → Fin N → ℂ) (n : ℕ) :
    vn (F n - F 0) ≤ ∑ t ∈ range n, vn (F (t + 1) - F t) := by
  induction n with
  | zero => simp [vn_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := vn_triangle (F (n + 1)) (F n) (F 0)
    linarith

/-- On `Ω₁` the zero extension of the field `φ` agrees with its extension `φ̄` by the data. -/
theorem svec_eq_barVec {G : GeneratingSet d L N₀ k ϱ} (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) : svec G φ x = barVec G D φ x := by
  funext i
  simp [svec, zeroExt, barVec, barField, hx]

end Avg

section Main
open Finset
variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- If the `k`-block of `s` is the translate by `-L^k e_μ` of that of `s'`, and the segments of length `L^k` in the direction `e_μ` from the sites of the block of `s` run through sites of `S ∩ Ω₁` where `GradClose` holds with tolerance `δ`, then the block averages of the field differ by less than `δ`: the difference is the mean over the block of `L^k` steps, each of norm `< δ / L^k`. -/
theorem blockAvg_sub_lt (G : GeneratingSet d L N₀ k ϱ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (S : Finset (Torus d (N₀ * L ^ k))) (δ : ℝ)
    (hk : 1 ≤ k) (hgrad : GradClose G D φ α ((L : ℝ) ^ k) S δ)
    {s s' : Torus d (N₀ * L ^ k)} (hs : s ∈ G.layer k) (hs' : s' ∈ G.layer k) (μ : Fin d)
    (htr : ∀ z, z ∈ G.blk k s ↔ z + blockShift d L N₀ k μ ∈ G.blk k s')
    (hseg : ∀ z ∈ G.blk k s, ∀ t : ℕ, t ≤ L ^ k →
      z + t • Pi.single μ (1 : ZMod (N₀ * L ^ k)) ∈ S ∧
      z + t • Pi.single μ (1 : ZMod (N₀ * L ^ k)) ∈ G.Ω 1) :
    vn (fun i => blockAvg G φ s i - blockAvg G φ s' i) < δ := by
  classical
  have hLpos : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hNpos : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L))
  have hi : G.layerIndex s = k := G.layerIndex_eq hk le_rfl hs
  have hi' : G.layerIndex s' = k := G.layerIndex_eq hk le_rfl hs'
  set c : ℂ := ((((((L : ℝ) ^ k) ^ d)⁻¹ : ℝ) : ℂ)) with hc
  have hsum : ∀ i, ∑ y ∈ G.blk k s', svec G φ y i =
      ∑ z ∈ G.blk k s, svec G φ (z + blockShift d L N₀ k μ) i := by
    intro i
    refine Finset.sum_nbij' (fun y => y - blockShift d L N₀ k μ)
      (fun z => z + blockShift d L N₀ k μ) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      exact (htr _).2 (by simpa using hy)
    · intro z hz
      exact (htr z).1 hz
    · intro y _; simp
    · intro z _; simp
    · intro y _; simp
  have hdiff : (fun i => blockAvg G φ s i - blockAvg G φ s' i) =
      fun i => c * ∑ z ∈ G.blk k s, (svec G φ z - svec G φ (z + blockShift d L N₀ k μ)) i := by
    funext i
    unfold blockAvg
    rw [hi, hi', hsum i]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
    rfl
  rw [hdiff]
  have hB : (G.blk k s).Nonempty := ⟨s, G.mem_blk.2 rfl⟩
  have hcard : ((G.blk k s).card : ℝ) = ((L : ℝ) ^ k) ^ d := card_blk_cast G k le_rfl s
  have hcn : ‖c‖ = (((L : ℝ) ^ k) ^ d)⁻¹ := by
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- the pointwise bound
  have hpt : ∀ z ∈ G.blk k s, vn (svec G φ z - svec G φ (z + blockShift d L N₀ k μ)) < δ := by
    intro z hz
    set F : ℕ → Fin N → ℂ := fun t => svec G φ (z + t • Pi.single μ (1 : ZMod (N₀ * L ^ k))) with hF
    have h0 : F 0 = svec G φ z := by simp [hF]
    have hN : F (L ^ k) = svec G φ (z + blockShift d L N₀ k μ) := by simp [hF, blockShift]
    have hstep : ∀ t ∈ range (L ^ k), vn (F (t + 1) - F t) < δ / (L : ℝ) ^ k := by
      intro t ht
      have ht' : t < L ^ k := Finset.mem_range.1 ht
      obtain ⟨h1S, h1Ω⟩ := hseg z hz t ht'.le
      obtain ⟨-, h2Ω⟩ := hseg z hz (t + 1) ht'
      have h := (hgrad ⟨_, h1Ω⟩ h1S).1 μ
      have e : z + (t + 1) • Pi.single μ (1 : ZMod (N₀ * L ^ k)) =
          z + t • Pi.single μ (1 : ZMod (N₀ * L ^ k)) + Pi.single μ 1 := by
        rw [succ_nsmul, add_assoc]
      have hF1 : F (t + 1) = barVec G D φ
          (z + t • Pi.single μ (1 : ZMod (N₀ * L ^ k)) + Pi.single μ 1) := by
        simp only [hF]; rw [e]; exact svec_eq_barVec D φ (e ▸ h2Ω)
      have hF0 : F t = barVec G D φ (z + t • Pi.single μ (1 : ZMod (N₀ * L ^ k))) := by
        simp only [hF]; exact svec_eq_barVec D φ h1Ω
      rw [hF1, hF0]
      rw [lt_div_iff₀ hLpos, mul_comm]
      exact h.1
    have hnz : (range (L ^ k)).Nonempty := ⟨0, Finset.mem_range.2 hNpos⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hnz hstep
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
    have hδ : ((L ^ k : ℕ) : ℝ) * (δ / (L : ℝ) ^ k) = δ := by
      push_cast; field_simp
    have := vn_telescope F (L ^ k)
    rw [h0, hN] at this
    rw [vn_sub_comm]
    linarith
  have hsumlt : ∑ z ∈ G.blk k s, vn (svec G φ z - svec G φ (z + blockShift d L N₀ k μ)) <
      ∑ z ∈ G.blk k s, δ := Finset.sum_lt_sum_of_nonempty hB hpt
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsumlt
  calc _ ≤ ‖c‖ * ∑ z ∈ G.blk k s, vn (svec G φ z - svec G φ (z + blockShift d L N₀ k μ)) :=
        vn_smul_sum_le c _ _
    _ < ‖c‖ * (((L : ℝ) ^ k) ^ d * δ) := by
        refine mul_lt_mul_of_pos_left hsumlt ?_
        rw [hcn]; positivity
    _ = δ := by
        rw [hcn]
        have : (((L : ℝ) ^ k) ^ d) ≠ 0 := by positivity
        field_simp
end Main

section Step
variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- A step `e_μ` leads to the same `k`-block or, if it crosses the face, to the translated block; in the second case the blocks differ by the shift `L^k e_μ`. -/
theorem block_step (p : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    jBlock d L N₀ k k (p + Pi.single μ 1) = jBlock d L N₀ k k p ∨
      ∀ z, jBlock d L N₀ k k z = jBlock d L N₀ k k p ↔
        jBlock d L N₀ k k (z + blockShift d L N₀ k μ) = jBlock d L N₀ k k (p + Pi.single μ 1) := by
  by_cases h : (p μ).val % L ^ k + 1 < L ^ k
  · left
    exact blockMap_add_single_of_inner (side_eq (N₀ := N₀) (L := L) (k := k) (j := k) le_rfl) h
  · right
    have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L))
    have htop : (p μ).val % L ^ k + 1 = L ^ k := by
      have := Nat.mod_lt (p μ).val hN
      omega
    intro z
    rw [jBlock_top_add_shift, jBlock_add_one_top μ p htop, add_left_inj]

/-- Two `k`-blocks containing adjacent sites are equal or differ by a shift of `L^k` in one coordinate direction (in one of the two orders). -/
theorem blocks_of_adj {y y' : Torus d (N₀ * L ^ k)} (h : Adj y y') :
    jBlock d L N₀ k k y = jBlock d L N₀ k k y' ∨
      (∃ μ, ∀ z, jBlock d L N₀ k k z = jBlock d L N₀ k k y ↔
        jBlock d L N₀ k k (z + blockShift d L N₀ k μ) = jBlock d L N₀ k k y') ∨
      (∃ μ, ∀ z, jBlock d L N₀ k k z = jBlock d L N₀ k k y' ↔
        jBlock d L N₀ k k (z + blockShift d L N₀ k μ) = jBlock d L N₀ k k y) := by
  obtain ⟨μ, rfl | rfl⟩ := h
  · rcases block_step y μ with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl ⟨μ, h⟩)
  · rcases block_step y' μ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨μ, h⟩)
end Step


section CubeSeg

variable {ℓ P m : ℕ} [NeZero ℓ]

/-- The block coordinate after adding `u` is `⌊(a + u) / P⌋` modulo the number of blocks. -/
theorem blockCoord_add_natCast_val (hℓ : ℓ = P * m) (a : ZMod ℓ) (u : ℕ) :
    blockCoord P m (a + (u : ZMod ℓ)) = (((a.val + u) / P : ℕ) : ZMod m) := by
  have key : ∀ x : ℕ, x % ℓ / P = x / P % m := fun x => by
    subst hℓ; exact Nat.mod_mul_right_div_self _ _ _
  have e : a + (u : ZMod ℓ) = ((a.val + u : ℕ) : ZMod ℓ) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have hv : (a + (u : ZMod ℓ)).val = (a.val + u) % ℓ := by
    rw [e, ZMod.val_natCast]
  unfold blockCoord
  rw [hv, key, ZMod.natCast_mod]

/-- For `t ≤ N ≤ P`, the block coordinate of `a + t` is that of `a` or that of `a + N`. -/
theorem blockCoord_add_nat_cases (hℓ : ℓ = P * m) (hP : 0 < P) (a : ZMod ℓ) {t N : ℕ}
    (ht : t ≤ N) (hN : N ≤ P) :
    blockCoord P m (a + (t : ZMod ℓ)) = blockCoord P m a ∨
      blockCoord P m (a + (t : ZMod ℓ)) = blockCoord P m (a + (N : ZMod ℓ)) := by
  have h0 : blockCoord P m a = ((a.val / P : ℕ) : ZMod m) := rfl
  rw [blockCoord_add_natCast_val hℓ a t, blockCoord_add_natCast_val hℓ a N, h0]
  have h1 : a.val / P ≤ (a.val + t) / P := Nat.div_le_div_right (by omega)
  have h2 : (a.val + t) / P ≤ (a.val + N) / P := Nat.div_le_div_right (by omega)
  have h3 : (a.val + N) / P ≤ a.val / P + 1 := by
    calc (a.val + N) / P ≤ (a.val + P) / P := Nat.div_le_div_right (by omega)
      _ = a.val / P + 1 := Nat.add_div_right _ hP
  rcases (by omega : (a.val + t) / P = a.val / P ∨ (a.val + t) / P = (a.val + N) / P) with h | h
  · left; rw [h]
  · right; rw [h]

end CubeSeg

section CubeSeg2

variable {d L N₀ k P m : ℕ} [NeZero N₀] [NeZero L]

/-- `t` steps in the direction `e_μ` are the unit vector with entry `t`. -/
theorem nsmul_single_eq (μ : Fin d) (t : ℕ) :
    t • Pi.single μ (1 : ZMod (N₀ * L ^ k)) =
      (Pi.single μ (t : ZMod (N₀ * L ^ k)) : Torus d (N₀ * L ^ k)) := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · simp [h]

/-- The `μ`-th coordinate of the shift is `L^k`. -/
theorem blockShift_apply_self (μ : Fin d) :
    blockShift d L N₀ k μ μ = ((L ^ k : ℕ) : ZMod (N₀ * L ^ k)) := by
  simp [blockShift]

/-- The other coordinates of the shift vanish. -/
theorem blockShift_apply_ne {μ i : Fin d} (h : i ≠ μ) : blockShift d L N₀ k μ i = 0 := by
  simp [blockShift, h]

/-- A segment of length `t ≤ L^k` in the direction `e_μ` from `z` stays over the cube of `z` or of `z + L^k e_μ`, for cubes of side `P ≥ L^k`. -/
theorem cube_seg (hℓ : N₀ * L ^ k = P * m) (hP : 0 < P) (hNP : L ^ k ≤ P) (μ : Fin d)
    (z : Torus d (N₀ * L ^ k)) {t : ℕ} (ht : t ≤ L ^ k) :
    blockMap P m (z + t • Pi.single μ 1) = blockMap P m z ∨
      blockMap P m (z + t • Pi.single μ 1) = blockMap P m (z + blockShift d L N₀ k μ) := by
  rcases blockCoord_add_nat_cases hℓ hP (z μ) ht hNP with h | h
  · left
    funext i
    by_cases hi : i = μ
    · subst hi
      simpa [blockMap_apply, nsmul_single_eq] using h
    · simp [blockMap_apply, hi]
  · right
    funext i
    by_cases hi : i = μ
    · subst hi
      simpa [blockMap_apply, nsmul_single_eq, blockShift_apply_self] using h
    · simp [blockMap_apply, hi, blockShift_apply_ne hi]

end CubeSeg2


section TopLayer

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- A site of the top domain `Ω_k` is in the layer `k`. -/
theorem mem_layer_top {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) : x ∈ G.layer k :=
  G.mem_layer.2 ⟨hx, by rw [G.top]; exact Finset.notMem_empty _⟩

/-- A site of `Ω_k` has layer index `k`. -/
theorem layerIndex_top (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) :
    G.layerIndex x = k :=
  G.layerIndex_eq hk le_rfl (mem_layer_top G hx)

/-- `Ω_k ⊆ Ω₁`. -/
theorem mem_Ω_one_of_top (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) :
    x ∈ G.Ω 1 :=
  G.Ω_antitone le_rfl hk (by omega) hx

/-- The block of a site of `Ω_k` is its `k`-block. -/
theorem blockSet_top (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) :
    blockSet G x = G.blk k x := by
  unfold blockSet
  simp only [mem_Ω_one_of_top G hk hx, ↓reduceIte]
  rw [layerIndex_top G hk hx]

/-- For two sites of the top domain `Ω_k`, the pair condition (R1) is exactly that their `k`-blocks contain adjacent sites: the layer indices are both `k`, so no pair of different layers occurs. -/
theorem isInterfacePair_top_iff (hk : 1 ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k)
    (hx' : x' ∈ G.Ω k) :
    IsInterfacePair G x x' ↔ ∃ y ∈ G.blk k x, ∃ y' ∈ G.blk k x', Adj y y' := by
  constructor
  · rintro ⟨-, -, -, y, hy, y', hy', hadj⟩
    rw [blockSet_top G hk hx] at hy
    rw [blockSet_top G hk hx'] at hy'
    exact ⟨y, hy, y', hy', hadj⟩
  · rintro ⟨y, hy, y', hy', hadj⟩
    refine ⟨?_, ?_, Or.inl ?_, y, ?_, y', ?_, hadj⟩
    · exact (mem_dataSites G).2 (Or.inl (mem_Ω_one_of_top G hk hx))
    · exact (mem_dataSites G).2 (Or.inl (mem_Ω_one_of_top G hk hx'))
    · rw [layerIndex_top G hk hx, layerIndex_top G hk hx']
    · rwa [blockSet_top G hk hx]
    · rwa [blockSet_top G hk hx']

/-- If a site in `Ω_k` has all the neighbours of its `k`-block in `Ω_k`, then so has the partner of an interface pair. -/
theorem partner_mem_top (hk : 1 ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k)
    (hp : IsInterfacePair G x x')
    (hnear : ∀ y ∈ G.blk k x, ∀ y', Adj y y' → y' ∈ G.Ω k) : x' ∈ G.Ω k := by
  obtain ⟨-, -, -, y, hy, y', hy', hadj⟩ := hp
  rw [blockSet_top G hk hx] at hy
  have hy'Ω := hnear y hy y' hadj
  have hb := jBlock_top_eq_of_mem_blockSet G hy'
  exact (G.blockUnion k hk le_rfl _ _ hb).1 hy'Ω

/-- A site of `Ω_k` is not in the collar. -/
theorem not_mem_collar_of_top (hk : 1 ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) :
    x ∉ collar G := fun h => ((mem_collar G).1 h).1 (mem_Ω_one_of_top G hk hx)

/-- If the second site of an interface pair lies in `Ω_k`, then so does the first and the pair condition is symmetric. -/
theorem isInterfacePair_symm_of_top (hk : 1 ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (hx' : x' ∈ G.Ω k) (hp : IsInterfacePair G x x') : IsInterfacePair G x' x := by
  obtain ⟨-, -, hidx, -⟩ := id hp
  have hle : G.layerIndex x ≤ k := by
    by_cases hxΩ : x ∈ G.Ω 1
    · exact (G.layerIndex_spec hxΩ).2.1
    · rw [layerIndex_of_not_mem G hxΩ]; omega
  have hx'k := layerIndex_top G hk hx'
  have hxk : G.layerIndex x = k := by omega
  have hxΩ : x ∈ G.Ω 1 := by
    by_contra h
    rw [layerIndex_of_not_mem G h] at hxk
    omega
  have hxl := (G.layerIndex_spec hxΩ).2.2
  rw [hxk] at hxl
  have hx : x ∈ G.Ω k := (G.mem_layer.1 hxl).1
  obtain ⟨y, hy, y', hy', hadj⟩ := (isInterfacePair_top_iff G hk hx hx').1 hp
  exact (isInterfacePair_top_iff G hk hx' hx).2 ⟨y', hy', y, hy, hadj.symm⟩

end TopLayer

section TopSF

variable {d M1 N₁ L q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- The top domain of `𝔹_q(W)` is the fine set of the cubes of `W`. -/
theorem genSF_top_mem (hm : N₁ * L ^ (q - q) = c * n) (W : Set (Torus d n))
    {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W).Ω q ↔
      blockMap (L ^ q * (c * M1)) n x ∈ W := by
  show x ∈ minLayer M1 N₁ L q q _ q ↔ _
  rw [minLayer_self, (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q) (le_refl q) hm
    W).cubeInterior_eq, mem_cubePre]

/-- The top domain of the generating set `G_q(y₁)` of a cube is the fine set of the cubes of `nbhd_2 {y₁}`. -/
theorem genCube_top_mem (hm : N₁ * L ^ (q - q) = c * n) (y₁ : Torus d n)
    {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y₁).Ω q ↔
      blockMap (L ^ q * (c * M1)) n x ∈ nbhd 2 {y₁} := by
  rw [genCube_Ω, minLayer_self, (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q)
    (le_refl q) hm (nbhd 2 {y₁})).cubeInterior_eq, mem_cubePre]

/-- Adjacent sites lie over cubes within one cube of each other. -/
theorem cube_adj_near (hm : N₁ * L ^ (q - q) = c * n) (hc : 0 < c * M1)
    {y y' : Torus d (M1 * N₁ * L ^ q)} (h : Adj y y') :
    supDist (blockMap (L ^ q * (c * M1)) n y) (blockMap (L ^ q * (c * M1)) n y') ≤ 1 := by
  have hP : 0 < L ^ q * (c * M1) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (pow_ne_zero q (NeZero.ne L))) hc
  have h2 := supDist_le_torusDist y y'
  have h3 := Multiscale.Adj.torusDist_le h
  have h1 : supDist y y' ≤ 1 := by
    have : (supDist y y' : ℝ) ≤ 1 := h2.trans h3
    exact_mod_cast this
  exact supDist_blockMap_le_one (cube_fine_eq hm) (D := 1) hP y y' h1

end TopSF


section PairBound

variable {d M1 N₁ L q c n N : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- Triangle inequality for `vn` in pointwise form. -/
theorem vn_triangle' (u v w : Fin N → ℂ) :
    vn (fun i => u i - w i) ≤ vn (fun i => u i - v i) + vn (fun i => v i - w i) :=
  vn_triangle u v w

/-- Classification of the interface pairs `(s, s')` with `s` over a cube `y₁` with `nbhd_2 {y₁} ⊆ W`, for a generating set whose top domain is the fine set of `W`: both sites are in the top domain, the cube of `s'` is within one cube of `y₁`, and the `q`-blocks of `s` and `s'` contain adjacent sites. -/
theorem pair_over_cube {ϱk : ℝ} (hm : N₁ * L ^ (q - q) = c * n) (hq : 1 ≤ q)
    (Gk : GeneratingSet d L (M1 * N₁) q ϱk) (W : Set (Torus d n)) (y₁ : Torus d n)
    (hW : nbhd 2 {y₁} ⊆ W)
    (hGk : ∀ x, x ∈ Gk.Ω q ↔ blockMap (L ^ q * (c * M1)) n x ∈ W)
    {s s' : Torus d (M1 * N₁ * L ^ q)} (hs : blockMap (L ^ q * (c * M1)) n s = y₁)
    (hp : IsInterfacePair Gk s s') :
    s ∈ Gk.Ω q ∧ s' ∈ Gk.Ω q ∧ blockMap (L ^ q * (c * M1)) n s' ∈ nbhd 1 {y₁} ∧
      ∃ y ∈ Gk.blk q s, ∃ y' ∈ Gk.blk q s', Adj y y' := by
  have hcN : N₁ = c * n := by simpa using hm
  have hc : 0 < c * M1 := by
    have h1 : c ≠ 0 := by
      rintro rfl
      exact NeZero.ne N₁ (by simpa using hcN)
    exact Nat.pos_of_ne_zero (mul_ne_zero h1 (NeZero.ne M1))
  have hn1 : ∀ z : Torus d n, z ∈ nbhd 1 {y₁} → z ∈ nbhd 2 {y₁} := fun z hz =>
    nbhd_mono (by omega) subset_rfl hz
  have hy₁ : y₁ ∈ nbhd 1 ({y₁} : Set (Torus d n)) := subset_nbhd 1 _ rfl
  have hsk : s ∈ Gk.Ω q := (hGk s).2 (hW (hn1 _ (hs ▸ hy₁)))
  have hnear : ∀ y ∈ Gk.blk q s, ∀ y', Adj y y' →
      blockMap (L ^ q * (c * M1)) n y' ∈ nbhd 1 {y₁} := by
    intro y hy y' hadj
    have hcy : blockMap (L ^ q * (c * M1)) n y = y₁ := by
      rw [← hs]; exact cube_eq_of_jBlock_eq hm (GeneratingSet.mem_blk.1 hy)
    have := cube_adj_near hm hc hadj
    rw [hcy] at this
    exact mem_nbhd.2 ⟨y₁, rfl, by rw [supDist_comm]; exact this⟩
  have hs'k : s' ∈ Gk.Ω q := by
    refine partner_mem_top Gk hq hsk hp fun y hy y' hadj => ?_
    exact (hGk y').2 (hW (hn1 _ (hnear y hy y' hadj)))
  obtain ⟨y, hy, y', hy', hadj⟩ := (isInterfacePair_top_iff Gk hq hsk hs'k).1 hp
  refine ⟨hsk, hs'k, ?_, y, hy, y', hy', hadj⟩
  have := hnear y hy y' hadj
  rwa [cube_eq_of_jBlock_eq hm (GeneratingSet.mem_blk.1 hy')] at this

/-- **The bond lift over a cube (bulk case).**  Let `Gc` have top domain over `nbhd_2 {y₁}` and `Gk` top domain over `W ⊇ nbhd_2 {y₁}`; if `BlockClose` and `GradClose` hold with tolerance `δ` on the stencil `nbhd_1 {y₁}` for the data `D` and the field `φ` on `Gc`, then for every interface pair `(s, s')` of `Gk` with `s` over `y₁`, `‖Ψ(s) - Ψ(s')‖ < 3 δ`. -/
theorem pair_bound_of_close {ϱc ϱk : ℝ} (hm : N₁ * L ^ (q - q) = c * n) (hq : 1 ≤ q)
    (Gc : GeneratingSet d L (M1 * N₁) q ϱc) (Gk : GeneratingSet d L (M1 * N₁) q ϱk)
    (W : Set (Torus d n)) (y₁ : Torus d n) (hW : nbhd 2 {y₁} ⊆ W)
    (hGc : ∀ x, x ∈ Gc.Ω q ↔ blockMap (L ^ q * (c * M1)) n x ∈ nbhd 2 {y₁})
    (hGk : ∀ x, x ∈ Gk.Ω q ↔ blockMap (L ^ q * (c * M1)) n x ∈ W)
    (D : BgData Gc N) (φ : Gc.Ω 1 × Fin N → ℂ) (α : Gc.Ω 1 → ℂ) (δ : ℝ)
    (hBC : BlockClose Gc D φ (cubeNbhd M1 N₁ L q c n 1 y₁) δ)
    (hGC : GradClose Gc D φ α ((L : ℝ) ^ q) (cubeNbhd M1 N₁ L q c n 1 y₁) δ)
    {s s' : Torus d (M1 * N₁ * L ^ q)} (hs : blockMap (L ^ q * (c * M1)) n s = y₁)
    (hp : IsInterfacePair Gk s s') :
    vn (fun i => D.Ψ s i - D.Ψ s' i) < 3 * δ := by
  classical
  have hcN : N₁ = c * n := by simpa using hm
  have hc : 0 < c * M1 := by
    have h1 : c ≠ 0 := by
      rintro rfl
      exact NeZero.ne N₁ (by simpa using hcN)
    exact Nat.pos_of_ne_zero (mul_ne_zero h1 (NeZero.ne M1))
  have hPpos : 0 < L ^ q * (c * M1) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (pow_ne_zero q (NeZero.ne L))) hc
  have hNP : L ^ q ≤ L ^ q * (c * M1) := Nat.le_mul_of_pos_right _ hc
  have hℓ : M1 * N₁ * L ^ q = (L ^ q * (c * M1)) * n := cube_fine_eq hm
  have hn1 : ∀ z : Torus d n, z ∈ nbhd 1 {y₁} → z ∈ nbhd 2 {y₁} := fun z hz =>
    nbhd_mono (by omega) subset_rfl hz
  have hT : ∀ z : Torus d (M1 * N₁ * L ^ q), z ∈ cubeNbhd M1 N₁ L q c n 1 y₁ ↔
      blockMap (L ^ q * (c * M1)) n z ∈ nbhd 1 {y₁} := fun z => mem_cubePre
  have hTc : ∀ z, z ∈ cubeNbhd M1 N₁ L q c n 1 y₁ → z ∈ Gc.Ω q := fun z hz =>
    (hGc z).2 (hn1 _ ((hT z).1 hz))
  have hTk : ∀ z, z ∈ cubeNbhd M1 N₁ L q c n 1 y₁ → z ∈ Gk.Ω q := fun z hz =>
    (hGk z).2 (hW (hn1 _ ((hT z).1 hz)))
  have hy₁ : y₁ ∈ nbhd 1 ({y₁} : Set (Torus d n)) := subset_nbhd 1 _ rfl
  have hsT : s ∈ cubeNbhd M1 N₁ L q c n 1 y₁ := (hT s).2 (hs ▸ hy₁)
  obtain ⟨hsk, hs'k, hs'cube, y, hy, y', hy', hadj⟩ :=
    pair_over_cube hm hq Gk W y₁ hW hGk hs hp
  have hs'T : s' ∈ cubeNbhd M1 N₁ L q c n 1 y₁ := (hT s').2 hs'cube
  have hsc : s ∈ Gc.Ω q := hTc s hsT
  have hs'c : s' ∈ Gc.Ω q := hTc s' hs'T
  have hδ : 0 < δ := lt_of_le_of_lt (vn_nonneg _) (hBC s hsT)
  have hA : vn (fun i => D.Ψ s i - blockAvg Gc φ s i) < δ := hBC s hsT
  have hC : vn (fun i => D.Ψ s' i - blockAvg Gc φ s' i) < δ := hBC s' hs'T
  have hsl : s ∈ Gc.layer q := mem_layer_top Gc hsc
  have hs'l : s' ∈ Gc.layer q := mem_layer_top Gc hs'c
  have hjy : jBlock d L (M1 * N₁) q q y = jBlock d L (M1 * N₁) q q s := GeneratingSet.mem_blk.1 hy
  have hjy' : jBlock d L (M1 * N₁) q q y' = jBlock d L (M1 * N₁) q q s' :=
    GeneratingSet.mem_blk.1 hy'
  have hseg : ∀ (μ : Fin d) {u u' : Torus d (M1 * N₁ * L ^ q)},
      blockMap (L ^ q * (c * M1)) n u ∈ nbhd 1 {y₁} →
      blockMap (L ^ q * (c * M1)) n u' ∈ nbhd 1 {y₁} →
      (∀ z, z ∈ Gc.blk q u ↔ z + blockShift d L (M1 * N₁) q μ ∈ Gc.blk q u') →
      ∀ z ∈ Gc.blk q u, ∀ t : ℕ, t ≤ L ^ q →
        z + t • Pi.single μ (1 : ZMod (M1 * N₁ * L ^ q)) ∈ cubeNbhd M1 N₁ L q c n 1 y₁ ∧
        z + t • Pi.single μ (1 : ZMod (M1 * N₁ * L ^ q)) ∈ Gc.Ω 1 := by
    intro μ u u' hu hu' htr z hz t ht
    have hcz : blockMap (L ^ q * (c * M1)) n z = blockMap (L ^ q * (c * M1)) n u :=
      cube_eq_of_jBlock_eq hm (GeneratingSet.mem_blk.1 hz)
    have hcz' : blockMap (L ^ q * (c * M1)) n (z + blockShift d L (M1 * N₁) q μ) =
        blockMap (L ^ q * (c * M1)) n u' :=
      cube_eq_of_jBlock_eq hm (GeneratingSet.mem_blk.1 ((htr z).1 hz))
    have hmem : z + t • Pi.single μ (1 : ZMod (M1 * N₁ * L ^ q)) ∈
        cubeNbhd M1 N₁ L q c n 1 y₁ := by
      rw [hT]
      rcases cube_seg hℓ hPpos hNP μ z ht with h | h
      · rw [h, hcz]; exact hu
      · rw [h, hcz']; exact hu'
    exact ⟨hmem, mem_Ω_one_of_top Gc hq (hTc _ hmem)⟩
  have hmid : vn (fun i => blockAvg Gc φ s i - blockAvg Gc φ s' i) < δ := by
    rcases blocks_of_adj hadj with hsame | ⟨μ, hμ⟩ | ⟨μ, hμ⟩
    · have hb : jBlock d L (M1 * N₁) q q s = jBlock d L (M1 * N₁) q q s' := by
        rw [← hjy, ← hjy', hsame]
      have hblk : Gc.blk q s' = Gc.blk q s := by
        ext z; rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, hb]
      have : (fun i => blockAvg Gc φ s i - blockAvg Gc φ s' i) = fun _ => 0 := by
        funext i
        unfold blockAvg
        rw [layerIndex_top Gc hq hsc, layerIndex_top Gc hq hs'c, hblk]
        simp
      rw [this]
      have h0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := vn_zero
      rw [h0]; exact hδ
    · refine blockAvg_sub_lt Gc D φ α _ δ hq hGC hsl hs'l μ ?_ ?_
      · intro z
        rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, ← hjy, ← hjy']
        exact hμ z
      · refine hseg μ (u := s) (u' := s') (hs ▸ hy₁) hs'cube ?_
        intro z
        rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, ← hjy, ← hjy']
        exact hμ z
    · have h := blockAvg_sub_lt Gc D φ α _ δ hq hGC hs'l hsl μ (by
        intro z
        rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, ← hjy, ← hjy']
        exact hμ z) (hseg μ (u := s') (u' := s) hs'cube (hs ▸ hy₁) (by
        intro z
        rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, ← hjy, ← hjy']
        exact hμ z))
      have e : vn (fun i => blockAvg Gc φ s i - blockAvg Gc φ s' i) =
          vn (fun i => blockAvg Gc φ s' i - blockAvg Gc φ s i) := vn_sub_comm _ _
      rw [e]
      exact h
  have h3 : vn (fun i => blockAvg Gc φ s' i - D.Ψ s' i) =
      vn (fun i => D.Ψ s' i - blockAvg Gc φ s' i) := vn_sub_comm _ _
  have t1 := vn_triangle' (fun i => D.Ψ s i) (fun i => blockAvg Gc φ s i) (fun i => D.Ψ s' i)
  have t2 := vn_triangle' (fun i => blockAvg Gc φ s i) (fun i => blockAvg Gc φ s' i)
    (fun i => D.Ψ s' i)
  linarith

end PairBound


section Succ

variable {d M1 N₁ L q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- The pair `(s, s + e_μ)` is an interface pair for a site `s` over a cube `y₁` with `nbhd_2 {y₁} ⊆ W`. -/
theorem interfacePair_succ_of_over_cube {ϱk : ℝ} (hm : N₁ * L ^ (q - q) = c * n) (hq : 1 ≤ q)
    (Gk : GeneratingSet d L (M1 * N₁) q ϱk) (W : Set (Torus d n)) (y₁ : Torus d n)
    (hW : nbhd 2 {y₁} ⊆ W)
    (hGk : ∀ x, x ∈ Gk.Ω q ↔ blockMap (L ^ q * (c * M1)) n x ∈ W)
    {s : Torus d (M1 * N₁ * L ^ q)} (hs : blockMap (L ^ q * (c * M1)) n s = y₁) (μ : Fin d) :
    IsInterfacePair Gk s (s + Pi.single μ 1) := by
  have hcN : N₁ = c * n := by simpa using hm
  have hc : 0 < c * M1 := by
    have h1 : c ≠ 0 := by
      rintro rfl
      exact NeZero.ne N₁ (by simpa using hcN)
    exact Nat.pos_of_ne_zero (mul_ne_zero h1 (NeZero.ne M1))
  have hadj : Adj s (s + Pi.single μ 1) := ⟨μ, Or.inl rfl⟩
  have hn : blockMap (L ^ q * (c * M1)) n (s + Pi.single μ 1) ∈ nbhd 2 {y₁} := by
    have := cube_adj_near hm hc hadj
    rw [hs] at this
    exact mem_nbhd.2 ⟨y₁, rfl, by rw [supDist_comm]; omega⟩
  have hy₁ : y₁ ∈ nbhd 2 ({y₁} : Set (Torus d n)) := subset_nbhd 2 _ rfl
  have hsk : s ∈ Gk.Ω q := (hGk s).2 (hW (hs ▸ hy₁))
  have hs'k : s + Pi.single μ 1 ∈ Gk.Ω q := (hGk _).2 (hW hn)
  exact (isInterfacePair_top_iff Gk hq hsk hs'k).2
    ⟨s, GeneratingSet.mem_blk.2 rfl, s + Pi.single μ 1, GeneratingSet.mem_blk.2 rfl, hadj⟩

end Succ

section Small

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- `nbhd_2 {y₁} ⊆ W₂(Y)` for a cube `y₁` of `Y`, because the halo of `W₂` has at least two cubes. -/
theorem nbhd_two_subset_W2 (Y : Set (Torus S.d (n (j + 1)))) {y₁ : Torus S.d (n (j + 1))}
    (hy₁ : y₁ ∈ Y) : nbhd 2 {y₁} ⊆ W2 R Y := by
  unfold W2 thick
  rw [nbhd_nbhd]
  exact nbhd_mono (by omega) (Set.singleton_subset_iff.2 hy₁)

/-- A site is in `Ω_k` of `G_k = 𝔹_k(W₂(Y))` iff its cube is in `W₂(Y)`. -/
theorem genW_mem_top_iff (Y : Set (Torus S.d (n (j + 1)))) {s : BgT Cx.geo (j + 1)} :
    s ∈ (Cx.genW Y).Ω (j + 1) ↔
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ W2 R Y :=
  genSF_top_mem (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
    (c := Cx.geo.c) (n := n (j + 1)) (by simp) _

/-- **Classification of the interface pairs over `Y`.**  If `s` is over a cube `y₁ ∈ Y` and `(s, s')` is an interface pair of `G_k`, then both sites are in the layer `k` (the top layer), neither is in the collar, the cube of `s'` is within one cube of `y₁`, and the `k`-blocks of `s` and `s'` contain adjacent sites. -/
theorem interfacePair_over_Y (Y : Set (Torus S.d (n (j + 1)))) {y₁ : Torus S.d (n (j + 1))}
    (hy₁ : y₁ ∈ Y) {s s' : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁)
    (hp : IsInterfacePair (Cx.genW Y) s s') :
    s ∈ (Cx.genW Y).layer (j + 1) ∧ s' ∈ (Cx.genW Y).layer (j + 1) ∧
      (Cx.genW Y).layerIndex s = j + 1 ∧ (Cx.genW Y).layerIndex s' = j + 1 ∧
      s ∉ collar (Cx.genW Y) ∧ s' ∉ collar (Cx.genW Y) ∧
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s' ∈ nbhd 1 {y₁} ∧
      ∃ y ∈ (Cx.genW Y).blk (j + 1) s, ∃ y' ∈ (Cx.genW Y).blk (j + 1) s', Adj y y' := by
  obtain ⟨hsk, hs'k, hcube, hadj⟩ := pair_over_cube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1))
    (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) (by simp) (Nat.succ_pos j)
    (Cx.genW Y) (W2 R Y) y₁ (nbhd_two_subset_W2 Y hy₁) (fun x => genW_mem_top_iff Cx Y) hs hp
  refine ⟨mem_layer_top _ hsk, mem_layer_top _ hs'k, layerIndex_top _ (Nat.succ_pos j) hsk,
    layerIndex_top _ (Nat.succ_pos j) hs'k, ?_, ?_, hcube, hadj⟩
  · exact ((mem_collar _).1 · |>.1 (mem_Ω_one_of_top _ (Nat.succ_pos j) hsk))
  · exact ((mem_collar _).1 · |>.1 (mem_Ω_one_of_top _ (Nat.succ_pos j) hs'k))

/-- Interface pairs over `Y` exist: `(s, s + e_μ)` for `s` over a cube of `Y`. -/
theorem interfacePair_succ_over_Y (Y : Set (Torus S.d (n (j + 1)))) {y₁ : Torus S.d (n (j + 1))}
    (hy₁ : y₁ ∈ Y) {s : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁)
    (μ : Fin S.d) : IsInterfacePair (Cx.genW Y) s (s + Pi.single μ 1) :=
  interfacePair_succ_of_over_cube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1))
    (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) (by simp) (Nat.succ_pos j)
    (Cx.genW Y) (W2 R Y) y₁ (nbhd_two_subset_W2 Y hy₁) (fun x => genW_mem_top_iff Cx Y) hs μ

end Small


section SmallPair

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **R1 over `Y`.**  Under `chiY ≠ 0`, for an interface pair `(s, s')` of `G_k` with `s` over a cube `y₁ ∈ Y`, the datum of `G_k` satisfies `‖Ψ(s) - Ψ(s')‖ < 3 δ_k` (`vn` is the Euclidean norm of a vector in `ℂ^N`). -/
theorem pair_bound_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₁ : Torus S.d (n (j + 1))} (hy₁ : y₁ ∈ Y)
    {s s' : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁)
    (hp : IsInterfacePair (Cx.genW Y) s s') :
    vn (fun i => (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s i -
        (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s' i) <
      3 * Cx.cs.delta (j + 1) := by
  classical
  have hmem : y₁ ∈ cubeFin Y := by simp [cubeFin, hy₁]
  obtain ⟨hBC, hGC⟩ := chiY_ne_zero_blockClose_gradClose Cx Y ψk hv h hmem
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have hGc : ∀ x, x ∈ (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₁).Ω (j + 1) ↔
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) x ∈ nbhd 2 {y₁} :=
    fun x => genCube_top_mem hm y₁
  have hmain := pair_bound_of_close (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1))
    (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) hm (Nat.succ_pos j) _ (Cx.genW Y)
    (W2 R Y) y₁ (nbhd_two_subset_W2 Y hy₁) hGc (fun x => genW_mem_top_iff Cx Y) _ _ _ _ hBC hGC
    hs hp
  obtain ⟨hsk, hs'k, hcube, -⟩ := pair_over_cube (M1 := Cx.geo.M1)
    (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) hm
    (Nat.succ_pos j) (Cx.genW Y) (W2 R Y) y₁ (nbhd_two_subset_W2 Y hy₁)
    (fun x => genW_mem_top_iff Cx Y) hs hp
  have hy₁' : y₁ ∈ nbhd 2 ({y₁} : Set (Torus S.d (n (j + 1)))) := subset_nbhd 2 _ rfl
  have hsc : s ∈ (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₁).Ω (j + 1) := (hGc s).2 (hs ▸ hy₁')
  have hs'c : s' ∈ (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₁).Ω (j + 1) :=
    (hGc s').2 (nbhd_mono (by omega) subset_rfl hcube)
  have e1 := cubeData_Ψ_eq_liftSingle_Ψ Cx Y ψk hv y₁
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hsc)))
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hsk)))
  have e2 := cubeData_Ψ_eq_liftSingle_Ψ Cx Y ψk hv y₁
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hs'c)))
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hs'k)))
  rw [← e1, ← e2]
  exact hmain

/-- If one of the sites of an interface pair is over a cube of `Y`, both are in the top domain of `G_k`. -/
theorem pair_top_of_either (Y : Set (Torus S.d (n (j + 1)))) {y₁ : Torus S.d (n (j + 1))}
    (hy₁ : y₁ ∈ Y) {s s' : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁ ∨
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s' = y₁)
    (hp : IsInterfacePair (Cx.genW Y) s s') :
    s ∈ (Cx.genW Y).Ω (j + 1) ∧ s' ∈ (Cx.genW Y).Ω (j + 1) := by
  have hy₁' : y₁ ∈ nbhd 2 ({y₁} : Set (Torus S.d (n (j + 1)))) := subset_nbhd 2 _ rfl
  rcases hs with hs | hs
  · obtain ⟨hsk, hs'k, -⟩ := pair_over_cube (M1 := Cx.geo.M1)
      (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1))
      (by simp) (Nat.succ_pos j) (Cx.genW Y) (W2 R Y) y₁ (nbhd_two_subset_W2 Y hy₁)
      (fun x => genW_mem_top_iff Cx Y) hs hp
    exact ⟨hsk, hs'k⟩
  · have hs'k : s' ∈ (Cx.genW Y).Ω (j + 1) :=
      (genW_mem_top_iff Cx Y).2 (nbhd_two_subset_W2 Y hy₁ (hs ▸ hy₁'))
    have hp' := isInterfacePair_symm_of_top (Cx.genW Y) (Nat.succ_pos j) hs'k hp
    obtain ⟨hsk, hs'k', -⟩ := pair_over_cube (M1 := Cx.geo.M1)
      (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1))
      (by simp) (Nat.succ_pos j) (Cx.genW Y) (W2 R Y) y₁ (nbhd_two_subset_W2 Y hy₁)
      (fun x => genW_mem_top_iff Cx Y) hs hp'
    exact ⟨hs'k', hsk⟩

/-- The bound `3 δ_k` of `pair_bound_over_Y` when either site of the pair is over a cube of `Y`. -/
theorem pair_bound_over_Y_either (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₁ : Torus S.d (n (j + 1))} (hy₁ : y₁ ∈ Y)
    {s s' : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁ ∨
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s' = y₁)
    (hp : IsInterfacePair (Cx.genW Y) s s') :
    vn (fun i => (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s i -
        (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s' i) <
      3 * Cx.cs.delta (j + 1) := by
  rcases hs with hs | hs
  · exact pair_bound_over_Y Cx Y ψk hv h hy₁ hs hp
  · have hy₁' : y₁ ∈ nbhd 2 ({y₁} : Set (Torus S.d (n (j + 1)))) := subset_nbhd 2 _ rfl
    have hs'k : s' ∈ (Cx.genW Y).Ω (j + 1) :=
      (genW_mem_top_iff Cx Y).2 (nbhd_two_subset_W2 Y hy₁ (hs ▸ hy₁'))
    have hp' := isInterfacePair_symm_of_top (Cx.genW Y) (Nat.succ_pos j) hs'k hp
    have := pair_bound_over_Y Cx Y ψk hv h hy₁ hs hp'
    have e := vn_sub_comm
      (fun i => (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s i)
      (fun i => (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s' i)
    exact e ▸ this

end SmallPair


section RealNorm

variable {N : ℕ}

/-- The complex norm of the difference of two real vectors is their Euclidean distance. -/
theorem vn_ofReal_sub (a b : EuclideanSpace ℝ (Fin N)) :
    vn (fun i => ((a i : ℝ) : ℂ) - ((b i : ℝ) : ℂ)) = ‖a - b‖ := by
  rw [vn_eq_sqrt, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_sub, Complex.norm_real]
  rfl

end RealNorm

section SmallPair2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **R1 over `Y`, in terms of the field `ψ_k`.**  Under `chiY ≠ 0`, for an interface pair with a site over a cube of `Y`, `‖ψ_k(b) - ψ_k(b')‖ < 3 δ_k` at the top blocks `b, b'` of the two sites (the quantity tested by `PsiTildeMulti`). -/
theorem psi_close_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₁ : Torus S.d (n (j + 1))} (hy₁ : y₁ ∈ Y)
    {s s' : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁ ∨
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s' = y₁)
    (hp : IsInterfacePair (Cx.genW Y) s s') :
    ‖ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) -
        ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s'))‖ <
      3 * Cx.cs.delta (j + 1) := by
  obtain ⟨hsk, hs'k⟩ := pair_top_of_either Cx Y hy₁ hs hp
  have hds : s ∈ dataSites (Cx.genW Y) :=
    (mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hsk))
  have hds' : s' ∈ dataSites (Cx.genW Y) :=
    (mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hs'k))
  have key := pair_bound_over_Y_either Cx Y ψk hv h hy₁ hs hp
  rw [liftSingle_genW_Ψ_top Cx Y ψk hv hds, liftSingle_genW_Ψ_top Cx Y ψk hv hds'] at key
  rwa [vn_ofReal_sub] at key

end SmallPair2


section Corner

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Walking from a site of the `k`-block of `s` to the corner of the block, one coordinate step at a time, changes the field `φ̄` by at most `n δ / L^k` after `n` steps, by `GradClose`. -/
theorem corner_close (G : GeneratingSet d L N₀ k ϱ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (S : Finset (Torus d (N₀ * L ^ k))) (δ : ℝ)
    (hgrad : GradClose G D φ α ((L : ℝ) ^ k) S δ)
    {s : Torus d (N₀ * L ^ k)}
    (hS : ∀ z, jBlock d L N₀ k k z = jBlock d L N₀ k k s → z ∈ S ∧ z ∈ G.Ω 1) :
    ∀ n : ℕ, ∀ z : Torus d (N₀ * L ^ k), jBlock d L N₀ k k z = jBlock d L N₀ k k s →
      ∑ μ, (z μ).val % L ^ k = n →
      ∃ c : Torus d (N₀ * L ^ k), (∀ μ, (c μ).val % L ^ k = 0) ∧
        jBlock d L N₀ k k c = jBlock d L N₀ k k s ∧
        vn (svec G φ z - svec G φ c) ≤ n * (δ / (L : ℝ) ^ k) := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  intro n
  induction n with
  | zero =>
      intro x hx hs
      refine ⟨x, fun μ => ?_, hx, ?_⟩
      · exact (Finset.sum_eq_zero_iff.1 hs) μ (Finset.mem_univ μ)
      · simp [vn_zero]
  | succ n ih =>
      intro x hx hs
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun μ => (x μ).val % L ^ k) (by rw [hs]; omega)
      have hpos : 0 < (x μ).val % L ^ k := Nat.pos_of_ne_zero hμ
      have hNpos : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L))
      obtain ⟨x₁, hx₁⟩ : ∃ x₁ : Torus d (N₀ * L ^ k), x₁ = x - Pi.single μ 1 := ⟨_, rfl⟩
      have hxx₁ : x = x₁ + Pi.single μ 1 := by rw [hx₁]; abel
      have hvpos : 0 < (x μ).val := by
        by_contra h0
        have : (x μ).val = 0 := by omega
        rw [this] at hpos; simp at hpos
      have hℓ2 : 1 < N₀ * L ^ k := by
        have := ZMod.val_lt (x μ)
        omega
      have hone : (1 : ZMod (N₀ * L ^ k)).val = 1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hℓ2]
      have hv1 : (x₁ μ).val = (x μ).val - 1 := by
        have : x₁ μ = x μ - 1 := by simp [hx₁]
        rw [this, ZMod.val_sub (by rw [hone]; omega), hone]
      have hother : ∀ ν, ν ≠ μ → x₁ ν = x ν := by
        intro ν hν; simp [hx₁, hν]
      have hrem1 : (x₁ μ).val % L ^ k = (x μ).val % L ^ k - 1 := by
        rw [hv1]; exact GeneratingSet.mod_pred hNpos hpos
      have hsum : ∑ ν, (x₁ ν).val % L ^ k = n := by
        have e1 : ∑ ν, (x ν).val % L ^ k =
            ((x μ).val % L ^ k) + ∑ ν ∈ Finset.univ.erase μ, (x ν).val % L ^ k :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
        have e2 : ∑ ν, (x₁ ν).val % L ^ k =
            ((x₁ μ).val % L ^ k) + ∑ ν ∈ Finset.univ.erase μ, (x₁ ν).val % L ^ k :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
        have e3 : ∑ ν ∈ Finset.univ.erase μ, (x₁ ν).val % L ^ k =
            ∑ ν ∈ Finset.univ.erase μ, (x ν).val % L ^ k :=
          Finset.sum_congr rfl fun ν hν => by rw [hother ν (Finset.ne_of_mem_erase hν)]
        omega
      have hlt : (x₁ μ).val % L ^ k + 1 < L ^ k := by
        have := Nat.mod_lt (x μ).val hNpos
        omega
      have hblock : jBlock d L N₀ k k x = jBlock d L N₀ k k x₁ := by
        unfold jBlock
        conv_lhs => rw [hxx₁]
        exact blockMap_add_single_of_inner (side_eq (le_refl k)) hlt
      obtain ⟨c, hc0, hcb, hcd⟩ := ih x₁ (hblock.symm.trans hx) hsum
      refine ⟨c, hc0, hcb, ?_⟩
      obtain ⟨hxS, hxΩ⟩ := hS x hx
      obtain ⟨-, hx₁Ω⟩ := hS x₁ (hblock.symm.trans hx)
      have hg := (hgrad ⟨x, hxΩ⟩ hxS).1 μ
      have hstep : vn (svec G φ x - svec G φ x₁) ≤ δ / (L : ℝ) ^ k := by
        have h1 : svec G φ x₁ = barVec G D φ (x - Pi.single μ 1) := by
          rw [← hx₁]; exact svec_eq_barVec D φ hx₁Ω
        have h2 : svec G φ x = barVec G D φ x := svec_eq_barVec D φ hxΩ
        rw [h2, h1, vn_sub_comm, le_div_iff₀ hLpos, mul_comm]
        exact hg.2.le
      have := vn_triangle (svec G φ x) (svec G φ x₁) (svec G φ c)
      push_cast
      have h3 : (↑n + 1 : ℝ) * (δ / (L : ℝ) ^ k) = ↑n * (δ / (L : ℝ) ^ k) + δ / (L : ℝ) ^ k := by
        ring
      linarith

/-- The block average of `φ` over a `k`-block is within `d δ` of the value of `φ` at the corner of the block, under `GradClose` on the block. -/
theorem blockAvg_near_corner (G : GeneratingSet d L N₀ k ϱ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (S : Finset (Torus d (N₀ * L ^ k))) (δ : ℝ)
    (hδ : 0 ≤ δ) (hk : 1 ≤ k) (hgrad : GradClose G D φ α ((L : ℝ) ^ k) S δ)
    {s : Torus d (N₀ * L ^ k)} (hs : s ∈ G.layer k)
    (hS : ∀ z, jBlock d L N₀ k k z = jBlock d L N₀ k k s → z ∈ S ∧ z ∈ G.Ω 1) :
    ∃ c : Torus d (N₀ * L ^ k), c ∈ G.blk k s ∧
      vn (fun i => blockAvg G φ s i - svec G φ c i) ≤ d * δ := by
  classical
  have hLpos : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hNpos : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero k (NeZero.ne L))
  have hi : G.layerIndex s = k := G.layerIndex_eq hk le_rfl hs
  obtain ⟨c, hc0, hcb, -⟩ := corner_close G D φ α S δ hgrad hS _ s rfl rfl
  have hcz : ∀ z ∈ G.blk k s, vn (svec G φ z - svec G φ c) ≤ d * δ := by
    intro z hz
    have hzb : jBlock d L N₀ k k z = jBlock d L N₀ k k s := GeneratingSet.mem_blk.1 hz
    obtain ⟨c', hc0', hcb', hbd⟩ := corner_close G D φ α S δ hgrad hS _ z hzb rfl
    have hcc : c' = c := GeneratingSet.corner_eq (le_refl k) hc0' hc0 (hcb'.trans hcb.symm)
    subst hcc
    refine hbd.trans ?_
    have hn : (((∑ μ, (z μ).val % L ^ k : ℕ)) : ℝ) ≤ d * (L : ℝ) ^ k := by
      have : ∑ μ, (z μ).val % L ^ k ≤ ∑ _μ : Fin d, L ^ k :=
        Finset.sum_le_sum fun μ _ => (Nat.mod_lt _ hNpos).le
      have h2 : (((∑ μ, (z μ).val % L ^ k : ℕ)) : ℝ) ≤ ((∑ _μ : Fin d, L ^ k : ℕ) : ℝ) :=
        Nat.cast_le.2 this
      simpa using h2
    calc (((∑ μ, (z μ).val % L ^ k : ℕ)) : ℝ) * (δ / (L : ℝ) ^ k)
        ≤ d * (L : ℝ) ^ k * (δ / (L : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_right hn (div_nonneg hδ hLpos.le)
      _ = d * δ := by field_simp
  refine ⟨c, GeneratingSet.mem_blk.2 hcb, ?_⟩
  set cf : ℂ := ((((((L : ℝ) ^ k) ^ d)⁻¹ : ℝ) : ℂ)) with hcf
  have hcard : ((G.blk k s).card : ℝ) = ((L : ℝ) ^ k) ^ d := card_blk_cast G k le_rfl s
  have hpow : (((L : ℝ) ^ k) ^ d) ≠ 0 := by positivity
  have e : (fun i => blockAvg G φ s i - svec G φ c i) =
      fun i => cf * ∑ z ∈ G.blk k s, (svec G φ z - svec G φ c) i := by
    funext i
    unfold blockAvg
    rw [hi]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub]
    have hc' : cf * ((G.blk k s).card : ℂ) = 1 := by
      have : ((G.blk k s).card : ℂ) = ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) := by
        exact_mod_cast hcard
      rw [this, hcf, ← Complex.ofReal_mul, inv_mul_cancel₀ hpow]
      simp
    linear_combination (svec G φ c i) * hc'
  rw [e]
  refine (vn_smul_sum_le cf _ _).trans ?_
  have hcn : ‖cf‖ = (((L : ℝ) ^ k) ^ d)⁻¹ := by
    rw [hcf, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖cf‖ * ∑ z ∈ G.blk k s, vn (svec G φ z - svec G φ c)
      ≤ ‖cf‖ * ∑ z ∈ G.blk k s, (d * δ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z hz => hcz z hz) (norm_nonneg _)
    _ = d * δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, hcn]
        field_simp

/-- A real unit field has norm one at the sites of `Ω₁`. -/
theorem vn_svec_eq_one (G : GeneratingSet d L N₀ k ϱ) {φ : G.Ω 1 × Fin N → ℂ}
    (hu : IsRealUnitField G φ) {c : Torus d (N₀ * L ^ k)} (hc : c ∈ G.Ω 1) :
    vn (svec G φ c) = 1 := by
  have h := (hu ⟨c, hc⟩).2
  have h2 : vn (svec G φ c) ^ 2 = 1 := by
    rw [vn_sq]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [svec, zeroExt, hc]
  have h3 := vn_nonneg (svec G φ c)
  nlinarith [h2, h3]

end Corner


section Sphere

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The reverse triangle inequality for `vn`. -/
theorem abs_vn_sub_vn_le (u w : Fin N → ℂ) :
    |vn u - vn w| ≤ vn (fun i => u i - w i) := by
  have h1 : vn u ≤ vn (fun i => u i - w i) + vn w := by
    have := vn_add (fun i => u i - w i) w
    have e : ((fun i => u i - w i) + w) = u := by funext i; simp
    rwa [e] at this
  have h2 : vn w ≤ vn (fun i => w i - u i) + vn u := by
    have := vn_add (fun i => w i - u i) u
    have e : ((fun i => w i - u i) + u) = w := by funext i; simp
    rwa [e] at this
  have h3 : vn (fun i => w i - u i) = vn (fun i => u i - w i) := vn_sub_comm w u
  rw [abs_le]
  constructor <;> linarith

/-- **Sphere bound for a unit field:** if `φ` is a real unit field, `BlockClose` holds at `s` and `GradClose` on the block of `s`, then `| ‖Ψ(s)‖ - 1 | < (d + 1) δ`. -/
theorem sphere_bound_of_close (G : GeneratingSet d L N₀ k ϱ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (S : Finset (Torus d (N₀ * L ^ k))) (δ : ℝ)
    (hk : 1 ≤ k) (hgrad : GradClose G D φ α ((L : ℝ) ^ k) S δ)
    (hunit : IsRealUnitField G φ) {s : Torus d (N₀ * L ^ k)} (hs : s ∈ G.layer k)
    (hS : ∀ z, jBlock d L N₀ k k z = jBlock d L N₀ k k s → z ∈ S ∧ z ∈ G.Ω 1)
    (hblock : vn (fun i => D.Ψ s i - blockAvg G φ s i) < δ) :
    |vn (D.Ψ s) - 1| < (d + 1) * δ := by
  have hδ : 0 ≤ δ := le_trans (vn_nonneg _) hblock.le
  obtain ⟨c, hc, hcl⟩ := blockAvg_near_corner G D φ α S δ hδ hk hgrad hs hS
  have hcΩ : c ∈ G.Ω 1 := (hS c (GeneratingSet.mem_blk.1 hc)).2
  have h1 := abs_vn_sub_vn_le (D.Ψ s) (blockAvg G φ s)
  have h2 := abs_vn_sub_vn_le (blockAvg G φ s) (svec G φ c)
  rw [vn_svec_eq_one G hunit hcΩ] at h2
  have h3 : |vn (D.Ψ s) - 1| ≤ |vn (D.Ψ s) - vn (blockAvg G φ s)| +
      |vn (blockAvg G φ s) - 1| := abs_sub_le _ _ _
  have : (d : ℝ) * δ + δ = (d + 1) * δ := by ring
  have h4 : |vn (D.Ψ s) - vn (blockAvg G φ s)| < δ := lt_of_le_of_lt h1 hblock
  have h5 : |vn (blockAvg G φ s) - 1| ≤ d * δ := h2.trans hcl
  linarith

end Sphere


section SmallSphere

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- The complex norm of a real vector is its Euclidean norm. -/
theorem vn_ofReal_euclid (a : EuclideanSpace ℝ (Fin N)) :
    vn (fun i => ((a i : ℝ) : ℂ)) = ‖a‖ := by
  rw [vn_eq_sqrt, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real]

/-- **R2 over `Y`.**  Under `chiY ≠ 0` and the numeric premise `BgHyp` of the background solver, for a site `s` over a cube `y₁ ∈ Y`, `| ‖ψ_k(b(s))‖ - 1 | < (d + 1) δ_k`. -/
theorem sphere_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0)
    (H : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    {y₁ : Torus S.d (n (j + 1))} (hy₁ : y₁ ∈ Y) {s : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁) :
    |‖ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s))‖ - 1| <
      (S.d + 1) * Cx.cs.delta (j + 1) := by
  classical
  have hmem : y₁ ∈ cubeFin Y := by simp [cubeFin, hy₁]
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have hK := chiKProp_of_chiY_ne_zero Cx Y ψk hv h hmem
  obtain ⟨hBC, hGC⟩ := chiY_ne_zero_blockClose_gradClose Cx Y ψk hv h hmem
  have hD := hK.1
  have hunit := (theorem71 H hD).2.1
  rw [← (theorem72_real H hD).1] at hunit
  have hy₁' : y₁ ∈ nbhd 1 ({y₁} : Set (Torus S.d (n (j + 1)))) := subset_nbhd 1 _ rfl
  have hn1 : ∀ z : Torus S.d (n (j + 1)), z ∈ nbhd 1 {y₁} → z ∈ nbhd 2 {y₁} := fun z hz =>
    nbhd_mono (by omega) subset_rfl hz
  have hsT : s ∈ cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1)) 1 y₁ :=
    mem_cubePre.2 (hs ▸ hy₁')
  have hTc : ∀ z, blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) z ∈ nbhd 1 {y₁} →
      z ∈ (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
        Cx.geo.c (n (j + 1)) y₁).Ω (j + 1) := fun z hz =>
    (genCube_top_mem hm y₁).2 (hn1 _ hz)
  have hsc := hTc s (hs ▸ hy₁')
  have hsk : s ∈ (Cx.genW Y).Ω (j + 1) :=
    (genW_mem_top_iff Cx Y).2 (nbhd_two_subset_W2 Y hy₁ (hn1 _ (hs ▸ hy₁')))
  have hcube : ∀ z : BgT Cx.geo (j + 1), jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1)))
      (j + 1) (j + 1) z = jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s →
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) z = y₁ := fun z hz =>
    (cube_eq_of_jBlock_eq (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) hm hz).trans hs
  have key := sphere_bound_of_close
    (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
      Cx.geo.c (n (j + 1)) y₁) _ _ _ _ (Cx.cs.delta (j + 1)) (Nat.succ_pos j) hGC hunit
    (s := s) (mem_layer_top _ hsc)
    (fun z hz => ⟨mem_cubePre.2 (hcube z hz ▸ hy₁'),
      mem_Ω_one_of_top _ (Nat.succ_pos j) (hTc z (hcube z hz ▸ hy₁'))⟩)
    (hBC s hsT)
  have e := cubeData_Ψ_eq_liftSingle_Ψ Cx Y ψk hv y₁
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hsc)))
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hsk)))
  rw [e, liftSingle_genW_Ψ_top Cx Y ψk hv
    ((mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hsk))), vn_ofReal_euclid] at key
  exact key

end SmallSphere


section SquareForm

/-- From `|x - 1| < ε` and `x ≥ 0` follows `|x² - 1| < ε (2 + ε)`. -/
theorem abs_sq_sub_one_lt {x ε : ℝ} (hx : 0 ≤ x) (h : |x - 1| < ε) : |x ^ 2 - 1| < ε * (2 + ε) := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) h.le
  have h1 := abs_lt.1 h
  rw [abs_lt]
  constructor <;> nlinarith [h1.1, h1.2]

end SquareForm

section SmallSphereSq

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **R2 over `Y`, squared form.**  `| ‖ψ_k(b(s))‖² - 1 | < (d + 1) δ_k (2 + (d + 1) δ_k)`; this is `< 3 (d + 1) δ_k` when `(d + 1) δ_k ≤ 1`. -/
theorem sphere_sq_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0)
    (H : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    {y₁ : Torus S.d (n (j + 1))} (hy₁ : y₁ ∈ Y) {s : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁) :
    |‖ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s))‖ ^ 2 - 1| <
      ((S.d + 1) * Cx.cs.delta (j + 1)) * (2 + (S.d + 1) * Cx.cs.delta (j + 1)) :=
  abs_sq_sub_one_lt (norm_nonneg _) (sphere_over_Y Cx Y ψk hv h H hy₁ hs)

end SmallSphereSq


section Instance

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- The level-`k` torus has at least two sites per side. -/
theorem two_le_bgT : 2 ≤ Cx.geo.M1 * (Cx.geo.c * n (j + 1)) * S.L ^ (j + 1) := by
  have h1 : 1 ≤ Cx.geo.M1 := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have h2 : 1 ≤ n (j + 1) := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have h3 : 1 ≤ S.L ^ (j + 1) := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne _))
  have h4 := Cx.geo.hc
  calc 2 ≤ 1 * (14 * 1) * 1 := by norm_num
    _ ≤ _ := by gcongr

/-- **Non-vacuity of the classification:** for `Y = {0}` there are a site `s` over the cube `0 ∈ Y` and a different site `s'` forming an interface pair of `G_k`, both in the top layer and not in the collar. -/
theorem exists_pair_over_Y (hd : 0 < S.d) :
    ∃ (Y : Set (Torus S.d (n (j + 1)))) (y₁ : Torus S.d (n (j + 1))) (s s' : BgT Cx.geo (j + 1)),
      y₁ ∈ Y ∧ blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁ ∧ s ≠ s' ∧
      IsInterfacePair (Cx.genW Y) s s' ∧
      (Cx.genW Y).layerIndex s = j + 1 ∧ (Cx.genW Y).layerIndex s' = j + 1 ∧
      s ∉ collar (Cx.genW Y) ∧ s' ∉ collar (Cx.genW Y) := by
  classical
  let Y : Set (Torus S.d (n (j + 1))) := {0}
  let μ : Fin S.d := ⟨0, hd⟩
  have hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1))
      (0 : BgT Cx.geo (j + 1)) = 0 := by
    funext i
    simp [blockMap, blockCoord]
  have hy : (0 : Torus S.d (n (j + 1))) ∈ Y := rfl
  have hp := interfacePair_succ_over_Y Cx Y hy hs μ
  have hne : (0 : BgT Cx.geo (j + 1)) ≠ 0 + Pi.single μ 1 := by
    intro h
    have h1 := congrFun h μ
    simp only [Pi.zero_apply, zero_add, Pi.single_eq_same] at h1
    have : Fact (1 < Cx.geo.M1 * (Cx.geo.c * n (j + 1)) * S.L ^ (j + 1)) := ⟨two_le_bgT Cx⟩
    exact one_ne_zero h1.symm
  obtain ⟨-, -, hli, hli', hnc, hnc', -, -⟩ := interfacePair_over_Y Cx Y hy hs hp
  exact ⟨Y, 0, 0, 0 + Pi.single μ 1, hy, hs, hne, hp, hli, hli', hnc, hnc'⟩

end Instance

end Balaban.LargeField
