/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BlockPath
public import Balaban.Background.Def5
public import Balaban.Background.CompositionDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Small-field spins lie in the chart (LF-RECONSTRUCTION Lemma II.7.5)

On the support of the base characteristic function `χ'^{(0)}` (block condition
`|θ(y) - (Qφ)(y)| < 2δ₀`, bond condition `|∂φ(b)| < δ₀`, regime-(B) site condition) the lifted data
`lift_{0,1}(φ, θ)` of `G_1(□')` lie in the real domain `Ψ̃(G_1(□'); 4 d L δ₀)` (`inDomainR_base`:
(R1)–(R4) of BG §1.3), hence by BG Theorem 7.1 (`theorem71`, the bounds of Theorem 5.2 (3)) the
step background `φ^b = bgField` is within `4 d K₁ L δ₀` of the block field, and
`spins_near_background` gives `|φ_x - φ^b(x)| ≤ C_hs L δ₀`, `C_hs = d + 2 + 4 d K₁`
(`≤ 1/4` by (Λ26)), the positivity `φ_x · φ^b(x) > 0` and the bound on the chart coordinate.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section One

variable (G : GeneratingSet d L N₀ 1 ϱ)

theorem mem_layer_one {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) : x ∈ G.layer 1 := by
  rw [GeneratingSet.mem_layer]
  refine ⟨hx, ?_⟩
  have := G.top
  simp [this]

theorem layerIndex_one {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) : G.layerIndex x = 1 :=
  G.layerIndex_eq le_rfl le_rfl (mem_layer_one G hx)

theorem spacing_one {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) : G.spacing x = L := by
  rw [G.spacing_eq le_rfl le_rfl (mem_layer_one G hx)]; simp

/-- The block average `(Qφ)(x) = L^{-d} ∑_{y ∈ B_1(x)} φ_y` of a spin field. -/
noncomputable def spinBlockAverage (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (x : Torus d (N₀ * L ^ 1))
    (i : Fin N) : ℝ :=
  ((L : ℝ) ^ d)⁻¹ * ∑ y ∈ G.blk 1 x, φ y i


/-- **The support data of the base step** (LF-RECONSTRUCTION Definition II.7.1, Lemma II.7.2 (d),
Lemma II.7.5): spins `φ` and the constant `h` of unit length, the lifted data `D` of `G_1(□')`
(`θ` on the blocks of `Ω₁`, the spins on the collar), and the conditions that the characteristic
function `χ'^{(0)}` imposes on the cubes meeting `Ω₁ ∪ collar` (these cubes are outside `P₁` by
Lemma II.7.2 (d)): the block condition `|θ(y) - (Qφ)(y)| < 2δ₀`, the bond condition
`|∂φ(b)| < δ₀` and, in regime (B), the site condition `|φ_x - h| < δ₀ ν^{-1/2}`
(written `ν |φ_x - h|² < δ₀²`, void when `ν = 0`, regime (A)). -/
structure BaseSpinSupport (G : GeneratingSet d L N₀ 1 ϱ) (ν δ₀ : ℝ)
    (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ) (D : BgData G N) : Prop where
  delta_pos : 0 < δ₀
  spin_unit : ∀ x, ∑ i, φ x i ^ 2 = 1
  h_unit : ∑ i, h i ^ 2 = 1
  block_real : ∀ x ∈ G.Ω 1, ∀ i, (D.Ψ x i).im = 0
  collar_eq : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (φ x i : ℂ)
  field_eq : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ)
  block_cond : ∀ x ∈ G.Ω 1, rn (fun i => (D.Ψ x i).re - spinBlockAverage G φ x i) < 2 * δ₀
  bond_cond : ∀ (x : Torus d (N₀ * L ^ 1)) (μ : Fin d),
    (x ∈ dataSites G ∨ x + Pi.single μ 1 ∈ dataSites G) →
      rn (fun i => φ (x + Pi.single μ 1) i - φ x i) < δ₀
  site_cond : ∀ x ∈ dataSites G, ν * ∑ i, (φ x i - h i) ^ 2 < δ₀ ^ 2

theorem spin_osc (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hB : ∀ (x : Torus d (N₀ * L ^ 1)) (μ : Fin d),
      (x ∈ dataSites G ∨ x + Pi.single μ 1 ∈ dataSites G) →
        rn (fun i => φ (x + Pi.single μ 1) i - φ x i) < δ₀)
    {x y : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) (hy : y ∈ G.blk 1 x) :
    rn (fun i => φ y i - φ x i) ≤ d * (L - 1) * δ₀ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set f : Torus d (N₀ * L ^ 1) → Fin N → ℂ := fun z i => (φ z i : ℂ) with hf
  have hbond : ∀ z z' : Torus d (N₀ * L ^ 1), z ∈ G.Ω 1 → z' ∈ G.Ω 1 → Adj z z' →
      vn (f z' - f z) ≤ (L * δ₀) * G.bondCost z z' := by
    intro z z' hz hz' hadj
    have hbc : G.bondCost z z' = 1 / L := by
      unfold GeneratingSet.bondCost
      rw [spacing_one G hz, spacing_one G hz', max_self]
    have hz1 : z ∈ dataSites G := (mem_dataSites G).2 (Or.inl hz)
    have hz1' : z' ∈ dataSites G := (mem_dataSites G).2 (Or.inl hz')
    have h1 : vn (f z' - f z) < δ₀ := by
      have e : vn (f z' - f z) = rn (fun i => φ z' i - φ z i) := vn_cast_sub _ _
      rw [e]
      obtain ⟨μ, h | h⟩ := hadj
      · subst h
        exact hB z μ (Or.inl hz1)
      · subst h
        have := hB z' μ (Or.inl hz1')
        rw [← vn_cast_sub] at this ⊢
        rwa [vn_sub_comm]
    rw [hbc]
    calc vn (f z' - f z) ≤ δ₀ := h1.le
      _ = (L * δ₀) * (1 / L) := by field_simp
  obtain ⟨c, hc, hp⟩ := exists_pathCost_block G le_rfl le_rfl (mem_layer_one G hx)
    (GeneratingSet.mem_blk.1 hy)
  have h := vn_sub_le_of_pathCost f hbond hp
  have e : vn (f y - f x) = rn (fun i => φ y i - φ x i) := vn_cast_sub _ _
  rw [e] at h
  refine h.trans ?_
  calc (L * δ₀) * c ≤ (L * δ₀) * (d * ((L : ℝ) ^ 1 - 1) / (L : ℝ) ^ 1) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = d * (L - 1) * δ₀ := by simp only [pow_one]; field_simp


theorem blockMean_cast (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (x : Torus d (N₀ * L ^ 1)) (i : Fin N) :
    blockMean G 1 (fun y => (φ y i : ℂ)) x = (spinBlockAverage G φ x i : ℂ) := by
  unfold blockMean spinBlockAverage
  push_cast
  simp

theorem rn_spinBlockAverage_sub_le (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hB : ∀ (x : Torus d (N₀ * L ^ 1)) (μ : Fin d),
      (x ∈ dataSites G ∨ x + Pi.single μ 1 ∈ dataSites G) →
        rn (fun i => φ (x + Pi.single μ 1) i - φ x i) < δ₀)
    {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) :
    rn (fun i => spinBlockAverage G φ x i - φ x i) ≤ d * (L - 1) * δ₀ := by
  have h := vn_blockMean_sub_le (G := G) (n := 1) le_rfl (fun y i => (φ y i : ℂ)) x
    (fun i => (φ x i : ℂ)) (c := d * (L - 1) * δ₀) (fun y hy => by
      have e : vn (fun i => (φ y i : ℂ) - (φ x i : ℂ)) = rn (fun i => φ y i - φ x i) :=
        vn_cast_sub _ _
      rw [e]; exact spin_osc G φ hδ₀ hB hx hy)
  simp only [blockMean_cast] at h
  have e : vn (fun i => (spinBlockAverage G φ x i : ℂ) - (φ x i : ℂ)) =
      rn (fun i => spinBlockAverage G φ x i - φ x i) := vn_cast_sub _ _
  rwa [e] at h

theorem rn_spinBlockAverage_le_one (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ)
    (hφ : ∀ x, ∑ i, φ x i ^ 2 = 1) {x : Torus d (N₀ * L ^ 1)} :
    rn (spinBlockAverage G φ x) ≤ 1 := by
  have h := vn_blockMean_le (G := G) (n := 1) le_rfl (fun y i => (φ y i : ℂ)) x (c := 1)
    (fun y _ => by
      rw [vn_ofReal]
      unfold rn
      rw [hφ y]; simp)
  simp only [blockMean_cast] at h
  rwa [vn_ofReal] at h

theorem sqrt_mul_rn_spinBlockAverage_sub_le (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    {ν δ₀ : ℝ} (hν : 0 ≤ ν) (hδ₀ : 0 < δ₀)
    (hS : ∀ y ∈ dataSites G, ν * ∑ i, (φ y i - h i) ^ 2 < δ₀ ^ 2)
    {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) :
    Real.sqrt ν * rn (fun i => spinBlockAverage G φ x i - h i) ≤ δ₀ := by
  have hm := vn_blockMean_sub_le_scaled (G := G) (n := 1) le_rfl (fun y i => (φ y i : ℂ)) x
    (fun i => (h i : ℂ)) (s := Real.sqrt ν) (c := δ₀) (Real.sqrt_nonneg ν) (fun y hy => by
      have hy1 : y ∈ G.Ω 1 := G.layer_subset le_rfl le_rfl
        (mem_layer_of_mem_blk (G := G) le_rfl le_rfl (mem_layer_one G hx) hy)
      have e : vn (fun i => (φ y i : ℂ) - (h i : ℂ)) = rn (fun i => φ y i - h i) := vn_cast_sub _ _
      rw [e]
      have h1 := hS y ((mem_dataSites G).2 (Or.inl hy1))
      have h2 : (Real.sqrt ν * rn (fun i => φ y i - h i)) ^ 2 ≤ δ₀ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hν, rn_sq_sum]; exact h1.le
      exact le_of_sq_le_sq h2 hδ₀.le)
  simp only [blockMean_cast] at hm
  have e : vn (fun i => (spinBlockAverage G φ x i : ℂ) - (h i : ℂ)) =
      rn (fun i => spinBlockAverage G φ x i - h i) := vn_cast_sub _ _
  rwa [e] at hm

theorem rn_sub_comm' (u v : Fin N → ℝ) :
    rn (fun i => u i - v i) = rn (fun i => v i - u i) := by
  have := rn_smul (-1) (fun i => u i - v i)
  rw [show (fun i => -1 * (u i - v i)) = fun i => v i - u i by funext i; ring] at this
  simpa using this.symm


/-- Two unit vectors at distance at most `r ≤ 1/4`: positive scalar product and tangent part
bounded by the distance. -/
theorem chart_aux (e w : Fin N → ℝ) (he : ∑ i, e i ^ 2 = 1) (hw : ∑ i, w i ^ 2 = 1) {r : ℝ}
    (hr : rn (fun i => w i - e i) ≤ r) (hr4 : r ≤ 1 / 4) :
    0 < ∑ i, e i * w i ∧
      rn (fun i => w i - (∑ j, e j * w j) * e i) ≤ r := by
  set p : ℝ := ∑ j, e j * w j with hp
  have hq : rn (fun i => w i - e i) ^ 2 = 2 - 2 * p := by
    rw [rn_sq_sum]
    calc ∑ i, (w i - e i) ^ 2 = ∑ i, (w i ^ 2 - 2 * (e i * w i) + e i ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = 2 - 2 * p := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, he]; ring
  have hq0 := rn_nonneg (fun i => w i - e i)
  have hr0 : rn (fun i => w i - e i) ≤ 1 / 4 := hr.trans hr4
  have hp1 : 1 - 1 / 32 ≤ p := by nlinarith
  have hp2 : p ≤ 1 := by nlinarith
  refine ⟨by linarith, ?_⟩
  have ht : rn (fun i => w i - p * e i) ^ 2 = 1 - p ^ 2 := by
    rw [rn_sq_sum]
    calc ∑ i, (w i - p * e i) ^ 2 = ∑ i, (w i ^ 2 - 2 * p * (e i * w i) + p ^ 2 * e i ^ 2) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = 1 - p ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hw, he, ← hp]; ring
  have : rn (fun i => w i - p * e i) ^ 2 ≤ rn (fun i => w i - e i) ^ 2 := by
    rw [ht, hq]; nlinarith
  exact (le_of_sq_le_sq (this.trans_eq' rfl) hq0 |>.trans hr)

section Domain

variable {G} {a : ℕ → ℝ} {ν δ₀ : ℝ} {φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ} {h : Fin N → ℝ}
  {D : BgData G N}

/-- The real part of the lifted data. -/
noncomputable def realPart (D : BgData G N) : Torus d (N₀ * L ^ 1) → Fin N → ℝ :=
  fun x i => (D.Ψ x i).re

theorem BaseSpinSupport.rn_realPart_sub_spin (S : BaseSpinSupport G ν δ₀ φ h D) {x : Torus d (N₀ * L ^ 1)}
    (hx : x ∈ G.Ω 1) :
    rn (fun i => realPart D x i - φ x i) < (d * (L - 1) + 2) * δ₀ := by
  have h1 := S.block_cond x hx
  have h2 := rn_spinBlockAverage_sub_le G φ S.delta_pos S.bond_cond hx
  have h3 := rn_triangle (realPart D x) (spinBlockAverage G φ x) (φ x)
  unfold realPart at h3 ⊢
  nlinarith

theorem BaseSpinSupport.anchor (S : BaseSpinSupport G ν δ₀ φ h D) {w v : Torus d (N₀ * L ^ 1)}
    (hw : w ∈ dataSites G) (hv : v ∈ blockSet G w) :
    rn (fun i => realPart D w i - φ v i) < 2 * δ₀ + d * (L - 1) * δ₀ := by
  have hpos := S.delta_pos
  have hK : 0 ≤ (d : ℝ) * (L - 1) * δ₀ := by
    have h1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have h2 : (0 : ℝ) ≤ d := by positivity
    exact mul_nonneg (mul_nonneg h2 (sub_nonneg.2 h1)) hpos.le
  rcases (mem_dataSites G).1 hw with hw1 | hw1
  · rw [blockSet_of_mem G hw1, layerIndex_one G hw1] at hv
    have hv1 : v ∈ G.Ω 1 := G.layer_subset le_rfl le_rfl
      (mem_layer_of_mem_blk (G := G) le_rfl le_rfl (mem_layer_one G hw1) hv)
    have hblk : G.blk 1 v = G.blk 1 w := by
      ext z
      rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk]
      rw [GeneratingSet.mem_blk] at hv
      rw [hv]
    have h1 := S.block_cond w hw1
    have h2 := rn_spinBlockAverage_sub_le G φ S.delta_pos S.bond_cond hv1
    have e : spinBlockAverage G φ v = spinBlockAverage G φ w := by
      funext i; unfold spinBlockAverage; rw [hblk]
    rw [e] at h2
    have h3 := rn_triangle (realPart D w) (spinBlockAverage G φ w) (φ v)
    unfold realPart at h3 ⊢
    linarith
  · have hn : w ∉ G.Ω 1 := ((mem_collar G).1 hw1).1
    rw [blockSet_of_not_mem G hn, Finset.mem_singleton] at hv
    subst hv
    have : (fun i => realPart D v i - φ v i) = fun _ => 0 := by
      funext i; unfold realPart; rw [S.collar_eq v hw1]; simp
    rw [this]
    have : rn (fun _ : Fin N => (0 : ℝ)) = 0 := by unfold rn; simp
    rw [this]; linarith

theorem bond_adj (S : BaseSpinSupport G ν δ₀ φ h D) {z z' : Torus d (N₀ * L ^ 1)} (hadj : Adj z z')
    (hz : z ∈ dataSites G) : rn (fun i => φ z i - φ z' i) < δ₀ := by
  obtain ⟨μ, hh | hh⟩ := hadj
  · subst hh
    have := S.bond_cond z μ (Or.inl hz)
    rwa [rn_sub_comm']
  · subst hh
    exact S.bond_cond z' μ (Or.inr hz)

/-- **The lifted data of the first step lie in `Ψ̃(G_1(□'); 4 d L δ₀)`**
(LF-RECONSTRUCTION Lemma II.7.5, proof: (R1)–(R4) of BG §1.3). -/
theorem inDomainR_base (H : BgHyp d L 1 ϱ a ν) (S : BaseSpinSupport G ν δ₀ φ h D)
    (hsmall : 4 * d * L * δ₀ ≤ 1 / 1024) : InDomainR G ν (4 * d * L * δ₀) D := by
  have hpos := S.delta_pos
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast H.hL
  set δ : ℝ := 4 * d * L * δ₀ with hδ
  have hδpos : 0 < δ := by positivity
  set K : ℝ := d * (L - 1) * δ₀ with hK
  set ε1 : ℝ := (d * (L - 1) + 2) * δ₀ with hε1
  have hdL : (3 : ℝ) * L ≤ d * L := by nlinarith
  have hε1le : ε1 ≤ δ₀ * (d * L) := by rw [hε1]; nlinarith
  have hε1small : 3 * ε1 ≤ 1 / 2 := by
    have : δ₀ * (d * L) ≤ 1 / 4096 := by rw [hδ] at hsmall; nlinarith
    nlinarith
  have hΨφ := fun {x : Torus d (N₀ * L ^ 1)} (hx : x ∈ G.Ω 1) => S.rn_realPart_sub_spin hx
  -- the norm of the data on blocks
  have hnorm : ∀ x ∈ G.Ω 1, |rn (realPart D x) ^ 2 - 1| < 3 * ε1 := by
    intro x hx
    have h1 := hΨφ hx
    have h2 := rn_triangle (realPart D x) (φ x) (fun _ => 0)
    have h3 := rn_triangle (φ x) (realPart D x) (fun _ => 0)
    have hφ1 : rn (φ x) = 1 := by unfold rn; rw [S.spin_unit x]; simp
    have e0 : ∀ v : Fin N → ℝ, rn (fun i => v i - 0) = rn v := fun v => by simp
    simp only [e0] at h2 h3
    have hsw : rn (fun i => φ x i - realPart D x i) = rn (fun i => realPart D x i - φ x i) := by
      have := rn_smul (-1) (fun i => realPart D x i - φ x i)
      rw [show (fun i => -1 * (realPart D x i - φ x i)) = fun i => φ x i - realPart D x i by
        funext i; ring] at this
      simpa using this
    rw [hsw] at h3
    have hr0 := rn_nonneg (realPart D x)
    have hε0 : 0 ≤ ε1 := by
      rw [hε1]; have : (1 : ℝ) ≤ L := by linarith
      have : (0 : ℝ) ≤ d := by linarith
      positivity
    rw [abs_lt]
    constructor <;> nlinarith
  refine ⟨realPart D, h, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n hn1 hnk x hx x' hx'
    have := D.Ψ_layerConst n hn1 hnk x hx x' hx'
    funext i
    simp only [realPart, this]
  · -- (R1)
    intro x x' hxx'
    obtain ⟨hx, hx', -, z, hz, z', hz', hadj⟩ := hxx'
    have h1 := S.anchor hx hz
    have h2 := S.anchor hx' hz'
    have hzd := blockSet_subset_dataSites hx hz
    have h3 := bond_adj S hadj hzd
    have t1 := rn_triangle (realPart D x) (φ z) (realPart D x')
    have t2 := rn_triangle (φ z) (φ z') (realPart D x')
    rw [rn_sub_comm' (φ z') (realPart D x')] at t2
    have : 5 * δ₀ + 2 * K ≤ δ := by
      rw [hK, hδ]; nlinarith
    linarith
  · -- (R2)
    intro x hx
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have := hnorm x hx1
      rw [← rn_sq_sum] at *
      have h3 : 3 * ε1 < δ := by rw [hε1, hδ]; nlinarith
      linarith
    · have : realPart D x = φ x := by
        funext i; unfold realPart; rw [S.collar_eq x hx1 i]; simp
      rw [this, S.spin_unit x]
      simpa using hδpos
  · -- (R3)
    intro x hx
    have hc0 : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := mul_nonneg H.mass (by positivity)
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have hli := layerIndex_one G hx1
      rw [hli]
      have hc1 : ν * ((L : ℝ) ^ 1) ^ 2 ≤ 1 := H.massLe
      have hs : Real.sqrt (ν * ((L : ℝ) ^ 1) ^ 2) = Real.sqrt ν * L := by
        rw [Real.sqrt_mul H.mass, pow_one, Real.sqrt_sq (by linarith)]
      have hν1 : Real.sqrt ν * L ≤ 1 := by rw [← hs]; exact Real.sqrt_le_one.2 hc1
      have hdist : Real.sqrt ν * L * rn (fun i => realPart D x i - h i) ≤ (L + 2) * δ₀ := by
        have t := rn_triangle (realPart D x) (spinBlockAverage G φ x) h
        have h1 := S.block_cond x hx1
        have h2 := sqrt_mul_rn_spinBlockAverage_sub_le G φ h H.mass hpos S.site_cond hx1
        have hs0 : 0 ≤ Real.sqrt ν * L := by positivity
        have hrn0 := rn_nonneg (fun i => spinBlockAverage G φ x i - h i)
        have hrn1 := rn_nonneg (fun i => realPart D x i - spinBlockAverage G φ x i)
        calc Real.sqrt ν * L * rn (fun i => realPart D x i - h i)
            ≤ Real.sqrt ν * L * (rn (fun i => realPart D x i - spinBlockAverage G φ x i) +
                rn (fun i => spinBlockAverage G φ x i - h i)) :=
              mul_le_mul_of_nonneg_left t hs0
          _ = Real.sqrt ν * L * rn (fun i => realPart D x i - spinBlockAverage G φ x i) +
                L * (Real.sqrt ν * rn (fun i => spinBlockAverage G φ x i - h i)) := by ring
          _ ≤ 1 * (2 * δ₀) + L * δ₀ := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by linarith))
              exact mul_le_mul hν1 (le_of_lt (by simpa [realPart] using h1)) hrn1 zero_le_one
          _ = (L + 2) * δ₀ := by ring
      have key := r3_core (Ψ := realPart D x) (h0 := h) (s := Real.sqrt ν * L)
        (c := ν * ((L : ℝ) ^ 1) ^ 2) (b := 3 * ε1) (E := (L + 2) * δ₀) (δ := δ)
        (by have : (0 : ℝ) ≤ L := by linarith
            have := Real.sqrt_nonneg ν
            positivity) hν1 (by rw [← hs, Real.sq_sqrt (mul_nonneg H.mass (by positivity))]) (hnorm x hx1).le hε1small
        hdist (by rw [S.h_unit]; simpa using pow_pos hδpos 2)
      have hbE : 3 * ε1 + (L + 2) * δ₀ ≤ δ := by rw [hε1, hδ]; nlinarith
      have hbE0 : 0 ≤ 3 * ε1 + (L + 2) * δ₀ := by
        have : 0 ≤ ε1 := by
          rw [hε1]; have : (1 : ℝ) ≤ L := by linarith
          have : (0 : ℝ) ≤ d := by linarith
          positivity
        positivity
      have := pow_le_pow_left₀ hbE0 hbE 2
      linarith
    · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx1).1
      have hli := layerIndex_of_not_mem G hn
      rw [hli]
      have hxφ : realPart D x = φ x := by
        funext i; unfold realPart; rw [S.collar_eq x hx1 i]; simp
      have hc1 : ν * ((L : ℝ) ^ 0) ^ 2 ≤ 1 := by
        have := H.massLe
        have hL1 : (1 : ℝ) ≤ L := by linarith
        simp only [pow_zero, one_pow, mul_one]
        simp only [pow_one] at this
        nlinarith [H.mass]
      have hdist : Real.sqrt (ν * ((L : ℝ) ^ 0) ^ 2) * rn (fun i => realPart D x i - h i) ≤ δ₀ := by
        have h1 := S.site_cond x hx
        rw [hxφ]
        simp only [pow_zero, one_pow, mul_one]
        have h2 : (Real.sqrt ν * rn (fun i => φ x i - h i)) ^ 2 ≤ δ₀ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt H.mass, rn_sq_sum]; exact h1.le
        exact le_of_sq_le_sq h2 hpos.le
      have hb : |rn (realPart D x) ^ 2 - 1| ≤ 0 := by
        rw [hxφ]; unfold rn; rw [S.spin_unit x]; simp
      have key := r3_core (Ψ := realPart D x) (h0 := h) (s := Real.sqrt (ν * ((L : ℝ) ^ 0) ^ 2))
        (c := ν * ((L : ℝ) ^ 0) ^ 2) (b := 0) (E := δ₀) (δ := δ)
        (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hc1) (by rw [Real.sq_sqrt (mul_nonneg H.mass (by positivity))]) hb
        (by norm_num) hdist (by rw [S.h_unit]; simpa using pow_pos hδpos 2)
      have hδ0δ : δ₀ ≤ δ := by rw [hδ]; nlinarith
      have := pow_le_pow_left₀ (by simpa using hpos.le : (0 : ℝ) ≤ 0 + δ₀) (by simpa using hδ0δ : 0 + δ₀ ≤ δ) 2
      linarith
  · -- (R4)
    rw [S.h_unit]; simpa using pow_pos hδpos 2
  · intro x hx i
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have him := S.block_real x hx1 i
      unfold realPart
      apply Complex.ext <;> simp [him]
    · rw [S.collar_eq x hx1 i]; unfold realPart; rw [S.collar_eq x hx1 i]; simp
  · intro x hx i
    exact S.field_eq x hx i

/-- **Lemma II.7.5** (small-field spins lie in the chart).  For the base data (`G_1(□')` with
`k = 1`; `BaseSpinSupport`) and the thresholds (Λ26) `4 d L δ₀ ≤ c₁`, `C_hs L δ₀ ≤ 1/4` with
`C_hs = d + 2 + 4 d K₁`, the step background `φ^b = bgField` satisfies, for every `x ∈ Ω₁`,
`|φ_x - φ^b(x)| ≤ C_hs L δ₀ (≤ 1/4)`; hence `φ_x · φ^b(x) > 0` (the spin lies in the open
hemisphere of the chart around `e_x = φ^b(x)`), and the chart coordinate
`ξ_x = φ_x - (φ_x · e_x) e_x ∈ e_x^⊥` satisfies `|ξ_x| ≤ C_hs L δ₀`. -/
theorem spins_near_background (H : BgHyp d L 1 ϱ a ν) (S : BaseSpinSupport G ν δ₀ φ h D)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4) (x : G.Ω 1) :
    ∑ i, ((bgField G a ν D (x, i)).re) ^ 2 = 1 ∧
    rn (fun i => φ x i - (bgField G a ν D (x, i)).re) ≤ (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ∧
    0 < ∑ i, (bgField G a ν D (x, i)).re * φ x i ∧
    rn (fun i => φ x i - (∑ j, (bgField G a ν D (x, j)).re * φ x j) *
        (bgField G a ν D (x, i)).re) ≤ (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ := by
  have hpos := S.delta_pos
  have hd0 : 0 < d := by have := H.hd; omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast H.hL
  have hsmall : 4 * d * L * δ₀ ≤ 1 / 1024 :=
    (approxDelta_le d L (bgC1_facts d L N hd0 hΛ1).1).1
  have hD := inDomainR_base H S hsmall
  have hU : InUnionDomainR G (bgC1 d L N) ν D := ⟨_, by positivity, hΛ1, hD⟩
  obtain ⟨-, hunit, -, -, hbd⟩ := theorem71 H hU
  have hb := hbd _ (by positivity) hΛ1 hD
  have hbx := hb.val x
  have hxΩ : (x : Torus d (N₀ * L ^ 1)) ∈ G.Ω 1 := x.2
  -- the data are real
  have hDre : ∀ i, D.Ψ x i = (realPart D x i : ℂ) := fun i => by
    unfold realPart
    apply Complex.ext <;> simp [S.block_real x hxΩ i]
  -- the distance between φ_x and the data
  have h1 := S.rn_realPart_sub_spin hxΩ
  have e1 : vn (fun i => (φ x i : ℂ) - D.Ψ x i) = rn (fun i => φ x i - realPart D x i) := by
    rw [← vn_cast_sub]
    congr 1
    funext i; simp [hDre i]
  have e2 : rn (fun i => φ x i - realPart D x i) = rn (fun i => realPart D x i - φ x i) :=
    rn_sub_comm' _ _
  have t := vn_triangle (fun i => (φ x i : ℂ)) (D.Ψ x) (fun i => bgField G a ν D (x, i))
  -- real form of the background
  have hre : ∀ i, (bgField G a ν D (x, i)).im = 0 := fun i => (hunit x).1 i
  have hu1 : ∑ i, ((bgField G a ν D (x, i)).re) ^ 2 = 1 := by
    have := (hunit x).2
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply, hre i]; ring
  have hvn : vn (fun i => (φ x i : ℂ) - bgField G a ν D (x, i)) =
      rn (fun i => φ x i - (bgField G a ν D (x, i)).re) := by
    rw [← vn_cast_sub]
    congr 1
    funext i
    have : bgField G a ν D (x, i) = (((bgField G a ν D (x, i)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using hre i)
    simp only [Pi.sub_apply]
    rw [← this]
  have hbound : rn (fun i => φ x i - (bgField G a ν D (x, i)).re) ≤
      (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ := by
    rw [← hvn]
    have h2 : vn (fun i => D.Ψ x i - bgField G a ν D (x, i)) ≤ bgK1 d L N * (4 * d * L * δ₀) := by
      exact (vn_sub_comm (D.Ψ x) (fun i => bgField G a ν D (x, i))).le.trans hbx
    have h3 : vn ((fun i => (φ x i : ℂ)) - fun i => bgField G a ν D (x, i)) =
        vn (fun i => (φ x i : ℂ) - bgField G a ν D (x, i)) := rfl
    have h4 : vn ((fun i => (φ x i : ℂ)) - D.Ψ x) = vn (fun i => (φ x i : ℂ) - D.Ψ x i) := rfl
    have h5 : vn (D.Ψ x - fun i => bgField G a ν D (x, i)) =
        vn (fun i => D.Ψ x i - bgField G a ν D (x, i)) := rfl
    rw [h3, h4, h5] at t
    have hK1 := bgK1_pos d L N
    have hdl : (d : ℝ) * L ≥ 3 * L := by nlinarith
    nlinarith [mul_pos hpos (by linarith : (0 : ℝ) < L)]
  have hφx : ∑ i, φ x i ^ 2 = 1 := S.spin_unit x
  have hr4 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4 := hΛ2
  obtain ⟨c1, c2⟩ := chart_aux (fun i => (bgField G a ν D (x, i)).re) (fun i => φ x i) hu1 hφx
    (r := (d + 2 + 4 * d * bgK1 d L N) * L * δ₀) hbound hr4
  exact ⟨hu1, hbound, c1, c2⟩

end Domain

end One

end Balaban.LargeField
