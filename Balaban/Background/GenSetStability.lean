/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.GenSetStabilityData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stability of the background under a change of generating set

P7 p. 501 (2.14) (with P2 §4, Proposition 4.1, and P3 Proposition 2.1 for the changed layers): two
generating sets `Gl`, `Gw` on tori identified by a bijection `e : 𝕋_w ≃ 𝕋_l` (commuting with the
lattice steps and carrying `n`-blocks to `n`-blocks, `n ≤ k_l ≤ k_w`), with the standing hypotheses
of Theorem 5.2 for the same weights `a` and mass `ν`, real data `D_l`, `D_w` in `𝒟_ℝ`, and on the
ball `B(X, r)` the same layers (`Ω_n`, `1 ≤ n ≤ k_l + 1`), the same `h̃` and data within `δ_d`.  Then
for `y ∈ X ∩ Ω^l_1`

`|φ_l(y) - φ_w(e⁻¹ y)| ≤ K (δ_d + (δ_l + δ_w) e^{-γ_w (r - (ϱ_B + 3d) L^{k_l} - 2) / L^{k_l}})`

with `K`, `δ_s` depending on `(d, L, N)` only, under the smallness `K₁ (δ_l + δ_w) + δ_d ≤ δ_s`;
`ϱ_B ≤ ϱ_l` is any separation admissible for Theorem 5.2 and the weighted Green's function
(`genSet_stability`).  `φ_w(e⁻¹ y)` is written `transportField e Ψ_w φ_w y`, the form read by the
restricted actions (`actionRegionC_transport`).

Proof (the route of P7 (2.14)): `G_B ≺ G_l` is the restriction of `G_l` to a neighbourhood of `X`
(`exists_restrictGen`); by the composition identity (P2 Theorem 6.1 (ii)) the restrictions of `φ_l`
and of the transported `φ_w` solve (EL) of `G_B` for the composed data (`isEL_compose`,
`isEL_restrict_transport`); the composed data differ by `δ_d` where the layers of `G_B` and `G_l`
agree and by `9 (K₁ (δ_l + δ_w) + δ_d)` near the boundary of `G_B` (`compose_sub_le`); the weighted
Proposition 5.1 with a capped distance weight gives the bound (`twoEL_near_far`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField.ActionConv Finset

section Close

variable {d L N N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero L] {ϱl ϱw : ℝ}
  {Gl : GeneratingSet d L N₀l kl ϱl} {Gw : GeneratingSet d L N₀w kw ϱw}
  {e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)}

/-- The transported field is within `c_w + δ_d + c_l` of `φ_l` at a site where both backgrounds
satisfy the bounds of Theorem 5.2 (sizes `c_l`, `c_w`) and the data are within `δ_d`. -/
theorem transport_close {Dl : BgData Gl N} {Dw : BgData Gw N} {φl : Gl.Ω 1 × Fin N → ℂ}
    {αl : Gl.Ω 1 → ℂ} {φw : Gw.Ω 1 × Fin N → ℂ} {αw : Gw.Ω 1 → ℂ} {cl cw δd : ℝ}
    (hbl : BgBounds Gl Dl φl αl cl) (hbw : BgBounds Gw Dw φw αw cw) (x : Gl.Ω 1)
    (hx' : e.symm (x : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1)
    (hΨ : vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd) :
    vn (fun i => transportField (Gl := Gl) e Dw.Ψ φw (x, i) - φl (x, i)) ≤ cw + δd + cl := by
  classical
  have e2 : (fun i => transportField (Gl := Gl) e Dw.Ψ φw (x, i) - φl (x, i)) =
      (fun i => φw (⟨e.symm x, hx'⟩, i)) - fun i => φl (x, i) := by
    funext i; simp [transportField, barField, hx']
  have h1 : vn ((fun i => φw (⟨e.symm x, hx'⟩, i)) - Dw.Ψ (e.symm x)) ≤ cw := hbw.val ⟨e.symm x, hx'⟩
  have h3 := hbl.val x
  have t1 := vn_triangle (fun i => φw (⟨e.symm x, hx'⟩, i)) (Dw.Ψ (e.symm x)) (fun i => φl (x, i))
  have t2 := vn_triangle (Dw.Ψ (e.symm x)) (Dl.Ψ x) (fun i => φl (x, i))
  have h2 : vn (Dw.Ψ (e.symm x) - Dl.Ψ x) ≤ δd := by
    rw [vn_sub_comm]; exact hΨ
  have h3' : vn (Dl.Ψ x - fun i => φl (x, i)) ≤ cl := by
    rw [vn_sub_comm]; exact h3
  rw [e2]
  linarith

end Close

section Reach

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem layerIndex_le_top (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    G.layerIndex x ≤ k := by
  by_cases hx : x ∈ G.Ω 1
  · exact (G.layerIndex_spec hx).2.1
  · rw [layerIndex_of_not_mem G hx]; exact Nat.zero_le _

/-- A site within `r₀ + 1` of `X` and the block of its layer lie within `r ≥ r₀ + 1 + d L^k` of
`X`. -/
theorem ball_reach (G : GeneratingSet d L N₀ k ϱ) (X : Finset (Torus d (N₀ * L ^ k)))
    {r r₀ : ℝ} (hr₀ : r₀ + 1 + d * (L : ℝ) ^ k ≤ r) {x : Torus d (N₀ * L ^ k)}
    (hx : ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z x ≤ r₀ + 1) :
    ∀ y ∈ G.blk (G.layerIndex x) x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ r := by
  obtain ⟨z, hz, hzx⟩ := hx
  intro y hy
  refine ⟨z, hz, ?_⟩
  have hn := layerIndex_le_top G x
  have h1 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) z x y
  have h2 := torusDist_le_of_mem_blk G hn hy
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h3 : (d : ℝ) * (L : ℝ) ^ G.layerIndex x ≤ d * (L : ℝ) ^ k :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hn) (Nat.cast_nonneg d)
  linarith

omit [NeZero N₀] [NeZero L] in
theorem ball_reach_self {X : Finset (Torus d (N₀ * L ^ k))} {r r₀ : ℝ}
    (hr₀ : r₀ + 1 + d * (L : ℝ) ^ k ≤ r) {x : Torus d (N₀ * L ^ k)}
    (hx : ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z x ≤ r₀ + 1) :
    ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z x ≤ r := by
  obtain ⟨z, hz, hzx⟩ := hx
  have : 0 ≤ (d : ℝ) * (L : ℝ) ^ k := by positivity
  exact ⟨z, hz, by linarith⟩

theorem ball_reach_adj {X : Finset (Torus d (N₀ * L ^ k))} {r₀ : ℝ} {x w : Torus d (N₀ * L ^ k)}
    (hx : ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z x ≤ r₀) (hadj : Adj x w) :
    ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z w ≤ r₀ + 1 := by
  obtain ⟨z, hz, hzx⟩ := hx
  have h1 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) z x w
  have h2 := Adj.torusDist_le hadj
  exact ⟨z, hz, by linarith⟩

end Reach

section Main

variable {d L N N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero L] {ϱl ϱw ϱB : ℝ}
  {Gl : GeneratingSet d L N₀l kl ϱl} {Gw : GeneratingSet d L N₀w kw ϱw}
  {e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)}
  {GB : GeneratingSet d L N₀l kl ϱB}

open Classical in
/-- The transported pair restricted to `G_B` solves (EL) of `G_B` when `Ω^B_1` lies within `r₀` of
`X` and the layers, `h̃` and the data (through `D'`) agree within `r ≥ r₀ + 1 + d L^{k_l}`. -/
theorem restrict_isEL_of_near (hk : kl ≤ kw)
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    (X : Finset (Torus d (N₀l * L ^ kl))) {r r₀ : ℝ} (hr₀ : r₀ + 1 + d * (L : ℝ) ^ kl ≤ r)
    (hag : ∀ x ∈ {x | ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r},
      ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    (hp : Precedes GB Gl)
    (hnearB : ∀ x ∈ GB.Ω 1, ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r₀)
    (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ j → j ≤ kl → a j ≠ 0) (ν : ℝ) {Dl D' : BgData Gl N}
    {Dw : BgData Gw N} (hD'h : ∀ x, D'.h x = Dl.h x)
    (hD'Ψ : ∀ x ∈ dataSites Gl, (∀ y ∈ Gl.blk (Gl.layerIndex x) x,
      y ∈ {x | ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r}) → D'.Ψ x = Dw.Ψ (e.symm x))
    (hh : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) → Dl.h x = Dw.h (e.symm x))
    {φw : Gw.Ω 1 × Fin N → ℂ} {αw : Gw.Ω 1 → ℂ} (hEL : IsEL Gw a ν Dw φw αw) :
    IsEL GB a ν (composeData hp a (transportField (Gl := Gl) e Dw.Ψ φw) D')
      (hp.restrictφ (transportField (Gl := Gl) e Dw.Ψ φw))
      (hp.restrictα
        (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0)) := by
  set A : Set (Torus d (N₀l * L ^ kl)) :=
    {x | ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r} with hA
  have hnear1 : ∀ x ∈ GB.Ω 1, ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r₀ + 1 := by
    intro x hx
    obtain ⟨z, hz, h⟩ := hnearB x hx
    exact ⟨z, hz, by linarith⟩
  have hxA : ∀ x ∈ GB.Ω 1, x ∈ A := fun x hx => ball_reach_self hr₀ (hnear1 x hx)
  have hΩ : ∀ x ∈ GB.Ω 1, e.symm x ∈ Gw.Ω 1 := fun x hx =>
    (hag x (hxA x hx) 1 le_rfl (by omega)).1 (hp.mem_Ω1 hx)
  have hΨ' : ∀ x ∈ GB.Ω 1, D'.Ψ x = Dw.Ψ (e.symm x) := fun x hx =>
    hD'Ψ x ((mem_dataSites Gl).2 (Or.inl (hp.mem_Ω1 hx))) (ball_reach Gl X hr₀ (hnear1 x hx))
  have hh' : ∀ x ∈ GB.Ω 1, D'.h x = Dw.h (e.symm x) := fun x hx => by
    rw [hD'h]; exact hh x (hxA x hx)
  have hw : ∀ x ∈ GB.Ω 1, ∀ w, Adj x w →
      w ∈ A ∧ (w ∉ Gl.Ω 1 → D'.Ψ w = Dw.Ψ (e.symm w)) := by
    intro x hx w hadj
    have hwn := ball_reach_adj (hnearB x hx) hadj
    refine ⟨ball_reach_self hr₀ hwn, fun hw1 => ?_⟩
    have hwc : w ∈ collar Gl := mem_collar_of_adj Gl (hp.mem_Ω1 hx) hw1 hadj
    exact hD'Ψ w ((mem_dataSites Gl).2 (Or.inr hwc)) (ball_reach Gl X hr₀ hwn)
  exact isEL_restrict_transport hk he hag hblk hp a ha ν D' Dw hEL hΩ hxA hΨ' hh'
    (fun x hx μ => ⟨hw x hx _ (adj_add_single x μ), hw x hx _ (adj_sub_single x μ)⟩)

/-- At a data site of `Gl` whose block lies in the ball, the transported datum is within `δ_d` of
`D_l`. -/
theorem transportData_close (X : Finset (Torus d (N₀l * L ^ kl))) {r δd : ℝ}
    {Dl D' : BgData Gl N} {Dw : BgData Gw N}
    (hD'Ψ : ∀ x ∈ dataSites Gl, (∀ y ∈ Gl.blk (Gl.layerIndex x) x,
      y ∈ {x | ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r}) → D'.Ψ x = Dw.Ψ (e.symm x))
    (hΨ : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd)
    {x : Torus d (N₀l * L ^ kl)} (hxd : x ∈ dataSites Gl)
    (hP : ∀ y ∈ Gl.blk (Gl.layerIndex x) x, ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z y ≤ r) :
    vn (fun i => D'.Ψ x i - Dl.Ψ x i) ≤ δd := by
  rw [hD'Ψ x hxd hP]
  have hxA := hP x (GeneratingSet.mem_blk.2 rfl)
  have h := hΨ x hxA
  have e1 : (fun i => Dw.Ψ (e.symm x) i - Dl.Ψ x i) = Dw.Ψ (e.symm x) - Dl.Ψ x := rfl
  have e2 : (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) = Dl.Ψ x - Dw.Ψ (e.symm x) := rfl
  rw [e1, vn_sub_comm, ← e2]
  exact h

/-- **The change of the composed datum on `G_B`**: at most `9 T` at every data site of `G_B`, if
the transported field is within `T ≥ δ_d` of `φ_l` on the ball. -/
theorem restrict_deltaPsi_le (hp : Precedes GB Gl) {a : ℕ → ℝ} (ha : IsAdmissibleWeights kl a)
    (X : Finset (Torus d (N₀l * L ^ kl))) {r r₀ δd T : ℝ} (hr₀ : r₀ + 1 + d * (L : ℝ) ^ kl ≤ r)
    (hnearB : ∀ x ∈ GB.Ω 1, ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r₀)
    {Dl D' : BgData Gl N} {Dw : BgData Gw N}
    (hD'Ψ : ∀ x ∈ dataSites Gl, (∀ y ∈ Gl.blk (Gl.layerIndex x) x,
      y ∈ {x | ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r}) → D'.Ψ x = Dw.Ψ (e.symm x))
    (hΨ : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd)
    {φl φ' : Gl.Ω 1 × Fin N → ℂ}
    (hS0 : ∀ x : Gl.Ω 1, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      vn (fun i => φ' (x, i) - φl (x, i)) ≤ T) (hδd : 0 ≤ δd) (hdT : δd ≤ T) :
    ∀ z ∈ dataSites GB, vn (fun i => (composeData hp a φ' D').Ψ z i -
      (composeData hp a φl Dl).Ψ z i) ≤ 9 * T := by
  classical
  have hT0 : 0 ≤ T := hδd.trans hdT
  intro z hz
  rcases (mem_dataSites GB).1 hz with hzB | hzc
  · have hnz : ∃ w ∈ X, Green.torusDist d (N₀l * L ^ kl) w z ≤ r₀ + 1 := by
      obtain ⟨w, hw, h⟩ := hnearB z hzB
      exact ⟨w, hw, by linarith⟩
    have hPz := ball_reach Gl X hr₀ hnz
    have hz1 := hp.mem_Ω1 hzB
    have hS : ∀ y ∈ Gl.blk (Gl.layerIndex z) z,
        vn (fun i => svec Gl φ' y i - svec Gl φl y i) ≤ T := by
      intro y hy
      obtain ⟨hn1, hnk, -⟩ := Gl.layerIndex_spec hz1
      have hy1 : y ∈ Gl.Ω 1 := Gl.layer_subset hn1 hnk (blk_mem_layer hz1 hy)
      have e1 : (fun i => svec Gl φ' y i - svec Gl φl y i) =
          fun i => φ' (⟨y, hy1⟩, i) - φl (⟨y, hy1⟩, i) := by
        funext i; rw [svec_of_mem' φ' hy1, svec_of_mem' φl hy1]
      rw [e1]
      exact hS0 ⟨y, hy1⟩ (hPz y hy)
    have hΨz := transportData_close X hD'Ψ hΨ ((mem_dataSites Gl).2 (Or.inl hz1)) hPz
    have h := compose_sub_le hp ha φl φ' Dl.Ψ D'.Ψ hzB hS hΨz
    show vn (fun i => composeField GB Gl a φ' D'.Ψ z i - composeField GB Gl a φl Dl.Ψ z i) ≤ 9 * T
    linarith
  · obtain ⟨hzn, x, hx, hadj⟩ := (mem_collar GB).1 hzc
    have hzn1 := ball_reach_adj (hnearB x hx) hadj
    have e1 : (fun i => (composeData hp a φ' D').Ψ z i - (composeData hp a φl Dl).Ψ z i) =
        fun i => barField Gl D'.Ψ φ' z i - barField Gl Dl.Ψ φl z i := by
      funext i
      show composeField GB Gl a φ' D'.Ψ z i - composeField GB Gl a φl Dl.Ψ z i = _
      rw [composeField_of_collar a φ' D'.Ψ hzc i, composeField_of_collar a φl Dl.Ψ hzc i]
    rw [e1]
    by_cases hz1 : z ∈ Gl.Ω 1
    · have e2 : (fun i => barField Gl D'.Ψ φ' z i - barField Gl Dl.Ψ φl z i) =
          fun i => φ' (⟨z, hz1⟩, i) - φl (⟨z, hz1⟩, i) := by
        funext i; simp [barField, hz1]
      rw [e2]
      have := hS0 ⟨z, hz1⟩ (ball_reach_self hr₀ hzn1)
      linarith
    · have hzc' : z ∈ collar Gl := mem_collar_of_adj Gl (hp.mem_Ω1 hx) hz1 (hadj.symm.symm)
      have e2 : (fun i => barField Gl D'.Ψ φ' z i - barField Gl Dl.Ψ φl z i) =
          fun i => D'.Ψ z i - Dl.Ψ z i := by
        funext i; simp [barField, hz1]
      rw [e2]
      have := transportData_close X hD'Ψ hΨ ((mem_dataSites Gl).2 (Or.inr hzc'))
        (ball_reach Gl X hr₀ hzn1)
      linarith

/-- **The change of the composed datum near `X`**: at a site of `Ω^B_1` where the two layer indices
agree and every neighbour in `Ω^l_1` is in `Ω^B_1`, the change at the site and at its collar
neighbours is at most `δ_d`. -/
theorem restrict_deltaPsi_near (hp : Precedes GB Gl) {a : ℕ → ℝ}
    (ha : ∀ j, 1 ≤ j → j ≤ kl → a j ≠ 0)
    (X : Finset (Torus d (N₀l * L ^ kl))) {r r₀ δd : ℝ} (hr₀ : r₀ + 1 + d * (L : ℝ) ^ kl ≤ r)
    (hnearB : ∀ x ∈ GB.Ω 1, ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r₀)
    {Dl D' : BgData Gl N} {Dw : BgData Gw N}
    (hD'Ψ : ∀ x ∈ dataSites Gl, (∀ y ∈ Gl.blk (Gl.layerIndex x) x,
      y ∈ {x | ∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r}) → D'.Ψ x = Dw.Ψ (e.symm x))
    (hΨ : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd)
    (φl φ' : Gl.Ω 1 × Fin N → ℂ) {x : Torus d (N₀l * L ^ kl)} (hx : x ∈ GB.Ω 1)
    (hlay : GB.layerIndex x = Gl.layerIndex x)
    (hnb : ∀ w, Adj x w → w ∈ Gl.Ω 1 → w ∈ GB.Ω 1) :
    vn (fun i => (composeData hp a φ' D').Ψ x i - (composeData hp a φl Dl).Ψ x i) ≤ δd ∧
      ∀ w ∈ collar GB, Adj x w →
        vn (fun i => (composeData hp a φ' D').Ψ w i - (composeData hp a φl Dl).Ψ w i) ≤ δd := by
  classical
  have hx1 := hp.mem_Ω1 hx
  have hnx : ∃ w ∈ X, Green.torusDist d (N₀l * L ^ kl) w x ≤ r₀ + 1 := by
    obtain ⟨w, hw, h⟩ := hnearB x hx
    exact ⟨w, hw, by linarith⟩
  have hax : a (Gl.layerIndex x) ≠ 0 := ha _ (Gl.layerIndex_spec hx1).1 (Gl.layerIndex_spec hx1).2.1
  refine ⟨?_, fun w hwc hadj => ?_⟩
  · have e1 : (fun i => (composeData hp a φ' D').Ψ x i - (composeData hp a φl Dl).Ψ x i) =
        fun i => D'.Ψ x i - Dl.Ψ x i := by
      funext i
      show composeField GB Gl a φ' D'.Ψ x i - composeField GB Gl a φl Dl.Ψ x i = _
      rw [composeField_eq_of_layer_eq a D' φ' hx hax hlay i,
        composeField_eq_of_layer_eq a Dl φl hx hax hlay i]
    rw [e1]
    exact transportData_close X hD'Ψ hΨ ((mem_dataSites Gl).2 (Or.inl hx1))
      (ball_reach Gl X hr₀ hnx)
  · have hwB : w ∉ GB.Ω 1 := ((mem_collar GB).1 hwc).1
    have hw1 : w ∉ Gl.Ω 1 := fun h => hwB (hnb w hadj h)
    have hwc' : w ∈ collar Gl := mem_collar_of_adj Gl hx1 hw1 hadj
    have e1 : (fun i => (composeData hp a φ' D').Ψ w i - (composeData hp a φl Dl).Ψ w i) =
        fun i => D'.Ψ w i - Dl.Ψ w i := by
      funext i
      show composeField GB Gl a φ' D'.Ψ w i - composeField GB Gl a φl Dl.Ψ w i = _
      rw [composeField_of_collar a φ' D'.Ψ hwc i, composeField_of_collar a φl Dl.Ψ hwc i]
      simp [barField, hw1]
    rw [e1]
    exact transportData_close X hD'Ψ hΨ ((mem_dataSites Gl).2 (Or.inr hwc'))
      (ball_reach Gl X hr₀ (ball_reach_adj (hnearB x hx) hadj))

end Main

end Balaban.Background
