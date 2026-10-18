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

open Classical in
/-- The multiplier change on `G_B` is small: both multipliers satisfy the bounds of Theorem 5.2 and
the spacing of `G_B` is at most those of `Gl` and `Gw`. -/
theorem restrict_small_alpha (hk : kl ≤ kw) {A : Set (Torus d (N₀l * L ^ kl))}
    (hag : ∀ x ∈ A, ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    (hp : Precedes GB Gl) (hA : ∀ x ∈ GB.Ω 1, x ∈ A) {Dl : BgData Gl N} {Dw : BgData Gw N}
    {φl : Gl.Ω 1 × Fin N → ℂ} {αl : Gl.Ω 1 → ℂ} {φw : Gw.Ω 1 × Fin N → ℂ} {αw : Gw.Ω 1 → ℂ}
    {cl cw : ℝ} (hbl : BgBounds Gl Dl φl αl cl) (hbw : BgBounds Gw Dw φw αw cw)
    (hc : cl + cw ≤ c6 d L N) :
    Small GB (hp.restrictα
        (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0) -
      hp.restrictα αl) (c6 d L N) := by
  intro x
  have hx := x.2
  have hxA := hA x hx
  have hx1 := hp.mem_Ω1 hx
  have hxw : e.symm (x : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 := (hag x hxA 1 le_rfl (by omega)).1 hx1
  have e1 : hp.restrictα
      (fun z => if h : e.symm (z : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1 then αw ⟨_, h⟩ else 0) x =
      αw ⟨e.symm x, hxw⟩ := by
    simp [Precedes.restrictα, hxw]
  simp only [Pi.sub_apply, e1]
  have hlay := layerIndex_transport hk hag hxA
  have hsp1 : GB.spacing (x : Torus d (N₀l * L ^ kl)) ≤ Gl.spacing (x : Torus d (N₀l * L ^ kl)) := by
    have := scaleGap_one hp x hx
    rwa [one_mul] at this
  have hsp2 : Gl.spacing (x : Torus d (N₀l * L ^ kl)) =
      Gw.spacing (e.symm (x : Torus d (N₀l * L ^ kl))) := by
    unfold GeneratingSet.spacing; rw [hlay]
  have h0 : 0 ≤ GB.spacing (x : Torus d (N₀l * L ^ kl)) := (spacing_pos GB).le
  have hq1 : GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 ≤ Gl.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 :=
    pow_le_pow_left₀ h0 hsp1 2
  have hq2 : GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 ≤
      Gw.spacing (e.symm (x : Torus d (N₀l * L ^ kl))) ^ 2 := hsp2 ▸ hq1
  have hw := hbw.alpha ⟨e.symm x, hxw⟩
  have hl := hbl.alpha (hp.incl x)
  have hn := norm_sub_le (αw ⟨e.symm x, hxw⟩) (αl (hp.incl x))
  have a1 : GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 * ‖αw ⟨e.symm x, hxw⟩‖ ≤ cw :=
    (mul_le_mul_of_nonneg_right hq2 (norm_nonneg _)).trans hw
  have a2 : GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 * ‖αl (hp.incl x)‖ ≤ cl :=
    (mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)).trans hl
  have hq0 : 0 ≤ GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 := by positivity
  calc GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 * ‖αw ⟨e.symm x, hxw⟩ - αl (hp.incl x)‖
      ≤ GB.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 * (‖αw ⟨e.symm x, hxw⟩‖ + ‖αl (hp.incl x)‖) :=
        mul_le_mul_of_nonneg_left hn hq0
    _ ≤ c6 d L N := by nlinarith

end Main

section Far

variable {d L N₁ m₁ kl : ℕ} [NeZero N₁] [NeZero L] {ϱl ϱB : ℝ}

open Classical in
/-- **The far set is far in the path metric of `G_B`**: from a site `y ∈ X`, the sites of `Ω^B_1`
where the layers of `G_B` and `G_l` differ or that have a neighbour in `Ω^l_1 ∖ Ω^B_1` are at path
distance at least `D₀` when `D₀ L^{k_l} ≤ ρ_far - 1`. -/
theorem restrict_far_dist {Gl : GeneratingSet d L (N₁ * L ^ m₁) kl ϱl}
    {GB : GeneratingSet d L (N₁ * L ^ m₁) kl ϱB} {X : Finset (CTorus d L N₁ m₁ kl)}
    {ρ : ℕ → ℝ}
    (hGB : ∀ n x, x ∈ GB.Ω n ↔ x ∈ Gl.Ω n ∧
      ∀ y ∈ Gl.blk n x, ∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z y ≤ ρ n)
    {ρfar : ℝ} (hρf : ∀ n, 1 ≤ n → n ≤ kl → ρfar + d * (L : ℝ) ^ n ≤ ρ n)
    {y : CTorus d L N₁ m₁ kl} (hy : y ∈ X) {D₀ : ℝ} (hD₀ : D₀ * (L : ℝ) ^ kl ≤ ρfar - 1) :
    ENNReal.ofReal D₀ ≤ siteSetDist GB (Finset.univ.filter fun x => x ∈ GB.Ω 1 ∧
      (GB.layerIndex x ≠ Gl.layerIndex x ∨ ∃ w, Adj x w ∧ w ∈ Gl.Ω 1 ∧ w ∉ GB.Ω 1)) y := by
  unfold siteSetDist
  refine le_iInf₂ fun f hf => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  have hdist : ρfar - 1 ≤ Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) y f := by
    rcases hf.2 with hne | ⟨w, hadj, hw1, hwB⟩
    · have := restrictGen_far_of_layer_ne hGB hρf hf.1 hne y hy
      linarith
    · have h1 := restrictGen_far_of_not_mem hGB hρf hw1 hwB y hy
      have h2 := torusDist_triangle' (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := kl) y f w
      have h3 := Adj.torusDist_le hadj
      linarith
  have hLk : (0 : ℝ) < (L : ℝ) ^ kl := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (pathDist_ge_torusDist GB y f)
  rw [le_div_iff₀ hLk]
  linarith

end Far

section Core

variable {d L N : ℕ} [NeZero L]

open Classical in
/-- **Stability, the main case** (`r ≥ (ϱ_B + 3d) L^{k_l} + 2`), for given solutions of (EL) with the
bounds of Theorem 5.2: the restriction `G_B`, the composition on both sides and the weighted
Proposition 5.1 (`twoEL_near_far`). -/
theorem genSet_stability_main {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw)
    {kl N₀w kw N₁ m₁ : ℕ} [NeZero N₀w] [NeZero N₁] {ϱl ϱw ϱB : ℝ}
    (Gl : GeneratingSet d L (N₁ * L ^ m₁) kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
    (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₁ * L ^ m₁ * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L kl ϱl a ν) (hϱB0 : bgR0 d L ≤ ϱB)
    (hsepB : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1)) (hϱB : ϱB ≤ ϱl) (hk : kl ≤ kw)
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L (N₁ * L ^ m₁) kl n x = jBlock d L (N₁ * L ^ m₁) kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ kl))) (r : ℝ)
    (hag : ∀ x, (∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r) →
      ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δw' δd : ℝ} (hδl0 : 0 ≤ δl) (hδw0 : 0 ≤ δw')
    (hδd : 0 ≤ δd)
    (hΨ : ∀ x, (∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r) →
      vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd)
    (hh : ∀ x, (∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r) →
      Dl.h x = Dw.h (e.symm x))
    (hsmall : 9 * (bgK1 d L N * (δl + δw') + δd) ≤ min (deltaStar d L N) δw)
    (hc6 : bgK1 d L N * δl + bgK1 d L N * δw' ≤ c6 d L N)
    {φl : Gl.Ω 1 × Fin N → ℂ} {αl : Gl.Ω 1 → ℂ} {φw : Gw.Ω 1 × Fin N → ℂ} {αw : Gw.Ω 1 → ℂ}
    (hsl : IsEL Gl a ν Dl φl αl) (hbl : BgBounds Gl Dl φl αl (bgK1 d L N * δl))
    (hunitl : IsRealUnitField Gl φl) (hsw : IsEL Gw a ν Dw φw αw)
    (hbw : BgBounds Gw Dw φw αw (bgK1 d L N * δw'))
    (hr : (ϱB + 3 * d) * (L : ℝ) ^ kl + 2 ≤ r)
    (y : Gl.Ω 1) (hy : (y : Torus d (N₁ * L ^ m₁ * L ^ kl)) ∈ X) (i : Fin N) :
    ‖transportField (Gl := Gl) e Dw.Ψ φw (y, i) - φl (y, i)‖ ≤
      Kw * (cF d L * (9 * (bgK1 d L N * (δl + δw') + δd) *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))) + δd)) := by
  have hd3 : 3 ≤ d := H.hd
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have hK1 := bgK1_pos d L N
  set K₁ := bgK1 d L N with hK₁
  set T : ℝ := K₁ * (δl + δw') + δd with hT
  have hdT : δd ≤ T := by
    have : 0 ≤ K₁ * (δl + δw') := by positivity
    linarith
  have hclose : ∀ x : Gl.Ω 1, (∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r) →
      vn (fun i => transportField (Gl := Gl) e Dw.Ψ φw (x, i) - φl (x, i)) ≤ T := by
    intro x hx
    have hx' := (hag x hx 1 le_rfl (by omega)).1 x.2
    have := transport_close (e := e) hbl hbw x hx' (hΨ x hx)
    rw [hT]; linarith
  -- the restricted generating set
  set r₀ : ℝ := r - d * (L : ℝ) ^ kl - 1 with hr₀def
  have hr₀ : r₀ + 1 + d * (L : ℝ) ^ kl ≤ r := by rw [hr₀def]; linarith
  have hϱB0' : 0 ≤ ϱB := by
    refine le_trans ?_ hϱB0
    unfold bgR0
    exact le_trans (by positivity) (le_max_left _ _)
  obtain ⟨GB, hGB⟩ := exists_restrictGen Gl hϱB0' hϱB X (fun n => r₀ - (ϱB + d) * (L : ℝ) ^ n)
    (fun n _ _ => restrict_radii_gap hL2 hϱB0' r₀ n)
  have hp := restrictGen_precedes hGB
  have hρf : ∀ n, 1 ≤ n → n ≤ kl → (r₀ - (ϱB + 2 * d) * (L : ℝ) ^ kl) + d * (L : ℝ) ^ n ≤
      r₀ - (ϱB + d) * (L : ℝ) ^ n := fun n _ hn => restrict_radii_far hϱB0' r₀ hn
  have hnearB : ∀ x ∈ GB.Ω 1, ∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r₀ := by
    intro x hx
    obtain ⟨z, hz, h⟩ := restrictGen_near hGB hx
    refine ⟨z, hz, h.trans ?_⟩
    have : 0 ≤ (ϱB + d) * (L : ℝ) ^ 1 := by positivity
    linarith
  have HB : BgHyp d L kl ϱB a ν := ⟨H.hd, H.hL, hϱB0, H.weights, H.mass, H.massLe⟩
  have hS : GreenSetting GB a ν := HB.green
  have hOp : Dec2.OpSetting GB a ν := ⟨⟨H.hd, H.hL, H.mass, H.weights, hsepB⟩, H.massLe⟩
  have ha : ∀ j, 1 ≤ j → j ≤ kl → a j ≠ 0 := fun j h1 h2 =>
    (lt_of_lt_of_le (by norm_num) (H.weights j h1 h2).1).ne'
  -- the transported datum and the two solutions on `G_B`
  obtain ⟨D', hD'h, hD'Ψ⟩ := exists_transportData hk hag hblk Dl Dw
  have hD'Ψ1 : ∀ x ∈ dataSites Gl, (∀ y ∈ Gl.blk (Gl.layerIndex x) x,
      y ∈ {x | ∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r}) →
      D'.Ψ x = Dw.Ψ (e.symm x) := fun x hx hP => (hD'Ψ x hx).1 hP
  have hELB' := restrict_isEL_of_near hk he hblk X hr₀ hag hp hnearB a ha ν hD'h hD'Ψ1 hh hsw
  have hELB := isEL_compose hp a ha ν Dl hsl
  have hdΨ := restrict_deltaPsi_le hp H.weights X hr₀ hnearB hD'Ψ1 hΨ hclose hδd hdT
  -- Proposition 5.1 at the base point
  have hmin := le_min_iff.1 hsmall
  have hK1δl : 0 ≤ K₁ * δl := by positivity
  have hlT : K₁ * δl ≤ T := by
    have : 0 ≤ K₁ * δw' := by positivity
    rw [hT]; nlinarith
  have hδ₀s : K₁ * δl ≤ deltaStar d L N := by linarith
  have hδ₀w : K₁ * δl ≤ δw := by linarith
  have hP := prop51Hyp_of_precedes hS hp hbl hK1δl hδ₀s hunitl (by positivity) hmin.1 hdΨ
  have hsmallB := restrict_small_alpha (A := {x | ∃ z ∈ X,
      Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z x ≤ r}) hk hag hp
    (fun x hx => ball_reach_self hr₀ (by
      obtain ⟨z, hz, h⟩ := hnearB x hx
      exact ⟨z, hz, by linarith⟩)) hbl hbw hc6
  -- the far set
  have hnear : ∀ x : GB.Ω 1, (x : CTorus d L N₁ m₁ kl) ∉ (Finset.univ.filter fun x =>
      x ∈ GB.Ω 1 ∧ (GB.layerIndex x ≠ Gl.layerIndex x ∨ ∃ w, Adj x w ∧ w ∈ Gl.Ω 1 ∧ w ∉ GB.Ω 1)) →
      vn (fun i => (composeData hp a (transportField (Gl := Gl) e Dw.Ψ φw) D').Ψ x i -
        (composeData hp a φl Dl).Ψ x i) ≤ δd ∧
      ∀ w ∈ collar GB, Adj (x : CTorus d L N₁ m₁ kl) w →
        vn (fun i => (composeData hp a (transportField (Gl := Gl) e Dw.Ψ φw) D').Ψ w i -
          (composeData hp a φl Dl).Ψ w i) ≤ δd := by
    intro x hxF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_or, not_exists,
      ne_eq, not_not] at hxF
    obtain ⟨hlay, hnb⟩ := hxF x.2
    exact restrict_deltaPsi_near hp ha X hr₀ hnearB hD'Ψ1 hΨ φl _ x.2 hlay hnb
  -- the site `y`
  have hlk : Gl.layerIndex (y : CTorus d L N₁ m₁ kl) ≤ kl := layerIndex_le_top Gl _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hyB : (y : CTorus d L N₁ m₁ kl) ∈ GB.Ω 1 := by
    refine (restrictGen_layerIndex_eq hGB y.2 fun y' hy' => ⟨y, hy, ?_⟩).1
    have h1 := torusDist_le_of_mem_blk Gl hlk hy'
    have h2 : (L : ℝ) ^ Gl.layerIndex (y : CTorus d L N₁ m₁ kl) ≤ (L : ℝ) ^ kl :=
      pow_le_pow_right₀ hL1 hlk
    have h3 : 0 ≤ ϱB + 2 * d := by positivity
    have h4 : (ϱB + 2 * d) * (L : ℝ) ^ Gl.layerIndex (y : CTorus d L N₁ m₁ kl) ≤
        (ϱB + 2 * d) * (L : ℝ) ^ kl := mul_le_mul_of_nonneg_left h2 h3
    have h5 : 0 ≤ (d : ℝ) * (L : ℝ) ^ kl := by positivity
    show _ ≤ r₀ - (ϱB + d) * (L : ℝ) ^ Gl.layerIndex (y : CTorus d L N₁ m₁ kl)
    rw [hr₀def]
    nlinarith
  have hLk : (0 : ℝ) < (L : ℝ) ^ kl := by positivity
  set D₀ : ℝ := (r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl with hD₀def
  have hD₀ : 0 ≤ D₀ := div_nonneg (by linarith) hLk.le
  have hdist := restrict_far_dist hGB hρf hy (D₀ := D₀) (by
    rw [hD₀def, div_mul_cancel₀ _ hLk.ne', hr₀def]; linarith)
  have hhB : ∀ x i, (composeData hp a (transportField (Gl := Gl) e Dw.Ψ φw) D').h x i =
      (composeData hp a φl Dl).h x i := fun x i => by
    simp [composeData, hD'h]
  have hφ₀ : ∀ (x : GB.Ω 1) i, barField Gl Dl.Ψ φl x i = hp.restrictφ φl (x, i) := fun x i => by
    simp [barField, Precedes.restrictφ, hp.mem_Ω1 x.2]
    rfl
  have key := twoEL_near_far hW hS hOp hELB hELB' hhB hsmallB hφ₀ hP hδ₀w hmin.2 _ hδd hnear
    hD₀ ⟨y, hyB⟩ hdist i
  have e1 : hp.incl ⟨(y : CTorus d L N₁ m₁ kl), hyB⟩ = y := Subtype.ext rfl
  simp only [Precedes.restrictφ, e1] at key
  exact key

end Core

section Final

variable {d L N : ℕ} [NeZero L]

/-- **Stability under a change of generating set, with the constants `K_w`, `δ_w` of the weighted
Proposition 5.1** (`WeightedProp51S`); the torus of `Gl` has side `N₀ L^{k_l}`, `N₀ = N₁ L^{m₁}`. -/
theorem genSet_stability_core {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw) (hKw : 0 ≤ Kw)
    {N₀l kl N₀w kw N₁ m₁ : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero N₁] (hN : N₀l = N₁ * L ^ m₁)
    {ϱl ϱw ϱB : ℝ} (Gl : GeneratingSet d L N₀l kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
    (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L kl ϱl a ν) (Hw : BgHyp d L kw ϱw a ν) (hϱB0 : bgR0 d L ≤ ϱB)
    (hsepB : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1)) (hϱB : ϱB ≤ ϱl) (hk : kl ≤ kw)
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    (X : Finset (Torus d (N₀l * L ^ kl))) (r : ℝ) (hr0 : 0 ≤ r)
    (hag : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δw' δd : ℝ}
    (hδl0 : 0 < δl) (hδl : δl ≤ bgC1 d L N) (hDl : InDomainR Gl ν δl Dl)
    (hδw0 : 0 < δw') (hδw : δw' ≤ bgC1 d L N) (hDw : InDomainR Gw ν δw' Dw) (hδd : 0 ≤ δd)
    (hΨ : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd)
    (hh : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) → Dl.h x = Dw.h (e.symm x))
    (hsmall : 9 * (bgK1 d L N * (δl + δw') + δd) ≤ min (deltaStar d L N) δw)
    (y : Gl.Ω 1) (hy : (y : Torus d (N₀l * L ^ kl)) ∈ X) (i : Fin N) :
    ‖bgFieldC Gl a ν (bgC0 d L N) Dl (y, i) -
        transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) (y, i)‖ ≤
      max (Kw * cF d L * 10 * (bgK1 d L N + 1)) (bgK1 d L N + 1) *
        (δd + (δl + δw') *
          Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl)))) := by
  subst hN
  have hd0 : 0 < d := by have := H.hd; omega
  have hK1 := bgK1_pos d L N
  have hcF := cF_pos d L
  have hγ := gammaW_nonneg hd0
  obtain ⟨φl, αl, hsl, hbl, hul, hunitl, -, -⟩ := bg_real H hδl0 hδl hDl
  obtain ⟨φw, αw, hsw, hbw, huw, -, -, -⟩ := bg_real Hw hδw0 hδw hDw
  rw [(bgFieldC_eq hsl hul).1, (bgFieldC_eq hsw huw).1, norm_sub_rev]
  have hLk : (0 : ℝ) < (L : ℝ) ^ kl := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set E : ℝ := Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl)))
    with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hδ0 : 0 ≤ δl + δw' := by positivity
  by_cases hr : (ϱB + 3 * d) * (L : ℝ) ^ kl + 2 ≤ r
  · have hc6 : bgK1 d L N * δl + bgK1 d L N * δw' ≤ c6 d L N := by
      have h1 := (bgC1_facts d L N hd0 hδl).2.2.2
      have h2 := (bgC1_facts d L N hd0 hδw).2.2.2
      have h3 := bgC0_le_c6 d L N
      linarith
    have hm := genSet_stability_main hW Gl Gw e H hϱB0 hsepB hϱB hk he hblk X r hag hδl0.le
      hδw0.le hδd hΨ hh hsmall hc6 hsl.1 hbl hunitl hsw.1 hbw hr y hy i
    have hE1 : E ≤ 1 := by
      rw [hE, Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hγ (div_nonneg (by linarith) hLk.le)
    have hP : 0 ≤ Kw * cF d L := mul_nonneg hKw hcF.le
    have hin : 9 * (bgK1 d L N * (δl + δw') + δd) * E + δd ≤
        10 * (bgK1 d L N + 1) * (δd + (δl + δw') * E) := by
      have a1 : δd * E ≤ δd := mul_le_of_le_one_right hδd hE1
      have a2 : 0 ≤ (δl + δw') * E := mul_nonneg hδ0 hE0.le
      have a3 : 0 ≤ bgK1 d L N * δd := by positivity
      nlinarith
    calc ‖transportField (Gl := Gl) e Dw.Ψ φw (y, i) - φl (y, i)‖
        ≤ Kw * (cF d L * (9 * (bgK1 d L N * (δl + δw') + δd) * E + δd)) := hm
      _ = (Kw * cF d L) * (9 * (bgK1 d L N * (δl + δw') + δd) * E + δd) := by ring
      _ ≤ (Kw * cF d L) * (10 * (bgK1 d L N + 1) * (δd + (δl + δw') * E)) :=
          mul_le_mul_of_nonneg_left hin hP
      _ = Kw * cF d L * 10 * (bgK1 d L N + 1) * (δd + (δl + δw') * E) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hyA : ∃ z ∈ X, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) z y ≤ r :=
      ⟨y, hy, by rw [torusDist_self']; exact hr0⟩
    have hy' := (hag y hyA 1 le_rfl (by omega)).1 y.2
    have hcl := transport_close (e := e) hbl hbw y hy' (hΨ y hyA)
    have h1 : ‖transportField (Gl := Gl) e Dw.Ψ φw (y, i) - φl (y, i)‖ ≤
        bgK1 d L N * δw' + δd + bgK1 d L N * δl :=
      (norm_le_vn (fun j => transportField (Gl := Gl) e Dw.Ψ φw (y, j) - φl (y, j)) i).trans hcl
    have hE1 : 1 ≤ E := by
      rw [hE, Real.one_le_exp_iff, neg_nonneg]
      refine mul_nonpos_of_nonneg_of_nonpos hγ (div_nonpos_of_nonpos_of_nonneg (by linarith) hLk.le)
    have hin : bgK1 d L N * δw' + δd + bgK1 d L N * δl ≤
        (bgK1 d L N + 1) * (δd + (δl + δw') * E) := by
      have a1 : δl + δw' ≤ (δl + δw') * E := le_mul_of_one_le_right hδ0 hE1
      nlinarith
    calc _ ≤ _ := h1
      _ ≤ (bgK1 d L N + 1) * (δd + (δl + δw') * E) := hin
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **Stability of the background under a change of generating set** (P7 (2.14); P2 §4,
P3 Proposition 2.1 for the changed layers).  There are `K, δ_s > 0` depending only on `(d, L, N)`
such that: for generating sets `Gl`, `Gw` with the hypotheses of Theorem 5.2 (`BgHyp`, same `a`,
`ν`), `k_l ≤ k_w`, an identification `e` of the tori commuting with the lattice steps and with the
`n`-blocks (`n ≤ k_l`), a separation `ϱ_B ≤ ϱ_l` admissible for Theorem 5.2 and for the weighted
Green's function, a set `X` and a radius `r ≥ 0` such that on the ball `B(X, r)` the layers
`Ω_n` (`1 ≤ n ≤ k_l + 1`) and `h̃` agree and the data `Ψ` differ by at most `δ_d`, real data in
`𝒟_ℝ` with `K₁ (δ_l + δ_w) + δ_d ≤ δ_s`: for `y ∈ X ∩ Ω^l_1`,
`|φ_l(y) - φ_w(e⁻¹ y)| ≤ K (δ_d + (δ_l + δ_w) e^{-γ_w (r - (ϱ_B + 3d) L^{k_l} - 2) / L^{k_l}})`,
`φ_l = bgFieldC Gl`, `φ_w = bgFieldC Gw` (the right side is read through `transportField`). -/
theorem genSet_stability (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K δs : ℝ, 0 < K ∧ 0 < δs ∧
      ∀ {N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw ϱB : ℝ}
        (Gl : GeneratingSet d L N₀l kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
        (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ},
        BgHyp d L kl ϱl a ν → BgHyp d L kw ϱw a ν → bgR0 d L ≤ ϱB →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1) → ϱB ≤ ϱl → kl ≤ kw →
        (∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1) →
        (∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
          jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y)) →
        ∀ (X : Finset (Torus d (N₀l * L ^ kl))) (r : ℝ), 0 ≤ r →
        (∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
          ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n)) →
        ∀ {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δw δd : ℝ},
        0 < δl → δl ≤ bgC1 d L N → InDomainR Gl ν δl Dl →
        0 < δw → δw ≤ bgC1 d L N → InDomainR Gw ν δw Dw → 0 ≤ δd →
        (∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
          vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd) →
        (∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
          Dl.h x = Dw.h (e.symm x)) →
        bgK1 d L N * (δl + δw) + δd ≤ δs →
        ∀ (y : Gl.Ω 1), (y : Torus d (N₀l * L ^ kl)) ∈ X → ∀ i : Fin N,
          ‖bgFieldC Gl a ν (bgC0 d L N) Dl (y, i) -
              transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) (y, i)‖ ≤
            K * (δd + (δl + δw) *
              Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl)))) := by
  obtain ⟨Kw, δw0, hKw, hδw0, hW⟩ := weightedProp51S_exists N hd hL
  have hK1 := bgK1_pos d L N
  have hd0 : 0 < d := by omega
  have hs0 := deltaStar_pos d L N hd0
  refine ⟨max (Kw * cF d L * 10 * (bgK1 d L N + 1)) (bgK1 d L N + 1), min (deltaStar d L N) δw0 / 9,
    lt_of_lt_of_le (by linarith) (le_max_right _ _), by positivity, ?_⟩
  intro N₀l kl N₀w kw _ _ ϱl ϱw ϱB Gl Gw e a ν H Hw hϱB0 hsepB hϱB hk he hblk X r hr0 hag Dl Dw
    δl δw δd hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hh hsm y hy i
  exact genSet_stability_core hW hKw.le (N₁ := N₀l) (m₁ := 0) (by simp) Gl Gw e H Hw hϱB0 hsepB
    hϱB hk he hblk X r hr0 hag hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hh (by linarith) y hy i

end Final

end Balaban.Background
