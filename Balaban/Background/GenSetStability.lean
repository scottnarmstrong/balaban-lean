/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.GenSetStabilityParts
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
    (y : Gl.Ω 1) (hy : (y : Torus d (N₁ * L ^ m₁ * L ^ kl)) ∈ X) :
    (∀ i, ‖transportField (Gl := Gl) e Dw.Ψ φw (y, i) - φl (y, i)‖ ≤
      Kw * (cF d L * (9 * (bgK1 d L N * (δl + δw') + δd) *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))) + δd))) ∧
    (∀ (μ : Fin d) (i : Fin N), Gl.spacing (y : Torus d (N₁ * L ^ m₁ * L ^ kl)) *
      ‖svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ φw p - φl p)
          ((y : Torus d (N₁ * L ^ m₁ * L ^ kl)) + Pi.single μ 1) i -
        svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ φw p - φl p) y i‖ ≤
      Kw * (cF d L * (9 * (bgK1 d L N * (δl + δw') + δd) *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))) + δd))) ∧
    (∀ (μ : Fin d) (i : Fin N), Gl.spacing (y : Torus d (N₁ * L ^ m₁ * L ^ kl)) *
      ‖svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ φw p - φl p)
          ((y : Torus d (N₁ * L ^ m₁ * L ^ kl)) - Pi.single μ 1) i -
        svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ φw p - φl p) y i‖ ≤
      Kw * (cF d L * (9 * (bgK1 d L N * (δl + δw') + δd) *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))) + δd))) := by
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
  -- the sites within distance `1` of `X`: in `Ω^B_1` (if in `Ω^l_1`) with the same layer
  have hdeep1 : ∀ z : CTorus d L N₁ m₁ kl, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) y z ≤ 1 →
      z ∈ Gl.Ω 1 → z ∈ GB.Ω 1 ∧ GB.layerIndex z = Gl.layerIndex z := by
    intro z hyz hz1
    refine restrictGen_layerIndex_eq hGB hz1 fun y' hy' => ⟨y, hy, ?_⟩
    have hlz : Gl.layerIndex z ≤ kl := layerIndex_le_top Gl z
    have h1 := torusDist_le_of_mem_blk Gl hlz hy'
    have h0 := torusDist_triangle' (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := kl) y z y'
    have h2 : (L : ℝ) ^ Gl.layerIndex z ≤ (L : ℝ) ^ kl := pow_le_pow_right₀ hL1 hlz
    have h3 : 0 ≤ ϱB + 2 * d := by positivity
    have h4 : (ϱB + 2 * d) * (L : ℝ) ^ Gl.layerIndex z ≤ (ϱB + 2 * d) * (L : ℝ) ^ kl :=
      mul_le_mul_of_nonneg_left h2 h3
    have h5 : 0 ≤ (d : ℝ) * (L : ℝ) ^ kl := by positivity
    show _ ≤ r₀ - (ϱB + d) * (L : ℝ) ^ Gl.layerIndex z
    rw [hr₀def]
    nlinarith
  have hyB : (y : CTorus d L N₁ m₁ kl) ∈ GB.Ω 1 :=
    (hdeep1 y (by rw [torusDist_self']; norm_num) y.2).1
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
  obtain ⟨kv, kf, kb⟩ := twoEL_near_far hW hS hOp hELB hELB' hhB hsmallB hφ₀ hP hδ₀w hmin.2 _
    hδd hnear hD₀ ⟨y, hyB⟩ hdist
  have e1 : hp.incl ⟨(y : CTorus d L N₁ m₁ kl), hyB⟩ = y := Subtype.ext rfl
  have hsp : GB.spacing (y : CTorus d L N₁ m₁ kl) = Gl.spacing (y : CTorus d L N₁ m₁ kl) := by
    unfold GeneratingSet.spacing
    rw [(hdeep1 y (by rw [torusDist_self']; norm_num) y.2).2]
  have hsv : ∀ z : CTorus d L N₁ m₁ kl, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) y z ≤ 1 →
      ∀ i, svec GB (hp.restrictφ (transportField (Gl := Gl) e Dw.Ψ φw) - hp.restrictφ φl) z i =
        svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ φw p - φl p) z i := by
    intro z hz i
    by_cases hz1 : z ∈ Gl.Ω 1
    · have hzB := (hdeep1 z hz hz1).1
      rw [svec_of_mem GB _ ⟨z, hzB⟩ i, svec_of_mem Gl _ ⟨z, hz1⟩ i]
      rfl
    · have hzB : z ∉ GB.Ω 1 := fun h => hz1 (hp.mem_Ω1 h)
      rw [svec_of_not_mem GB _ hzB i, svec_of_not_mem Gl _ hz1 i]
  have hd0 : Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) y y ≤ 1 := by
    rw [torusDist_self']; norm_num
  have hdp : ∀ μ : Fin d, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) y
      ((y : CTorus d L N₁ m₁ kl) + Pi.single μ 1) ≤ 1 := fun μ =>
    Adj.torusDist_le (adj_add_single _ μ)
  have hdm : ∀ μ : Fin d, Green.torusDist d (N₁ * L ^ m₁ * L ^ kl) y
      ((y : CTorus d L N₁ m₁ kl) - Pi.single μ 1) ≤ 1 := fun μ =>
    Adj.torusDist_le (adj_sub_single _ μ)
  refine ⟨fun i => ?_, fun μ i => ?_, fun μ i => ?_⟩
  · have := kv i
    simp only [Pi.sub_apply, Precedes.restrictφ, e1] at this
    exact this
  · have := kf μ i
    rw [hsp, hsv _ (hdp μ) i, hsv _ hd0 i] at this
    exact this
  · have := kb μ i
    rw [hsp, hsv _ (hdm μ) i, hsv _ hd0 i] at this
    exact this

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
    have hm := (genSet_stability_main hW Gl Gw e H hϱB0 hsepB hϱB hk he hblk X r hag hδl0.le
      hδw0.le hδd hΨ hh hsmall hc6 hsl.1 hbl hunitl hsw.1 hbw hr y hy).1 i
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

/-- The bound of the main case in the form `K (δ_d + (δ_l + δ_w) E)`, `E ≤ 1`. -/
theorem stab_bound_le {Kw c K₁ δl δw δd E : ℝ} (hKw : 0 ≤ Kw) (hc : 0 ≤ c) (hK₁ : 0 ≤ K₁)
    (hδ : 0 ≤ δl + δw) (hδd : 0 ≤ δd) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    Kw * (c * (9 * (K₁ * (δl + δw) + δd) * E + δd)) ≤
      Kw * c * 10 * (K₁ + 1) * (δd + (δl + δw) * E) := by
  have hin : 9 * (K₁ * (δl + δw) + δd) * E + δd ≤ 10 * (K₁ + 1) * (δd + (δl + δw) * E) := by
    have a1 : δd * E ≤ δd := mul_le_of_le_one_right hδd hE1
    have a2 : 0 ≤ (δl + δw) * E := mul_nonneg hδ hE0
    have a3 : 0 ≤ K₁ * δd := mul_nonneg hK₁ hδd
    nlinarith
  calc Kw * (c * (9 * (K₁ * (δl + δw) + δd) * E + δd))
      = (Kw * c) * (9 * (K₁ * (δl + δw) + δd) * E + δd) := by ring
    _ ≤ (Kw * c) * (10 * (K₁ + 1) * (δd + (δl + δw) * E)) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hKw hc)
    _ = _ := by ring

/-- **Stability with the difference quotients** (main regime `r ≥ (ϱ_B + 3d) L^{k_l} + 2`), with
the constants of the weighted Proposition 5.1: for `y ∈ X ∩ Ω^l_1` the difference
`w = φ_w ∘ e⁻¹ - φ_l` satisfies `|w(y)|, ℓ(y) |∂w(y)| ≤ K (δ_d + (δ_l + δ_w) e^{-γ_w D₀})`. -/
theorem genSet_stability_grad_core {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw) (hKw : 0 ≤ Kw)
    {N₀l kl N₀w kw N₁ m₁ : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero N₁] (hN : N₀l = N₁ * L ^ m₁)
    {ϱl ϱw ϱB : ℝ} (Gl : GeneratingSet d L N₀l kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
    (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L kl ϱl a ν) (Hw : BgHyp d L kw ϱw a ν) (hϱB0 : bgR0 d L ≤ ϱB)
    (hsepB : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1)) (hϱB : ϱB ≤ ϱl) (hk : kl ≤ kw)
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hblk : ∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
      jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y))
    (X : Finset (Torus d (N₀l * L ^ kl))) (r : ℝ) (hr : (ϱB + 3 * d) * (L : ℝ) ^ kl + 2 ≤ r)
    (hag : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n))
    {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δw' δd : ℝ}
    (hδl0 : 0 < δl) (hδl : δl ≤ bgC1 d L N) (hDl : InDomainR Gl ν δl Dl)
    (hδw0 : 0 < δw') (hδw : δw' ≤ bgC1 d L N) (hDw : InDomainR Gw ν δw' Dw) (hδd : 0 ≤ δd)
    (hΨ : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) →
      vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd)
    (hh : ∀ x, (∃ z ∈ X, Green.torusDist d (N₀l * L ^ kl) z x ≤ r) → Dl.h x = Dw.h (e.symm x))
    (hsmall : 9 * (bgK1 d L N * (δl + δw') + δd) ≤ min (deltaStar d L N) δw)
    (y : Gl.Ω 1) (hy : (y : Torus d (N₀l * L ^ kl)) ∈ X) :
    (∀ i, ‖transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) (y, i) -
        bgFieldC Gl a ν (bgC0 d L N) Dl (y, i)‖ ≤
      Kw * cF d L * 10 * (bgK1 d L N + 1) * (δd + (δl + δw') *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))))) ∧
    (∀ (μ : Fin d) (i : Fin N), Gl.spacing (y : Torus d (N₀l * L ^ kl)) *
      ‖svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
            bgFieldC Gl a ν (bgC0 d L N) Dl p) ((y : Torus d (N₀l * L ^ kl)) + Pi.single μ 1) i -
        svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
            bgFieldC Gl a ν (bgC0 d L N) Dl p) y i‖ ≤
      Kw * cF d L * 10 * (bgK1 d L N + 1) * (δd + (δl + δw') *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))))) ∧
    (∀ (μ : Fin d) (i : Fin N), Gl.spacing (y : Torus d (N₀l * L ^ kl)) *
      ‖svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
            bgFieldC Gl a ν (bgC0 d L N) Dl p) ((y : Torus d (N₀l * L ^ kl)) - Pi.single μ 1) i -
        svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
            bgFieldC Gl a ν (bgC0 d L N) Dl p) y i‖ ≤
      Kw * cF d L * 10 * (bgK1 d L N + 1) * (δd + (δl + δw') *
        Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))))) := by
  subst hN
  have hd0 : 0 < d := by have := H.hd; omega
  have hK1 := bgK1_pos d L N
  have hcF := cF_pos d L
  have hγ := gammaW_nonneg hd0
  obtain ⟨φl, αl, hsl, hbl, hul, hunitl, -, -⟩ := bg_real H hδl0 hδl hDl
  obtain ⟨φw, αw, hsw, hbw, huw, -, -, -⟩ := bg_real Hw hδw0 hδw hDw
  rw [(bgFieldC_eq hsl hul).1, (bgFieldC_eq hsw huw).1]
  have hLk : (0 : ℝ) < (L : ℝ) ^ kl := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hc6 : bgK1 d L N * δl + bgK1 d L N * δw' ≤ c6 d L N := by
    have h1 := (bgC1_facts d L N hd0 hδl).2.2.2
    have h2 := (bgC1_facts d L N hd0 hδw).2.2.2
    have h3 := bgC0_le_c6 d L N
    linarith
  obtain ⟨hv, hf, hb⟩ := genSet_stability_main hW Gl Gw e H hϱB0 hsepB hϱB hk he hblk X r hag
    hδl0.le hδw0.le hδd hΨ hh hsmall hc6 hsl.1 hbl hunitl hsw.1 hbw hr y hy
  have hE1 : Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hγ (div_nonneg (by linarith) hLk.le)
  have hB := stab_bound_le hKw hcF.le hK1.le (by positivity) hδd (Real.exp_pos _).le hE1
    (K₁ := bgK1 d L N) (δl := δl) (δw := δw') (δd := δd)
  exact ⟨fun i => (hv i).trans hB, fun μ i => (hf μ i).trans hB, fun μ i => (hb μ i).trans hB⟩

/-- **Stability with the difference quotients**, constants depending on `(d, L, N)` only (main
regime `r ≥ (ϱ_B + 3d) L^{k_l} + 2`): `|w(y)|, ℓ(y) |∂w(y)| ≤ K (δ_d + (δ_l + δ_w) e^{-γ_w D₀})` for
`w = φ_w ∘ e⁻¹ - φ_l`, `y ∈ X ∩ Ω^l_1`, under the hypotheses of `genSet_stability`. -/
theorem genSet_stability_grad (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K δs : ℝ, 0 < K ∧ 0 < δs ∧
      ∀ {N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw ϱB : ℝ}
        (Gl : GeneratingSet d L N₀l kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
        (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ},
        BgHyp d L kl ϱl a ν → BgHyp d L kw ϱw a ν → bgR0 d L ≤ ϱB →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1) → ϱB ≤ ϱl → kl ≤ kw →
        (∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1) →
        (∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
          jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y)) →
        ∀ (X : Finset (Torus d (N₀l * L ^ kl))) (r : ℝ), (ϱB + 3 * d) * (L : ℝ) ^ kl + 2 ≤ r →
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
        ∀ (y : Gl.Ω 1), (y : Torus d (N₀l * L ^ kl)) ∈ X →
          (∀ i, ‖transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) (y, i) -
              bgFieldC Gl a ν (bgC0 d L N) Dl (y, i)‖ ≤
            K * (δd + (δl + δw) *
              Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))))) ∧
          (∀ (μ : Fin d) (i : Fin N), Gl.spacing (y : Torus d (N₀l * L ^ kl)) *
            ‖svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
                  bgFieldC Gl a ν (bgC0 d L N) Dl p) ((y : Torus d (N₀l * L ^ kl)) + Pi.single μ 1) i -
              svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
                  bgFieldC Gl a ν (bgC0 d L N) Dl p) y i‖ ≤
            K * (δd + (δl + δw) *
              Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))))) ∧
          (∀ (μ : Fin d) (i : Fin N), Gl.spacing (y : Torus d (N₀l * L ^ kl)) *
            ‖svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
                  bgFieldC Gl a ν (bgC0 d L N) Dl p) ((y : Torus d (N₀l * L ^ kl)) - Pi.single μ 1) i -
              svec Gl (fun p => transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) p -
                  bgFieldC Gl a ν (bgC0 d L N) Dl p) y i‖ ≤
            K * (δd + (δl + δw) *
              Real.exp (-(gammaW d * ((r - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl))))) := by
  obtain ⟨Kw, δw0, hKw, hδw0, hW⟩ := weightedProp51S_exists N hd hL
  have hK1 := bgK1_pos d L N
  have hd0 : 0 < d := by omega
  have hs0 := deltaStar_pos d L N hd0
  have hcF := cF_pos d L
  refine ⟨Kw * cF d L * 10 * (bgK1 d L N + 1), min (deltaStar d L N) δw0 / 9, by positivity,
    by positivity, ?_⟩
  intro N₀l kl N₀w kw _ _ ϱl ϱw ϱB Gl Gw e a ν H Hw hϱB0 hsepB hϱB hk he hblk X r hr hag Dl Dw
    δl δw δd hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hh hsm y hy
  exact genSet_stability_grad_core hW hKw.le (N₁ := N₀l) (m₁ := 0) (by simp) Gl Gw e H Hw hϱB0
    hsepB hϱB hk he hblk X r hr hag hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hh (by linarith) y hy

end Final

end Balaban.Background
