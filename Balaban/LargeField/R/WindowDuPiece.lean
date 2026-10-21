/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseCubeMain
public import Balaban.LargeField.R.WindowDuRead
public import Balaban.LargeField.R.WindowConvPhysSwitchLocPiece

/-!
# The switch of one piece to the window background at mass `0` on the real flow (blocker 4)

`switch_piece_massZero` is `switch_piece_of_flow` with the window background `bgFieldC Gw a 0` of a
datum `Dw` at mass `0` (external field `0`, equal `Ψ` on the ball) in place of the window background at
the mass `ν_k` of the piece: the local background at `ν_k` and the field transported from the window
background at mass `0` differ in the restricted action at `(a, ν_k, Dl)` by at most `K_switch |X|_{mix}`
(`switch_massZero_of_genSet`: stability at mass `0` and the mass response).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.Fluctuation Finset

variable {d L N : ℕ} [NeZero L]

omit [NeZero L] in
/-- The standing hypotheses at the mass `0`. -/
theorem BgHyp.of_mass_zero {k : ℕ} {ϱ : ℝ} {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) :
    BgHyp d L k ϱ a 0 :=
  ⟨H.hd, H.hL, H.hϱ, H.weights, le_rfl, by simp⟩

/-- **The switch of one piece to the window background at mass `0` on the real flow** (P7 (2.14)–(2.16)). -/
theorem switch_piece_massZeroP (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Ks δs Kw δm : ℝ, 0 < Ks ∧ 0 < δs ∧ 0 < Kw ∧ 0 < δm ∧
      ∀ {N₀l j N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw ϱB : ℝ}
        (Gl : GeneratingSet d L N₀l (j + 1) ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
        (h : N₀w * L ^ kw = N₀l * L ^ (j + 1)) {a : ℕ → ℝ} {νk : ℝ},
        (∃ N₁ m₁ : ℕ, N₀l = N₁ * L ^ m₁) →
        BgHyp d L (j + 1) ϱl a νk → BgHyp d L kw ϱw a 0 → bgR0 d L ≤ ϱB →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1) → ϱB ≤ ϱl → j + 1 ≤ kw →
        ∀ (X : Region Gl) (Dc : StepDecomp X), (∀ c, Dc.wt c = 1) →
        (∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = Gl.blk (Gl.layerIndex x) x ∧
          Gl.layerIndex x ≤ j + 1) →
        ∀ (rad : ℝ), (ϱB + 3 * d) * (L : ℝ) ^ (j + 1) + 2 ≤ rad →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ (j + 1)) z x ≤ rad) →
          ∀ q, 1 ≤ q → q ≤ j + 1 + 1 →
            (x ∈ Gl.Ω q ↔ (Equiv.cast (congrArg (Torus d) h)).symm x ∈ Gw.Ω q)) →
        ∀ {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δwin δd m : ℝ},
        0 < δl → δl ≤ bgC1 d L N → InDomainR Gl νk δl Dl →
        0 < δwin → δwin ≤ bgC1 d L N → InDomainR Gw 0 δwin Dw → 0 ≤ δd →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ (j + 1)) z x ≤ rad) →
          vn (fun i => Dl.Ψ x i - Dw.Ψ ((Equiv.cast (congrArg (Torus d) h)).symm x) i) ≤ δd) →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ (j + 1)) z x ≤ rad) →
          ∀ i, Dw.h ((Equiv.cast (congrArg (Torus d) h)).symm x) i = 0) →
        (∀ x : Gl.Ω 1, ∑ i, ‖Dl.h x i‖ ^ 2 = 1) →
        bgK1 d L N * (δl + δwin) + δd ≤ δs →
        bgK1 d L N * δl ≤ min (deltaStar d L N) δm → 0 ≤ m →
        m * 2 ≤ min (deltaStar d L N) δm →
        (∀ x : Gl.Ω 1, νk * Gl.spacing (x : Torus d (N₀l * L ^ (j + 1))) ^ 2 ≤ m) →
        -- the real flow at the two scales
        ∀ {βc β η gk gj ν δk Ka ε₀ E Emax Amax Cb Cg Cm V Kswitch : ℝ},
        βc = β * gk → 0 < β → gk ≤ Real.exp η → Real.exp (-η) ≤ gk → Real.exp (-η) ≤ gj →
        νk = ν * δk → 0 < νk →
        0 < ε₀ → ε₀ ^ 2 ≤ E ^ 2 → (∀ ℓ, |a ℓ| ≤ Ka) →
        Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb → Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg →
        0 ≤ Cm → β * Real.exp η * (((L : ℝ) ^ (j + 1)) ^ d * (|ν| * |δk|)) ≤
          Cm * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2) →
        -- the class domain of the local datum (the reads)
        0 < E → (4 * d + 6) * ((2 * d + 1) * E) ≤ 1 → xiC1 d * E ≤ bgC1 d L N →
        XiCOneReal Gl a νk E Dl → E ≤ Emax →
        β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 ≤ Amax →
        Ks * (δd + (δl + δwin) * Real.exp (-(gammaW d *
          ((rad - (ϱB + 3 * d) * (L : ℝ) ^ (j + 1) - 2) / (L : ℝ) ^ (j + 1))))) + Kw * (m * 2) ≤ V →
        Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |νk|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤ Kswitch →
        ‖(βc : ℂ) * actionRegionC X a νk Dl (bgFieldC Gl a νk (bgC0 d L N) Dl) -
            (βc : ℂ) * actionRegionC X a νk Dl
              (transportField (Gl := Gl) (Equiv.cast (congrArg (Torus d) h)) Dw.Ψ
                (bgFieldC Gw a 0 (bgC0 d L N) Dw))‖ ≤ Kswitch * Dc.total := by
  obtain ⟨Ks, δs, Kw, δm, hKs, hδs, hKw, hδm, hsw⟩ := switch_massZero_of_genSet (L := L) N hd hL
  refine ⟨Ks, δs, Kw, δm, hKs, hδs, hKw, hδm, ?_⟩
  intro N₀l j N₀w kw _ _ ϱl ϱw ϱB Gl Gw h a νk hN H Hw hϱB0 hsepB hϱB hjk X Dc hwt1 hcells rad hrad
    hag Dl Dw δl δwin δd m hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hhw hhl hsm hδm1 hm0 hm2 hsp βc β η gk gj ν δk Ka ε₀ E
    Emax Amax Cb Cg Cm V Kswitch hβc hβ hgk hgk' hgj hνk hνk0 hε₀ hE hKa hCb hCg hCm0 hCm
    hEpos hsmE hc1 hXi hEmax hAmax hV hK
  have hd2 : 2 ≤ d := by omega
  have hgk0 : 0 < gk := lt_of_lt_of_le (Real.exp_pos _) hgk'
  have hgj0 : 0 < gj := lt_of_lt_of_le (Real.exp_pos _) hgj
  have hβc0 : 0 ≤ βc := by rw [hβc]; exact (mul_pos hβ hgk0).le
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  obtain ⟨hcb, hcg, hcm⟩ := switch_cube_budgetsP X Dc hd2 hjk hwt1 hcells a hβ hgk hgj hε₀ hE hKa
    hCb hCg hCm0 hCm
  rw [← hνk, ← hβc] at hcm
  rw [← hβc] at hcb hcg
  have hA0 : 0 ≤ β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 := by positivity
  have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb
  have hCg0 : 0 ≤ Cg := le_trans (by positivity) hCg
  have hε2 : 4 * E ^ 2 ≤ 4 * Emax ^ 2 := by nlinarith
  have hνabs : |νk| = νk := abs_of_pos hνk0
  have key := hsw Gl Gw (Equiv.cast (congrArg (Torus d) h)) hN H (BgHyp.of_mass_zero H) Hw hϱB0 hsepB
    hϱB hjk
    (Balaban.LargeField.equivCast_add_single h)
    (fun q hq x y => jBlock_equivCast_iff h hq (hq.trans hjk) x y) X Dc rad hrad hag hδl0 hδl hDl
    hδw0 hδw hDw hδd hΨ hhw hhl hsm hδm1 hm0 hm2 hsp (V := V) (Sb := 4 * Emax ^ 2) (Sg := 4 * Emax ^ 2)
    (Sm := 4 * Emax ^ 2 / |νk|) hβc0 hA0 hCb0 hCg0 hCm0 (by positivity) (by positivity)
    (by positivity) hcb hcg hcm
    (fun x hx => (blockRead_le H hEpos hsmE hc1 hXi (X.sub_Ω hx)).trans hε2)
    (fun x hx μ => ((bondRead_le H hEpos hsmE hc1 hXi (X.sub_Ω hx) μ).1).trans hε2)
    (fun x hx μ => ((bondRead_le H hEpos hsmE hc1 hXi (X.sub_Ω hx) μ).2).trans hε2)
    (fun x hx => by
      rw [hνabs]
      exact (massRead_le H hνk0 hEpos hsmE hc1 hXi (X.sub_Ω hx)).trans
        (div_le_div_of_nonneg_right hε2 hνk0.le))
    hV
  have hT := Dc.total_nonneg
  have hV0 : 0 ≤ V := le_trans (by
    have := Real.exp_pos (-(gammaW d * ((rad - (ϱB + 3 * d) * (L : ℝ) ^ (j + 1) - 2) /
      (L : ℝ) ^ (j + 1))))
    have := hKs.le
    positivity) hV
  have hY : 0 ≤ V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
      Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) +
      Real.sqrt (((4 * Emax ^ 2 / |νk|) * Cm) * (N * Cm))) +
      V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm) := by positivity
  calc _ ≤ _ := key
    _ ≤ Amax * Dc.total * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |νk|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAmax hT) hY
    _ = (Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |νk|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) * Dc.total := by ring
    _ ≤ Kswitch * Dc.total := mul_le_mul_of_nonneg_right hK hT

/-- **The switch of one piece to the window background at mass `0` on the real flow** (P7 (2.14)–(2.16)). -/
theorem switch_piece_massZero (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Ks δs Kw δm : ℝ, 0 < Ks ∧ 0 < δs ∧ 0 < Kw ∧ 0 < δm ∧
      ∀ {N₀l j N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw ϱB : ℝ}
        (Gl : GeneratingSet d L N₀l (j + 1) ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
        (h : N₀w * L ^ kw = N₀l * L ^ (j + 1)) {a : ℕ → ℝ} {νk : ℝ},
        (∃ N₁ m₁ : ℕ, N₀l = N₁ * L ^ m₁) →
        BgHyp d L (j + 1) ϱl a νk → BgHyp d L kw ϱw a 0 → bgR0 d L ≤ ϱB →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1) → ϱB ≤ ϱl → j + 1 ≤ kw →
        ∀ (X : Region Gl) (Dc : StepDecomp X), (∀ c, Dc.wt c = 1) →
        (∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = Gl.blk (Gl.layerIndex x) x ∧
          Gl.layerIndex x ≤ j + 1) →
        ∀ (rad : ℝ), (ϱB + 3 * d) * (L : ℝ) ^ (j + 1) + 2 ≤ rad →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ (j + 1)) z x ≤ rad) →
          ∀ q, 1 ≤ q → q ≤ j + 1 + 1 →
            (x ∈ Gl.Ω q ↔ (Equiv.cast (congrArg (Torus d) h)).symm x ∈ Gw.Ω q)) →
        ∀ {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δwin δd m : ℝ},
        0 < δl → δl ≤ bgC1 d L N → InDomainR Gl νk δl Dl →
        0 < δwin → δwin ≤ bgC1 d L N → InDomainR Gw 0 δwin Dw → 0 ≤ δd →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ (j + 1)) z x ≤ rad) →
          vn (fun i => Dl.Ψ x i - Dw.Ψ ((Equiv.cast (congrArg (Torus d) h)).symm x) i) ≤ δd) →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ (j + 1)) z x ≤ rad) →
          ∀ i, Dw.h ((Equiv.cast (congrArg (Torus d) h)).symm x) i = 0) →
        (∀ x : Gl.Ω 1, ∑ i, ‖Dl.h x i‖ ^ 2 = 1) →
        bgK1 d L N * (δl + δwin) + δd ≤ δs →
        bgK1 d L N * δl ≤ min (deltaStar d L N) δm → 0 ≤ m →
        m * 2 ≤ min (deltaStar d L N) δm →
        (∀ x : Gl.Ω 1, νk * Gl.spacing (x : Torus d (N₀l * L ^ (j + 1))) ^ 2 ≤ m) →
        -- the real flow at the two scales
        ∀ {βc β η gk gj ν δk Ka Dδ ε₀ E Emax Amax Cb Cg Cm V Kswitch : ℝ},
        βc = β * gk → 0 < β → gk ≤ Real.exp η → Real.exp (-η) ≤ gk → Real.exp (-η) ≤ gj →
        νk = ν * δk → 0 < νk → β * |ν| * (L : ℝ) ^ (kw * d) ≤ 1 → |δk| ≤ Dδ →
        0 < ε₀ → ε₀ ^ 2 ≤ E ^ 2 → (∀ ℓ, |a ℓ| ≤ Ka) →
        Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb → Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg →
        Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm →
        -- the class domain of the local datum (the reads)
        0 < E → (4 * d + 6) * ((2 * d + 1) * E) ≤ 1 → xiC1 d * E ≤ bgC1 d L N →
        XiCOneReal Gl a νk E Dl → E ≤ Emax →
        β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 ≤ Amax →
        Ks * (δd + (δl + δwin) * Real.exp (-(gammaW d *
          ((rad - (ϱB + 3 * d) * (L : ℝ) ^ (j + 1) - 2) / (L : ℝ) ^ (j + 1))))) + Kw * (m * 2) ≤ V →
        Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |νk|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤ Kswitch →
        ‖(βc : ℂ) * actionRegionC X a νk Dl (bgFieldC Gl a νk (bgC0 d L N) Dl) -
            (βc : ℂ) * actionRegionC X a νk Dl
              (transportField (Gl := Gl) (Equiv.cast (congrArg (Torus d) h)) Dw.Ψ
                (bgFieldC Gw a 0 (bgC0 d L N) Dw))‖ ≤ Kswitch * Dc.total := by
  obtain ⟨Ks, δs, Kw, δm, hKs, hδs, hKw, hδm, HP⟩ := switch_piece_massZeroP (L := L) N hd hL
  refine ⟨Ks, δs, Kw, δm, hKs, hδs, hKw, hδm, ?_⟩
  intro N₀l j N₀w kw _ _ ϱl ϱw ϱB Gl Gw h a νk hN H Hw hϱB0 hsepB hϱB hjk X Dc hwt1 hcells rad hrad
    hag Dl Dw δl δwin δd m hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hhw hhl hsm hδm1 hm0 hm2 hsp βc β η gk gj ν δk Ka Dδ ε₀ E
    Emax Amax Cb Cg Cm V Kswitch hβc hβ hgk hgk' hgj hνk hνk0 hreg hδk hε₀ hE hKa hCb hCg hCm
    hEpos hsmE hc1 hXi hEmax hAmax hV hK
  have hDδ0 : 0 ≤ Dδ := (abs_nonneg _).trans hδk
  have hCm0' : 0 ≤ Cm := le_trans (by positivity) hCm
  have hCm' : β * Real.exp η * (((L : ℝ) ^ (j + 1)) ^ d * (|ν| * |δk|)) ≤
      Cm * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2) :=
    mass_budget_of_regime hβ hjk hε₀ hE hgj hreg hδk hCm
  exact @HP N₀l j N₀w kw _ _ ϱl ϱw ϱB Gl Gw h a νk hN H Hw hϱB0 hsepB hϱB hjk X Dc hwt1 hcells rad hrad hag Dl Dw δl δwin δd m hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hhw hhl hsm hδm1 hm0 hm2 hsp βc β η gk gj ν δk Ka ε₀ E Emax Amax Cb Cg Cm V Kswitch hβc hβ hgk hgk' hgj hνk hνk0 hε₀ hE hKa hCb hCg hCm0' hCm' hEpos hsmE hc1 hXi hEmax hAmax hV hK

end Balaban.LargeField.ActionConv
