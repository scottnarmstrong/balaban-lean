/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseReads
public import Balaban.LargeField.R.CoeffResponseResp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `hcoef` with the read sup bounds discharged (P7 p. 500 (2.11); P6 p. 14 (2.31))

`PieceWindowSetup.exists_hcoef_of_flow_cubes_reads` is
`PieceWindowSetup.exists_hcoef_of_flow_cubes_resp` with the sup bounds of the block, bond and mass
reads at `φ⁰ = bgFieldC` supplied by `XiCOneReal.factors` (`blockRead_le`, `bondRead_le`,
`massRead_le`): `S_b = S_g = 4 ε_max²`, `S_m = 4 ε_max² / ν_k`, `ν_k = cs.muAct k`.
Only the originating block budget (51) `hblock` remains of the budgets.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

section Reads

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **`hcoef` with the response supremum discharged.**  There are `K_w, δ_w > 0`, depending only on
`(d, L, N)`, such that the coefficient residual bound of `hcoef_of_response_flow_cubes` holds with
`H_resp = A_max (V_max (…) + V_max²/2 (…))`, `V_max = K_w (Δ · 2 E_max)`, for the backgrounds of
the pieces; the supremum premises `hval`, `hfwd`, `hbwd`, `hresp` and the premise `V` are
replaced by the standing hypotheses of the backgrounds (`BgHyp`), the class domains
(`XiCOneReal`) at the two coefficients, and the smallness of `ε_{j+1}` and `Δ ε_{j+1}`. -/
theorem PieceWindowSetup.exists_hcoef_of_flow_cubes_reads (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (Asrc : ι → ℝ)
    {CB A₀ Kwt Cb Cg Cm Amax Emax : ℝ}
    (_ : ∀ i, 0 ≤ Asrc i) (_ : 0 ≤ CB)
    (_ : 2 ≤ d)
    -- the cells of the decomposition: layer blocks of weight one
    (_ : ∀ i c, (W.decomp i).wt c = 1)
    (_ : ∀ i c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1)
    (cs : OpConsts)
    -- the originating block budget (51)
    (_ : ∀ i, ∀ u ∈ S, (W.chain i).β (sc i + 1) * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2) ≤
      CB * (Asrc i * W.mcount i))
    -- the real flow
    (β ν η Cξ q : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (_ : 0 < β) (_ : 0 ≤ Cξ) (_ : 0 ≤ q) (_ : q < 1)
    (_ : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n)
    (_ : ∀ n, cs.muAct n = ν * δ n)
    (_ : ∀ n, g n = g (n + 1) * (1 + ξ n 2))
    (_ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (_ : ∀ n, cs.muAct n ≠ 0)
    (_ : ∀ n, Real.exp (-η) ≤ g n ∧ g n ≤ Real.exp η)
    (_ : ∀ n c, |ξ n c| ≤ Cξ * β⁻¹ * q ^ (n + 1))
    (_ : ∀ i, (W.chain i).β (sc i + 1) = betaCanon d L (cs.beta (sc i + 1)) (sc i + 1) 0)
    (_ : ∀ i, (W.chain i).β k = betaCanon d L (cs.beta k) k 0)
    (_ : ∀ i, Asrc i * q ^ (sc i + 1) ≤ A₀)
    -- the source size `A_i = cs.beta (j+1) ε_{j+1}²`, `ε_n ≥ ε₀ > 0` for `n ≤ k`
    (α α₀ ε₀ : ℝ) (_ : 0 ≤ α) (_ : 0 < α₀) (_ : 0 < ε₀)
    (_ : ε₀ ≤ α₀ * ((L : ℝ) ^ (-α)) ^ k)
    (_ : ∀ i, Asrc i = cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2)
    -- the sizes of the coefficients and the regime
    (Ka Δ Dδ : ℝ) (_ : ∀ ℓ, |W.ak ℓ| ≤ Ka)
    (_ : ∀ i, (W.chain i).a (sc i + 1) = cs.aw) (_ : ∀ ℓ, |cs.aw ℓ - W.ak ℓ| ≤ Δ)
    (_ : ∀ i, (W.chain i).ν k = cs.muAct k)
    (_ : β * |ν| * (L : ℝ) ^ (k * d) ≤ 1) (_ : |δ k| ≤ Dδ)
    -- the constants
    (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (_ : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
    (_ : (4 * Emax ^ 2) * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) / 2 ≤ Kwt)
    -- the standing hypotheses and the class domain of the two coefficients at the mass of the piece
    (_ : ∀ i, ∃ N₁ m₁ : ℕ, W.N₀c i = N₁ * L ^ m₁)
    (_ : ∀ i, BgHyp d L (W.Kc i) (W.ϱc i) cs.aw ((W.chain i).ν k))
    (_ : ∀ i, BgHyp d L (W.Kc i) (W.ϱc i) W.ak ((W.chain i).ν k))
    (_ : ∀ i, 2 * d * Real.log L ≤ agmonRate d / 16 * (W.ϱc i - 1))
    (_ : ∀ i, (4 * d + 6) * ((2 * d + 1) * epsSeq L α α₀ (sc i + 1)) ≤ 1)
    (_ : ∀ i, xiC1 d * epsSeq L α α₀ (sc i + 1) ≤ bgC1 d L N)
    (_ : ∀ i, ∀ u ∈ S, XiCOneReal (W.Gc i) cs.aw ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    (_ : ∀ i, ∀ u ∈ S, XiCOneReal (W.Gc i) W.ak ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    (_ : ∀ i, bgK1 d L N * (xiC1 d * epsSeq L α α₀ (sc i + 1)) ≤
      min (deltaStar d L N) δw)
    (_ : ∀ i, Δ * (2 * epsSeq L α α₀ (sc i + 1)) ≤ min (deltaStar d L N) δw)
    (_ : ∀ i, epsSeq L α α₀ (sc i + 1) ≤ Emax) (_ : ∀ i, Asrc i ≤ Amax),
    ∀ i, ∀ u ∈ S,
      ‖((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) ((W.chain i).a k) ((W.chain i).ν k)
          ((W.chain i).Dat u k) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) -
        ((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) W.ak ((W.chain i).ν k)
          ((W.chain i).Dat u k) ((bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))‖ ≤
        (CB * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) + Kwt +
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) + Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) + Real.sqrt (((4 * Emax ^ 2 / |cs.muAct k|) * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) *
        W.mcount i := by
  obtain ⟨Kw, δw, hK, hδw, Hp⟩ := exists_hcoef_of_flow_cubes_resp (d := d) (L := L) (N₀ := N₀) (K := K) (N := N) (S := S) (ι := ι) (sc := sc) (k1 := k1) (k := k) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro W Asrc CB A₀ Kwt Cb Cg Cm Amax Emax hA hCB hd hwt1 hcells cs hblock β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ hchj hchk hAq α α₀ ε₀ hα hα₀ hε₀ hε₀le hAsrc Ka Δ Dδ hKa hchA hΔ hchν hreg hδk hCb hCg hCm hKwt hN H0 H1 hsepO hsm hc1 D0 D1 hsmall hmB hEmax hAmax
  have hεpos : ∀ i, 0 < epsSeq L α α₀ (sc i + 1) := fun i => by
    have := one_le_epsTail (sc i + 1)
    unfold epsSeq
    have : 0 < epsTail (sc i + 1) := by linarith
    positivity
  have hν : ∀ i, 0 < (W.chain i).ν k := fun i => by
    rw [hchν i]
    exact lt_of_le_of_ne (hchν i ▸ (H0 i).mass) (Ne.symm (hμne k))
  have hνabs : ∀ i, |cs.muAct k| = (W.chain i).ν k := fun i => by
    rw [← hchν i]; exact abs_of_pos (hchν i ▸ hν i)
  have hε2 : ∀ i, 4 * epsSeq L α α₀ (sc i + 1) ^ 2 ≤ 4 * Emax ^ 2 := fun i => by
    have := hεpos i
    have := hEmax i
    nlinarith
  refine Hp W Asrc (Sb := 4 * Emax ^ 2) (Sg := 4 * Emax ^ 2) (Sm := 4 * Emax ^ 2 / |cs.muAct k|)
    hA hCB (by positivity) (by positivity) (by positivity) hd hwt1 hcells cs hblock β ν η Cξ q g δ ξ
    hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ hchj hchk hAq α α₀ ε₀ hα hα₀ hε₀ hε₀le hAsrc
    Ka Δ Dδ hKa hchA hΔ hchν hreg hδk hCb hCg hCm hKwt ?_ ?_ ?_ ?_ hN H0 H1 hsepO hsm hc1 D0 D1
    hsmall hmB hEmax hAmax
  · intro i u hu x hx
    exact (blockRead_le (H0 i) (hεpos i) (hsm i) (hc1 i) (D0 i u hu) ((W.Xc i).sub_Ω hx)).trans
      (hε2 i)
  · intro i u hu x hx μ
    exact ((bondRead_le (H0 i) (hεpos i) (hsm i) (hc1 i) (D0 i u hu) ((W.Xc i).sub_Ω hx) μ).1).trans
      (hε2 i)
  · intro i u hu x hx μ
    exact ((bondRead_le (H0 i) (hεpos i) (hsm i) (hc1 i) (D0 i u hu) ((W.Xc i).sub_Ω hx) μ).2).trans
      (hε2 i)
  · intro i u hu x hx
    rw [hνabs i]
    exact (massRead_le (H0 i) (hν i) (hεpos i) (hsm i) (hc1 i) (D0 i u hu)
      ((W.Xc i).sub_Ω hx)).trans (div_le_div_of_nonneg_right (hε2 i) (hν i).le)

end Reads

end Balaban.LargeField.ActionConv
