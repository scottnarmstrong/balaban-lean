/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBlock
public import Balaban.LargeField.R.WindowSingle

/-!
# The coefficient comparison of one piece (blocker 4)

`PieceWindowSetup.coef_piece_of_flow_consts` is `exists_hcoef_of_flow_cubes_block_constsP` for the family of
the single piece `i` (`PieceWindowSetup.single`), with the hypotheses stated for the piece: the constants
`A_i, K_wt, C_b, C_g, C_m, A_max, E_max, ε₀, Δ` are the constants of the piece, so they may depend on `i`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset

variable {d L N : ℕ} [NeZero L]

/-- **The constant `K_w` of the coefficient comparison may be replaced by a larger one in `K_coef`.** -/
theorem coef_piece_le {d N : ℕ} {a Kwt Amax E Δ Cb Cg Cm μ Kc Kw Kcoef : ℝ} (hA : 0 ≤ Amax)
    (hX : 0 ≤ Δ * (2 * E)) (hKc : 0 ≤ Kc) (hle : Kc ≤ Kw) (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg)
    (hCm : 0 ≤ Cm) (hE : 0 ≤ E)
    (hK : a + Kwt + Amax * (Kw * (Δ * (2 * E)) * (Real.sqrt (((4 * E ^ 2) * Cb) * (N * Cb)) +
        Real.sqrt ((d * ((4 * E ^ 2) * Cg)) * (d * (N * Cg))) +
        Real.sqrt (((4 * E ^ 2 / |μ|) * Cm) * (N * Cm))) +
        (Kw * (Δ * (2 * E))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤ Kcoef) :
    a + Kwt + Amax * (Kc * (Δ * (2 * E)) * (Real.sqrt (((4 * E ^ 2) * Cb) * (N * Cb)) +
        Real.sqrt ((d * ((4 * E ^ 2) * Cg)) * (d * (N * Cg))) +
        Real.sqrt (((4 * E ^ 2 / |μ|) * Cm) * (N * Cm))) +
        (Kc * (Δ * (2 * E))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤ Kcoef := by
  refine le_trans ?_ hK
  have hS : 0 ≤ Real.sqrt (((4 * E ^ 2) * Cb) * (N * Cb)) +
        Real.sqrt ((d * ((4 * E ^ 2) * Cg)) * (d * (N * Cg))) +
        Real.sqrt (((4 * E ^ 2 / |μ|) * Cm) * (N * Cm)) := by positivity
  have hT : 0 ≤ (N : ℝ) * Cb + d * (N * Cg) + N * Cm := by positivity
  have h1 : Kc * (Δ * (2 * E)) ≤ Kw * (Δ * (2 * E)) := mul_le_mul_of_nonneg_right hle hX
  have h0 : 0 ≤ Kc * (Δ * (2 * E)) := mul_nonneg hKc hX
  gcongr


theorem PieceWindowSetup.coef_piece_of_flow_consts (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
    {sc : ι → ℕ} {k1 k : ℕ}
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (i : ι)
    (A : ℝ)
    {A₀ Kwt Cb Cg Cm Amax Emax : ℝ}
    (_ : 0 ≤ A)
    (_ : 2 ≤ d)
    -- the cells of the decomposition: layer blocks of weight one
    (_ : ∀ c, (W.decomp i).wt c = 1)
    (_ : ∀ c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1)
    (cs : OpConsts)
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
    (_ : (W.chain i).β (sc i + 1) = betaCanon d L (cs.beta (sc i + 1)) (sc i + 1) 0)
    (_ : (W.chain i).β k = betaCanon d L (cs.beta k) k 0)
    (_ : A * q ^ (sc i + 1) ≤ A₀)
    -- the source size `A_i = cs.beta (j+1) ε_{j+1}²`, `ε_n ≥ ε₀ > 0` for `n ≤ k`
    (α α₀ ε₀ : ℝ) (_ : 0 ≤ α) (_ : 0 < α₀) (_ : 0 < ε₀)
    (_ : ε₀ ^ 2 ≤ epsSeq L α α₀ (sc i + 1) ^ 2)
    (_ : A = cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2)
    -- the sizes of the coefficients and the regime
    (Ka Δ : ℝ) (_ : ∀ ℓ, |W.ak ℓ| ≤ Ka)
    (_ : (W.chain i).a (sc i + 1) = cs.aw) (_ : ∀ ℓ, |cs.aw ℓ - W.ak ℓ| ≤ Δ)
    (_ : (W.chain i).ν k = cs.muAct k)
    -- the constants
    (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (_ : 0 ≤ Cm)
    (_ : β * Real.exp η * (((L : ℝ) ^ (sc i + 1)) ^ d * (|ν| * |δ k|)) ≤ Cm * A)
    (_ : (4 * Emax ^ 2) * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * (sc i + 1)) * Δ) / 2 ≤ Kwt)
    -- the standing hypotheses and the class domain of the two coefficients at the mass of the piece
    (_ : ∃ N₁ m₁ : ℕ, W.N₀c i = N₁ * L ^ m₁)
    (_ : BgHyp d L (W.Kc i) (W.ϱc i) cs.aw ((W.chain i).ν k))
    (_ : BgHyp d L (W.Kc i) (W.ϱc i) W.ak ((W.chain i).ν k))
    (_ : 2 * d * Real.log L ≤ agmonRate d / 16 * (W.ϱc i - 1))
    (_ : (4 * d + 6) * ((2 * d + 1) * epsSeq L α α₀ (sc i + 1)) ≤ 1)
    (_ : xiC1 d * epsSeq L α α₀ (sc i + 1) ≤ bgC1 d L N)
    (_ : ∀ u ∈ S, XiCOneReal (W.Gc i) cs.aw ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    (_ : ∀ u ∈ S, XiCOneReal (W.Gc i) W.ak ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    (_ : bgK1 d L N * (xiC1 d * epsSeq L α α₀ (sc i + 1)) ≤
      min (deltaStar d L N) δw)
    (_ : Δ * (2 * epsSeq L α α₀ (sc i + 1)) ≤ min (deltaStar d L N) δw)
    (_ : epsSeq L α α₀ (sc i + 1) ≤ Emax) (_ : A ≤ Amax),
    ∀ u ∈ S,
      ‖((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) ((W.chain i).a k) ((W.chain i).ν k)
          ((W.chain i).Dat u k) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) -
        ((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) W.ak ((W.chain i).ν k)
          ((W.chain i).Dat u k) ((bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))‖ ≤
        (2 * (Ka + Δ) * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) + Kwt +
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) + Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) + Real.sqrt (((4 * Emax ^ 2 / |cs.muAct k|) * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) *
        W.mcount i
 := by
  obtain ⟨Kw, δw, hK, hδ, Hc⟩ := PieceWindowSetup.exists_hcoef_of_flow_cubes_block_constsP
    (d := d) (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₀ K _ U S ι _ sc k1 k W i A A₀ Kwt Cb Cg Cm Amax Emax hA hd hwt1 hcells cs β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ' hμne hgenv hξ hchj hchk hAq α α₀ ε₀ hα hα₀ hε₀ hE2 hAsrc Ka Δ hKa hchA hΔ hchν hCb hCg hCm0 hCm hKwt hN H0 H1 hsepO hsm hc1 D0 D1 hsmall hmB hEmax hAmax u hu
  exact Hc (W.single i) (fun _ => A) (fun _ => hA) hd (fun _ c => hwt1 c) (fun _ c => hcells c) cs
    β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ' hμne hgenv hξ (fun _ => hchj) (fun _ => hchk)
    (fun _ => hAq) α α₀ ε₀ hα hα₀ hε₀ (fun _ => hE2) (fun _ => hAsrc) Ka Δ hKa (fun _ => hchA) hΔ
    (fun _ => hchν) hCb hCg hCm0 (fun _ => hCm) (fun _ => hKwt) (fun _ => hN) (fun _ => H0)
    (fun _ => H1) (fun _ => hsepO) (fun _ => hsm) (fun _ => hc1) (fun _ u hu => D0 u hu)
    (fun _ u hu => D1 u hu) (fun _ => hsmall) (fun _ => hmB) (fun _ => hEmax) (fun _ => hAmax)
    PUnit.unit u hu

end Balaban.LargeField.ActionConv
