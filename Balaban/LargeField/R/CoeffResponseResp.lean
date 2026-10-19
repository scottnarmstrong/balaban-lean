/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseCubeMain
public import Balaban.LargeField.R.CoeffResponseRespPiece
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `hcoef` with the response supremum `hresp` discharged (P7 p. 500 (2.10)–(2.12); P7CONV (53))

`PieceWindowSetup.exists_hcoef_of_flow_cubes_resp` is `hcoef_of_response_flow_cubes` with the
reference field `φ⁰` of a piece `i` at `u ∈ S` the complex background `bgFieldC` of the datum
`(W.chain i).Dat u k` at the block coefficient `cs.aw` and mass `(W.chain i).ν k`, the field `φ¹`
the background at the window coefficient `W.ak`, and the response supremum `V_i` and its
consequence `hresp` obtained from the coefficient response (`coeffResponse_piece`, so from
`coeffChange_sameData_response`) with `m = Δ`, `Bh = 2 ε_{j+1}`.  Only the originating block budget
(51) `hblock` remains of the budgets, together with the sup bounds of the reads at `φ⁰`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

section Resp

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **exists_hcoef_of_flow_cubes_resp with the constants first**: the constants `K_w, δ_w` are produced before the data
`(N₀, K, S, ι, sc, k1, k, W, …)` and depend only on `(d, L, N)`.  The landed `PieceWindowSetup.exists_hcoef_of_flow_cubes_resp` is this theorem
at the data. -/
theorem PieceWindowSetup.exists_hcoef_of_flow_cubes_resp_consts (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
    {sc : ι → ℕ} {k1 k : ℕ}
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (Asrc : ι → ℝ)
    {CB A₀ Kwt Cb Cg Cm Sb Sg Sm Amax Emax : ℝ}
    (_ : ∀ i, 0 ≤ Asrc i) (_ : 0 ≤ CB)
    (_ : 0 ≤ Sb) (_ : 0 ≤ Sg) (_ : 0 ≤ Sm) (_ : 2 ≤ d)
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
    (_ : Sb * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) / 2 ≤ Kwt)
    -- the sup bounds of the datum reads at the reference field `φ⁰`
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites,
      ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2 ≤ Sb)
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites, ∀ μ : Fin d,
      (W.Gc i).spacing x ^ 2 * ∑ j, ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))
        (x + Pi.single μ 1) j - barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2 ≤ Sg)
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites, ∀ μ : Fin d,
      (W.Gc i).spacing x ^ 2 * ∑ j, ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))
        (x - Pi.single μ 1) j - barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2 ≤ Sg)
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites,
      ∑ j, ‖svec (W.Gc i) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j - ((W.chain i).Dat u k).h x j‖ ^ 2 ≤ Sm)
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
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt ((Sb * Cb) * (N * Cb)) + Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) *
        W.mcount i := by
  obtain ⟨Kw, δw, hK, hδw, Hp⟩ := coeffResponse_piece (d := d) (L := L) N hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₀ K _ U S ι _ sc k1 k W Asrc CB A₀ Kwt Cb Cg Cm Sb Sg Sm Amax Emax hA hCB hSb hSg hSm hd hwt1 hcells cs hblock β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ hchj hchk hAq α α₀ ε₀ hα hα₀ hε₀ hε₀le hAsrc Ka Δ Dδ hKa hchA hΔ hchν hreg hδk hCb hCg hCm hKwt hrB hrGf hrGb hrM hN H0 H1 hsepO hsm hc1 D0 D1 hsmall hmB hEmax hAmax
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
  have hDδ0 : 0 ≤ Dδ := (abs_nonneg _).trans hδk
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb
  have hCg0 : 0 ≤ Cg := le_trans (by positivity) hCg
  have hCm0 : 0 ≤ Cm := le_trans (by positivity) hCm
  have hεpos : ∀ i, 0 < epsSeq L α α₀ (sc i + 1) := fun i => by
    have := one_le_epsTail (sc i + 1)
    unfold epsSeq
    have : 0 < epsTail (sc i + 1) := by linarith
    positivity
  set V : ι → ℝ := fun i => Kw * (Δ * (2 * epsSeq L α α₀ (sc i + 1))) with hVdef
  have hV : ∀ i, 0 ≤ V i := fun i => by have := hεpos i; simp only [hVdef]; positivity
  have hsup : ∀ i, ∀ u ∈ S,
      (∀ (x : (W.Gc i).Ω 1) (j : Fin N), 1 * ‖(bgFieldC (W.Gc i) W.ak ((W.chain i).ν k)
          (bgC0 d L N) ((W.chain i).Dat u k) - bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k)
          (bgC0 d L N) ((W.chain i).Dat u k)) (x, j)‖ ≤ V i) ∧
      (∀ x ∈ (W.Gc i).Ω 1, ∀ (μ : Fin d) (j : Fin N), 1 * ((W.Gc i).spacing x *
        ‖svec (W.Gc i) (bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k) - bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k)) (x + Pi.single μ 1) j -
          svec (W.Gc i) (bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k) - bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k)) x j‖) ≤ V i) ∧
      (∀ x ∈ (W.Gc i).Ω 1, ∀ (μ : Fin d) (j : Fin N), 1 * ((W.Gc i).spacing x *
        ‖svec (W.Gc i) (bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k) - bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k)) (x - Pi.single μ 1) j -
          svec (W.Gc i) (bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k) - bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k)) x j‖) ≤ V i) := fun i u hu =>
    Hp (hN i) cs.aw W.ak ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1)) Δ ((W.chain i).Dat u k)
      (H0 i) (H1 i) (hsepO i) (hsm i) (hεpos i) (hc1 i) (D0 i u hu) (D1 i u hu) (hsmall i) hΔ0
      (fun x => by rw [abs_sub_comm]; exact hΔ _) (hmB i)
  have hresp : ∀ i, Asrc i * (V i * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
      V i ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤
      Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt ((Sb * Cb) * (N * Cb)) + Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) := fun i => by
    have hVle : V i ≤ Kw * (Δ * (2 * Emax)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hEmax i]) hΔ0) hK.le
    have hs : 0 ≤ Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm)) := by
      positivity
    have ht : 0 ≤ (N : ℝ) * Cb + d * (N * Cg) + N * Cm := by positivity
    have hin : V i * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
      V i ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm) ≤
      Kw * (Δ * (2 * Emax)) * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
      (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm) :=
      add_le_add (mul_le_mul_of_nonneg_right hVle hs)
        (mul_le_mul_of_nonneg_right (by
          have := pow_le_pow_left₀ (hV i) hVle 2; linarith) ht)
    exact mul_le_mul (hAmax i) hin (by have := hV i; positivity) ((hA i).trans (hAmax i))
  exact W.hcoef_of_response_flow_cubes (fun i u => bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)) (fun i u => bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)) Asrc V hA hV hCB hSb hSg hSm hd hwt1 hcells
    hblock cs β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ hchj hchk hAq α α₀ ε₀
    hα hα₀ hε₀ hε₀le hAsrc Ka Δ Dδ hKa hchA hΔ hchν hreg hδk hCb hCg hCm hKwt
    (fun i u hu => (hsup i u hu).1) (fun i u hu => (hsup i u hu).2.1)
    (fun i u hu => (hsup i u hu).2.2) hrB hrGf hrGb hrM hresp


/-- **`hcoef` with the response supremum discharged.**  There are `K_w, δ_w > 0`, depending only on
`(d, L, N)`, such that the coefficient residual bound of `hcoef_of_response_flow_cubes` holds with
`H_resp = A_max (V_max (…) + V_max²/2 (…))`, `V_max = K_w (Δ · 2 E_max)`, for the backgrounds of
the pieces; the supremum premises `hval`, `hfwd`, `hbwd`, `hresp` and the premise `V` are
replaced by the standing hypotheses of the backgrounds (`BgHyp`), the class domains
(`XiCOneReal`) at the two coefficients, and the smallness of `ε_{j+1}` and `Δ ε_{j+1}`. -/
theorem PieceWindowSetup.exists_hcoef_of_flow_cubes_resp (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (Asrc : ι → ℝ)
    {CB A₀ Kwt Cb Cg Cm Sb Sg Sm Amax Emax : ℝ}
    (_ : ∀ i, 0 ≤ Asrc i) (_ : 0 ≤ CB)
    (_ : 0 ≤ Sb) (_ : 0 ≤ Sg) (_ : 0 ≤ Sm) (_ : 2 ≤ d)
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
    (_ : Sb * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) / 2 ≤ Kwt)
    -- the sup bounds of the datum reads at the reference field `φ⁰`
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites,
      ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2 ≤ Sb)
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites, ∀ μ : Fin d,
      (W.Gc i).spacing x ^ 2 * ∑ j, ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))
        (x + Pi.single μ 1) j - barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2 ≤ Sg)
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites, ∀ μ : Fin d,
      (W.Gc i).spacing x ^ 2 * ∑ j, ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))
        (x - Pi.single μ 1) j - barField (W.Gc i) ((W.chain i).Dat u k).Ψ ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j‖ ^ 2 ≤ Sg)
    (_ : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites,
      ∑ j, ‖svec (W.Gc i) ((bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))) x j - ((W.chain i).Dat u k).h x j‖ ^ 2 ≤ Sm)
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
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt ((Sb * Cb) * (N * Cb)) + Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) *
        W.mcount i := by
  obtain ⟨Kw, δw, hK, hδw, H⟩ := PieceWindowSetup.exists_hcoef_of_flow_cubes_resp_consts (d := d) (L := L) (N := N) hd3 hL3
  exact ⟨Kw, δw, hK, hδw, H⟩

end Resp

end Balaban.LargeField.ActionConv
