/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseReads
public import Balaban.LargeField.R.CoeffResponseReadsMain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `hcoef` with the originating block budget (51) discharged (P7 p. 500 (2.11); P6 p. 14 (2.31))

`PieceWindowSetup.exists_hcoef_of_flow_cubes_block` has no budget premise left.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

section Block

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **exists_hcoef_of_flow_cubes_block with the constants first**: the constants `K_w, δ_w` are produced before the data
`(N₀, K, S, ι, sc, k1, k, W, …)` and depend only on `(d, L, N)`.  The landed `PieceWindowSetup.exists_hcoef_of_flow_cubes_block` is this theorem
at the data. -/
theorem PieceWindowSetup.exists_hcoef_of_flow_cubes_block_consts (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
    {sc : ι → ℕ} {k1 k : ℕ}
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (Asrc : ι → ℝ)
    {A₀ Kwt Cb Cg Cm Amax Emax : ℝ}
    (_ : ∀ i, 0 ≤ Asrc i)
    (_ : 2 ≤ d)
    -- the cells of the decomposition: layer blocks of weight one
    (_ : ∀ i c, (W.decomp i).wt c = 1)
    (_ : ∀ i c, ∃ x ∈ (W.Xc i).sites,
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
        (2 * (Ka + Δ) * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) + Kwt +
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) + Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) + Real.sqrt (((4 * Emax ^ 2 / |cs.muAct k|) * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) *
        W.mcount i := by
  obtain ⟨Kw, δw, hK, hδw, Hp⟩ := exists_hcoef_of_flow_cubes_reads_consts (d := d) (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₀ K _ U S ι _ sc k1 k W Asrc A₀ Kwt Cb Cg Cm Amax Emax hA hd hwt1 hcells cs β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ hchj hchk hAq α α₀ ε₀ hα hα₀ hε₀ hε₀le hAsrc Ka Δ Dδ hKa hchA hΔ hchν hreg hδk hCb hCg hCm hKwt hN H0 H1 hsepO hsm hc1 D0 D1 hsmall hmB hEmax hAmax
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
  have hεpos : ∀ i, 0 < epsSeq L α α₀ (sc i + 1) := fun i => by
    have := one_le_epsTail (sc i + 1)
    unfold epsSeq
    have : 0 < epsTail (sc i + 1) := by linarith
    positivity
  have hgp : ∀ n, 0 < g n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hgenv n).1
  have hbj : ∀ i, (W.chain i).β (sc i + 1) = β * g (sc i + 1) := fun i => by
    rw [hchj i, betaCanon_eq_of_flow cs d L β g hβ]
  have hblock : ∀ i, ∀ u ∈ S, (W.chain i).β (sc i + 1) * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)) x j‖ ^ 2) ≤
      (2 * (Ka + Δ)) * (Asrc i * W.mcount i) := by
    intro i u hu
    have hcube : ∀ c, (W.chain i).β (sc i + 1) *
        ∑ x ∈ ((W.decomp i).cube c).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ ≤
        (cs.beta (sc i + 1) * (Ka + Δ)) * (W.decomp i).wt c := by
      intro c
      obtain ⟨x, hx, hs, hl⟩ := hcells i c
      rw [hs, (W.Xc i).layerBlock_sum_levelCoeff hx, pow_layer_mul hd, hbj i, hwt1, mul_one,
        hchA i, hβ]
      have habs : |cs.aw ((W.Gc i).layerIndex x)| ≤ Ka + Δ := by
        have h1 := hKa ((W.Gc i).layerIndex x)
        have h2 := hΔ ((W.Gc i).layerIndex x)
        calc _ = |(cs.aw ((W.Gc i).layerIndex x) - W.ak ((W.Gc i).layerIndex x)) +
              W.ak ((W.Gc i).layerIndex x)| := by ring_nf
          _ ≤ _ := (abs_add_le _ _).trans (by linarith)
      have hP : (L : ℝ) ^ ((W.Gc i).layerIndex x * (d - 2)) ≤
          (L : ℝ) ^ ((d - 2) * (sc i + 1)) := by
        apply pow_L_mono
        rw [mul_comm]; exact Nat.mul_le_mul_left _ hl
      have hg0 := hgp (sc i + 1)
      calc β * g (sc i + 1) * (|cs.aw ((W.Gc i).layerIndex x)| *
            (L : ℝ) ^ ((W.Gc i).layerIndex x * (d - 2)))
          ≤ β * g (sc i + 1) * ((Ka + Δ) * (L : ℝ) ^ ((d - 2) * (sc i + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul habs hP (by positivity) (by linarith))
              (by positivity)
        _ = _ := by ring
    have h := (W.Xc i).siteEnergy_le (W.decomp i)
      (fun x => ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖)
      (fun x j => ((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)) x j)
      (B := 4 * epsSeq L α α₀ (sc i + 1) ^ 2)
      (by rw [hbj i]; exact mul_nonneg hβpos.le (hgp _).le) (by positivity)
      (fun x => norm_nonneg _)
      (fun x hx => blockRead_le (H0 i) (hεpos i) (hsm i) (hc1 i) (D0 i u hu)
        ((W.Xc i).sub_Ω hx)) hcube
    rw [← W.mcount_eq] at h
    have hAi := hAsrc i
    calc _ = (1 / 2) * ((W.chain i).β (sc i + 1) *
          ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ *
            ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)) x j‖ ^ 2) := by ring
      _ ≤ (1 / 2) * (4 * epsSeq L α α₀ (sc i + 1) ^ 2 *
          ((cs.beta (sc i + 1) * (Ka + Δ)) * W.mcount i)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by rw [hAi]; ring
  exact Hp W Asrc (CB := 2 * (Ka + Δ)) hA (by linarith) hd hwt1 hcells cs hblock β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ
    hμne hgenv hξ hchj hchk hAq α α₀ ε₀ hα hα₀ hε₀ hε₀le hAsrc Ka Δ Dδ hKa hchA hΔ hchν hreg hδk hCb hCg
    hCm hKwt hN H0 H1 hsepO hsm hc1 D0 D1 hsmall hmB hEmax hAmax


/-- **`hcoef` with no remaining budget.**  `exists_hcoef_of_flow_cubes_reads` with the originating
block budget (51) proved: the block read is at most `4 ε_{j+1}²` (`blockRead_le`), `A_i =
cs.beta (j+1) ε_{j+1}²`, and per layer block `β̂_{j+1} |a(ℓ)| L^{ℓ(d-2)} ≤ cs.beta (j+1) (K_a + Δ)`
for `ℓ ≤ j + 1`, so `C_B = 2 (K_a + Δ)`, with no factor `ε₀⁻²`. -/
theorem PieceWindowSetup.exists_hcoef_of_flow_cubes_block (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (Asrc : ι → ℝ)
    {A₀ Kwt Cb Cg Cm Amax Emax : ℝ}
    (_ : ∀ i, 0 ≤ Asrc i)
    (_ : 2 ≤ d)
    -- the cells of the decomposition: layer blocks of weight one
    (_ : ∀ i c, (W.decomp i).wt c = 1)
    (_ : ∀ i c, ∃ x ∈ (W.Xc i).sites,
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
        (2 * (Ka + Δ) * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) + Kwt +
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) + Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) + Real.sqrt (((4 * Emax ^ 2 / |cs.muAct k|) * Cm) * (N * Cm))) + (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm))) *
        W.mcount i := by
  obtain ⟨Kw, δw, hK, hδw, H⟩ := PieceWindowSetup.exists_hcoef_of_flow_cubes_block_consts (d := d) (L := L) (N := N) hd3 hL3
  exact ⟨Kw, δw, hK, hδw, H⟩

end Block

end Balaban.LargeField.ActionConv
