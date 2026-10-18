/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysPairMain
public import Balaban.LargeField.R.WindowConvUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `hpair` of `window_uniform_of_parts` (P6 pp. 6–7 (2.13)–(2.16); P7 p. 501 (2.14))

`PieceWindowSetup.exists_hpair_of_flow`: for the reference
`P_i(u) = β_k A_{X_i}(a_k, ν_k; ψ, bgFieldC (cs.aw, ν_k))` of `hcoef`
(`exists_hcoef_of_flow_cubes_block`), the chain action `T_{j,k}` satisfies
`‖T_{j,k} - P_i‖ ≤ K_pair |X_i|_{mix}`, from the geometric RG step bound and the response of the
background to the coefficient change `aw → a_k`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

universe u₁ u₂

variable {d L N : ℕ} [NeZero L]

/-- **`hpair` of `window_uniform_of_parts`.** -/
theorem PieceWindowSetup.exists_hpair_of_flow (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {U : Type u₁} {S : Set U}
    {ι : Type u₂} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (cs : OpConsts)
    (β ν η Ka cν Dδ V1 Ksrc Cξ q α α₀ A₀ Kpair : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    -- the real flow
    (_ : 0 < β) (_ : 0 < ν) (_ : 0 < α₀) (_ : 0 ≤ Cξ) (_ : 0 ≤ q) (_ : q < 1)
    (_ : ∀ m, cs.beta m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (_ : ∀ m, cs.muAct m = ν * δ m)
    (_ : ∀ m, g m = g (m + 1) * (1 + ξ m 2))
    (_ : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
    (_ : ∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η)
    (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ)
    (_ : ∀ m c, |ξ m c| ≤ Cξ * β⁻¹ * q ^ (m + 1))
    (_ : Cξ * Real.exp (2 * η) * q / (β * (1 - q)) ≤ 1)
    -- the size of the source `A_i = cs.beta (sc i + 1) ε²` against the geometric decay
    (_ : ∀ i, cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 * q ^ (sc i + 1) ≤ A₀)
    -- the typing of the chains
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k → (W.chain i).β m = betaCanon d L (cs.beta m) m 0)
    (_ : ∀ i, (W.chain i).ν k = cs.muAct k)
    (_ : ∀ i, (W.chain i).a (sc i + 1) = cs.aw)
    (_ : ∀ i, ∀ u ∈ S, (W.chain i).φ u k =
      bgFieldC (W.Gc i) ((W.chain i).a k) ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))
    -- the cells of the decompositions: layer blocks of weight one
    (_ : ∀ i c, (W.decomp i).wt c = 1)
    (_ : ∀ i c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1)
    -- the sizes of the coefficients and of the mass
    (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : 0 ≤ cν)
    (_ : ∀ i, ∀ x : (W.Gc i).Ω 1, ν * (W.Gc i).spacing x ^ 2 * Dδ ≤ cν ^ 2)
    -- the standing hypotheses and the class domains at the coefficients `aw` and `a_k`
    (_ : ∀ i, ∃ N₁ m₁ : ℕ, W.N₀c i = N₁ * L ^ m₁)
    (_ : ∀ i, BgHyp d L (W.Kc i) (W.ϱc i) cs.aw ((W.chain i).ν k))
    (_ : ∀ i, BgHyp d L (W.Kc i) (W.ϱc i) ((W.chain i).a k) ((W.chain i).ν k))
    (_ : ∀ i, 2 * d * Real.log L ≤ agmonRate d / 16 * (W.ϱc i - 1))
    (_ : ∀ i, (4 * d + 6) * ((2 * d + 1) * epsSeq L α α₀ (sc i + 1)) ≤ 1)
    (_ : ∀ i, xiC1 d * epsSeq L α α₀ (sc i + 1) ≤ bgC1 d L N)
    (_ : ∀ i, ∀ u ∈ S, XiCOneReal (W.Gc i) cs.aw ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    (_ : ∀ i, ∀ u ∈ S, XiCOneReal (W.Gc i) ((W.chain i).a k) ((W.chain i).ν k)
      (epsSeq L α α₀ (sc i + 1)) ((W.chain i).Dat u k))
    (_ : ∀ i, bgK1 d L N * (xiC1 d * epsSeq L α α₀ (sc i + 1)) ≤ min (deltaStar d L N) δw)
    (_ : ∀ i, epsSeq L α α₀ (sc i + 1) * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤
      min (deltaStar d L N) δw)
    -- the constants
    (_ : Kw * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ V1)
    (_ : Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
      Real.sqrt ((4 * d * Real.exp (2 * η)) * (d * (N * Real.exp (2 * η)) * V1 ^ 2)) +
      Real.sqrt ((12 * Real.exp (2 * η)) * (N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2)) +
      (N * Ka * V1 ^ 2 + d * (N * Real.exp (2 * η)) * V1 ^ 2 +
        N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2) / 2 +
      4 * d * Real.exp (2 * η) + 12 * Real.exp (2 * η) ≤ Ksrc)
    (_ : Ksrc * (Cξ * Real.exp (2 * η) * q * A₀ / (2 * β * (1 - q))) ≤ Kpair),
    ∀ i, ∀ u ∈ S,
      ‖(W.chain i).T u k - (W.chain i).β k * actionRegionC (W.Xc i) ((W.chain i).a k)
          ((W.chain i).ν k) ((W.chain i).Dat u k)
          (bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k))‖ ≤
        Kpair * W.mcount i := by
  obtain ⟨Kw, δw, hKw, hδw, H⟩ := ConvChain.pair_le_of_flow.{u₁} (d := d) (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hKw, hδw, ?_⟩
  intro N₀ K _ U S ι _ sc k1 k W cs β ν η Ka cν Dδ V1 Ksrc Cξ q α α₀ A₀ Kpair g δ ξ hβ hν hα₀ hCξ
    hq0 hq1 hβcs hμcs hg hδ hgenv hδp hδb hξ hρs hAq hchβ hchν hchA hchφ hwt1 hcells hKa hcν0 hcν
    hN hB0 hB1 hsepO hsm hc1 hX0 hX1 hsmall hSB hV1 hK hKp i u hu
  have hε : 0 < epsSeq L α α₀ (sc i + 1) := by
    have := one_le_epsTail (sc i + 1)
    unfold epsSeq
    have : 0 < epsTail (sc i + 1) := by linarith
    positivity
  have hjk : sc i + 1 ≤ k := by have := W.sc_lt i; omega
  have h := H (W.chain i) (W.decomp i) (W.mcount i) cs β ν η Ka cν Dδ _ V1 Ksrc Cξ q g δ ξ u
    (W.mcount_eq i) hjk hu hβ hν hCξ hq0 hq1 hβcs hμcs hg hδ hgenv hδp hδb hξ hρs (hchβ i)
    (hchν i) (hchA i) (hchφ i u hu) (hwt1 i) (hcells i) hKa hcν0 (hcν i) (hN i) (hB0 i) (hB1 i)
    (hsepO i) hε (hsm i) (hc1 i) (hX0 i u hu) (hX1 i u hu) (hsmall i) (hSB i) hV1 hK
  refine h.trans ?_
  have hq' : 0 < 1 - q := by linarith
  have hmc := W.mcount_nonneg i
  have hKs : 0 ≤ Ksrc * (Cξ * Real.exp (2 * η) * q / (2 * β * (1 - q))) := by
    have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
    have : 0 ≤ Ksrc := le_trans (by positivity) hK
    positivity
  calc Ksrc * (cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) *
        (Cξ * Real.exp (2 * η) * q ^ (sc i + 2) / (2 * β * (1 - q))) * W.mcount i
      = (Ksrc * (Cξ * Real.exp (2 * η) * q / (2 * β * (1 - q)))) *
          (cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 * q ^ (sc i + 1)) * W.mcount i := by
        ring
    _ ≤ (Ksrc * (Cξ * Real.exp (2 * η) * q / (2 * β * (1 - q)))) * A₀ * W.mcount i := by
        gcongr
        exact hAq i
    _ = Ksrc * (Cξ * Real.exp (2 * η) * q * A₀ / (2 * β * (1 - q))) * W.mcount i := by ring
    _ ≤ Kpair * W.mcount i := mul_le_mul_of_nonneg_right hKp hmc

end Balaban.LargeField.ActionConv
