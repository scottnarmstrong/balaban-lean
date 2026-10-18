/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSourceMain
public import Balaban.LargeField.R.WindowConvSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The originating-piece source estimate of the window (P7 p. 500 (2.11); P6 p. 14 (2.31))

`PieceWindowSetup.exists_hsource_of_flow` proves the premise `hsource` of `p7_first_of_rg_source`
for the pieces of a window from the real RG flow, the class domains of the data at the scales
`sc i + 1, …, k`, and the typing of the chains.  The only mass convention used is the complete
one: the background of the chain at the scale `m` is `bgFieldC` at its own coefficients and mass
(for `m = sc i + 1` this is the coherence of the first mass with the Euler–Lagrange mass,
`cs.mu (sc i + 1) = br.elMass (cs.muAct (sc i + 1))`, and of `locBg` with `bgFieldC`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

universe u₁ u₂

variable {d L N : ℕ} [NeZero L]

/-- **`hsource` of `p7_first_of_rg_source`** for the pieces of a window, with the constant
`K_src` of P7CONV (39). -/
theorem PieceWindowSetup.exists_hsource_of_flow (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {U : Type u₁} {S : Set U}
    {ι : Type u₂} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (cs : OpConsts)
    (β ν η Ka cν Dδ V1 Ksrc α α₀ : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    -- the real flow
    (_ : 0 < β) (_ : 0 < ν) (_ : 0 < α₀)
    (_ : ∀ m, cs.beta m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (_ : ∀ m, cs.muAct m = ν * δ m)
    (_ : ∀ m, g m = g (m + 1) * (1 + ξ m 2))
    (_ : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
    (_ : ∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η)
    (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ) (_ : ∀ t, ‖ξ t‖ ≤ 1 / 2)
    -- the typing of the chains
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k → (W.chain i).β m = betaCanon d L (cs.beta m) m 0)
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k → (W.chain i).ν m = cs.muAct m)
    (_ : ∀ i, (W.chain i).a (sc i + 1) = cs.aw)
    (_ : ∀ i, ∀ u ∈ S, ∀ m, sc i + 1 ≤ m → m ≤ k → (W.chain i).Dat u m = (W.chain i).Dat u k)
    (_ : ∀ i, ∀ u ∈ S, ∀ m, sc i + 1 ≤ m → m ≤ k → (W.chain i).φ u m =
      bgFieldC (W.Gc i) ((W.chain i).a m) ((W.chain i).ν m) (bgC0 d L N) ((W.chain i).Dat u m))
    -- the cells of the decompositions: layer blocks of weight one
    (_ : ∀ i c, (W.decomp i).wt c = 1)
    (_ : ∀ i c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1)
    -- the sizes of the coefficients and of the mass
    (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : 0 ≤ cν)
    (_ : ∀ i, ∀ x : (W.Gc i).Ω 1, ν * (W.Gc i).spacing x ^ 2 * Dδ ≤ cν ^ 2)
    -- the standing hypotheses and the class domains of the data at the scales `sc i + 1, …, k`
    (_ : ∀ i, ∃ N₁ m₁ : ℕ, W.N₀c i = N₁ * L ^ m₁)
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k →
      BgHyp d L (W.Kc i) (W.ϱc i) ((W.chain i).a m) ((W.chain i).ν m))
    (_ : ∀ i, 2 * d * Real.log L ≤ agmonRate d / 16 * (W.ϱc i - 1))
    (_ : ∀ i, (4 * d + 6) * ((2 * d + 1) * epsSeq L α α₀ (sc i + 1)) ≤ 1)
    (_ : ∀ i, xiC1 d * epsSeq L α α₀ (sc i + 1) ≤ bgC1 d L N)
    (_ : ∀ i, ∀ u ∈ S, ∀ m, sc i + 1 ≤ m → m ≤ k →
      XiCOneReal (W.Gc i) ((W.chain i).a m) ((W.chain i).ν m) (epsSeq L α α₀ (sc i + 1))
        ((W.chain i).Dat u m))
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
      4 * d * Real.exp (2 * η) + 12 * Real.exp (2 * η) ≤ Ksrc),
    ∀ i n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
      ‖(W.chain i).cost u n‖ ≤
        Ksrc * (cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) * ‖ξ (n - 1)‖ *
          W.mcount i := by
  obtain ⟨Kw, δw, hKw, hδw, H⟩ := ConvChain.cost_le_of_flow.{u₁} (d := d) (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hKw, hδw, ?_⟩
  intro N₀ K _ U S ι _ sc k1 k W cs β ν η Ka cν Dδ V1 Ksrc α α₀ g δ ξ hβ hν hα₀ hβcs hμcs hg hδ
    hgenv hδp hδb hξ hchβ hchν hchA hchD hchφ hwt1 hcells hKa hcν0 hcν hN hBg hsepO hsm hc1 hXi
    hsmall hSB hV1 hK i n hn1 hn2 u hu
  have hε : 0 < epsSeq L α α₀ (sc i + 1) := by
    have := one_le_epsTail (sc i + 1)
    unfold epsSeq
    have : 0 < epsTail (sc i + 1) := by linarith
    positivity
  exact H (W.chain i) (W.decomp i) (W.mcount i) cs β ν η Ka cν Dδ _ V1 Ksrc g δ ξ u n
    (W.mcount_eq i) hn1 hn2 hu hβ hν hβcs hμcs hg hδ hgenv hδp hδb (hξ _) (hchβ i) (hchν i)
    (hchA i) (hchD i u hu) (hchφ i u hu) (hwt1 i) (hcells i) hKa hcν0 (hcν i) (hN i) (hBg i)
    (hsepO i) hε (hsm i) (hc1 i) (hXi i u hu) (hsmall i) (hSB i) hV1 hK

end Balaban.LargeField.ActionConv
