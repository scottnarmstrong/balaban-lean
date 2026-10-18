/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSourceAlg
public import Balaban.LargeField.R.WindowConvPhysSourceStep
public import Balaban.LargeField.R.WindowConvPhysSourceCube
public import Balaban.LargeField.R.WindowConvPhysSourceFlow
public import Balaban.LargeField.R.WindowConvPhysSourceBudget
public import Balaban.LargeField.R.WindowConvPhysSourceCostGen
public import Balaban.LargeField.R.CoeffResponseReads
public import Balaban.LargeField.R.WindowConvCoeff
public import Balaban.LargeField.R.WindowConvFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cost of one conversion step of a piece, from the flow (P7 p. 500 (2.11); P6 p. 14 (2.31))

`PieceWindowSetup.convCost_step_le`: for one piece `i`, one configuration `u` and one scale
`n` with `sc i + 2 ≤ n ≤ k`, the cost `R_{j,n}` of the conversion step `n - 1 → n` is at most
`K_src · (cs.beta (sc i + 1) ε²) · ‖ξ_{n-1}‖ · |X_i|_{mix}`.

The proof: `cost = T_{n-1} - T_n` (`ConvChain.step`); `T_{n-1}` and `T_n` are the actions at the
backgrounds `φ¹ = bgFieldC (a_{n-1}, ν_{n-1})` and `φ⁰ = bgFieldC (a_n, ν_n)` of one datum, with
`β_{n-1} a_{n-1} = β_n a_n`; the exact expansion (`actionRegionC_step_le`) bounds the cost by the
six read budgets (P7CONV (38)); the unprimed budgets come from the reads `blockRead_le`,
`bondRead_le`, `massRead_le` at `φ⁰` and the counting of the cube decomposition, with the originating
`ε_{j+1}`; the primed budgets come from the joint response `jointResponse_piece` of `φ¹ - φ⁰` to
the change of coefficient and mass over the step, which is proportional to `‖ξ_{n-1}‖`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

universe u₁

variable {d L N : ℕ} [NeZero L]

/-- **The cost of one conversion step of a chain, from the flow** (generic form). -/
theorem ConvChain.cost_le_of_flow (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {ϱ : ℝ} {U : Type u₁} {S : Set U}
    {j k : ℕ} {G : GeneratingSet d L N₀ K ϱ} {X : Region G} {br : MassBranch}
    (C : ConvChain S j k G X br N) (Dc : StepDecomp X)
    (mcount : ℝ) (cs : OpConsts)
    (β ν η Ka cν Dδ ε V1 Ksrc : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ) (u : U) (n : ℕ)
    (_ : mcount = Dc.total)
    (_ : j + 2 ≤ n) (_ : n ≤ k) (_ : u ∈ S)
    -- the real flow
    (_ : 0 < β) (_ : 0 < ν)
    (_ : ∀ m, cs.beta m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (_ : ∀ m, cs.muAct m = ν * δ m)
    (_ : ∀ m, g m = g (m + 1) * (1 + ξ m 2))
    (_ : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
    (_ : ∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η)
    (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ) (_ : ‖ξ (n - 1)‖ ≤ 1 / 2)
    -- the typing of the chain
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → C.β m = betaCanon d L (cs.beta m) m 0)
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → C.ν m = cs.muAct m)
    (_ : C.a (j + 1) = cs.aw)
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → C.Dat u m = C.Dat u k)
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → C.φ u m =
      bgFieldC G (C.a m) (C.ν m) (bgC0 d L N) (C.Dat u m))
    -- the cells of the decomposition: layer blocks of weight one
    (_ : ∀ c, Dc.wt c = 1)
    (_ : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
        G.layerIndex x ≤ j + 1)
    -- the sizes of the coefficients and of the mass
    (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : 0 ≤ cν)
    (_ : ∀ x : G.Ω 1, ν * G.spacing x ^ 2 * Dδ ≤ cν ^ 2)
    -- the standing hypotheses and the class domains at the scales `n - 1` and `n`
    (_ : ∃ N₁ m₁ : ℕ, N₀ = N₁ * L ^ m₁)
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → BgHyp d L K ϱ (C.a m) (C.ν m))
    (_ : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (_ : 0 < ε) (_ : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (_ : xiC1 d * ε ≤ bgC1 d L N)
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → XiCOneReal G (C.a m) (C.ν m) ε (C.Dat u m))
    (_ : bgK1 d L N * (xiC1 d * ε) ≤ min (deltaStar d L N) δw)
    (_ : ε * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ min (deltaStar d L N) δw)
    -- the constants
    (_ : Kw * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ V1)
    (_ : Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
      Real.sqrt ((4 * d * Real.exp (2 * η)) * (d * (N * Real.exp (2 * η)) * V1 ^ 2)) +
      Real.sqrt ((12 * Real.exp (2 * η)) * (N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2)) +
      (N * Ka * V1 ^ 2 + d * (N * Real.exp (2 * η)) * V1 ^ 2 +
        N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2) / 2 +
      4 * d * Real.exp (2 * η) + 12 * Real.exp (2 * η) ≤ Ksrc),
    ‖C.cost u n‖ ≤ Ksrc * (cs.beta (j + 1) * ε ^ 2) * ‖ξ (n - 1)‖ * mcount := by
  obtain ⟨Kw, δw, hKw, hδw, Hresp⟩ := jointResponse_step (d := d) (L := L) N hd3 hL3
  refine ⟨Kw, δw, hKw, hδw, ?_⟩
  intro N₀ K _ ϱ U S j k G X br C Dc mcount cs β ν η Ka cν Dδ ε V1 Ksrc g δ ξ u n hmc hn1 hn2 hu hβ hν hβcs hμcs hg hδ hgenv hδp hδb hξ
    hchβ hchν hchA hchD hchφ hwt1 hcells hKa hcν0 hcν hN hBg hsepO hε hsm hc1 hXi hsmall hSB hV1 hK
  have hd2 : 2 ≤ d := by omega
  have hnj : j + 1 ≤ n := by omega
  have hm1 : j + 1 ≤ n - 1 := by omega
  have hm1k : n - 1 ≤ k := by omega
  have hnn : n - 1 + 1 = n := by omega
  have hgp : ∀ m, 0 < g m := fun m => lt_of_lt_of_le (Real.exp_pos _) (hgenv m).1
  have hβm : ∀ m, j + 1 ≤ m → m ≤ k → C.β m = β * g m := fun m h1 h2 => by
    rw [hchβ m h1 h2, betaCanon_eq_of_flow cs d L β g hβcs m]
  have hνm : ∀ m, j + 1 ≤ m → m ≤ k → C.ν m = ν * δ m := fun m h1 h2 => by
    rw [hchν m h1 h2, hμcs]
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  -- the increments of one step
  set ρ := ‖ξ (n - 1)‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hξc : ∀ c, |ξ (n - 1) c| ≤ ρ := fun c => by
    simpa using norm_le_pi_norm (ξ (n - 1)) c
  have hgg : g (n - 1) = g n * (1 + ξ (n - 1) 2) := by
    have := hg (n - 1); rwa [hnn] at this
  have hδδ : δ (n - 1) * (1 + ξ (n - 1) 2) = δ n * (1 + ξ (n - 1) 1) := by
    have := hδ (n - 1); rwa [hnn] at this
  obtain ⟨hδ1p, hb, hc, hν13, hν31, hΔν⟩ :=
    step_flow_bounds hβ hν (hgp n) (hδp n) hgg hδδ (hξc 1) (hξc 2) hξ
  have eβ1 := hβm (n - 1) hm1 hm1k
  have eβ0 := hβm n hnj hn2
  have eν1 := hνm (n - 1) hm1 hm1k
  have eν0 := hνm n hnj hn2
  have hβ1p : 0 < C.β (n - 1) := by rw [eβ1]; exact mul_pos hβ (hgp _)
  have hν1p : 0 < C.ν (n - 1) := by rw [eν1]; exact mul_pos hν hδ1p
  have hb' : |C.β (n - 1) - C.β n| ≤ 2 * ρ * C.β (n - 1) := by
    rw [eβ1, eβ0]; exact hb
  have hc' : |C.β (n - 1) * C.ν (n - 1) -
      C.β n * C.ν n| ≤
      2 * ρ * (C.β (n - 1) * |C.ν (n - 1)|) := by
    rw [eβ1, eβ0, eν1, eν0]; exact hc
  have hcoef := C.coeff n hn1 hn2
  have hAj : 0 ≤ cs.beta (j + 1) := by
    rw [hβcs]; exact mul_nonneg (mul_nonneg hβ.le (by positivity)) (hgp _).le
  have hcsj : cs.beta (j + 1) = β * (L : ℝ) ^ ((d - 2) * (j + 1)) * g (j + 1) :=
    hβcs _
  have hβj : C.β (j + 1) = β * g (j + 1) :=
    hβm (j + 1) le_rfl (by omega)
  have hca1 : ∀ ℓ, β * g (j + 1) * cs.aw ℓ = β * g (n - 1) * C.a (n - 1) ℓ := by
    intro ℓ
    have := C.coeff_from_start hm1 hm1k ℓ
    rwa [hβj, eβ1, hchA] at this
  have hca0 : ∀ ℓ, β * g (j + 1) * cs.aw ℓ = β * g n * C.a n ℓ := by
    intro ℓ
    have := C.coeff_from_start hnj hn2 ℓ
    rwa [hβj, eβ0, hchA] at this
  have hνsp : ∀ x : G.Ω 1, C.ν (n - 1) * G.spacing x ^ 2 ≤ cν ^ 2 := fun x => by
    rw [eν1]
    exact mass_spacing_le hν (hδb (n - 1)) (by positivity) (hcν x)
  -- the per-cube budgets
  obtain ⟨hcb, hcg, hcm⟩ := cube_budgets X Dc hd2 (j := j) hwt1 hcells
    (a₁ := C.a (n - 1)) (aw := cs.aw) (β := β) (g1 := g (n - 1)) (gj := g (j + 1))
    (η := η) (Ka := Ka) (cν := cν) (ν1 := C.ν (n - 1)) (cb := cs.beta (j + 1)) hβ
    (hgenv (n - 1)).2 (hgp _) (hgenv _).1 (hgp _) hKa hca1
    (fun x hx => by
      rw [abs_of_pos hν1p]
      have h := hνsp ⟨x, X.sub_Ω hx⟩
      have hsp : G.spacing x = (L : ℝ) ^ G.layerIndex x := rfl
      rwa [hsp] at h) hcsj
  rw [← eβ1] at hcb hcg hcm
  -- the data and the backgrounds
  have hDn := hchD n hnj hn2
  have hDm := hchD (n - 1) hm1 hm1k
  have hT : ∀ m, j + 1 ≤ m → m ≤ k → C.T u m =
      (C.β m : ℂ) * actionRegionC X (C.a m) (C.ν m)
        (C.Dat u k) (bgFieldC G (C.a m) (C.ν m)
          (bgC0 d L N) (C.Dat u k)) := by
    intro m h1 h2
    simp only [ConvChain.T, hchφ m h1 h2, hchD m h1 h2]
  have hcost : C.cost u n = C.T u (n - 1) - C.T u n := by
    have := C.step hu hn1 hn2
    rw [this]; ring
  have hX0 : XiCOneReal G (C.a n) (C.ν n) ε (C.Dat u k) := by
    have := hXi n hnj hn2; rwa [hDn] at this
  have hX1 : XiCOneReal G (C.a (n - 1)) (C.ν (n - 1)) ε
      (C.Dat u k) := by
    have := hXi (n - 1) hm1 hm1k; rwa [hDm] at this
  -- the reads at the scale `n`
  have h13 : C.ν (n - 1) ≤ 3 * C.ν n := by
    rw [eν1, eν0]; exact hν13
  obtain ⟨hrB, hrGf, hrGb, hrM⟩ := step_reads (hBg n hnj hn2) hν1p h13 hε hsm hc1 hX0 X
  -- the response of the step
  have hm : ∀ x : G.Ω 1, |C.a (n - 1) (G.layerIndex (x : Torus d _)) -
      C.a n (G.layerIndex (x : Torus d _))| ≤ 2 * ρ * (Real.exp (2 * η) * Ka) := fun x =>
    coeff_step_le hβ hβ1p hρ0 (hcoef (G.layerIndex x)) hb' (hgenv (j + 1)).2 (hgenv n).1
      (hgp _) (hca0 (G.layerIndex x)).symm (hKa _)
  have hmν : ∀ x : G.Ω 1, G.spacing (x : Torus d _) ^ 2 *
      (C.ν (n - 1) - C.ν n) ^ 2 ≤ (12 * ρ * cν) ^ 2 * C.ν (n - 1) := fun x =>
    mass_step_sq_le hν1p (by positivity) (by rw [eν1, eν0]; exact hΔν) (hνsp x)
  obtain ⟨hv, hf, hbw⟩ := Hresp hN (C.a n) (C.a (n - 1)) (C.ν n)
    (C.ν (n - 1)) ε ρ Ka cν (Real.exp (2 * η)) V1 (C.Dat u k)
    (hBg n hnj hn2) (hBg (n - 1) hm1 hm1k) hsepO hsm hε hc1 hX0 hX1 hsmall hρ0 hξ hKa0 hcν0
    (Real.exp_pos _).le hν1p hm hmν hSB hV1
  have hV10 : 0 ≤ V1 := le_trans (by positivity) hV1
  have hfin := convCost_le_of_budgets X Dc (C.Dat u k)
    (bgFieldC G (C.a n) (C.ν n) (bgC0 d L N) (C.Dat u k))
    (bgFieldC G (C.a (n - 1)) (C.ν (n - 1)) (bgC0 d L N)
      (C.Dat u k)) hcoef hβ1p hρ0 hξ hb' hc' hAj hKa0 (Real.exp_pos _).le hcb hcg hcm
    hrB hrGf hrGb hrM (Vb := ρ * ε * V1) (by positivity) le_rfl hv hf hbw hK
  rw [hcost, hT (n - 1) hm1 hm1k, hT n hnj hn2, hmc]
  exact hfin

end Balaban.LargeField.ActionConv
