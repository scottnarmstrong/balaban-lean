/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSourceCostGen
public import Balaban.LargeField.R.WindowConvPhysSourceStep
public import Balaban.LargeField.R.WindowConvPhysSourceCube
public import Balaban.LargeField.R.WindowConvPhysSourceFlow
public import Balaban.LargeField.R.WindowConvPhysSourceBudget
public import Balaban.LargeField.R.CoeffResponseBudgetFlow
public import Balaban.LargeField.R.WindowConvCoeff
public import Balaban.LargeField.R.WindowConvFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The local solution against the unconverted background (P6 pp. 6–7 (2.13)–(2.16); P7 p. 501 (2.14))

At the last scale `k` the chain's action `T_{j,k} = β_k A(a_k, ν_k; ψ, φ_k)` has the background
`φ_k = bgFieldC (a_k, ν_k)` while the reference `P_k` of `hcoef` has the background
`bgFieldC (cs.aw, ν_k)` of the initial coefficient, at the same action.  The coefficients differ by
`a_k - aw = aw (β_{j+1} - β_k)/β_k`, which is geometrically small by the RG step bound, so the
fixed-action expansion (P7CONV (36) with `b = e = 0`) and the response to the coefficient change
bound `T_{j,k} - P_k` by `K_src A_i ρ_i |X_i|` with `ρ_i = C_ξ e^{2η} q^{j+2}/(2 β (1 - q))`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

universe u₁

variable {d L N : ℕ} [NeZero L]

/-- **The local solution against the unconverted background** (generic form). -/
theorem ConvChain.pair_le_of_flow (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {N₀ K : ℕ} [NeZero N₀] {ϱ : ℝ} {U : Type u₁} {S : Set U}
    {j k : ℕ} {G : GeneratingSet d L N₀ K ϱ} {X : Region G} {br : MassBranch}
    (C : ConvChain S j k G X br N) (Dc : StepDecomp X)
    (mcount : ℝ) (cs : OpConsts)
    (β ν η Ka cν Dδ ε V1 Ksrc Cξ q : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ) (u : U)
    (_ : mcount = Dc.total) (_ : j + 1 ≤ k) (_ : u ∈ S)
    -- the real flow
    (_ : 0 < β) (_ : 0 < ν) (_ : 0 ≤ Cξ) (_ : 0 ≤ q) (_ : q < 1)
    (_ : ∀ m, cs.beta m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (_ : ∀ m, cs.muAct m = ν * δ m)
    (_ : ∀ m, g m = g (m + 1) * (1 + ξ m 2))
    (_ : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
    (_ : ∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η)
    (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ)
    (_ : ∀ m c, |ξ m c| ≤ Cξ * β⁻¹ * q ^ (m + 1))
    (_ : Cξ * Real.exp (2 * η) * q / (β * (1 - q)) ≤ 1)
    -- the typing of the chain
    (_ : ∀ m, j + 1 ≤ m → m ≤ k → C.β m = betaCanon d L (cs.beta m) m 0)
    (_ : C.ν k = cs.muAct k)
    (_ : C.a (j + 1) = cs.aw)
    (_ : C.φ u k = bgFieldC G (C.a k) (C.ν k) (bgC0 d L N) (C.Dat u k))
    -- the cells of the decomposition: layer blocks of weight one
    (_ : ∀ c, Dc.wt c = 1)
    (_ : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
        G.layerIndex x ≤ j + 1)
    -- the sizes of the coefficients and of the mass
    (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : 0 ≤ cν)
    (_ : ∀ x : G.Ω 1, ν * G.spacing x ^ 2 * Dδ ≤ cν ^ 2)
    -- the standing hypotheses and the class domains at the coefficients `aw` and `a_k`
    (_ : ∃ N₁ m₁ : ℕ, N₀ = N₁ * L ^ m₁)
    (_ : BgHyp d L K ϱ cs.aw (C.ν k)) (_ : BgHyp d L K ϱ (C.a k) (C.ν k))
    (_ : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (_ : 0 < ε) (_ : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (_ : xiC1 d * ε ≤ bgC1 d L N)
    (_ : XiCOneReal G cs.aw (C.ν k) ε (C.Dat u k))
    (_ : XiCOneReal G (C.a k) (C.ν k) ε (C.Dat u k))
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
    ‖C.T u k - (C.β k : ℂ) * actionRegionC X (C.a k) (C.ν k) (C.Dat u k)
        (bgFieldC G cs.aw (C.ν k) (bgC0 d L N) (C.Dat u k))‖ ≤
      Ksrc * (cs.beta (j + 1) * ε ^ 2) *
        (Cξ * Real.exp (2 * η) * q ^ (j + 2) / (2 * β * (1 - q))) * mcount := by
  obtain ⟨Kw, δw, hKw, hδw, Hresp⟩ := jointResponse_step (d := d) (L := L) N hd3 hL3
  refine ⟨Kw, δw, hKw, hδw, ?_⟩
  intro N₀ K _ ϱ U S j k G X br C Dc mcount cs β ν η Ka cν Dδ ε V1 Ksrc Cξ q g δ ξ u hmc hjk hu hβ hν
    hCξ hq0 hq1 hβcs hμcs hg hδ hgenv hδp hδb hξ hρs hchβ hchν hchA hchφ hwt1 hcells hKa hcν0 hcν
    hN hB0 hB1 hsepO hε hsm hc1 hX0 hX1 hsmall hSB hV1 hK
  have hd2 : 2 ≤ d := by omega
  have hgp : ∀ m, 0 < g m := fun m => lt_of_lt_of_le (Real.exp_pos _) (hgenv m).1
  have hβm : ∀ m, j + 1 ≤ m → m ≤ k → C.β m = β * g m := fun m h1 h2 => by
    rw [hchβ m h1 h2, betaCanon_eq_of_flow cs d L β g hβcs m]
  have eβj := hβm (j + 1) le_rfl hjk
  have eβk := hβm k hjk le_rfl
  have eνk : C.ν k = ν * δ k := by rw [hchν, hμcs]
  have hβkp : 0 < C.β k := by rw [eβk]; exact mul_pos hβ (hgp _)
  have hν1p : 0 < C.ν k := by rw [eνk]; exact mul_pos hν (hδp _)
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hq' : 0 < 1 - q := by linarith
  set ρ := Cξ * Real.exp (2 * η) * q ^ (j + 2) / (2 * β * (1 - q)) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 / 2 := by
    have e : ρ = (Cξ * Real.exp (2 * η) * q / (β * (1 - q))) * q ^ (j + 1) / 2 := by
      rw [hρdef]; field_simp; ring
    rw [e]
    have h1 : q ^ (j + 1) ≤ 1 := pow_le_one₀ hq0 hq1.le
    have h2 : 0 ≤ Cξ * Real.exp (2 * η) * q / (β * (1 - q)) := by positivity
    calc (Cξ * Real.exp (2 * η) * q / (β * (1 - q))) * q ^ (j + 1) / 2
        ≤ 1 * 1 / 2 := by gcongr
      _ = 1 / 2 := by norm_num
  -- the telescoping of the couplings
  have hinc : ∀ n, |betaCanon d L (cs.beta n) n 0 - betaCanon d L (cs.beta (n + 1)) (n + 1) 0| ≤
      (Cξ * Real.exp η) * q ^ (n + 1) := fun n =>
    (flow_increment_abs_le_of_ident cs d L β ν η Cξ q g δ ξ hβ hCξ hq0 hβcs hμcs hg hδ
      (fun m => by rw [hμcs]; exact (mul_pos hν (hδp m)).ne')
      (fun n => ⟨(hgp n).le, (hgenv n).2⟩) hξ n).1
  have htel := abs_sub_le_geom_of_incr (fun n => betaCanon d L (cs.beta n) n 0)
    (Cξ * Real.exp η) q (by positivity) hq0 hq1 hinc hjk
  have e2 : Real.exp (2 * η) * Real.exp (-η) = Real.exp η := by
    rw [← Real.exp_add]; ring_nf
  have e1 : Cξ * Real.exp η * q ^ (j + 2) / (1 - q) = 2 * ρ * (β * Real.exp (-η)) := by
    rw [hρdef, ← e2]; field_simp
  have hb : |C.β (j + 1) - C.β k| ≤ 2 * ρ * C.β (j + 1) := by
    rw [hchβ (j + 1) le_rfl hjk, hchβ k hjk le_rfl]
    refine htel.trans ?_
    rw [e1, ← hchβ (j + 1) le_rfl hjk, eβj]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgenv (j + 1)).1 hβ.le)
      (by positivity)
  have hβjp : 0 < C.β (j + 1) := by rw [eβj]; exact mul_pos hβ (hgp _)
  have hcoefk : ∀ ℓ, C.β (j + 1) * C.a (j + 1) ℓ = C.β k * C.a k ℓ :=
    fun ℓ => C.coeff_from_start hjk le_rfl ℓ
  have hca : ∀ ℓ, β * g (j + 1) * cs.aw ℓ = β * g k * C.a k ℓ := by
    intro ℓ
    have := hcoefk ℓ
    rwa [eβj, eβk, hchA] at this
  have hm : ∀ x : G.Ω 1, |C.a k (G.layerIndex (x : Torus d _)) -
      cs.aw (G.layerIndex (x : Torus d _))| ≤ 2 * ρ * (Real.exp (2 * η) * Ka) := fun x => by
    rw [abs_sub_comm]
    have h1 := coeff_step_le (a₁ := cs.aw (G.layerIndex x)) (a₀ := C.a k (G.layerIndex x))
      (β₀ := C.β k) (β₁ := C.β (j + 1)) (β := β) (gj := g (j + 1)) (gn := g k) (η := η)
      hβ hβjp hρ0 (by rw [← hchA]; exact hcoefk _) hb (hgenv (j + 1)).2 (hgenv k).1 (hgp _)
      (hca (G.layerIndex x)).symm (hKa _)
    exact h1
  have hmν : ∀ x : G.Ω 1, G.spacing (x : Torus d _) ^ 2 * (C.ν k - C.ν k) ^ 2 ≤
      (12 * ρ * cν) ^ 2 * C.ν k := fun x => by
    rw [sub_self]
    have : 0 ≤ (12 * ρ * cν) ^ 2 * C.ν k := by positivity
    simpa using this
  have hV10 : 0 ≤ V1 := le_trans (by positivity) hV1
  obtain ⟨hv, hf, hbw⟩ := Hresp hN cs.aw (C.a k) (C.ν k) (C.ν k) ε ρ Ka cν (Real.exp (2 * η)) V1
    (C.Dat u k) hB0 hB1 hsepO hsm hε hc1 hX0 hX1 hsmall hρ0 hρ1 hKa0 hcν0 (Real.exp_pos _).le
    hν1p hm hmν hSB hV1
  obtain ⟨hrB, hrGf, hrGb, hrM⟩ := step_reads hB0 hν1p (by linarith) hε hsm hc1 hX0 X
  have hcsj : cs.beta (j + 1) = β * (L : ℝ) ^ ((d - 2) * (j + 1)) * g (j + 1) := hβcs _
  obtain ⟨hcb, hcg, hcm⟩ := cube_budgets X Dc hd2 (j := j) hwt1 hcells (a₁ := C.a k) (aw := cs.aw)
    (β := β) (g1 := g k) (gj := g (j + 1)) (η := η) (Ka := Ka) (cν := cν) (ν1 := C.ν k)
    (cb := cs.beta (j + 1)) hβ (hgenv k).2 (hgp _) (hgenv _).1 (hgp _) hKa hca
    (fun x hx => by
      rw [abs_of_pos hν1p, eνk]
      have h := hcν ⟨x, X.sub_Ω hx⟩
      have hsp : G.spacing x = (L : ℝ) ^ G.layerIndex x := rfl
      rw [hsp] at h
      calc ν * δ k * ((L : ℝ) ^ G.layerIndex x) ^ 2 =
          ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * δ k := by ring
        _ ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * Dδ :=
          mul_le_mul_of_nonneg_left (hδb k) (by positivity)
        _ ≤ cν ^ 2 := h) hcsj
  rw [← eβk] at hcb hcg hcm
  have hAj : 0 ≤ cs.beta (j + 1) := by
    rw [hcsj]; exact mul_nonneg (mul_nonneg hβ.le (by positivity)) (hgp _).le
  have hfin := convCost_le_of_budgets X Dc (a₀ := C.a k) (a₁ := C.a k) (ν₀ := C.ν k)
    (ν₁ := C.ν k) (β₀ := C.β k) (β₁ := C.β k) (ρ := ρ) (A' := cs.beta (j + 1)) (ε := ε)
    (Ka := Ka) (cν := cν) (e := Real.exp (2 * η)) (V1 := V1) (Vb := ρ * ε * V1) (C.Dat u k)
    (bgFieldC G cs.aw (C.ν k) (bgC0 d L N) (C.Dat u k))
    (bgFieldC G (C.a k) (C.ν k) (bgC0 d L N) (C.Dat u k)) (fun ℓ => rfl) hβkp hρ0 hρ1
    (by rw [sub_self, abs_zero]; positivity) (by rw [sub_self, abs_zero]; positivity) hAj hKa0
    (Real.exp_pos _).le hcb hcg hcm hrB hrGf hrGb hrM (mul_nonneg (mul_nonneg hρ0 hε.le) hV10) le_rfl hv hf hbw hK
  have hT : C.T u k = (C.β k : ℂ) * actionRegionC X (C.a k) (C.ν k) (C.Dat u k)
      (bgFieldC G (C.a k) (C.ν k) (bgC0 d L N) (C.Dat u k)) := by
    unfold ConvChain.T; rw [hchφ]
  rw [hT, hmc]
  exact hfin

end Balaban.LargeField.ActionConv
