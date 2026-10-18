/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBudgetHcoef
public import Balaban.LargeField.R.WindowConvFlow
public import Balaban.LargeField.R.ActionConvPieces
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The flow absorption of `hcoef` (P7CONV (30)–(31))

Telescoping the fine-coupling increments of `flow_increment_abs_le_of_ident` gives
`|β̂_{j+1} - β̂_k| ≤ C_ξ e^η q^{j+2} / (1 - q)`, and with the originating source size
`A q^{j+1} ≤ A₀` the block budget absorbs to `K_blk β̂_{j+1}`, `K_blk = C_B A₀ C_ξ e^{2η} q / (β (1 - q))`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Finset

/-- Telescoping of a sequence with geometric increments. -/
theorem abs_sub_le_geom_of_incr (b : ℕ → ℝ) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ n, |b n - b (n + 1)| ≤ C * q ^ (n + 1)) {j k : ℕ} (hjk : j + 1 ≤ k) :
    |b (j + 1) - b k| ≤ C * q ^ (j + 2) / (1 - q) := by
  have h1 : ∀ k, j + 1 ≤ k → |b (j + 1) - b k| ≤ ∑ n ∈ Finset.Ico (j + 1) k, C * q ^ (n + 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk]
      calc |b (j + 1) - b (k + 1)| = |(b (j + 1) - b k) + (b k - b (k + 1))| := by ring_nf
        _ ≤ |b (j + 1) - b k| + |b k - b (k + 1)| := abs_add_le _ _
        _ ≤ _ := add_le_add ih (hb k)
  refine (h1 k hjk).trans ?_
  have h2 : ∑ n ∈ Finset.Ico (j + 1) k, C * q ^ (n + 1) =
      C * q * ∑ n ∈ Finset.Ico (j + 1) k, q ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h2]
  have h3 := geom_sum_Ico_le_of_lt_one hq0 hq1 (m := j + 1) (n := k)
  have h4 : 0 < 1 - q := by linarith
  calc C * q * ∑ n ∈ Finset.Ico (j + 1) k, q ^ n ≤ C * q * (q ^ (j + 1) / (1 - q)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hC hq0)
    _ = C * q ^ (j + 2) / (1 - q) := by ring

/-- **The flow absorption `hflow`** (P7CONV (30)–(31)): under the identification of the operator
constants with the real flow with the RG step bound `|ξ_n| ≤ C_ξ β⁻¹ q^{n+1}`, the fine couplings
`β̂_{j+1}, β̂_k` satisfy `|β̂_{j+1} - β̂_k| (C_B A) ≤ K_blk β̂_{j+1}` for every source size `A` with
`A q^{j+1} ≤ A₀`. -/
theorem flow_absorb_of_ident (cs : OpConsts) (d L : ℕ) [NeZero L]
    (β ν η Cξ q : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (hβpos : 0 < β) (hCξ : 0 ≤ Cξ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hβ : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hμ : ∀ n, cs.muAct n = ν * δ n)
    (hg : ∀ n, g n = g (n + 1) * (1 + ξ n 2))
    (hδ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (hμne : ∀ n, cs.muAct n ≠ 0)
    (hgenv : ∀ n, Real.exp (-η) ≤ g n ∧ g n ≤ Real.exp η)
    (hξ : ∀ n c, |ξ n c| ≤ Cξ * β⁻¹ * q ^ (n + 1))
    {j k : ℕ} (hjk : j + 1 ≤ k) {A CB A₀ : ℝ} (hCB : 0 ≤ CB) (hA : 0 ≤ A)
    (hAq : A * q ^ (j + 1) ≤ A₀) :
    |betaCanon d L (cs.beta (j + 1)) (j + 1) 0 - betaCanon d L (cs.beta k) k 0| * (CB * A) ≤
      (CB * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q))) *
        betaCanon d L (cs.beta (j + 1)) (j + 1) 0 := by
  have hq : 0 < 1 - q := by linarith
  have hgp : ∀ n, 0 < g n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hgenv n).1
  have hinc : ∀ n, |betaCanon d L (cs.beta n) n 0 - betaCanon d L (cs.beta (n + 1)) (n + 1) 0| ≤
      (Cξ * Real.exp η) * q ^ (n + 1) := fun n =>
    (flow_increment_abs_le_of_ident cs d L β ν η Cξ q g δ ξ hβpos hCξ hq0 hβ hμ hg hδ hμne
      (fun n => ⟨(hgp n).le, (hgenv n).2⟩) hξ n).1
  have htel := abs_sub_le_geom_of_incr (fun n => betaCanon d L (cs.beta n) n 0)
    (Cξ * Real.exp η) q (by positivity) hq0 hq1 hinc hjk
  have hbj : betaCanon d L (cs.beta (j + 1)) (j + 1) 0 = β * g (j + 1) :=
    betaCanon_eq_of_flow cs d L β g hβ (j + 1)
  have hA0 : 0 ≤ A₀ := le_trans (by positivity) hAq
  have hlow : β * Real.exp (-η) ≤ betaCanon d L (cs.beta (j + 1)) (j + 1) 0 := by
    rw [hbj]; exact mul_le_mul_of_nonneg_left (hgenv (j + 1)).1 hβpos.le
  have e2 : Real.exp (2 * η) * Real.exp (-η) = Real.exp η := by
    rw [← Real.exp_add]; ring_nf
  have hK : 0 ≤ CB * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) := by positivity
  calc _ ≤ (Cξ * Real.exp η * q ^ (j + 2) / (1 - q)) * (CB * A) :=
        mul_le_mul_of_nonneg_right htel (mul_nonneg hCB hA)
    _ = (CB * Cξ * Real.exp η * q / (1 - q)) * (A * q ^ (j + 1)) := by ring
    _ ≤ (CB * Cξ * Real.exp η * q / (1 - q)) * A₀ :=
        mul_le_mul_of_nonneg_left hAq (by positivity)
    _ = (CB * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q))) * (β * Real.exp (-η)) := by
        rw [← e2]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hK

section Close

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **`hcoef` with the response budgets and the flow absorption discharged** (P7CONV (30)–(31),
(52)–(54)): only the originating block budget `hblock` (51), the target weight budget `hwt`, the
counting budgets of the cubes and the sup bounds of the reads remain as source premises. The
constant is `K_coef = K_blk + K_wt + H_resp`, `K_blk = C_B A₀ C_ξ e^{2η} q / (β (1 - q))`. -/
theorem PieceWindowSetup.hcoef_of_response_flow (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (φ0 φ1 : (i : ι) → U → (W.Gc i).Ω 1 × Fin N → ℂ) (Asrc V : ι → ℝ)
    {CB A₀ Kwt Hresp Cb Cg Cm Sb Sg Sm : ℝ}
    (hA : ∀ i, 0 ≤ Asrc i) (hV : ∀ i, 0 ≤ V i) (hCB : 0 ≤ CB)
    (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hCm : 0 ≤ Cm) (hSb : 0 ≤ Sb) (hSg : 0 ≤ Sg) (hSm : 0 ≤ Sm)
    -- the originating block budget (51), the flow estimate and the target weight budget
    (hblock : ∀ i, ∀ u ∈ S, (W.chain i).β (sc i + 1) * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2) ≤
      CB * (Asrc i * W.mcount i))
    -- the flow: identification of the operator constants with the real RG flow, the step bound,
    -- the originating source size `Asrc i q^{sc i + 1} ≤ A₀`
    (cs : OpConsts) (β ν η Cξ q : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (hβpos : 0 < β) (hCξ : 0 ≤ Cξ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hβ : ∀ n, cs.beta n = β * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hμ : ∀ n, cs.muAct n = ν * δ n)
    (hg : ∀ n, g n = g (n + 1) * (1 + ξ n 2))
    (hδ : ∀ n, δ n * (1 + ξ n 2) = δ (n + 1) * (1 + ξ n 1))
    (hμne : ∀ n, cs.muAct n ≠ 0)
    (hgenv : ∀ n, Real.exp (-η) ≤ g n ∧ g n ≤ Real.exp η)
    (hξ : ∀ n c, |ξ n c| ≤ Cξ * β⁻¹ * q ^ (n + 1))
    (hchj : ∀ i, (W.chain i).β (sc i + 1) = betaCanon d L (cs.beta (sc i + 1)) (sc i + 1) 0)
    (hchk : ∀ i, (W.chain i).β k = betaCanon d L (cs.beta k) k 0)
    (hAq : ∀ i, Asrc i * q ^ (sc i + 1) ≤ A₀)
    (hwt : ∀ i, ∀ u ∈ S, (W.chain i).β k * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites,
        ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1) - W.ak) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2) ≤
      Kwt * W.mcount i)
    -- the counting of the decomposition: per-cube coefficient, spacing and mass budgets
    (hcb : ∀ i, ∀ c, (W.chain i).β k *
      ∑ x ∈ ((W.decomp i).cube c).sites, ‖levelCoeff (W.Gc i) W.ak x‖ ≤
        Cb * (Asrc i * (W.decomp i).wt c))
    (hcg : ∀ i, ∀ c, (W.chain i).β k *
      ∑ x ∈ ((W.decomp i).cube c).sites, (((W.Gc i).spacing x) ^ 2)⁻¹ ≤
        Cg * (Asrc i * (W.decomp i).wt c))
    (hcm : ∀ i, ∀ c, (W.chain i).β k *
      ∑ _x ∈ ((W.decomp i).cube c).sites, |(W.chain i).ν k| ≤
        Cm * (Asrc i * (W.decomp i).wt c))
    -- the sup bounds of the response `φ¹ - φ⁰` (weight one)
    (hval : ∀ i, ∀ u ∈ S, ∀ (x : (W.Gc i).Ω 1) (j : Fin N),
      1 * ‖(φ1 i u - φ0 i u) (x, j)‖ ≤ V i)
    (hfwd : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Gc i).Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * ((W.Gc i).spacing x * ‖svec (W.Gc i) (φ1 i u - φ0 i u) (x + Pi.single μ 1) j -
        svec (W.Gc i) (φ1 i u - φ0 i u) x j‖) ≤ V i)
    (hbwd : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Gc i).Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * ((W.Gc i).spacing x * ‖svec (W.Gc i) (φ1 i u - φ0 i u) (x - Pi.single μ 1) j -
        svec (W.Gc i) (φ1 i u - φ0 i u) x j‖) ≤ V i)
    -- the sup bounds of the datum reads at the reference field `φ⁰`
    (hrB : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites,
      ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2 ≤ Sb)
    (hrGf : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites, ∀ μ : Fin d,
      (W.Gc i).spacing x ^ 2 * ∑ j, ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u)
        (x + Pi.single μ 1) j - barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u) x j‖ ^ 2 ≤ Sg)
    (hrGb : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites, ∀ μ : Fin d,
      (W.Gc i).spacing x ^ 2 * ∑ j, ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u)
        (x - Pi.single μ 1) j - barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u) x j‖ ^ 2 ≤ Sg)
    (hrM : ∀ i, ∀ u ∈ S, ∀ x ∈ (W.Xc i).sites,
      ∑ j, ‖svec (W.Gc i) (φ0 i u) x j - ((W.chain i).Dat u k).h x j‖ ^ 2 ≤ Sm)
    -- the supremum (53)
    (hresp : ∀ i, Asrc i * (V i * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
      V i ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤ Hresp) :
    ∀ i, ∀ u ∈ S,
      ‖((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) ((W.chain i).a k) ((W.chain i).ν k)
          ((W.chain i).Dat u k) (φ0 i u) -
        ((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) W.ak ((W.chain i).ν k)
          ((W.chain i).Dat u k) (φ1 i u)‖ ≤ (CB * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) + Kwt + Hresp) *
        W.mcount i := by
  have hgp : ∀ n, 0 < g n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hgenv n).1
  have hbpos : ∀ n, 0 < betaCanon d L (cs.beta n) n 0 := fun n => by
    rw [betaCanon_eq_of_flow cs d L β g hβ n]; exact mul_pos hβpos (hgp n)
  refine W.hcoef_of_response φ0 φ1 Asrc V hA hV (fun i => by rw [hchk i]; exact (hbpos k).le)
    (fun i => by rw [hchj i]; exact hbpos _) hCb hCg hCm hSb hSg hSm hblock ?_ hwt hcb hcg hcm hval
    hfwd hbwd hrB hrGf hrGb hrM hresp
  intro i
  rw [hchj i, hchk i]
  exact flow_absorb_of_ident cs d L β ν η Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ
    (by have := W.sc_lt i; omega) hCB (hA i) (hAq i)

end Close

end Balaban.LargeField.ActionConv
