/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseCubeBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `hcoef` with the cube budgets and the target-weight budget discharged

`PieceWindowSetup.hcoef_of_response_flow_cubes` is `hcoef_of_response_flow` with the per-cube
budgets `C_b, C_g, C_m` and the target weight budget `hwt` proved, for a decomposition whose cells
are layer blocks of weight one (`exists_piece_stepDecomp_total_le_cells`), from

* the real flow `cs.beta n = β L^{(d-2)n} g_n`, `e^{-η} ≤ g_n ≤ e^η`;
* the source size `A_i = cs.beta(j+1) ε_{j+1}²`, `ε_n = epsSeq L α α₀ n`, `0 ≤ α`, `ε_n ≥ ε₀ > 0`
  for `n ≤ k` (`ε₀ = α₀ L^{-α k}` is admissible);
* the sizes `|ak ℓ| ≤ K_a`, `|cs.aw ℓ - ak ℓ| ≤ Δ`;
* the a priori regime `β |ν| L^{k d} ≤ 1` and `|δ_k| ≤ D_δ` for the mass `cs.muAct k = ν δ_k`.

The constants are `C_b = e^{2η} K_a/ε₀²`, `C_g = e^{2η}/ε₀²`, `C_m = e^{2η} D_δ/(β ε₀²)`,
`K_wt = S_b β e^η L^{(d-2)k} Δ / 2`.  Only the originating block budget (51) `hblock` and the
supremum `hresp` of the response remain.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Finset

/-- The lower bound `ε_n ≥ α₀ L^{-α k}` for `n ≤ k`. -/
theorem epsSeq_sq_ge (L : ℕ) [NeZero L] {α α₀ : ℝ} (hα : 0 ≤ α) (hα₀ : 0 < α₀) {n k : ℕ}
    (hnk : n ≤ k) : (α₀ * ((L : ℝ) ^ (-α)) ^ k) ^ 2 ≤ epsSeq L α α₀ n ^ 2 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hr0 : 0 < (L : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : (L : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have h1 : ((L : ℝ) ^ (-α)) ^ k ≤ ((L : ℝ) ^ (-α)) ^ n := pow_le_pow_of_le_one hr0.le hr1 hnk
  have ht := one_le_epsTail n
  unfold epsSeq
  apply pow_le_pow_left₀ (by positivity)
  have h2 : 0 ≤ ((L : ℝ) ^ (-α)) ^ n := by positivity
  calc α₀ * ((L : ℝ) ^ (-α)) ^ k ≤ α₀ * ((L : ℝ) ^ (-α)) ^ n :=
        mul_le_mul_of_nonneg_left h1 hα₀.le
    _ = α₀ * 1 * ((L : ℝ) ^ (-α)) ^ n := by ring
    _ ≤ α₀ * epsTail n * ((L : ℝ) ^ (-α)) ^ n := by
        apply mul_le_mul_of_nonneg_right _ h2
        exact mul_le_mul_of_nonneg_left ht hα₀.le

section Close

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **`hcoef` with the cube budgets `C_b, C_g, C_m` and the target weight budget discharged.**
`hcells` says that the cells of the decomposition of the piece are layer blocks of weight one of
layer `ℓ ≤ sc i + 1` (`exists_piece_stepDecomp_total_le_cells`, with `ℓ ∈ {j, j + 1}`). -/
theorem PieceWindowSetup.hcoef_of_response_flow_cubes
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (φ0 φ1 : (i : ι) → U → (W.Gc i).Ω 1 × Fin N → ℂ) (Asrc V : ι → ℝ)
    {CB A₀ Kwt Hresp Cb Cg Cm Sb Sg Sm : ℝ}
    (hA : ∀ i, 0 ≤ Asrc i) (hV : ∀ i, 0 ≤ V i) (hCB : 0 ≤ CB)
    (hSb : 0 ≤ Sb) (hSg : 0 ≤ Sg) (hSm : 0 ≤ Sm) (hd : 2 ≤ d)
    -- the cells of the decomposition: layer blocks of weight one
    (hwt1 : ∀ i c, (W.decomp i).wt c = 1)
    (hcells : ∀ i c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1)
    -- the originating block budget (51)
    (hblock : ∀ i, ∀ u ∈ S, (W.chain i).β (sc i + 1) * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2) ≤
      CB * (Asrc i * W.mcount i))
    -- the real flow
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
    -- the source size `A_i = cs.beta (j+1) ε_{j+1}²`, `ε_n ≥ ε₀ > 0` for `n ≤ k`
    (α α₀ ε₀ : ℝ) (hα : 0 ≤ α) (hα₀ : 0 < α₀) (hε₀ : 0 < ε₀)
    (hε₀le : ε₀ ≤ α₀ * ((L : ℝ) ^ (-α)) ^ k)
    (hAsrc : ∀ i, Asrc i = cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2)
    -- the sizes of the coefficients and the regime
    (Ka Δ Dδ : ℝ) (hKa : ∀ ℓ, |W.ak ℓ| ≤ Ka)
    (hchA : ∀ i, (W.chain i).a (sc i + 1) = cs.aw) (hΔ : ∀ ℓ, |cs.aw ℓ - W.ak ℓ| ≤ Δ)
    (hchν : ∀ i, (W.chain i).ν k = cs.muAct k)
    (hreg : β * |ν| * (L : ℝ) ^ (k * d) ≤ 1) (hδk : |δ k| ≤ Dδ)
    -- the constants
    (hCb : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (hCg : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (hCm : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
    (hKwt : Sb * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) / 2 ≤ Kwt)
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
          ((W.chain i).Dat u k) (φ1 i u)‖ ≤
        (CB * A₀ * Cξ * Real.exp (2 * η) * q / (β * (1 - q)) + Kwt + Hresp) *
        W.mcount i := by
  have hgp : ∀ n, 0 < g n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hgenv n).1
  have hbk : ∀ i, (W.chain i).β k = β * g k := fun i => by
    rw [hchk i, betaCanon_eq_of_flow cs d L β g hβ k]
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
  have hDδ0 : 0 ≤ Dδ := (abs_nonneg _).trans hδk
  have hE2 : ∀ i, ε₀ ^ 2 ≤ epsSeq L α α₀ (sc i + 1) ^ 2 := fun i =>
    (pow_le_pow_left₀ hε₀.le hε₀le 2).trans
      (epsSeq_sq_ge L hα hα₀ (by have := W.sc_lt i; omega))
  have hA' : ∀ i, Asrc i =
      β * (L : ℝ) ^ ((d - 2) * (sc i + 1)) * g (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 :=
    fun i => by rw [hAsrc, hβ]
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb
  have hCg0 : 0 ≤ Cg := le_trans (by positivity) hCg
  have hCm0 : 0 ≤ Cm := le_trans (by positivity) hCm
  -- the data of a cell
  have hcell : ∀ i c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1 := hcells
  have hcb : ∀ i, ∀ c, (W.chain i).β k *
      ∑ x ∈ ((W.decomp i).cube c).sites, ‖levelCoeff (W.Gc i) W.ak x‖ ≤
        Cb * (Asrc i * (W.decomp i).wt c) := by
    intro i c
    obtain ⟨x, hx, hs, hl⟩ := hcell i c
    rw [hs, (W.Xc i).layerBlock_sum_levelCoeff hx, pow_layer_mul hd, hbk i, hwt1, mul_one, hA' i]
    calc _ ≤ (Real.exp (2 * η) * |W.ak ((W.Gc i).layerIndex x)| / ε₀ ^ 2) *
          (β * (L : ℝ) ^ ((d - 2) * (sc i + 1)) * g (sc i + 1) *
            epsSeq L α α₀ (sc i + 1) ^ 2) :=
          cube_budget_core hβpos (hgenv k).2 (hgenv _).1 (abs_nonneg _) hε2 (hE2 i) hl
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right
          · exact le_trans (by gcongr; exact hKa _) hCb
          · rw [← hA' i]; exact hA i
  have hcg : ∀ i, ∀ c, (W.chain i).β k *
      ∑ x ∈ ((W.decomp i).cube c).sites, (((W.Gc i).spacing x) ^ 2)⁻¹ ≤
        Cg * (Asrc i * (W.decomp i).wt c) := by
    intro i c
    obtain ⟨x, hx, hs, hl⟩ := hcell i c
    have hp := pow_layer_mul (L := L) hd ((W.Gc i).layerIndex x) 1
    rw [one_div] at hp
    rw [hs, (W.Xc i).layerBlock_sum_spacing hx, hp, hbk i, hwt1, mul_one, hA' i]
    calc _ ≤ (Real.exp (2 * η) * 1 / ε₀ ^ 2) *
          (β * (L : ℝ) ^ ((d - 2) * (sc i + 1)) * g (sc i + 1) *
            epsSeq L α α₀ (sc i + 1) ^ 2) := by
          have := cube_budget_core (L := L) (d := d) hβpos (hgenv k).2
            (hgenv (sc i + 1)).1 (X := 1) (by norm_num) hε2 (hE2 i) hl
          simpa only [one_mul] using this
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right
          · rw [mul_one]; exact hCg
          · rw [← hA' i]; exact hA i
  have hcm : ∀ i, ∀ c, (W.chain i).β k *
      ∑ _x ∈ ((W.decomp i).cube c).sites, |(W.chain i).ν k| ≤
        Cm * (Asrc i * (W.decomp i).wt c) := by
    intro i c
    obtain ⟨x, hx, hs, hl⟩ := hcell i c
    have hk' : sc i + 1 ≤ k := by have := W.sc_lt i; omega
    rw [hs, (W.Xc i).layerBlock_sum_const hx, hbk i, hwt1, mul_one, hA' i, hchν i, hμ, abs_mul]
    set ℓ := (W.Gc i).layerIndex x
    have hLk : ((L : ℝ) ^ ℓ) ^ d ≤ (L : ℝ) ^ (k * d) := by
      rw [← pow_mul]; exact pow_L_mono (Nat.mul_le_mul_right _ (hl.trans hk'))
    have hgkb := (hgenv k).2
    have hgj := (hgenv (sc i + 1)).1
    have hP : 1 ≤ (L : ℝ) ^ ((d - 2) * (sc i + 1)) := one_le_pow_L _
    have e2 : Real.exp (2 * η) * Real.exp (-η) = Real.exp η := by
      rw [← Real.exp_add]; ring_nf
    have hgjE : Real.exp (-η) * ε₀ ^ 2 ≤ g (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 :=
      mul_le_mul hgj (hE2 i) hε2.le ((Real.exp_pos _).le.trans hgj)
    calc β * g k * (((L : ℝ) ^ ℓ) ^ d * (|ν| * |δ k|))
        ≤ β * Real.exp η * ((L : ℝ) ^ (k * d) * (|ν| * Dδ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hgkb hβpos.le)
            (mul_le_mul hLk (mul_le_mul_of_nonneg_left hδk (abs_nonneg _)) (by positivity)
              (by positivity)) (by positivity) (by positivity)
      _ = Real.exp η * Dδ * (β * |ν| * (L : ℝ) ^ (k * d)) := by ring
      _ ≤ Real.exp η * Dδ * 1 :=
          mul_le_mul_of_nonneg_left hreg (by positivity)
      _ = (Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2)) *
          (β * 1 * (Real.exp (-η) * ε₀ ^ 2)) := by
          rw [← e2]; field_simp
      _ ≤ (Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2)) *
          (β * (L : ℝ) ^ ((d - 2) * (sc i + 1)) *
            (g (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 1 * (Real.exp (-η) * ε₀ ^ 2) ≤ (L : ℝ) ^ ((d - 2) * (sc i + 1)) *
              (g (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) :=
            (mul_le_mul_of_nonneg_right hP (by positivity)).trans
              (mul_le_mul_of_nonneg_left hgjE (by linarith))
          calc β * 1 * (Real.exp (-η) * ε₀ ^ 2) = β * (1 * (Real.exp (-η) * ε₀ ^ 2)) := by ring
            _ ≤ β * ((L : ℝ) ^ ((d - 2) * (sc i + 1)) *
                (g (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2)) :=
                mul_le_mul_of_nonneg_left h1 hβpos.le
            _ = _ := by ring
      _ ≤ Cm * _ := by
          have := hgp (sc i + 1)
          apply mul_le_mul hCm (le_of_eq (by ring)) (by positivity) hCm0
  have hwt : ∀ i, ∀ u ∈ S, (W.chain i).β k * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites,
        ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1) - W.ak) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2) ≤
      Kwt * W.mcount i := by
    intro i u hu
    have hcube : ∀ c, (W.chain i).β k *
        ∑ x ∈ ((W.decomp i).cube c).sites,
          ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1) - W.ak) x‖ ≤
        (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) * (W.decomp i).wt c := by
      intro c
      obtain ⟨x, hx, hs, hl⟩ := hcell i c
      have hk' : sc i + 1 ≤ k := by have := W.sc_lt i; omega
      rw [hs, (W.Xc i).layerBlock_sum_levelCoeff hx, pow_layer_mul hd, hbk i, hwt1, mul_one]
      have hdiff : |((W.chain i).a (sc i + 1) - W.ak) ((W.Gc i).layerIndex x)| ≤ Δ := by
        rw [Pi.sub_apply, hchA i]; exact hΔ _
      have hP : (L : ℝ) ^ ((W.Gc i).layerIndex x * (d - 2)) ≤ (L : ℝ) ^ ((d - 2) * k) := by
        apply pow_L_mono
        rw [mul_comm]; exact Nat.mul_le_mul_left _ (hl.trans hk')
      calc β * g k * (|((W.chain i).a (sc i + 1) - W.ak) ((W.Gc i).layerIndex x)| *
            (L : ℝ) ^ ((W.Gc i).layerIndex x * (d - 2)))
          ≤ β * Real.exp η * (Δ * (L : ℝ) ^ ((d - 2) * k)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left (hgenv k).2 hβpos.le)
              (mul_le_mul hdiff hP (by positivity) hΔ0) (by positivity) (by positivity)
        _ = _ := by ring
    have h := (W.Xc i).siteEnergy_le (W.decomp i)
      (fun x => ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1) - W.ak) x‖)
      (fun x j => ((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j)
      (by rw [hbk i]; exact mul_nonneg hβpos.le (hgp k).le) hSb (fun x => norm_nonneg _)
      (hrB i u hu) hcube
    rw [← W.mcount_eq] at h
    calc _ = (1 / 2) * ((W.chain i).β k *
          ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1) - W.ak) x‖ *
            ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2) := by
          ring
      _ ≤ (1 / 2) * (Sb * ((β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) * W.mcount i)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (Sb * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) / 2) * W.mcount i := by ring
      _ ≤ Kwt * W.mcount i := mul_le_mul_of_nonneg_right hKwt (W.mcount_nonneg i)
  exact W.hcoef_of_response_flow φ0 φ1 Asrc V hA hV hCB hCb0 hCg0 hCm0 hSb hSg hSm hblock cs β ν η
    Cξ q g δ ξ hβpos hCξ hq0 hq1 hβ hμ hg hδ hμne hgenv hξ hchj hchk hAq hwt hcb hcg hcm hval hfwd
    hbwd hrB hrGf hrGb hrM hresp

end Close

end Balaban.LargeField.ActionConv
