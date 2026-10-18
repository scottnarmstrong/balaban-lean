/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `hcoef` from the response sup bounds and the cube counting (P7CONV §3.4, (52)–(54))

`PieceWindowSetup.hcoef_of_response` is `PieceWindowSetup.hcoef_of_budgets` with the six read
budgets (52) proved from

* the weight-one sup bounds `V i` of the response `φ¹ - φ⁰` (value, forward and backward
  difference quotients; the output of `coeffChange_sameData_response`);
* sup bounds `S_b, S_g, S_m` of the datum reads at the reference field `φ⁰` (block read, bond
  difference quotients of `φ̄⁰`, mass read);
* the per-cube budgets of the decomposition (`C_b, C_g, C_m`).

The constants are `GB = S_b C_b`, `GG = d S_g C_g`, `GM = S_m C_m` and
`GB' = N C_b`, `GG' = d N C_g`, `GM' = N C_m`, with `σ_i = V_i`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **`hcoef` from the response sup bounds** (P7CONV (52)–(54), with the energy budgets proved from
the sup bounds and the counting of the cube decomposition). -/
theorem PieceWindowSetup.hcoef_of_response (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (φ0 φ1 : (i : ι) → U → (W.Gc i).Ω 1 × Fin N → ℂ) (Asrc V : ι → ℝ)
    {CB Kblk Kwt Hresp Cb Cg Cm Sb Sg Sm : ℝ}
    (hA : ∀ i, 0 ≤ Asrc i) (hV : ∀ i, 0 ≤ V i)
    (hβk : ∀ i, 0 ≤ (W.chain i).β k) (hβj : ∀ i, 0 < (W.chain i).β (sc i + 1))
    (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hCm : 0 ≤ Cm) (hSb : 0 ≤ Sb) (hSg : 0 ≤ Sg) (hSm : 0 ≤ Sm)
    -- the originating block budget (51), the flow estimate and the target weight budget
    (hblock : ∀ i, ∀ u ∈ S, (W.chain i).β (sc i + 1) * ((1 / 2) *
      ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) ((W.chain i).a (sc i + 1)) x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2) ≤
      CB * (Asrc i * W.mcount i))
    (hflow : ∀ i, |(W.chain i).β (sc i + 1) - (W.chain i).β k| * (CB * Asrc i) ≤
      Kblk * (W.chain i).β (sc i + 1))
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
          ((W.chain i).Dat u k) (φ1 i u)‖ ≤ (Kblk + Kwt + Hresp) * W.mcount i := by
  have hmc := W.mcount_eq
  refine W.hcoef_of_budgets φ0 φ1 Asrc V (GB := Sb * Cb) (GB' := N * Cb)
    (GG := d * (Sg * Cg)) (GG' := d * (N * Cg)) (GM := Sm * Cm) (GM' := N * Cm)
    hA hV hβk hβj (mul_nonneg hSb hCb) (by positivity) (mul_nonneg hSm hCm)
    hblock hflow hwt ?_ ?_ ?_ ?_ ?_ ?_ hresp
  · intro i u hu
    have := Region.siteEnergy_le (W.decomp i) (fun x => ‖levelCoeff (W.Gc i) W.ak x‖)
      (fun x j => ((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j)
      (B := Sb) (κ := Cb * Asrc i) (hβk i) hSb (fun x => norm_nonneg _) (hrB i u hu)
      (fun c => by simpa only [mul_assoc] using hcb i c)
    rw [hmc i]
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro i u hu
    have := Region.blockEnergy_response_le (W.decomp i) W.ak (φ1 i u - φ0 i u) (V := V i)
      (A := Asrc i) (Cb := Cb) (hβk i) (hval i u hu) (hcb i)
    rw [hmc i]
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro i u hu
    have := Region.bondEnergy_le (W.decomp i)
      (barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u)) (B := Sg) (κ := Cg * Asrc i)
      (hβk i) hSg (hrGf i u hu) (hrGb i u hu)
      (fun c => by simpa only [mul_assoc] using hcg i c)
    rw [hmc i]
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro i u hu
    have := Region.bondEnergy_response_le (W.decomp i) (φ1 i u - φ0 i u) (V := V i)
      (A := Asrc i) (Cg := Cg) (hβk i) (hfwd i u hu) (hbwd i u hu) (hcg i)
    rw [hmc i]
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro i u hu
    have := Region.siteEnergy_le (W.decomp i) (fun _ => |(W.chain i).ν k|)
      (fun x j => svec (W.Gc i) (φ0 i u) x j - ((W.chain i).Dat u k).h x j)
      (B := Sm) (κ := Cm * Asrc i) (hβk i) hSm (fun _ => abs_nonneg _) (hrM i u hu)
      (fun c => by simpa only [mul_assoc] using hcm i c)
    rw [hmc i]
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro i u hu
    have := Region.massEnergy_response_le (W.decomp i) (φ1 i u - φ0 i u) (V := V i)
      (A := Asrc i) (Cm := Cm) (ν := (W.chain i).ν k) (hβk i) (hval i u hu) (hcm i)
    rw [hmc i]
    calc _ ≤ _ := this
      _ = _ := by ring

end Balaban.LargeField.ActionConv
