/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseMismatch
public import Balaban.LargeField.R.WindowConvUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The coefficient residual `hcoef` from the block and response budgets (P7CONV §3.4, (48)–(54))

For a piece `i` put `P_i = β̂_k A_{X_i}(a_i, μ_i; D_i, φ⁰_i)` (the terminal action of the chain
read at the reference field `φ⁰_i` of the coefficient `a_i`) and
`Q_i = β̂_k A_{X_i}(ak, μ_i; D_i, φ¹_i)` (the action at the common window coefficient `ak` and its
background `φ¹_i`).  Then `‖P_i - Q_i‖ ≤ K_coef m_i`, with `K_coef = K_blk + K_wt + H_resp`,
is the `hcoef` binder of `window_uniform_of_parts`.  The inputs, all named premises:

* the originating block budget (51): `β̂_{j+1} B_i ≤ C_B A_i`, the flow estimate absorbing
  `|β̂_{j+1} - β̂_k| C_B A_i ≤ K_blk β̂_{j+1}`, and the target weight budget `β̂_k B_i^{wt} ≤ K_wt m_i`;
* the six read budgets (52) of the perturbation `φ¹ - φ⁰` at fixed `ak`, and the supremum (53).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι] {sc : ι → ℕ} {k1 k : ℕ}

/-- **`hcoef` from the block budget (51) and the response budgets (52)–(53).** -/
theorem PieceWindowSetup.hcoef_of_budgets (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (φ0 φ1 : (i : ι) → U → (W.Gc i).Ω 1 × Fin N → ℂ) (Asrc σ : ι → ℝ)
    {CB Kblk Kwt Hresp GB GB' GG GG' GM GM' : ℝ}
    (hA : ∀ i, 0 ≤ Asrc i) (hσ : ∀ i, 0 ≤ σ i)
    (hβk : ∀ i, 0 ≤ (W.chain i).β k) (hβj : ∀ i, 0 < (W.chain i).β (sc i + 1))
    (hGB : 0 ≤ GB) (hGG : 0 ≤ GG) (hGM : 0 ≤ GM)
    -- the originating block budget (51)
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
    -- the six read budgets (52) of the perturbation `φ¹ - φ⁰` at fixed `ak`
    (hB : ∀ i, ∀ u ∈ S, (W.chain i).β k * ∑ x ∈ (W.Xc i).sites,
      ‖levelCoeff (W.Gc i) W.ak x‖ *
        ∑ j, ‖((W.chain i).Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2 ≤
      GB * (Asrc i * W.mcount i))
    (hB' : ∀ i, ∀ u ∈ S, (W.chain i).β k * ∑ x ∈ (W.Xc i).sites,
      ‖levelCoeff (W.Gc i) W.ak x‖ *
        ∑ j, ‖blockAvg (W.Gc i) (φ1 i u - φ0 i u) x j‖ ^ 2 ≤
      GB' * (Asrc i * W.mcount i * σ i ^ 2))
    (hG : ∀ i, ∀ u ∈ S, (W.chain i).β k *
      ∑ z : Torus d (W.N₀c i * L ^ W.Kc i) × Fin d, (W.Xc i).starWeight z.1 z.2 * ∑ j,
        ‖barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u) (z.1 + Pi.single z.2 1) j -
          barField (W.Gc i) ((W.chain i).Dat u k).Ψ (φ0 i u) z.1 j‖ ^ 2 ≤
      GG * (Asrc i * W.mcount i))
    (hG' : ∀ i, ∀ u ∈ S, (W.chain i).β k *
      ∑ z : Torus d (W.N₀c i * L ^ W.Kc i) × Fin d, (W.Xc i).starWeight z.1 z.2 * ∑ j,
        ‖svec (W.Gc i) (φ1 i u - φ0 i u) (z.1 + Pi.single z.2 1) j -
          svec (W.Gc i) (φ1 i u - φ0 i u) z.1 j‖ ^ 2 ≤
      GG' * (Asrc i * W.mcount i * σ i ^ 2))
    (hM : ∀ i, ∀ u ∈ S, (W.chain i).β k * ∑ x ∈ (W.Xc i).sites, |(W.chain i).ν k| * ∑ j,
      ‖svec (W.Gc i) (φ0 i u) x j - ((W.chain i).Dat u k).h x j‖ ^ 2 ≤
      GM * (Asrc i * W.mcount i))
    (hM' : ∀ i, ∀ u ∈ S, (W.chain i).β k * ∑ x ∈ (W.Xc i).sites, |(W.chain i).ν k| * ∑ j,
      ‖svec (W.Gc i) (φ1 i u - φ0 i u) x j‖ ^ 2 ≤
      GM' * (Asrc i * W.mcount i * σ i ^ 2))
    -- the supremum (53)
    (hresp : ∀ i, Asrc i * (σ i * (Real.sqrt (GB * GB') + Real.sqrt (GG * GG') +
      Real.sqrt (GM * GM')) + σ i ^ 2 / 2 * (GB' + GG' + GM')) ≤ Hresp) :
    ∀ i, ∀ u ∈ S,
      ‖((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) ((W.chain i).a k) ((W.chain i).ν k)
          ((W.chain i).Dat u k) (φ0 i u) -
        ((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) W.ak ((W.chain i).ν k)
          ((W.chain i).Dat u k) (φ1 i u)‖ ≤ (Kblk + Kwt + Hresp) * W.mcount i := by
  intro i u hu
  have hm := W.mcount_nonneg i
  set C := W.chain i with hC
  set Bk : ℝ := (1 / 2) * ∑ x ∈ (W.Xc i).sites, ‖levelCoeff (W.Gc i) (C.a (sc i + 1)) x‖ *
    ∑ j, ‖(C.Dat u k).Ψ x j - blockAvg (W.Gc i) (φ0 i u) x j‖ ^ 2 with hBk
  have hBk0 : 0 ≤ Bk := by rw [hBk]; positivity
  -- the coefficient mismatch (48)–(50)
  have s1 := coeff_mismatch_action_le (W.Xc i) (C.a k) W.ak (C.a (sc i + 1)) (C.ν k) (C.Dat u k)
    (φ0 i u) (hβk i) (fun ℓ => W.coeff_target_mismatch i ℓ)
  rw [← hBk] at s1
  -- the originating block charge
  have s2 : |C.β (sc i + 1) - C.β k| * Bk ≤ Kblk * W.mcount i := by
    refine le_of_mul_le_mul_right ?_ (hβj i)
    calc |C.β (sc i + 1) - C.β k| * Bk * C.β (sc i + 1)
        = |C.β (sc i + 1) - C.β k| * (C.β (sc i + 1) * Bk) := by ring
      _ ≤ |C.β (sc i + 1) - C.β k| * (CB * (Asrc i * W.mcount i)) :=
          mul_le_mul_of_nonneg_left (hblock i u hu) (abs_nonneg _)
      _ = (|C.β (sc i + 1) - C.β k| * (CB * Asrc i)) * W.mcount i := by ring
      _ ≤ (Kblk * C.β (sc i + 1)) * W.mcount i :=
          mul_le_mul_of_nonneg_right (hflow i) hm
      _ = Kblk * W.mcount i * C.β (sc i + 1) := by ring
  -- the response charge
  have s3 := actionRegionC_add_sub_le (W.Xc i) W.ak (C.ν k) (C.Dat u k) (φ0 i u)
    (φ1 i u - φ0 i u) (β := C.β k) (A := Asrc i * W.mcount i) (σ := σ i) (hβk i)
    (mul_nonneg (hA i) hm) (hσ i) hGB hGG hGM (hB i u hu) (hB' i u hu) (hG i u hu) (hG' i u hu)
    (hM i u hu) (hM' i u hu)
  rw [add_sub_cancel] at s3
  have s4 : Asrc i * W.mcount i * (σ i * (Real.sqrt (GB * GB') + Real.sqrt (GG * GG') +
      Real.sqrt (GM * GM')) + σ i ^ 2 / 2 * (GB' + GG' + GM')) ≤ Hresp * W.mcount i := by
    have := mul_le_mul_of_nonneg_right (hresp i) hm
    linarith
  have hsplit : ((C.β k : ℝ) : ℂ) * actionRegionC (W.Xc i) (C.a k) (C.ν k) (C.Dat u k) (φ0 i u) -
        ((C.β k : ℝ) : ℂ) * actionRegionC (W.Xc i) W.ak (C.ν k) (C.Dat u k) (φ1 i u) =
      ((C.β k : ℝ) : ℂ) * (actionRegionC (W.Xc i) (C.a k) (C.ν k) (C.Dat u k) (φ0 i u) -
        actionRegionC (W.Xc i) W.ak (C.ν k) (C.Dat u k) (φ0 i u)) -
      ((C.β k : ℝ) : ℂ) * (actionRegionC (W.Xc i) W.ak (C.ν k) (C.Dat u k) (φ1 i u) -
        actionRegionC (W.Xc i) W.ak (C.ν k) (C.Dat u k) (φ0 i u)) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have := hwt i u hu
  nlinarith [s1, s2, s3, s4, this]

end Balaban.LargeField.ActionConv
