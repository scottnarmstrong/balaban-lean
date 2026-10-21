/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ScaledDomain

/-!
# The renormalized datum for complex `ζ` in the complex data domain

For complex `ζ` the datum `(1 + ζ) Ψ` is not real.  As in the same-centre choice of
`RenormThetaDatum`, the real centre `Ψ` of the datum stays and the displacement `ζ Ψ` is absorbed into the
complex perturbation `Ψ'` of `Ψ̃^c(𝔹_k; δ, ε)`.  This is not an instance of the real scaling
(`InPsiTilde.scale`, which moves the centre); both rest on the scaling lemmas `vn_smul_complex`, `rn_smul`.

* `InPsiTilde.mono_delta`: the real domain is monotone in `δ`;
* `InDomainR.toScaledC`: the datum `(1 + ζ) Ψ` with the same `h` is in `InDomainC G ν (δ + 4|ζ|) ε'`
  for `|ζ| ≤ 1/256`, `0 < δ ≤ 1/3`, `2|ζ| ≤ ε'`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- The real data domain is monotone in the parameter `δ`. -/
theorem InPsiTilde.mono_delta {ν δ δ' : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    (hP : InPsiTilde G ν δ Ψ h) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ') : InPsiTilde G ν δ' Ψ h where
  layerConst := hP.layerConst
  r1 x x' hxx := (hP.r1 x x' hxx).trans_le hδ
  r2 x hx := (hP.r2 x hx).trans_le hδ
  r3 x hx := (hP.r3 x hx).trans_le (by nlinarith)
  r4 := hP.r4.trans_le (by nlinarith)

/-- **The renormalized datum for complex `ζ` lies in the complex domain.**  The real centre `Ψ` of `D`
stays, the displacement is `Ψ' = ζ Ψ`, `h' = 0`. -/
theorem InDomainR.toScaledC {ν δ ε' : ℝ} {ζ : ℂ} {D Dc : BgData G N} (hD : InDomainR G ν δ D)
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Dc.Ψ x i = (1 + ζ) * D.Ψ x i)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, Dc.h x i = D.h x i) (hζ : ‖ζ‖ ≤ 1 / 256)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) (hε : 0 < ε') (hε2 : 2 * ‖ζ‖ ≤ ε') :
    InDomainC G ν (δ + 4 * ‖ζ‖) ε' Dc := by
  obtain ⟨Ψ, h, hP, hΨ0, hh0⟩ := hD
  have hρ := norm_nonneg ζ
  have hδ'0 : 0 < δ + 4 * ‖ζ‖ := by positivity
  have hPm := hP.mono_delta hδ0.le (by linarith : δ ≤ δ + 4 * ‖ζ‖)
  have hΨ' : ∀ x ∈ dataSites G, ∀ i, Dc.Ψ x i = (Ψ x i : ℂ) + ζ * (Ψ x i : ℂ) := by
    intro x hx i; rw [hΨ x hx i, hΨ0 x hx i]; ring
  refine ⟨Ψ, h, fun x i => ζ * (Ψ x i : ℂ), fun _ _ => 0, ?_, hΨ', fun x hx i => ?_⟩
  · refine
      { hPm with
        eps_pos := hε
        layerConst' := ?_
        hLayerConst' := ?_
        c1 := ?_
        c2a := ?_
        c2b := ?_
        c3a := ?_
        c3b := ?_ }
    · intro n hn1 hnk x hx x' hx'
      funext i
      simp only [hP.layerConst n hn1 hnk x hx x' hx']
    · intro n hn1 hnk x hx x' hx'
      rfl
    · intro x x' hxx
      have e : (fun i => ζ * (Ψ x i : ℂ)) - (fun i => ζ * (Ψ x' i : ℂ)) =
          fun i => ζ * (((Ψ x i - Ψ x' i : ℝ)) : ℂ) := by funext i; simp; ring
      rw [e, vn_smul_complex, vn_ofReal]
      have := hP.r1 x x' hxx
      nlinarith
    · intro x hx
      rw [show (fun i => ζ * (Ψ x i : ℂ)) = fun i => ζ * ((Ψ x i : ℝ) : ℂ) from rfl, vn_smul_complex,
        vn_ofReal]
      have h2 := hP.r2 x hx
      have hsq : rn (Ψ x) ^ 2 = ∑ i, Ψ x i ^ 2 := by
        unfold rn; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      have hr0 : 0 ≤ rn (Ψ x) := Real.sqrt_nonneg _
      have hr : rn (Ψ x) ≤ 2 := by
        by_contra hc; push Not at hc
        have := abs_lt.mp h2
        nlinarith
      nlinarith
    · intro x hx
      have e : ∑ i, ((Ψ x i : ℂ) + ζ * (Ψ x i : ℂ)) * ((Ψ x i : ℂ) + ζ * (Ψ x i : ℂ)) -
          ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) = ((2 * ζ + ζ ^ 2 : ℂ)) * ((∑ i, Ψ x i ^ 2 : ℝ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h2 := abs_lt.mp (hP.r2 x hx)
      have hS : |∑ i, Ψ x i ^ 2| ≤ 4 / 3 := by
        rw [abs_le]; constructor <;> nlinarith
      have hz : ‖(2 * ζ + ζ ^ 2 : ℂ)‖ ≤ 3 * ‖ζ‖ := by
        calc ‖(2 * ζ + ζ ^ 2 : ℂ)‖ ≤ ‖2 * ζ‖ + ‖ζ ^ 2‖ := norm_add_le _ _
          _ ≤ 3 * ‖ζ‖ := by
            rw [norm_mul, norm_pow]
            have : ‖(2 : ℂ)‖ = 2 := by simp
            rw [this]
            nlinarith
      calc ‖(2 * ζ + ζ ^ 2 : ℂ)‖ * |∑ i, Ψ x i ^ 2| ≤ 3 * ‖ζ‖ * (4 / 3) :=
            mul_le_mul hz hS (abs_nonneg _) (by positivity)
        _ < δ + 4 * ‖ζ‖ := by nlinarith
    · intro x hx
      have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
      rw [h0, mul_zero]
      positivity
    · intro x hx
      simp only [mul_zero, Finset.sum_const_zero, norm_zero]
      positivity
  · rw [hh x hx i, hh0 x hx i]; simp
