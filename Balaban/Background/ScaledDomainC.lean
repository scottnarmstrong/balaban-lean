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
* `InPsiTildeC.scale`: if `(Ψ, h, Ψ', 0)` is in `Ψ̃^c(𝔹_k; δ, ε)` then `(Ψ, h, Ψ' + ζ(Ψ + Ψ'), 0)` is in
  `Ψ̃^c(𝔹_k; δ + 5|ζ|, ε + 2|ζ|)` (`|ζ| ≤ 1/256`, `0 < δ ≤ 1/3`, `ε ≤ 1/16`), i.e. the datum
  `(1 + ζ)(Ψ + Ψ')`;
* `InDomainC.scale`, `InDomainR.toScaledC`: the same for `BgData` (the real case has `Ψ' = 0`).
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

/-- `v + ζ (u + v)` has norm at most `|v| + |ζ| (|u| + |v|)`. -/
theorem vn_aux (u v : Fin N → ℂ) (ζ : ℂ) :
    vn (fun i => v i + ζ * (u i + v i)) ≤ vn v + ‖ζ‖ * (vn u + vn v) := by
  have h1 := vn_add' v (fun i => ζ * (u i + v i))
  have h2 := vn_smul_complex ζ (fun i => u i + v i)
  have h3 := vn_add' u v
  have h0 := norm_nonneg ζ
  nlinarith [vn_nonneg u, vn_nonneg v]

/-- **Scaling the datum in the complex domain.**  The real centre `(Ψ, h)` stays and the displacement
`Ψ'` becomes `Ψ' + ζ(Ψ + Ψ')`, so that the datum `Ψ + Ψ'` is multiplied by `1 + ζ`. -/
theorem InPsiTildeC.scale {ν δ ε : ℝ} {ζ : ℂ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h : Fin N → ℝ} {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hP : InPsiTildeC G ν δ ε Ψ h Ψ' (fun _ _ => 0)) (hζ : ‖ζ‖ ≤ 1 / 256) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 3) (hε1 : ε ≤ 1 / 16) :
    InPsiTildeC G ν (δ + 5 * ‖ζ‖) (ε + 2 * ‖ζ‖) Ψ h
      (fun x i => Ψ' x i + ζ * ((Ψ x i : ℂ) + Ψ' x i)) (fun _ _ => 0) := by
  have hρ := norm_nonneg ζ
  have hδ'0 : 0 < δ + 5 * ‖ζ‖ := by positivity
  have hPm := hP.toInPsiTilde.mono_delta hδ0.le (by linarith : δ ≤ δ + 5 * ‖ζ‖)
  have hΨvn : ∀ x ∈ dataSites G, vn (fun i => (Ψ x i : ℂ)) ≤ 2 := by
    intro x hx
    rw [vn_ofReal]
    have h2 := hP.r2 x hx
    have hsq : rn (Ψ x) ^ 2 = ∑ i, Ψ x i ^ 2 := by
      unfold rn; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have hr0 : 0 ≤ rn (Ψ x) := Real.sqrt_nonneg _
    by_contra hc; push Not at hc
    have := abs_lt.mp h2
    nlinarith
  have hΨ'vn : ∀ x ∈ dataSites G, vn (Ψ' x) ≤ 1 / 2 := fun x hx => by
    have := hP.c2a x hx; linarith
  refine
    { hPm with
      eps_pos := by linarith [hP.eps_pos]
      layerConst' := ?_
      hLayerConst' := hP.hLayerConst'
      c1 := ?_
      c2a := ?_
      c2b := ?_
      c3a := ?_
      c3b := ?_ }
  · intro n hn1 hnk x hx x' hx'
    funext i
    simp only [hP.layerConst n hn1 hnk x hx x' hx', hP.layerConst' n hn1 hnk x hx x' hx']
  · intro x x' hxx
    have e : (fun i => (Ψ' x i + ζ * ((Ψ x i : ℂ) + Ψ' x i)) -
        (Ψ' x' i + ζ * ((Ψ x' i : ℂ) + Ψ' x' i))) =
        fun i => (Ψ' x i - Ψ' x' i) + ζ * (((Ψ x i - Ψ x' i : ℝ) : ℂ) + (Ψ' x i - Ψ' x' i)) := by
      funext i; push_cast; ring
    have e' : (Ψ' x - Ψ' x' : Fin N → ℂ) = fun i => Ψ' x i - Ψ' x' i := rfl
    have h1 := vn_aux (fun i => ((Ψ x i - Ψ x' i : ℝ) : ℂ)) (fun i => Ψ' x i - Ψ' x' i) ζ
    rw [vn_ofReal] at h1
    have a1 := hP.r1 x x' hxx
    have a2 := hP.c1 x x' hxx
    rw [e']  at a2
    have e2 : ((fun i => Ψ' x i + ζ * ((Ψ x i : ℂ) + Ψ' x i)) -
        (fun i => Ψ' x' i + ζ * ((Ψ x' i : ℂ) + Ψ' x' i))) = fun i => (Ψ' x i - Ψ' x' i) +
          ζ * (((Ψ x i - Ψ x' i : ℝ) : ℂ) + (Ψ' x i - Ψ' x' i)) := by
      funext i; simp only [Pi.sub_apply]; push_cast; ring
    rw [e2]
    nlinarith
  · intro x hx
    have h1 := vn_aux (fun i => (Ψ x i : ℂ)) (Ψ' x) ζ
    have a1 := hP.c2a x hx
    have a2 := hΨvn x hx
    have a3 := hΨ'vn x hx
    nlinarith
  · intro x hx
    have e : ∑ i, ((Ψ x i : ℂ) + (Ψ' x i + ζ * ((Ψ x i : ℂ) + Ψ' x i))) *
          ((Ψ x i : ℂ) + (Ψ' x i + ζ * ((Ψ x i : ℂ) + Ψ' x i))) -
        ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) =
        (1 + ζ) ^ 2 * (∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) -
          ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)) +
        (2 * ζ + ζ ^ 2) * ((∑ i, Ψ x i ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have a1 := hP.c2b x hx
    have a2 := abs_lt.mp (hP.r2 x hx)
    have hS : |∑ i, Ψ x i ^ 2| ≤ 4 / 3 := by
      rw [abs_le]; constructor <;> nlinarith
    have hz1 : ‖(1 + ζ) ^ 2‖ ≤ 1 + 3 * ‖ζ‖ := by
      rw [norm_pow]
      have : ‖1 + ζ‖ ≤ 1 + ‖ζ‖ := (norm_add_le _ _).trans (by simp)
      nlinarith [norm_nonneg (1 + ζ)]
    have hz : ‖(2 * ζ + ζ ^ 2 : ℂ)‖ ≤ 3 * ‖ζ‖ := by
      calc ‖(2 * ζ + ζ ^ 2 : ℂ)‖ ≤ ‖2 * ζ‖ + ‖ζ ^ 2‖ := norm_add_le _ _
        _ ≤ 3 * ‖ζ‖ := by
          rw [norm_mul, norm_pow]
          have : ‖(2 : ℂ)‖ = 2 := by simp
          rw [this]
          nlinarith
    have hn1 : ‖(1 + ζ) ^ 2 * (∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) -
          ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ))‖ < (1 + 3 * ‖ζ‖) * δ := by
      rw [norm_mul]
      have hpos : 0 < ‖(1 + ζ) ^ 2‖ := by
        rw [norm_pos_iff]; apply pow_ne_zero
        intro h0
        have : ‖ζ‖ = 1 := by
          have : ζ = -1 := by linear_combination h0
          rw [this]; simp
        linarith
      calc ‖(1 + ζ) ^ 2‖ * ‖∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) -
              ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ < ‖(1 + ζ) ^ 2‖ * δ :=
            mul_lt_mul_of_pos_left a1 hpos
        _ ≤ (1 + 3 * ‖ζ‖) * δ := mul_le_mul_of_nonneg_right hz1 hδ0.le
    have hn2 : ‖(2 * ζ + ζ ^ 2 : ℂ) * ((∑ i, Ψ x i ^ 2 : ℝ) : ℂ)‖ ≤ 3 * ‖ζ‖ * (4 / 3) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hz hS (abs_nonneg _) (by positivity)
    calc _ ≤ _ := norm_add_le _ _
      _ < δ + 5 * ‖ζ‖ := by nlinarith
  · intro x hx
    have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
    rw [h0, mul_zero]
    exact div_pos (pow_pos hδ'0 2) (by linarith [hP.eps_pos])
  · intro x hx
    simp only [mul_zero, Finset.sum_const_zero, norm_zero]
    positivity

/-- **The renormalized datum in the complex domain.**  If `D` has the witness `(Ψ, h, Ψ', 0)`
(`h' = 0`, the fixed external field), then a datum `Dc` with `Dc.Ψ = (1 + ζ) D.Ψ` and `Dc.h = D.h`
lies in `InDomainC G ν (δ + 5|ζ|) (ε + 2|ζ|)`. -/
theorem InDomainC.scale {ν δ ε : ℝ} {ζ : ℂ} {D Dc : BgData G N}
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hP : InPsiTildeC G ν δ ε Ψ h Ψ' (fun _ _ => 0))
    (hΨ0 : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ) + Ψ' x i)
    (hh0 : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ))
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Dc.Ψ x i = (1 + ζ) * D.Ψ x i)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, Dc.h x i = D.h x i) (hζ : ‖ζ‖ ≤ 1 / 256) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 3) (hε1 : ε ≤ 1 / 16) :
    InDomainC G ν (δ + 5 * ‖ζ‖) (ε + 2 * ‖ζ‖) Dc := by
  refine ⟨Ψ, h, _, fun _ _ => 0, hP.scale hζ hδ0 hδ1 hε1, fun x hx i => ?_, fun x hx i => ?_⟩
  · rw [hΨ x hx i, hΨ0 x hx i]; ring
  · rw [hh x hx i, hh0 x hx i]; simp

/-- **The renormalized datum of a real datum for complex `ζ` lies in the complex domain.** -/
theorem InDomainR.toScaledC {ν δ ε' : ℝ} {ζ : ℂ} {D Dc : BgData G N} (hD : InDomainR G ν δ D)
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Dc.Ψ x i = (1 + ζ) * D.Ψ x i)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, Dc.h x i = D.h x i) (hζ : ‖ζ‖ ≤ 1 / 256)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) (hε : 0 < ε') (hε2 : ε' ≤ 1 / 16) :
    InDomainC G ν (δ + 5 * ‖ζ‖) (ε' + 2 * ‖ζ‖) Dc := by
  obtain ⟨Ψ, h, hP, hΨ0, hh0⟩ := hD
  refine InDomainC.scale (Ψ := Ψ) (h := h) (Ψ' := fun _ _ => 0) (D := D) ?_ (fun x hx i => by simp [hΨ0 x hx i])
    hh0 hΨ hh hζ hδ0 hδ1 hε2
  exact
    { hP with
      eps_pos := hε
      layerConst' := fun _ _ _ _ _ _ _ => rfl
      hLayerConst' := fun _ _ _ _ _ _ _ => rfl
      c1 := fun x x' _ => by
        have e0 : ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x -
            (fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x') = 0 := by
          funext i; simp
        rw [e0, vn_zero]; exact hδ0
      c2a := fun x _ => by
        have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
        rw [h0]; linarith
      c2b := fun x _ => by simpa using hδ0
      c3a := fun x _ => by
        have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
        rw [h0, mul_zero]; positivity
      c3b := fun x _ => by
        simp only [mul_zero, Finset.sum_const_zero, norm_zero]; positivity }

end Balaban.Background
