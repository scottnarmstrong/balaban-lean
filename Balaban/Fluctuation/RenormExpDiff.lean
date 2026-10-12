/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The old-term differences: Cauchy's estimate along the composed perturbation (FLUCTUATION §3.6)

FLUCTUATION.md v2.3 §3.6, (3.10), (3.11) and the proofs of (g), (h): the old terms enter through
`ℰ^{(j)}(ψ^{(j)}_{k+1} + δψ^{(j)}) - ℰ^{(j)}(ψ^{(j)}_{k+1})`, where (Lemma 3.5 (iii)) the composed
datum `ψ^{(j)}_{k+1} = composeField(𝔹_j, 𝔹_{k+1}; φ, ψ)` is perturbed to
`ψ^{(j)}_{k+1,u} = composeField(𝔹_j, 𝔹_{k+1}; φ + δφ, (1 + ζ) ψ)` with `(δφ, δα)` the solution map of
Lemma 3.5 (ii) (`IsRenSol`).  This file proves, for the actual objects:

* `composedRaw`, `composedRawU`: the composed and the perturbed composed raw data;
* `composedRawU_zero`: at `ξ = 0` the perturbation vanishes (`IsRenSol.eq_zero`, `ζ = 0`);
* `analyticAt_composedRawU`: the perturbed composed datum is analytic in `ξ`;
* `oldDiff_cauchy`: for any old term `E` analytic and bounded by `M` at the perturbed composed
  data of the polydisc `|ξ|_∞ < r` (the class domain together with the inclusion (R-S)/(Ξ3) of
  the source), `|E(ψ^{(j)}_u) - E(ψ^{(j)})| ≤ (2 M / r) |ξ|_∞` — Cauchy's estimate ("the
  `τ`-derivative is bounded by Cauchy on `|τ| = c_r/ε`"), which gives the factor `ε` of
  `C₅ E₀ ε` in (g) and of `C₆ ε` in (h) before the localization (the open fluctuation I-5 (V0) of
  `RenormExpInput.expOld`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix Metric

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Compose

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}

theorem an_blockMean (G' : GeneratingSet d L N₀ k ϱ') (n : ℕ) (w : Q → Torus d (N₀ * L ^ k) → ℂ)
    (hw : ∀ y, AnalyticAt ℂ (fun q => w q y) q) (x : Torus d (N₀ * L ^ k)) :
    AnalyticAt ℂ (fun q => blockMean G' n (w q) x) q := by
  unfold blockMean
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ => hw y)

/-- The composed field (6.2) is analytic in its arguments `(φ', Ψ')` (it is affine in them). -/
theorem an_composeField (G' : GeneratingSet d L N₀ k ϱ') (G : GeneratingSet d L N₀ k ϱ)
    (a : ℕ → ℝ) (φ : Q → G.Ω 1 × Fin N → ℂ) (Ψ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q)
    (hΨ : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) q) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun q => composeField G' G a (φ q) (Ψ q) x i) q := by
  have hs : ∀ y, AnalyticAt ℂ (fun q => svec G (φ q) y i) q := fun y => an_svec φ hφ y i
  unfold composeField
  by_cases h1 : x ∈ G'.Ω 1
  · simp only [h1, ↓reduceIte]
    exact (an_blockMean G' _ _ hs x).add
      (analyticAt_const.mul ((hΨ x i).sub (an_blockMean G _ _ hs x)))
  · by_cases h2 : x ∈ collar G'
    · simp only [h1, h2, ↓reduceIte]
      exact an_barField Ψ φ hΨ hφ x i
    · simp only [h1, h2, ↓reduceIte]
      exact analyticAt_const

variable (G' : GeneratingSet d L N₀ k ϱ') (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- The composed raw datum `ψ^{(j)} = (composeField(𝔹_j, 𝔹_{k+1}; φ, Ψ), h̃|_{Ω₁(𝔹_j)})` of
Lemma 3.5 (iii) (`(composeData _ a φ D).Ψ, .h` for the data `D`). -/
noncomputable def composedRaw (φ : G.Ω 1 × Fin N → ℂ) (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    RawData d L N₀ k N :=
  (fun x i => composeField G' G a φ Ψ x i, fun x i => by
    classical exact if x ∈ G'.Ω 1 then h x i else 0)

/-- The perturbed composed raw datum `ψ^{(j)}_{k+1,u}` at `(D, ξ)`:
`composeField(𝔹_j, 𝔹_{k+1}; φ + δφ, (1 + ζ) ψ)` with `(δφ, ·) = F((ψ, h), ξ)`. -/
noncomputable def composedRawU (ν εζ : ℝ)
    (F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (D : BgData G N) (ξ : Fin 3 → ℂ) : RawData d L N₀ k N :=
  composedRaw G' G a (bgFieldC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).1)
    (fun x i => (1 + renZeta εζ ξ) * D.Ψ x i) D.h

variable {G' G a}

theorem composedRaw_composeData (hP : Precedes G' G) (φ : G.Ω 1 × Fin N → ℂ) (D : BgData G N) :
    composedRaw G' G a φ D.Ψ D.h = ((composeData hP a φ D).Ψ, (composeData hP a φ D).h) := rfl

variable {ν εζ ε r B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}

/-- At `ξ = 0` the composed datum is not perturbed. -/
theorem composedRawU_zero (hF : IsRenSol G a ν εζ ε r B F) (hr : 0 < r) {D : BgData G N}
    (hD : XiCOne G a ν ε D) :
    composedRawU G' G a ν εζ F D 0 = composedRaw G' G a (bgFieldC G a ν (bgC0 d L N) D) D.Ψ D.h := by
  unfold composedRawU
  rw [hF.eq_zero hr hD]
  simp [renZeta]

/-- The perturbed composed datum is analytic in `ξ` on the polydisc. -/
theorem analyticAt_composedRawU (hF : IsRenSol G a ν εζ ε r B F) {D : BgData G N}
    (hD : XiCOne G a ν ε D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r) :
    AnalyticAt ℂ (fun ξ' => composedRawU G' G a ν εζ F D ξ') ξ := by
  have hFa : AnalyticAt ℂ (fun ξ' : Fin 3 → ℂ => F ((D.Ψ, D.h), ξ')) ξ :=
    (hF.analytic _ ⟨D, hD, rfl, hξ⟩).comp (analyticAt_const.prod analyticAt_id)
  have hφ : ∀ (y : G.Ω 1) (i : Fin N), AnalyticAt ℂ
      (fun ξ' : Fin 3 → ℂ => (bgFieldC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ')).1) (y, i)) ξ :=
    fun y i => analyticAt_const.add ((aa_eval' (y, i) _).comp ((aa_fst' _).comp hFa))
  have hz : AnalyticAt ℂ (fun ξ' : Fin 3 → ℂ => renZeta εζ ξ') ξ := by
    unfold renZeta; exact analyticAt_const.mul ((aa_eval' 0 ξ))
  have hΨ : ∀ (x : Torus d (N₀ * L ^ k)) (i : Fin N), AnalyticAt ℂ
      (fun ξ' : Fin 3 → ℂ => (1 + renZeta εζ ξ') * D.Ψ x i) ξ :=
    fun x i => (analyticAt_const.add hz).mul analyticAt_const
  unfold composedRawU composedRaw
  refine AnalyticAt.prod ?_ analyticAt_const
  exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i =>
    an_composeField G' G a _ _ hφ hΨ x i

/-- **Cauchy's estimate for an old-term difference** (FLUCTUATION.md §3.6, proofs of (g), (h)):
if the old term `E` is analytic and bounded by `M` at the perturbed composed data of the polydisc
`|ξ|_∞ < r`, then `|E(ψ^{(j)}_{k+1,u}) - E(ψ^{(j)}_{k+1})| ≤ (2 M / r) |ξ|_∞`. -/
theorem oldDiff_cauchy (hF : IsRenSol G a ν εζ ε r B F) {D : BgData G N}
    (hD : XiCOne G a ν ε D) {E : RawData d L N₀ k N → ℂ} {M : ℝ}
    (hE : ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → AnalyticAt ℂ E (composedRawU G' G a ν εζ F D ξ))
    (hEM : ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → ‖E (composedRawU G' G a ν εζ F D ξ)‖ ≤ M)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r) :
    ‖E (composedRawU G' G a ν εζ F D ξ) -
        E (composedRaw G' G a (bgFieldC G a ν (bgC0 d L N) D) D.Ψ D.h)‖ ≤ 2 * M / r * ‖ξ‖ := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg ξ) hξ
  have hd : DifferentiableOn ℂ (fun ξ' => E (composedRawU G' G a ν εζ F D ξ')) (ball 0 r) :=
    fun ξ' hξ' => ((hE ξ' (mem_ball_zero_iff.1 hξ')).comp
      (analyticAt_composedRawU hF hD (mem_ball_zero_iff.1 hξ'))).differentiableAt
        |>.differentiableWithinAt
  have h := norm_sub_le_two_mul_of_ball hd (fun ξ' hξ' => hEM ξ' (mem_ball_zero_iff.1 hξ'))
    (mem_ball_zero_iff.2 hξ)
  rwa [composedRawU_zero hF hr hD] at h

end Compose

end Balaban.Fluctuation
