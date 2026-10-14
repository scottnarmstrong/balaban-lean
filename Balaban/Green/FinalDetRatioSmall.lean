/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalDetRatio
public import Balaban.Green.FinalAmplitude
public import Balaban.Localization.ParameterAnalytic

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized determinant-ratio coefficients are proportional to the size of the perturbation (W805)

If `1 - K_E(s, t)` is the perturbed tagged defect of `Green/FinalDetRatio.lean` with
`E` of size `η ≤ η₀` (`η₀` any size for which the smallness condition holds), then
`‖coef ellE C - coef ell0 C‖ ≤ (η / η₀) · 2 |C| (8M + 1)^d / (e^κ - 1)^{|C|}`.

Proof: an extra complex coordinate `σ` scales the perturbation, `E_σ = (η₀ / (η e^κ)) σ E`, so that
the smallness condition holds for `|σ| ≤ e^κ`.  The logarithm of the determinant is analytic in
`(σ, s)` jointly (`exists_analytic_log_det_one_sub` with the parameter index enlarged by one
coordinate); by uniqueness of logarithms its slices are the given logarithms.  The coefficient
`ψ(σ) = coef (ell (σ, ·)) C` is analytic in `σ` (`analyticOnNhd_coef`), bounded by the landed
volume-uniform bound, and `ψ(σ) - ψ(0)` vanishes at `σ = 0`; the Schwarz lemma gives the factor
`|σ| / e^κ = η / η₀`.
-/

@[expose] public section

namespace Balaban.Green

section Generic

open Balaban.Localization Balaban.Analysis

variable {d N₀ M : ℕ} [NeZero N₀]

local notation "𝐓[" a ", " s "]" => taggedMat Finset.univ (macTags d N₀ M) a s

/-- Composition of an analytic `ell` on the polydisc of the enlarged parameter space with the
embedding `(σ, s) ↦ (σ, s restricted to C)`. -/
theorem analyticAt_ell_embed {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ' : ℝ}
    {ell : (Option ι → ℂ) → ℂ} (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (C : Finset ι)
    (x : ℂ × (ι → ℂ))
    (hx : (fun o : Option ι => o.elim x.1 (fun i => if i ∈ C then x.2 i else 0)) ∈
      Metric.ball (0 : Option ι → ℂ) ρ') :
    AnalyticAt ℂ (fun y : ℂ × (ι → ℂ) =>
      ell (fun o : Option ι => o.elim y.1 (fun i => if i ∈ C then y.2 i else 0))) x := by
  let T : (ℂ × (ι → ℂ)) →L[ℂ] (Option ι → ℂ) :=
    ContinuousLinearMap.pi fun o => match o with
      | none => ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)
      | some i => if i ∈ C then (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).comp
          (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)) else 0
  have hT : ∀ y, T y = fun o : Option ι => o.elim y.1 (fun i => if i ∈ C then y.2 i else 0) := by
    intro y; funext o; cases o with
    | none => rfl
    | some i => by_cases hi : i ∈ C <;> simp [T, hi]
  have := (hell (T x) (by rw [hT]; exact hx)).comp (T.analyticAt x)
  simpa [Function.comp_def, hT] using this

/-- **Coefficient difference along a one-parameter family of defects.**  Let `a σ` be a family of
entry families depending analytically on a complex parameter `σ` (jointly analytic with the cut
parameters), with row sums at most `1/2` and `1 - K` invertible for `|σ| ≤ e^κ`, `‖s p‖ ≤ e^κ`.
For analytic logarithms `ell0` of `det (1 - K(a 0, s))` and `ell1` of `det (1 - K(a σ1, s))` on
polydiscs past `e^κ`, vanishing at `0`, and `|σ1| ≤ e^κ`:
`‖coef ell1 C - coef ell0 C‖ ≤ 2 |C| (8M+1)^d / (e^κ-1)^{|C|} · (|σ1| / e^κ)`. -/
theorem tm_coef_sub_le_of_family (hM : 0 < M) (hd : 0 < d) {κ : ℝ} (hκ : 0 < κ)
    (a : ℂ → MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    (han : ∀ x y (p0 : Option (MacIdx d N₀ M) → ℂ),
      AnalyticAt ℂ (fun p : Option (MacIdx d N₀ M) → ℂ =>
        𝐓[a (p none), fun i => p (some i)] x y) p0)
    (hKU : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s : MacIdx d N₀ M → ℂ,
      (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x, ∑ y, ‖𝐓[a σ, s] x y‖ ≤ 1 / 2)
    (hunit : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s : MacIdx d N₀ M → ℂ,
      (∀ p, ‖s p‖ ≤ Real.exp κ) → IsUnit (1 - 𝐓[a σ, s]))
    {σ1 : ℂ} (hσ1 : ‖σ1‖ ≤ Real.exp κ) {ρ0 ρ1 : ℝ} (hρ0 : Real.exp κ < ρ0)
    (hρ1 : Real.exp κ < ρ1) {ell0 ell1 : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell0 : AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ0))
    (hell1 : AnalyticOnNhd ℂ ell1 (Metric.ball 0 ρ1)) (h00 : ell0 0 = 0) (h10 : ell1 0 = 0)
    (hdet0 : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ0,
      (1 - 𝐓[a 0, s]).det = Complex.exp (ell0 s))
    (hdet1 : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ1,
      (1 - 𝐓[a σ1, s]).det = Complex.exp (ell1 s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ell1 C - coef ell0 C‖ ≤
      2 * ((C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card) * (‖σ1‖ / Real.exp κ) := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  obtain ⟨ρ', hρ', ell, hellA, hdet, hell0'⟩ := exists_analytic_log_det_one_sub
    (Pc := Option (MacIdx d N₀ M))
    (fun p => 𝐓[a (p none), fun i => p (some i)]) han (tm_zero hM hd _) hR0.le
    (fun p hp => hunit (p none) ((norm_le_pi_norm p none).trans hp) _
      (fun i => (norm_le_pi_norm p (some i)).trans hp))
  have hρ'0 : 0 < ρ' := by linarith
  set e : ℂ → (MacIdx d N₀ M → ℂ) → (Option (MacIdx d N₀ M) → ℂ) :=
    fun σ s o => o.elim σ s with he
  have hmemB : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s : MacIdx d N₀ M → ℂ, ‖s‖ ≤ Real.exp κ →
      e σ s ∈ Metric.ball (0 : Option (MacIdx d N₀ M) → ℂ) ρ' := by
    intro σ hσ s hs
    rw [mem_ball_zero_iff]
    refine (pi_norm_lt_iff hρ'0).2 fun o => ?_
    cases o with
    | none => exact lt_of_le_of_lt hσ hρ'
    | some i => exact lt_of_le_of_lt ((norm_le_pi_norm s i).trans hs) hρ'
  have hmemA : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s : MacIdx d N₀ M → ℂ, ‖s‖ < ρ' →
      e σ s ∈ Metric.ball (0 : Option (MacIdx d N₀ M) → ℂ) ρ' := by
    intro σ hσ s hs
    rw [mem_ball_zero_iff]
    refine (pi_norm_lt_iff hρ'0).2 fun o => ?_
    cases o with
    | none => exact lt_of_le_of_lt hσ hρ'
    | some i => exact lt_of_le_of_lt (norm_le_pi_norm s i) hs
  have he0 : e 0 0 = 0 := by funext o; cases o <;> rfl
  -- slices vanish at `s = 0`
  have hslice0 : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ell (e σ 0) = 0 := by
    have hcont : Continuous fun σ : ℂ => e σ 0 := by
      refine continuous_pi fun o => ?_
      cases o with
      | none => exact continuous_id
      | some i => exact continuous_const
    have := eq_of_exp_eq_of_continuousOn (S := Metric.closedBall (0 : ℂ) (Real.exp κ))
      (convex_closedBall _ _).isPreconnected (x₀ := 0) (Metric.mem_closedBall_self hR0.le)
      (f := fun σ : ℂ => ell (e σ 0)) (g := fun _ => 0)
      (hellA.continuousOn.comp hcont.continuousOn fun σ hσ =>
        hmemB σ (mem_closedBall_zero_iff.1 hσ) 0 (by simpa using hR0.le))
      continuousOn_const (by simp [he0, hell0'])
      (fun σ hσ => by
        have h1 := hdet (e σ 0) (hmemB σ (mem_closedBall_zero_iff.1 hσ) 0 (by simpa using hR0.le))
        have h2 : 𝐓[a σ, fun i => e σ 0 (some i)] = 0 := tm_zero hM hd (a σ)
        have h3 : (1 - 𝐓[a (e σ 0 none), fun i => e σ 0 (some i)]).det = 1 := by
          show (1 - 𝐓[a σ, fun i => e σ 0 (some i)]).det = 1
          rw [h2]; simp
        rw [← h1, h3]; simp)
    exact fun σ hσ => this σ (mem_closedBall_zero_iff.2 hσ)
  have hdets : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
      (1 - 𝐓[a σ, s]).det = Complex.exp (ell (e σ s)) := fun σ hσ s hs =>
    hdet (e σ s) (hmemA σ hσ s (mem_ball_zero_iff.1 hs))
  have hslan : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ →
      AnalyticOnNhd ℂ (fun s => ell (e σ s)) (Metric.ball 0 ρ') := by
    intro σ hσ s hs
    have h1 := analyticAt_ell_embed hellA Finset.univ (σ, s)
      (by simpa using hmemA σ hσ s (mem_ball_zero_iff.1 hs))
    have h2 := h1.comp (f := fun s' : MacIdx d N₀ M → ℂ => (σ, s'))
      ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))
    simpa [Function.comp_def, he] using h2
  set B : ℝ := C.card * (8 * M + 1) ^ d with hBdef
  have hsup : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s ∈ supportedOn C, ‖s‖ ≤ Real.exp κ →
      ‖ell (e σ s)‖ ≤ B := by
    intro σ hσ s hs hsn
    have := tm_norm_le_of_supported hM hd (a σ) (κ := κ) (q := 1 / 2) (by norm_num) (by norm_num)
      (hKU σ hσ) hρ' (hslan σ hσ) (by simpa [he0] using hslice0 σ hσ)
      (hdets σ hσ) C hs hsn
    have e1 : ((1 : ℝ) / 2) / (1 - 1 / 2) = 1 := by norm_num
    rw [e1, mul_one] at this
    exact this
  set Φ : ℂ × (MacIdx d N₀ M → ℂ) → ℂ := fun x =>
    ell (fun o : Option (MacIdx d N₀ M) => o.elim x.1 (fun i => if i ∈ C then x.2 i else 0))
    with hΦdef
  have hprojn : ∀ s : MacIdx d N₀ M → ℂ, (∀ i, ‖s i‖ < Real.exp κ) →
      ‖(fun i => if i ∈ C then s i else 0 : MacIdx d N₀ M → ℂ)‖ ≤ Real.exp κ := by
    intro s hs
    refine (pi_norm_le_iff_of_nonneg hR0.le).2 fun p => ?_
    by_cases hp : p ∈ C
    · simpa [hp] using (hs p).le
    · simpa [hp] using hR0.le
  have hΦan : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ)
      (fun _ => Real.exp κ), AnalyticAt ℂ Φ (σ, s) := by
    intro σ hσ s hs
    refine analyticAt_ell_embed hellA C (σ, s) ?_
    exact hmemB σ hσ _ (hprojn s (fun i => by simpa using hs i))
  have hΦb : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ)
      (fun _ => Real.exp κ), ‖Φ (σ, s)‖ ≤ B := by
    intro σ hσ s hs
    exact hsup σ hσ _ (fun i hi => by simp [hi]) (hprojn s (fun i => by simpa using hs i))
  set ψ : ℂ → ℂ := fun σ => coef (fun s => Φ (σ, s)) C with hψdef
  have hψan : AnalyticOnNhd ℂ ψ (Metric.ball (0 : ℂ) (Real.exp κ)) :=
    analyticOnNhd_coef hR Metric.isOpen_ball
      (fun x hx => hΦan x.1 (mem_ball_zero_iff.1 hx.1).le x.2 hx.2)
      (fun x hx => hΦb x.1 (mem_ball_zero_iff.1 hx.1).le x.2 hx.2) C
  have hψb : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ‖ψ σ‖ ≤ B / (Real.exp κ - 1) ^ C.card := by
    intro σ hσ
    refine norm_coef_le hR (f := fun s => Φ (σ, s)) ?_ (hΦb σ hσ) C
    intro s hs
    exact (hΦan σ hσ s hs).comp (f := fun s' : MacIdx d N₀ M → ℂ => (σ, s'))
      ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))
  -- identification of the given logarithms with the slices
  have hid : ∀ (σ : ℂ), ‖σ‖ ≤ Real.exp κ → ∀ {ρ_ : ℝ}, Real.exp κ < ρ_ →
      ∀ {ellX : (MacIdx d N₀ M → ℂ) → ℂ}, AnalyticOnNhd ℂ ellX (Metric.ball 0 ρ_) →
      ellX 0 = 0 → (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ_,
        (1 - 𝐓[a σ, s]).det = Complex.exp (ellX s)) → coef ellX C = ψ σ := by
    intro σ hσ ρ_ hρ_ ellX hellX hX0 hdetX
    have hb1 : Metric.ball (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ_ :=
      Metric.ball_subset_ball hρ_.le
    have hb2 : Metric.ball (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
      Metric.ball_subset_ball hρ'.le
    have h1 : coef ellX C = coef (fun s => ell (e σ s)) C :=
      tm_coef_eq_of_agree (a := a σ) (a' := a σ) hR (fun _ _ _ _ => rfl)
        (hellX.continuousOn.mono hb1) ((hslan σ hσ).continuousOn.mono hb2) hX0
        (by simpa [he0] using hslice0 σ hσ) (fun s hs => hdetX s (hb1 hs))
        (fun s hs => hdets σ hσ s (hb2 hs))
    rw [h1]
    refine coef_congr fun w hw => ?_
    simp only [hΦdef, he]
    congr 1; funext o; cases o with
    | none => rfl
    | some i =>
      by_cases hi : i ∈ C
      · simp [hi]
      · simp [hi, hw i hi]
  rw [hid σ1 hσ1 hρ1 hell1 h10 hdet1, hid 0 (by simpa using hR0.le) hρ0 hell0 h00 hdet0]
  have h0B := hψb 0 (by simpa using hR0.le)
  have h1B := hψb σ1 hσ1
  have hBc : 0 ≤ B / (Real.exp κ - 1) ^ C.card :=
    (norm_nonneg _).trans h0B
  have hsum : ‖ψ σ1 - ψ 0‖ ≤ 2 * (B / (Real.exp κ - 1) ^ C.card) := by
    calc ‖ψ σ1 - ψ 0‖ ≤ ‖ψ σ1‖ + ‖ψ 0‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  rcases hσ1.lt_or_eq with hlt | heq
  · have hG := norm_le_of_vanishing_zero (ι := Unit) (R := 1) (T := Real.exp κ)
      (B := 2 * (B / (Real.exp κ - 1) ^ C.card))
      (fun t (_ : Unit → ℂ) => ψ t - ψ 0)
      (fun p hp => ((hψan p.1 hp.1).sub analyticAt_const).comp (f := fun q : ℂ × (Unit → ℂ) => q.1)
        analyticAt_fst)
      (fun _ => by simp)
      (fun t ht _ _ => by
        have h1 := hψb t (mem_ball_zero_iff.1 ht).le
        calc ‖ψ t - ψ 0‖ ≤ ‖ψ t‖ + ‖ψ 0‖ := norm_sub_le _ _
          _ ≤ _ := by linarith)
      hlt (s := fun _ => 0) (fun i => by simp)
    calc ‖ψ σ1 - ψ 0‖ ≤ _ := hG
      _ = _ := by ring
  · have : ‖σ1‖ / Real.exp κ = 1 := by rw [heq]; exact div_self hR0.ne'
    rw [this, mul_one]; exact hsum


end Generic

section Instance

open Balaban.Localization Balaban.Analysis

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- The smallness condition `hη` is monotone in `η`. -/
theorem smallness_mono (hd : 0 < d) {η η₀ : ℝ} (hη : η ≤ η₀) (κ : ℝ)
    (h₀ : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η₀ *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) :
    4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1 := by
  have hg : 0 < finalGap d L := finalGap_pos (Nat.pos_of_ne_zero (NeZero.ne L))
  have hb : 0 ≤ ballConst d (3 * pdEps d L / 4) :=
    ballConst_nonneg (by have := pdEps_pos (L := L) hd; positivity)
  refine le_trans ?_ h₀
  gcongr

/-- **The coefficient bound, perturbation of positive size.** -/
theorem norm_coef_sub_le_of_pos (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {rE η η₀ : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
    (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (hηpos : 0 < η) (hηη₀ : η ≤ η₀)
    (hη₀ : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η₀ *
      ballConst d (3 * pdEps d L / 4))) ≤ 1)
    {ρ0 ρE : ℝ} (hρ0 : Real.exp κ < ρ0) (hρE : Real.exp κ < ρE)
    {ell0 ellE : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell0 : AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ0))
    (hellE : AnalyticOnNhd ℂ ellE (Metric.ball 0 ρE)) (h00 : ell0 0 = 0) (hE0 : ellE 0 = 0)
    (hdet0 : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ0,
      (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s).det = Complex.exp (ell0 s))
    (hdetE : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρE,
      (1 - taggedMat Finset.univ (macTags d N₀ M)
        (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
            (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det =
        Complex.exp (ellE s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ellE C - coef ell0 C‖ ≤
      (η / η₀) * (2 * ((C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card)) := by
  have hη₀pos : 0 < η₀ := lt_of_lt_of_le hηpos hηη₀
  have hR0 : 0 < Real.exp κ := Real.exp_pos κ
  set m : ℝ := η₀ / (η * Real.exp κ) with hm
  have hmpos : 0 < m := by positivity
  set μ : ℂ → ℂ := fun σ => (m : ℂ) * σ with hμ
  set aF : ℂ → MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ := fun σ z =>
    boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
        (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
      (μ σ • E) * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t) with haF
  have hμn : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ → ‖μ σ‖ * η ≤ η₀ := by
    intro σ hσ
    have : ‖μ σ‖ = m * ‖σ‖ := by
      simp only [hμ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos]
    rw [this]
    calc m * ‖σ‖ * η ≤ m * Real.exp κ * η := by gcongr
      _ = η₀ := by rw [hm]; field_simp
  have hsmall : ∀ σ : ℂ, ‖σ‖ ≤ Real.exp κ →
      4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * (‖μ σ‖ * η) *
        ballConst d (3 * pdEps d L / 4))) ≤ 1 := fun σ hσ =>
    smallness_mono hd (hμn σ hσ) κ hη₀
  have hEσ : ∀ σ : ℂ, WSmall rE (‖μ σ‖ * η) (μ σ • E) := fun σ => hE.smul (μ σ)
  refine tm_coef_sub_le_of_family (d := d) (N₀ := N₀) (M := M) hM hd hκ aF ?_ ?_ ?_
    (σ1 := ((Real.exp κ * η / η₀ : ℝ) : ℂ)) ?_ hρ0 hρE hell0 hellE h00 hE0 ?_ ?_ C |>.trans ?_
  · -- joint analyticity
    intro x y p0
    simp only [taggedMat, Matrix.of_apply]
    refine Finset.analyticAt_fun_sum _ fun z _ => AnalyticAt.mul ?_ ?_
    · unfold tagMon
      exact Finset.analyticAt_fun_prod _ fun q _ =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (MacIdx d N₀ M) => ℂ)
          (some q)).analyticAt p0
    · have hp : AnalyticAt ℂ (fun p : Option (MacIdx d N₀ M) → ℂ => p none) p0 :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (MacIdx d N₀ M) => ℂ)
          none).analyticAt p0
      simp only [haF, hμ, Matrix.sub_apply, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul]
      exact analyticAt_const.sub ((analyticAt_const.mul hp).mul analyticAt_const)
  · intro σ hσ s hs x
    exact taggedKE_rowsum_le_half (E := μ σ • E) hd hk hv0 hv1 ha1 ha2 hmass (hEσ σ) hrE ht hM
      hκ.le hMB hMκ (hsmall σ hσ) hs x
  · intro σ hσ s hs
    exact (taggedKE_isUnit_inv_weighted (E := μ σ • E) hd hk hv0 hv1 ha1 ha2 hmass (hEσ σ) hrE ht
      hM hκ.le hMB hMκ (hsmall σ hσ) le_rfl (div_nonneg (pdEps_pos hd).le (by norm_num))
      (s := s) hs).1
  · -- the norm of `σ1`
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ hη₀pos]
    nlinarith [mul_le_mul_of_nonneg_left hηη₀ hR0.le]
  · have hz : aF 0 = fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
        (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t := by
      funext z; simp [haF, hμ]
    intro s hs
    rw [hz]
    exact hdet0 s hs
  · have hμ1 : μ ((Real.exp κ * η / η₀ : ℝ) : ℂ) = 1 := by
      simp only [hμ, hm]
      rw [← Complex.ofReal_mul]
      rw [Complex.ofReal_eq_one]
      field_simp
    have hz : aF ((Real.exp κ * η / η₀ : ℝ) : ℂ) = fun z => boxR (finalOp d L N₀ k v a)
        (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t) := by
      funext z; simp only [haF, hμ1, one_smul]
    intro s hs
    rw [hz]
    exact hdetE s hs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : Real.exp κ * η / η₀ / Real.exp κ = η / η₀ := by field_simp
    rw [this]; ring_nf; exact le_rfl

/-- **The coefficients of the determinant-ratio logarithm are proportional to the size of the
perturbation.**  Let `E` be `(rE, η)`-small, `0 ≤ η ≤ η₀`, where the smallness condition of
`exists_det_ratio_localized` holds with `η₀` in place of `η`.  For any analytic logarithms `ell0`
of `det (1 - K(s, t))` and `ellE` of `det (1 - K_E(s, t))` on polydiscs past `e^κ`, vanishing at
`0`:
`‖coef ellE C - coef ell0 C‖ ≤ (η / η₀) · 2 |C| (8M + 1)^d / (e^κ - 1)^{|C|}`. -/
theorem norm_coef_sub_le_of_WSmall (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {rE η η₀ : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
    (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (hη0 : 0 ≤ η) (hηη₀ : η ≤ η₀) (hη₀pos : 0 < η₀)
    (hη₀ : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η₀ *
      ballConst d (3 * pdEps d L / 4))) ≤ 1)
    {ρ0 ρE : ℝ} (hρ0 : Real.exp κ < ρ0) (hρE : Real.exp κ < ρE)
    {ell0 ellE : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell0 : AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ0))
    (hellE : AnalyticOnNhd ℂ ellE (Metric.ball 0 ρE)) (h00 : ell0 0 = 0) (hE0 : ellE 0 = 0)
    (hdet0 : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ0,
      (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s).det = Complex.exp (ell0 s))
    (hdetE : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρE,
      (1 - taggedMat Finset.univ (macTags d N₀ M)
        (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
            (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det =
        Complex.exp (ellE s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ellE C - coef ell0 C‖ ≤
      (η / η₀) * (2 * ((C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card)) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  set X : ℝ := 2 * ((C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card) with hX
  have hX0 : 0 ≤ X := by
    have : 0 < Real.exp κ - 1 := by linarith
    positivity
  have main : ∀ η' : ℝ, 0 < η' → η' ≤ η₀ → WSmall rE η' E →
      ‖coef ellE C - coef ell0 C‖ ≤ (η' / η₀) * X := fun η' h1 h2 h3 =>
    norm_coef_sub_le_of_pos hd hk hv0 hv1 ha1 ha2 hmass h3 hrE ht hM hκ hMB hMκ h1 h2 hη₀ hρ0 hρE
      hell0 hellE h00 hE0 hdet0 hdetE C
  rcases hη0.lt_or_eq with hpos | hzero
  · exact main η hpos hηη₀ hE
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hX1 : 0 < X + 1 := by linarith
    set η' : ℝ := min η₀ (ε * η₀ / (X + 1)) with hη'
    have hη'pos : 0 < η' := lt_min hη₀pos (by positivity)
    have h1 := main η' hη'pos (min_le_left _ _) (hE.mono (by rw [← hzero]; exact hη'pos.le))
    refine h1.trans ?_
    rw [← hzero, zero_div, zero_mul, zero_add]
    calc η' / η₀ * X ≤ (ε * η₀ / (X + 1)) / η₀ * X := by
          gcongr; exact min_le_right _ _
      _ = ε * (X / (X + 1)) := by field_simp
      _ ≤ ε := by
          have : X / (X + 1) ≤ 1 := by rw [div_le_one hX1]; linarith
          nlinarith

/-- **The localized determinant ratio, with the size of the perturbation** (E1, E2, W805).
The conclusion of `exists_det_ratio_localized` with the last bound improved to
`‖coef ellE C - coef ell0 C‖ ≤ (η / η₀) · 2 |C| (8M + 1)^d / (e^κ - 1)^{|C|}`, for `0 ≤ η ≤ η₀`
and `η₀` satisfying the smallness condition. -/
theorem exists_det_ratio_localized_eta (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {rE η η₀ : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
    (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (hη0 : 0 ≤ η) (hηη₀ : η ≤ η₀) (hη₀pos : 0 < η₀)
    (hη₀ : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η₀ *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) :
    ∃ ρ' : ℝ, Real.exp κ < ρ' ∧ ∃ ell0 ellE : (MacIdx d N₀ M → ℂ) → ℂ,
      AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ') ∧ AnalyticOnNhd ℂ ellE (Metric.ball 0 ρ') ∧
      ell0 0 = 0 ∧ ellE 0 = 0 ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s).det = Complex.exp (ell0 s)) ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det =
          Complex.exp (ellE s)) ∧
      (shiftMat (finalOp d L N₀ k v a + E) t).det = (shiftMat (finalOp d L N₀ k v a) t).det *
        ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ellE C - coef ell0 C) ∧
      (∀ C : Finset (MacIdx d N₀ M),
        (∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, E x y = 0) →
          coef ellE C = coef ell0 C) ∧
      (∀ C A : Finset (MacIdx d N₀ M), A ⊆ C → A.Nonempty → (C \ A).Nonempty →
        Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)) →
          coef ellE C = 0 ∧ coef ell0 C = 0) ∧
      (∀ C : Finset (MacIdx d N₀ M), ‖coef ellE C - coef ell0 C‖ ≤
        (η / η₀) * (2 * ((C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card))) := by
  obtain ⟨ρ', hρ', ell0, ellE, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
    exists_det_ratio_localized hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hMB hMκ
      (smallness_mono hd hηη₀ κ hη₀)
  exact ⟨ρ', hρ', ell0, ellE, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun C =>
    norm_coef_sub_le_of_WSmall hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hMB hMκ hη0 hηη₀ hη₀pos
      hη₀ hρ' hρ' h1 h2 h3 h4 h5 h6 C⟩

end Instance

end Balaban.Green
