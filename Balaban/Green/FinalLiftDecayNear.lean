/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayData
public import Balaban.Green.FinalLiftDecayLocal
public import Balaban.Green.FinalLiftDecayFar
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Near-locality of the lift (blocker 5): the hypothesis `hnear` of `norm_coef_cutoff_class_le_decay`

For `w, w'` in the polydisc agreeing on a set `S n j y X` of the unit lattice that contains the
`L^j`-blocks meeting `X` and the unit points `ω`-near to them (path distance `< n`), the lifts
`Λ_j w`, `Λ_j w'` of the class terms differ by
`‖ℰ(Λ_j w) - ℰ(Λ_j w')‖ ≤ E₀ e^{-κ d_j(X)} · 20 N e^{2dγ_w} K_w C_F e^{-γ_w n}`:
the far-data response of the composed datum (`composeField_response_le`) bounds the datum of the
lift on the blocks meeting `X`, and the Cauchy estimate in the local chart
(`norm_E_sub_le_of_local_diff`) turns it into a bound on the term.  The numerical conditions are
those of `cutoffInteraction_final_class_polydisc_local` at the radius `2 c ε_K` (room for the tube).
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField

namespace Balaban.Green

theorem epsSeq_pos' (L : ℕ) [NeZero L] {α α₀ : ℝ} (hα₀ : 0 < α₀) (j : ℕ) :
    0 < epsSeq L α α₀ j := by
  unfold epsSeq
  have := epsTail_pos j
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

variable {d' : ℕ} {L : ℕ} [NeZero L] {N : ℕ}

/-- **The variation of the term at the lifts, from the variation of the composed datum on the blocks
meeting `X`**: the numerical and typing hypotheses of the tube, and a bound `M` of the difference of
the composed data on the union of `L^j`-blocks meeting `X` (`hfar`). -/
theorem norm_E_lift_sub_le_of_far {N₁ m₁ kS : ℕ} [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d' L N₁ m₁ kS N ϱ) {P : Consts} {Tm : Terms d' L N₁ m₁ (kS + 1) N ϱ}
    {α α₀ : ℝ}
    (hT : SFTermClauses P
      (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ) Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ kS) {y : CTorus d' L N₁ m₁ (kS + 1)}
    {X : Set (CTorus d' L N₁ m₁ (kS + 1))} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {hsep : ϱ ≤ minSep L (L ^ m₁)}
    (hgs : Tm.gs j X = localB j (hjk.trans (Nat.le_succ kS)) X hsep)
    (HB : BgHyp d' L (kS + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε₁ ε₂ δ₃ : ℝ}
    (hδ₃0 : 0 < δ₃) (hδ₃1 : δ₃ ≤ 1) (hε₂e : ε₁ + xiK2 d' L N * δ₃ = ε₂)
    (hsm1 : (4 * d' + 6) * ((2 * d' + 1) * ε₁) ≤ 1) (hth1 : xiC1 d' * ε₁ ≤ thm73C1 d' L N)
    (hδ₂ : xiC1 d' * ε₁ + 5 * δ₃ ≤ bgC1 d' L N) (hstar : δ₃ ≤ deltaStar d' L N)
    (hK1s : bgK1 d' L N * (xiC1 d' * ε₁) ≤ deltaStar d' L N)
    (hsm : bgK1 d' L N * (xiC1 d' * ε₁) + cK2 d' L N * δ₃ < bgC0 d' L N)
    (hsmall2 : (4 * d' + 6) * ((2 * d' + 1) * ε₂) ≤ 1)
    (hc0 : xiC1 d' * ε₂ ≤ bgC0 d' L N) (hc1 : xiC1 d' * ε₂ ≤ bgC1 d' L N)
    (hεb : (2 * bgK1 d' L N + 2) * (xiC1 d' * ε₂) ≤ epsSeq L α α₀ j)
    (hc0₁ : xiC1 d' * ε₁ ≤ bgC0 d' L N) (hc1₁ : xiC1 d' * ε₁ ≤ bgC1 d' L N)
    (hεb₁ : (2 * bgK1 d' L N + 2) * (xiC1 d' * ε₁) ≤ epsSeq L α α₀ j)
    {Dw Dw' : BgData (stepG d' L N₁ m₁ kS ϱ) N}
    (hDw : XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ Dw)
    (hDw' : XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ Dw')
    (hh : ∀ x i, Dw'.h x i = Dw.h x i) {M : ℝ} (hNM : 0 < (N : ℝ) * M)
    (hfar : ∀ x : CTorus d' L N₁ m₁ (kS + 1),
      (∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
        jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) → ∀ i : Fin N,
      ‖(composedDataAtC S.a S.ν hjk (Nat.le_succ kS) Dw').Ψ x i -
        (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) Dw).Ψ x i‖ ≤ M) :
    ‖Tm.E j y X (composedPairAtC S.a S.ν (Nat.le_succ kS) j Dw).1
        (composedPairAtC S.a S.ν (Nat.le_succ kS) j Dw).2 -
      Tm.E j y X (composedPairAtC S.a S.ν (Nat.le_succ kS) j Dw').1
        (composedPairAtC S.a S.ν (Nat.le_succ kS) j Dw').2‖ ≤
      2 * (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)) * ((N * M) / δ₃) := by
  have hjk1 : j ≤ kS + 1 := hjk.trans (Nat.le_succ kS)
  have ep : ∀ D : BgData (stepG d' L N₁ m₁ kS ϱ) N, composedPairAtC S.a S.ν (Nat.le_succ kS) j D =
      ((composedDataAtC S.a S.ν hjk (Nat.le_succ kS) D).Ψ,
        (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) D).h) := by
    intro D
    simp only [composedPairAtC, hjk, ↓reduceDIte]
  have hdom : ∀ D : BgData (stepG d' L N₁ m₁ kS ϱ) N,
      XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ D →
      XiDom (localB j hjk1 X hsep) S.a S.ν j (epsSeq L α α₀ j)
        (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) D).Ψ
        (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) D).h := by
    intro D hD
    have := composedPair_xiDom_localB_of_xiCData S HB ha₁ hD hsm1 hth1 hc0₁ hc1₁ hεb₁ hj1 hjk
      (X := X) (hsep := hsep)
    rw [ep] at this
    exact this
  have hhC : ∀ x i, (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) Dw').h x i =
      (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) Dw).h x i := by
    intro x i
    simp only [composedDataAtC, composeData]
    rw [hh]
  rw [ep, ep, norm_sub_rev]
  exact norm_E_sub_le_of_local_diff hT hj1 hjk1 hX hy hgs HB hδ₃0 hδ₃1 hsm1 hδ₂ hstar hK1s hsm
    (by rw [hε₂e]; exact hsmall2) (by rw [hε₂e]; exact hc0) (by rw [hε₂e]; exact hc1)
    (by rw [hε₂e]; exact hεb) (xiCData_composedDataAtC S HB ha₁ hDw hsm1 hth1 hjk) (hdom Dw hDw)
    (hdom Dw' hDw') hhC (B := {x | ∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
      jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z}) (fun x x' hxx' => by
      constructor
      · rintro ⟨z, hz, h⟩; exact ⟨z, hz, hxx'.symm.trans h⟩
      · rintro ⟨z, hz, h⟩; exact ⟨z, hz, hxx'.trans h⟩)
    (fun x hx => ⟨x, hx, rfl⟩) hNM (fun x hx i => hfar x hx i)

variable {d N₀ : ℕ}

/-- **`hnear` for the lift** (see the module docstring): `Sset n j y X` is any set of the unit
lattice containing the points `q` with `(e q).1 = unitPt x` for a site `x` in a `L^j`-block meeting
`X`, or with a site `z` of such a block at path distance `< n` from a site `ω ∈ Ω₁` equal or adjacent
to `x`.  The constants `K_w, δ_w > 0` depend only on `(d', L, N)`. -/
theorem hnear_lift (hd3 : 3 ≤ d') (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {c α α₀ : ℝ} {N₁ m₁ kS : ℕ} [NeZero N₁] {ϱ : ℝ}
        (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N)
        {P : Consts} {Tm : Terms d' L N₁ m₁ (kS + 1) N ϱ}
        (_ : SFTermClauses P
          (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ) Tm)
        {K : ℕ} (_ : K ≤ kS) {hsep : ϱ ≤ minSep L (L ^ m₁)}
        (_ : ∀ j (hjk : j ≤ kS + 1), 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
          Tm.gs j X = localB j hjk X hsep)
        (_ : BgHyp d' L (kS + 1) ϱ S.a S.ν) (_ : 0 < S.a₁) {ε₀ : ℝ}
        (_ : XiCData S.G' S.a S.ν (kS + 1) 1 ε₀ S.D')
        (_ : Dec2.OpSetting (stepG d' L N₁ m₁ kS ϱ) S.a S.ν)
        (_ : 0 < N) (_ : 0 < c) (_ : 0 < α₀) (_ : 0 ≤ α)
        (_ : (2 * bgK1 d' L N + 2) * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ epsSeq L α α₀ K)
        (_ : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) ≤
          bgC0 d' L N)
        (_ : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) ≤
          bgC1 d' L N)
        (_ : (4 * d' + 6) * ((2 * d' + 1) * epsSeq L α α₀ K) ≤ 1)
        (_ : xiC1 d' * epsSeq L α α₀ K ≤ thm73C1 d' L N)
        (_ : (N : ℝ) * (c * epsSeq L α α₀ K) ≤ 1)
        (_ : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) +
          5 * ((N : ℝ) * (c * epsSeq L α α₀ K)) ≤ bgC1 d' L N)
        (_ : (N : ℝ) * (2 * (c * epsSeq L α α₀ K)) ≤ deltaStar d' L N)
        (_ : bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ deltaStar d' L N)
        (_ : bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) +
          cK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) < bgC0 d' L N)
        (_ : bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
          ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ δw)
        (_ : (N : ℝ) * (2 * (c * epsSeq L α α₀ K)) ≤ δw)
        (Sset : ℕ → ℕ → CTorus d' L N₁ m₁ (kS + 1) → Set (CTorus d' L N₁ m₁ (kS + 1)) →
          Set (L1Torus d N₀))
        (_ : ∀ (n j : ℕ) y X (q : L1Torus d N₀) (x : CTorus d' L N₁ m₁ (kS + 1)),
          (e q).1 = unitPt S.hG' x →
          ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
              jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
            ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
                jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
              ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
                (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ)) →
          q ∈ Sset n j y X),
        ∀ (n j : ℕ) y X, 1 ≤ j → j ≤ K → IsPolyDom P.m₀ j X → y ∈ X →
          ∀ w ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K),
          ∀ w' ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K),
            (∀ x ∈ Sset n j y X, w x = w' x) →
          ‖Tm.E j y X
              (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).1
              (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).2 -
            Tm.E j y X
              (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w' (e.symm q)))).1
              (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w' (e.symm q)))).2‖ ≤
            P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) *
              (20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) * (Kw * cF d' L) *
                Real.exp (-(gammaW d' * n))) := by
  obtain ⟨Kw, δw, hK, hδw, hfar⟩ := lift_far_bound (d' := d') (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro c α α₀ N₁ m₁ kS _ ϱ S e P Tm hT K hKk hsep hgs HB ha₁ ε₀ hθ hOp hN hc hα₀ hα0 hroom hc0
    hc1 hsmall hth hm1 hδ₂ hstar hK1s hsm hKw hδw' Sset hS n j y X hj1 hjK hX hy w hw w' hw' hag
  have hjk : j ≤ kS := hjK.trans hKk
  have hεKpos : 0 < epsSeq L α α₀ K := epsSeq_pos' L hα₀ K
  have hεj : epsSeq L α α₀ K ≤ epsSeq L α α₀ j := epsSeq_anti L α α₀ hα₀.le hα0 hjK
  have hRpos : 0 < c * epsSeq L α α₀ K := mul_pos hc hεKpos
  obtain ⟨εK, hεK⟩ : ∃ x, x = epsSeq L α α₀ K := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ x, x = c * epsSeq L α α₀ K := ⟨_, rfl⟩
  rw [← hR] at hRpos hw hw' hm1 hδ₂ hstar hK1s hsm hKw hδw' hroom hc0 hc1
  rw [← hεK] at hεKpos hεj hroom hsmall hth
  obtain ⟨ε₁, hε₁⟩ : ∃ x, x = ε₀ + xiK2 d' L N * ((N : ℝ) * R) := ⟨_, rfl⟩
  obtain ⟨ε₂, hε₂⟩ : ∃ x, x = ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * R)) := ⟨_, rfl⟩
  rw [← hε₂] at hroom hc0 hc1 hδ₂ hK1s hsm hKw
  have hε₀ : 0 < ε₀ := by
    obtain ⟨_, _, _, _, ⟨_, h, _⟩, _⟩ := hθ
    exact h
  have hxk : 0 ≤ xiK2 d' L N := by
    unfold xiK2
    have := cK2_pos d' L N
    positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hc1' : 0 ≤ xiC1 d' := by have := one_le_xiC1 d'; linarith
  have hKloc : 1 ≤ (2 * bgK1 d' L N + 2) * xiC1 d' := by
    have h1 := bgK1_pos d' L N
    have h2 := one_le_xiC1 d'
    have : 1 * 1 ≤ (2 * bgK1 d' L N + 2) * xiC1 d' :=
      mul_le_mul (by linarith) h2 zero_le_one (by linarith)
    linarith
  have hNR : (N : ℝ) * R ≤ (N : ℝ) * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) hN0
  have hNR0 : 0 ≤ (N : ℝ) * R := mul_nonneg hN0 hRpos.le
  have hNR20 : 0 ≤ (N : ℝ) * (2 * R) := mul_nonneg hN0 (by linarith)
  have hxN : 0 ≤ xiK2 d' L N * ((N : ℝ) * R) := mul_nonneg hxk hNR0
  have hxN2 : 0 ≤ xiK2 d' L N * ((N : ℝ) * (2 * R)) := mul_nonneg hxk hNR20
  have hε₁₂ : ε₁ ≤ ε₂ := by
    rw [hε₁, hε₂]
    have := mul_le_mul_of_nonneg_left hNR hxk
    linarith
  have hε₀₁ : ε₀ ≤ ε₁ := by rw [hε₁]; linarith
  have hε₂e : ε₁ + xiK2 d' L N * ((N : ℝ) * R) = ε₂ := by rw [hε₁, hε₂]; ring
  have hε₂K : ε₂ ≤ εK := by
    refine le_trans ?_ hroom
    have h0 : 0 ≤ ε₂ := by rw [hε₂]; linarith
    calc ε₂ = 1 * ε₂ := (one_mul _).symm
      _ ≤ ((2 * bgK1 d' L N + 2) * xiC1 d') * ε₂ := mul_le_mul_of_nonneg_right hKloc h0
      _ = _ := by ring
  have hmono : ∀ ε, ε ≤ εK → (4 * d' + 6) * ((2 * d' + 1) * ε) ≤ 1 ∧
      xiC1 d' * ε ≤ thm73C1 d' L N := fun ε h =>
    ⟨le_trans (by gcongr) hsmall, le_trans (mul_le_mul_of_nonneg_left h hc1') hth⟩
  have hε₁K : ε₁ ≤ εK := hε₁₂.trans hε₂K
  have hx₀ : xiC1 d' * ε₀ ≤ xiC1 d' * ε₂ := mul_le_mul_of_nonneg_left (hε₀₁.trans hε₁₂) hc1'
  have hx₁ : xiC1 d' * ε₁ ≤ xiC1 d' * ε₂ := mul_le_mul_of_nonneg_left hε₁₂ hc1'
  have hK1' : 0 ≤ bgK1 d' L N := (bgK1_pos d' L N).le
  have hk₀ := mul_le_mul_of_nonneg_left hx₀ hK1'
  have hk₁ := mul_le_mul_of_nonneg_left hx₁ hK1'
  have hε₁pos : 0 < ε₁ := by rw [hε₁]; linarith
  have hDw : ∀ {v : L1Torus d N₀ → ℂ}, v ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => R) →
      XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ (S.dataUC (fun q => v (e.symm q))) := by
    intro v hv
    rw [hε₁]
    exact polydisc_dataUC_xiCData S e HB ha₁ hθ (hmono ε₀ (hε₀₁.trans hε₁K)).1
      (hmono ε₀ (hε₀₁.trans hε₁K)).2 hRpos.le hm1 (by linarith) (by linarith) (by linarith)
      (by linarith) hv
  have hdiff : ∀ x (i : Fin N), ‖(S.dataUC (fun q => w' (e.symm q))).Ψ x i -
      (S.dataUC (fun q => w (e.symm q))).Ψ x i‖ ≤ 2 * R := by
    intro x i
    rw [S.dataUC_Ψ, S.dataUC_Ψ]
    have h1 := hw' (e.symm (unitPt S.hG' x, i))
    have h2 := hw (e.symm (unitPt S.hG' x, i))
    simp only [Equiv.apply_symm_apply] at h1 h2
    calc _ ≤ ‖w' (e.symm (unitPt S.hG' x, i)) - S.psi0C (unitPt S.hG' x, i)‖ +
          ‖w (e.symm (unitPt S.hG' x, i)) - S.psi0C (unitPt S.hG' x, i)‖ := by
          rw [← norm_neg (w (e.symm (unitPt S.hG' x, i)) - _)]
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ ≤ 2 * R := by linarith
  have hfar' := hfar S HB hOp hjk hε₁pos (by positivity : (0 : ℝ) ≤ 2 * R)
    (hmono ε₁ hε₁K).1 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hδw'
    (hDw hw) (hDw hw') (fun x i => by rw [S.dataUC_h, S.dataUC_h]) hdiff
    (Bs := {x | ∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
      jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z}) n (fun x i hx => by
        rw [S.dataUC_Ψ, S.dataUC_Ψ]
        exact (hag _ (hS n j y X (e.symm (unitPt S.hG' x, i)) x (by simp) hx)).symm)
  have hcF := cF_pos d' L
  have hM : 0 < 5 * Real.exp (gammaW d' * (2 * d')) * (Kw * (cF d' L * ((N : ℝ) * (2 * R)))) *
      Real.exp (-(gammaW d' * n)) := by positivity
  have hNM := mul_pos hNpos hM
  have hK2 : 0 ≤ 2 * bgK1 d' L N + 2 := by linarith
  have hroomj : (2 * bgK1 d' L N + 2) * (xiC1 d' * ε₂) ≤ epsSeq L α α₀ j := hroom.trans hεj
  have key := norm_E_lift_sub_le_of_far S hT hj1 hjk hX hy
    (hgs j (hjk.trans (Nat.le_succ kS)) hj1 hjK X hX) HB ha₁ (ε₁ := ε₁) (ε₂ := ε₂)
    (δ₃ := (N : ℝ) * R) (mul_pos hNpos hRpos) hm1 hε₂e (hmono ε₁ hε₁K).1 (hmono ε₁ hε₁K).2
    (by linarith) (by linarith) (by linarith) (by linarith) (hmono ε₂ hε₂K).1 hc0 hc1 hroomj
    (hx₁.trans hc0) (hx₁.trans hc1)
    ((mul_le_mul_of_nonneg_left hx₁ hK2).trans hroomj) (hDw hw) (hDw hw')
    (fun x i => by rw [S.dataUC_h, S.dataUC_h]) hNM (fun x hx i => hfar' x hx i)
  refine key.trans (le_of_eq ?_)
  have hR0 : R ≠ 0 := hRpos.ne'
  have hN0' : (N : ℝ) ≠ 0 := hNpos.ne'
  field_simp
  ring

end Balaban.Green
