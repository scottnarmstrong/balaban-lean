/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayData
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Analyticity and the domain inclusion of the lifts, with the room of the tube (blocker 5)

`lift_polydisc_facts`: under the numerical conditions of `hnear_lift` (those of
`cutoffInteraction_final_class_polydisc_local` at the radius `2 c ε_K`), the lifts `Λ_j` are analytic
on the polydisc of radius `c ε_K` and map it into the local chart of every term.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField

namespace Balaban.Green

variable {d N₀ : ℕ} [NeZero N₀] {d' : ℕ} {L : ℕ} [NeZero L] {N : ℕ}

/-- **The lifts are analytic on the polydisc and map it into the local charts.** -/
theorem lift_polydisc_facts {c α α₀ : ℝ} {N₁ m₁ kS : ℕ} [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N) {P : Consts}
    {Tm : Terms d' L N₁ m₁ (kS + 1) N ϱ} {K : ℕ} (hK : K ≤ kS) {hsep : ϱ ≤ minSep L (L ^ m₁)}
    (hgs : ∀ j (hjk : j ≤ kS + 1), 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
      Tm.gs j X = localB j hjk X hsep)
    (HB : BgHyp d' L (kS + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε₀ : ℝ}
    (hθ : XiCData S.G' S.a S.ν (kS + 1) 1 ε₀ S.D')
    (hN : 0 < N) (hc : 0 < c) (hα₀ : 0 < α₀) (hα0 : 0 ≤ α)
    (hroom : (2 * bgK1 d' L N + 2) * (xiC1 d' * (ε₀ + xiK2 d' L N *
      ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ epsSeq L α α₀ K)
    (hc0 : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) ≤
      bgC0 d' L N)
    (hc1 : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) ≤
      bgC1 d' L N)
    (hsmall : (4 * d' + 6) * ((2 * d' + 1) * epsSeq L α α₀ K) ≤ 1)
    (hth : xiC1 d' * epsSeq L α α₀ K ≤ thm73C1 d' L N)
    (hm1 : (N : ℝ) * (c * epsSeq L α α₀ K) ≤ 1)
    (hδ₂ : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * (c * epsSeq L α α₀ K)))) +
      5 * ((N : ℝ) * (c * epsSeq L α α₀ K)) ≤ bgC1 d' L N)
    (hstar : (N : ℝ) * (2 * (c * epsSeq L α α₀ K)) ≤ deltaStar d' L N)
    (hK1s : bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
      ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) ≤ deltaStar d' L N)
    (hsm : bgK1 d' L N * (xiC1 d' * (ε₀ + xiK2 d' L N *
      ((N : ℝ) * (2 * (c * epsSeq L α α₀ K))))) +
      cK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) < bgC0 d' L N) :
    (∀ j, AnalyticOnNhd ℂ (fun w : L1Torus d N₀ → ℂ =>
      composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q))))
      (polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K))) ∧
    (∀ w ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K),
      ∀ j, 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
      (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ).dom j (Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).1
        (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).2) := by
  have hεKpos : 0 < epsSeq L α α₀ K := epsSeq_pos' L hα₀ K
  have hRpos : 0 < c * epsSeq L α α₀ K := mul_pos hc hεKpos
  obtain ⟨εK, hεK⟩ : ∃ x, x = epsSeq L α α₀ K := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ x, x = c * epsSeq L α α₀ K := ⟨_, rfl⟩
  rw [← hR] at hRpos hm1 hδ₂ hstar hK1s hsm hroom hc0 hc1
  rw [← hR]
  rw [← hεK] at hεKpos hroom hsmall hth
  have hroomj : ∀ j, j ≤ K → εK ≤ epsSeq L α α₀ j := fun j hjK => by
    rw [hεK]; exact epsSeq_anti L α α₀ hα₀.le hα0 hjK
  obtain ⟨ε₁, hε₁⟩ : ∃ x, x = ε₀ + xiK2 d' L N * ((N : ℝ) * R) := ⟨_, rfl⟩
  obtain ⟨ε₂, hε₂⟩ : ∃ x, x = ε₀ + xiK2 d' L N * ((N : ℝ) * (2 * R)) := ⟨_, rfl⟩
  rw [← hε₂] at hroom hc0 hc1 hδ₂ hK1s hsm
  have hε₀ : 0 < ε₀ := by
    obtain ⟨_, _, _, _, ⟨_, h, _⟩, _⟩ := hθ
    exact h
  have hxk : 0 ≤ xiK2 d' L N := by
    unfold xiK2
    have := cK2_pos d' L N
    positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
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
  have hDw : ∀ {v : L1Torus d N₀ → ℂ}, v ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => R) →
      XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ (S.dataUC (fun q => v (e.symm q))) := by
    intro v hv
    rw [hε₁]
    exact polydisc_dataUC_xiCData S e HB ha₁ hθ (hmono ε₀ (hε₀₁.trans hε₁K)).1
      (hmono ε₀ (hε₀₁.trans hε₁K)).2 hRpos.le hm1 (by linarith) (by linarith) (by linarith)
      (by linarith) hv
  refine ⟨fun j => analyticOnNhd_composedPair S HB (isOpen_polydisc _ _)
    (ψ := fun (w : L1Torus d N₀ → ℂ) q => w (e.symm q))
    (fun q w _ => (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : L1Torus d N₀ => ℂ) (e.symm q)).analyticAt w)
    (fun w hw => xiCData_unionC (hDw hw)) j, ?_⟩
  intro w hw j hj1 hjK X hX
  have hjk : j ≤ kS := hjK.trans hK
  rw [hgs j (hjk.trans (Nat.le_succ kS)) hj1 hjK X hX]
  have hK2 : 0 ≤ 2 * bgK1 d' L N + 2 := by linarith
  have := composedPair_xiDom_localB_of_xiCData S HB ha₁ (hDw hw) (hmono ε₁ hε₁K).1
    (hmono ε₁ hε₁K).2 (hx₁.trans hc0) (hx₁.trans hc1)
    ((mul_le_mul_of_nonneg_left hx₁ hK2).trans (hroom.trans (hroomj j hjK))) hj1 hjk
    (X := X) (hsep := hsep)
  exact this

end Balaban.Green
