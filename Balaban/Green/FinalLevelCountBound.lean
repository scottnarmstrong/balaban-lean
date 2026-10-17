/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLevelCount
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The volume-uniform coefficient bound of the last integral with the counting inputs discharged

`norm_coef_cutoff_class_le_levels`: `norm_coef_cutoff_class_le_lift` with the read sets `Sset`
(`readSet_hS`), the finite site sets `W n`, the reach `hreach` and the placement `hW` discharged by
`FinalLevelCount.lean`, the count `|W n| ≤ Cw (n+1)^{d'}` fed into `sum_poly_decay_le`.  The bound
is `γ(box) e^{-(κ-1)|C|} K A E₀ Cw (1 + A' ∑_m e^{-γ_w m} (m+2)^{d'})` with
`Cw = |C| (8M+1)^d (L^{kS})^{d'} (2 L^{kS+1} + 2 d' L^{kS+1} + 3)^{d'}`, independent of the torus
sizes `N₀`, `N₁`, `m₁` and of the number of levels.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField Balaban.LargeField.ActionConv

namespace Balaban.Green

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ} {d' N : ℕ}

open Classical in
/-- **The volume-uniform coefficient bound with the counting inputs discharged** (see the module docstring). -/
theorem norm_coef_cutoff_class_le_levels (hd3 : 3 ≤ d') (hL3 : 3 ≤ L) :
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
        (_ : 0 < d) (_ : 1 ≤ k) (_ : 0 ≤ v) (_ : v ≤ 1) (_ : 1 / 2 ≤ a) (_ : a ≤ 2)
        (_ : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (_ : 0 < M) {κ : ℝ} (_ : 1 ≤ κ)
        (_ : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (_ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
        {A₁ β₀ : ℝ} {p : ℕ} {γ : Measure (L1Torus d N₀ → ℝ)}
        (_ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)} < ⊤)
        (_ : 1 ≤ p) (_ : 0 ≤ A₁) (_ : α ≤ ((d' : ℝ) - 2) * (1 / 4)) (_ : 1 < β₀)
        (_ : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * A₁ * (4 * (p : ℝ)) ^ p < c * α₀ * β₀ ^ (1 / 4 : ℝ))
        (_ : 0 ≤ P.E₀) (_ : L ^ P.m₀ ∣ N₁) (_ : aEnt d' L + 2 ≤ P.κ)
        (C : Finset (MacIdx d N₀ M)) (_ : C.Nonempty),
        ‖coef (fun s : MacIdx d N₀ M → ℂ =>
          ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)},
            (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
                Edens P.m₀ Tm j
                  (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).1
                  (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).2)
              (fun x => (fun q => S.psi0C (e q)) x +
                (((betaK d' L K β₀) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
          (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)}).toReal *
            Real.exp (-(κ - 1) * C.card) *
           ((K : ℝ) * ((L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1)) * P.E₀ *
              (((C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d' *
                (2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) ^ d' : ℕ) : ℝ) *
                (1 + 20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) * (Kw * cF d' L) *
                  ∑' m : ℕ, Real.exp (-(gammaW d' * m)) * ((m : ℝ) + 2) ^ d'))) := by
  obtain ⟨Kw, δw, hK, hδw, H⟩ := norm_coef_cutoff_class_le_lift (d := d) (N₀ := N₀) (M := M)
    (L := L) (k := k) (v := v) (a := a) (d' := d') (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro c α α₀ N₁ m₁ kS _ ϱ S e P Tm hT K hKk hsep hgs HB ha₁ ε₀ hθ hOp hN hc hα₀ hα0 hroom hc0
    hc1 hsmall hth hm1 hδ₂ hstar hK1s hsm hKw hδw' hd hk hv0 hv1 ha1 ha2 hmass hM κ hκ hMB
    hMκ A₁ β₀ p γ hγ hp hA hα hβ₀ hsize hE₀ hNd hκP C hC
  obtain ⟨Sset, hSdef⟩ : ∃ Sset : ℕ → ℕ → CTorus d' L N₁ m₁ (kS + 1) →
      Set (CTorus d' L N₁ m₁ (kS + 1)) → Set (L1Torus d N₀),
      ∀ n j (y : CTorus d' L N₁ m₁ (kS + 1)) X (q : L1Torus d N₀), q ∈ Sset n j y X ↔
        ∃ x : CTorus d' L N₁ m₁ (kS + 1), (e q).1 = unitPt S.hG' x ∧
        ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
            jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
          ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
              jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
            ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
              (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ)) :=
    ⟨fun n j y X => {q | ∃ x : CTorus d' L N₁ m₁ (kS + 1), (e q).1 = unitPt S.hG' x ∧
        ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
            jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
          ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
              jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
            ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
              (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ))}, fun _ _ _ _ _ => Iff.rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ → Finset (CTorus d' L N₁ m₁ (kS + 1)),
      ∀ n w, w ∈ W n ↔ ∃ x : CTorus d' L N₁ m₁ (kS + 1),
        (∃ q ∈ macRegion d N₀ M C, (e q).1 = unitPt S.hG' x) ∧
          Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) x w ≤
            ((L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1 : ℕ) : ℝ) :=
    ⟨fun n => Finset.univ.filter fun w => ∃ x : CTorus d' L N₁ m₁ (kS + 1),
        (∃ q ∈ macRegion d N₀ M C, (e q).1 = unitPt S.hG' x) ∧
          Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) x w ≤
            ((L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1 : ℕ) : ℝ), fun n w => by simp⟩
  have hSsub := fun n j (y : CTorus d' L N₁ m₁ (kS + 1)) X (q : L1Torus d N₀) hq =>
    (hSdef n j y X q).1 hq
  have hmain := H S e hT hKk hgs HB ha₁ hθ hOp hN hc hα₀ hα0 hroom hc0 hc1 hsmall hth hm1 hδ₂ hstar
    hK1s hsm hKw hδw' Sset (fun n j y X q x hx hc' => (hSdef n j y X q).2 ⟨x, hx, hc'⟩) hd hk hv0
    hv1 ha1 ha2 hmass hM hκ hMB hMκ hγ hp hA hα hβ₀ hsize hE₀ hNd hκP C hC
    (d' * ((N₁ * L ^ m₁) * L ^ (kS + 1)) + 1) W
    (fun j _ _ y X _ hy => exists_level_reach S e hM hC Sset
      (fun n j y X q x hx hc' => (hSdef n j y X q).2 ⟨x, hx, hc'⟩) j y X hy)
    (fun n j _ hjK y X _ hy h => exists_mem_level_set S e Sset hSsub W hWdef n j
      (by omega) y X h)
  have hγw : 0 < gammaW d' := by
    unfold gammaW
    have := agmonRate_pos (d := d') (by omega)
    positivity
  have hcF := cF_pos d' L
  have hA0 : 0 ≤ 20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) * (Kw * cF d' L) := by positivity
  have hCw : (0 : ℝ) ≤ ((C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d' *
      (2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) ^ d' : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsum := sum_poly_decay_le (A := 20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) *
    (Kw * cF d' L)) (r := d') hA0 hγw hCw W
    (fun n => card_level_set_le S e hM C W hWdef n) (d' * ((N₁ * L ^ m₁) * L ^ (kS + 1)) + 1)
  have hP : 0 ≤ (K : ℝ) * ((L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1)) * P.E₀ := by
    have := K0_pos d' L (P.κ - 1)
    unfold c1
    positivity
  refine hmain.trans ?_
  gcongr

end Balaban.Green
