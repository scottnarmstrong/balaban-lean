/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayNear
public import Balaban.Green.FinalLiftDecayPoly
public import Balaban.Green.FinalCountNear
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The volume-uniform coefficient bound with the near-locality of the lift discharged (blocker 5)

`norm_coef_cutoff_class_le_decay` with `hnear` replaced by `hnear_lift`: the lifts `Λ_j w` of the
terms of the class are analytic on the polydisc and map it into the local charts
(`lift_polydisc_facts`), and the term `(j, y, X)` varies by at most
`E₀ e^{-κ d_j(X)} ε(n)`, `ε(n) = 20 N e^{2dγ_w} K_w C_F e^{-γ_w n}`, under changes of the field off
the read set `S n j y X` (`hnear_lift`).  The coefficient bound is then
`γ(box) e^{-(κ-1)|C|} K A E₀ ∑_{n ≤ N} ω_n |W n|` with `ω_0 = 1`, `ω_n = ε(n-1)`.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField Balaban.LargeField.ActionConv

namespace Balaban.Green

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ} {d' N : ℕ}

open Classical in
/-- **The volume-uniform coefficient bound for the lift of the class** (see the module docstring). -/
theorem norm_coef_cutoff_class_le_lift (hd3 : 3 ≤ d') (hL3 : 3 ≤ L) :
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
          q ∈ Sset n j y X)
        (_ : 0 < d) (_ : 1 ≤ k) (_ : 0 ≤ v) (_ : v ≤ 1) (_ : 1 / 2 ≤ a) (_ : a ≤ 2)
        (_ : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (_ : 0 < M) {κ : ℝ} (_ : 1 ≤ κ)
        (_ : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (_ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
        {A₁ β₀ : ℝ} {p : ℕ} {γ : Measure (L1Torus d N₀ → ℝ)}
        (_ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)} < ⊤)
        (_ : 1 ≤ p) (_ : 0 ≤ A₁) (_ : α ≤ ((d' : ℝ) - 2) * (1 / 4)) (_ : 1 < β₀)
        (_ : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * A₁ * (4 * (p : ℝ)) ^ p < c * α₀ * β₀ ^ (1 / 4 : ℝ))
        (_ : 0 ≤ P.E₀) (_ : L ^ P.m₀ ∣ N₁) (_ : aEnt d' L + 2 ≤ P.κ)
        (C : Finset (MacIdx d N₀ M)) (_ : C.Nonempty) (Nm : ℕ)
        (W : ℕ → Finset (CTorus d' L N₁ m₁ (kS + 1)))
        (_ : ∀ j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
          ∃ n ≤ Nm, ∃ x ∈ Sset n j y X, x ∈ macRegion d N₀ M C)
        (_ : ∀ n j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
          (∃ x ∈ Sset n j y X, x ∈ macRegion d N₀ M C) → ∃ w ∈ W n, w ∈ X),
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
              ∑ n ∈ Finset.range (Nm + 1),
                (if n = 0 then (1 : ℝ) else 20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) *
                  (Kw * cF d' L) * Real.exp (-(gammaW d' * ((n - 1 : ℕ) : ℝ)))) *
                ((W n).card : ℝ)) := by
  obtain ⟨Kw, δw, hK, hδw, hnear⟩ :=
    hnear_lift (d := d) (N₀ := N₀) (d' := d') (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro c α α₀ N₁ m₁ kS _ ϱ S e P Tm hT K hKk hsep hgs HB ha₁ ε₀ hθ hOp hN hc hα₀ hα0 hroom hc0
    hc1 hsmall hth hm1 hδ₂ hstar hK1s hsm hKw hδw' Sset hS hd hk hv0 hv1 ha1 ha2 hmass hM κ hκ hMB
    hMκ A₁ β₀ p γ hγ hp hA hα hβ₀ hsize hE₀ hNd hκP C hC Nm W hreach hW
  have hd2 : 2 ≤ d' := by omega
  have hpoly := lift_polydisc_facts S e hKk hgs HB ha₁ hθ hN hc hα₀ hα0 hroom hc0 hc1 hsmall hth
    hm1 hδ₂ hstar hK1s hsm
  have hBc : 0 ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) := (cutConst_pos (d := d) (L := L) hd κ).le
  have hβ1 : 1 ≤ betaK d' L K β₀ := by
    rw [betaK_eq_rpow K hd2]
    have h1 : 1 ≤ (L : ℝ) ^ (((d' : ℝ) - 2) * K) :=
      Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
        (by have : (2 : ℝ) ≤ d' := by exact_mod_cast hd2
            positivity)
    nlinarith
  have hβpos : 0 < betaK d' L K β₀ := by linarith
  have hBR := cutConst_mul_pLog_lt_epsSeq (d := d') (L := L) hd2 hp hBc hA hα₀ hc hα hβ₀ hsize K
  have hcF := cF_pos d' L
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact norm_coef_cutoff_class_le_decay (d := d) (N₀ := N₀) (M := M) (L := L) (k := k) (v := v) (a := a) (d' := d') (N₁ := N₁)
    (m₁ := m₁) (kc := kS + 1) (N := N)
    (ϱ := ϱ) (R := c * epsSeq L α α₀ K) hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
    (pLog_nonneg hA p hβ1) hβpos hγ hBR hT (hKk.trans (Nat.le_succ kS))
    (φ₀ := fun q => S.psi0C (e q)) (fun j _ _ => hpoly.1 j) hpoly.2 Sset
    (fun n => 20 * (N : ℝ) * Real.exp (gammaW d' * (2 * d')) * (Kw * cF d' L) *
      Real.exp (-(gammaW d' * (n : ℝ))))
    (fun n => by positivity)
    (fun n j y X hj1 hjK hX hy w hw w' hw' hag => hnear S e hT hKk hgs HB ha₁ hθ hOp hN hc hα₀ hα0
      hroom hc0 hc1 hsmall hth hm1 hδ₂ hstar hK1s hsm hKw hδw' Sset hS n j y X hj1 hjK hX hy w hw
      w' hw' hag)
    hE₀ hNd hκP C hC Nm W hreach hW

end Balaban.Green
