/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalPolydiscClass
public import Balaban.Fluctuation.LocalClassDensityChart
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The polydisc inclusion of the last integral for the class, local generating sets (blocker 5)

`FinalPolydiscClass.lean` proves the inclusion under `Tm.gs j X = levelGS j`.  Here the terms of the
class use the local generating sets `𝔹_j(X) = localB j X` (the minimal sets of P3 (4.4)-(4.6)).  The
composed pair `Λ_j(w)` of the polydisc is the composition of the datum to the whole-level set
`levelGS j`; it lies in `Ξ^c_j(𝔹_j(X); 1, ε_j)` after the restriction to the data sites of
`𝔹_j(X)` with the loss `K_loc = (2 K₁ + 2) C₁` (`localB_xiDom_level_linear`).

* `composedPair_xiDom_localB_of_xiCData`: a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` composes, at every level
  `1 ≤ j ≤ k`, to a pair of `Ξ^c_j(localB j X; 1, ε')` whenever `K_loc ε ≤ ε'`;
* `cutoffInteraction_final_class_polydisc_local`: the composed theorem for the class with
  `Tm.gs j X = localB j X`; the room condition is `K_loc (ε₀ + K₂' N c ε_K) ≤ ε_K`.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField Balaban.LargeField.ActionConv

namespace Balaban.Green

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The composition of a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` to the level `j` lies in the local chart**:
for `1 ≤ j ≤ k`, the pair `(ψ_k^{(j)}, h)` of (H.2) lies in `Ξ^c_j(𝔹_j(X); 1, ε')` of the local
generating set for every `ε'` with `(2 K₁ + 2) C₁ ε ≤ ε'` (composition (Ξ3) at `b = 1`, then the
restriction `localB_xiDom_level_linear`). -/
theorem composedPair_xiDom_localB_of_xiCData (S : StepSetting d L N₁ m₁ k N ϱ)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε ε' : ℝ}
    {D : BgData (stepG d L N₁ m₁ k ϱ) N}
    (hD : XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 ε D)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hth : xiC1 d * ε ≤ thm73C1 d L N)
    (hc0 : xiC1 d * ε ≤ bgC0 d L N) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hε : (2 * bgK1 d L N + 2) * (xiC1 d * ε) ≤ ε') {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {hsep : ϱ ≤ minSep L (L ^ m₁)} :
    XiDom (localB j (hjk.trans (Nat.le_succ k)) X hsep) S.a S.ν j ε'
      (composedPairAtC S.a S.ν (Nat.le_succ k) j D).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) j D).2 := by
  have h1 := xiCData_compose_of_one_le (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k + 1) (ϱ := ϱ) j (hjk.trans (Nat.le_succ k))) (G' := stepG d L N₁ m₁ k ϱ) (b := 1)
    le_rfl ha₁ HB HB (levelGS_precedes_at hjk (Nat.le_succ k)) (fun z _ => (S.hG z).1) hsmall hth hD
  rw [one_mul] at h1
  have e : composedPairAtC S.a S.ν (Nat.le_succ k) j D =
      ((composedDataAtC S.a S.ν hjk (Nat.le_succ k) D).Ψ,
        (composedDataAtC S.a S.ν hjk (Nat.le_succ k) D).h) := by
    simp only [composedPairAtC, hjk, ↓reduceDIte]
  rw [e]
  exact localB_xiDom_level_linear hj1 (hjk.trans (Nat.le_succ k)) HB hsmall hc0 hc1 hε h1
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end Chart

section Composed

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The last integral for the interaction of the class: the polydisc inclusion discharged**
(local generating sets).  As `cutoffInteraction_final_class_polydisc`, but the terms of the class
use the minimal sets `Tm.gs j X = 𝔹_j(X) = localB j X` (`hgs`), `1 ≤ j ≤ K`.  The restriction of
the whole-level chart to `𝔹_j(X)` costs the factor `K_loc = (2 K₁ + 2) C₁`: with the radius
`ε' = ε₀ + K₂' N c ε_K` of the data of the polydisc, the conditions are
`K_loc ε' ≤ ε_K` (`hroom`; `ε_K ≤ ε_j` for `j ≤ K`) and `C₁ ε' ≤ c₀, c₁` (`hc0`, `hc1`), besides
the smallness and perturbation conditions of the whole-level version. -/
theorem cutoffInteraction_final_class_polydisc_local
    {d' : ℕ} {c α α₀ β₀ A₁ : ℝ} {p : ℕ} {N₁ m₁ kS N : ℕ} [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N)
    {P : Consts} {Tm : Terms d' L N₁ m₁ (kS + 1) N ϱ}
    (hT : SFTermClauses P
      (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ) Tm)
    {K : ℕ} (hK : K ≤ kS) (hE₀ : 0 ≤ P.E₀)
    {hsep : ϱ ≤ minSep L (L ^ m₁)}
    (hgs : ∀ j (hjk : j ≤ kS + 1), 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
      Tm.gs j X = localB j hjk X hsep)
    (HB : BgHyp d' L (kS + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε₀ : ℝ}
    (hθ : XiCData S.G' S.a S.ν (kS + 1) 1 ε₀ S.D')
    (hroom : (2 * bgK1 d' L N + 2) * (xiC1 d' * (ε₀ + xiK2 d' L N *
      ((N : ℝ) * (c * epsSeq L α α₀ K)))) ≤ epsSeq L α α₀ K)
    (hc0 : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K))) ≤ bgC0 d' L N)
    (hc1 : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K))) ≤ bgC1 d' L N)
    (hsmall : (4 * d' + 6) * ((2 * d' + 1) * epsSeq L α α₀ K) ≤ 1)
    (hth : xiC1 d' * epsSeq L α α₀ K ≤ thm73C1 d' L N)
    (hm1 : (N : ℝ) * (c * epsSeq L α α₀ K) ≤ 1)
    (hδ₂ : xiC1 d' * ε₀ + 5 * ((N : ℝ) * (c * epsSeq L α α₀ K)) ≤ bgC1 d' L N)
    (hstar : (N : ℝ) * (c * epsSeq L α α₀ K) ≤ deltaStar d' L N)
    (hK1s : bgK1 d' L N * (xiC1 d' * ε₀) ≤ deltaStar d' L N)
    (hsm : bgK1 d' L N * (xiC1 d' * ε₀) + cK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) <
      bgC0 d' L N)
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : MeasureTheory.Measure (L1Torus d N₀ → ℝ)}
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)} < ⊤)
    (hd2 : 2 ≤ d') (hp : 1 ≤ p) (hA : 0 ≤ A₁) (hα₀ : 0 < α₀) (hα0 : 0 ≤ α) (hc : 0 < c)
    (hα : α ≤ ((d' : ℝ) - 2) * (1 / 4)) (hβ₀ : 1 < β₀)
    (hsize : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * A₁ * (4 * (p : ℝ)) ^ p < c * α₀ * β₀ ^ (1 / 4 : ℝ)) :
    AnalyticOnNhd ℂ (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p (betaK d' L K β₀)},
        (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
            Edens P.m₀ Tm j
              (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).1
              (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).2)
          (fun x => (fun q => S.psi0C (e q)) x +
            (((betaK d' L K β₀) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := by
  have hεK0 : 0 ≤ epsSeq L α α₀ K := epsSeq_nonneg' L α α₀ hα₀.le K
  have hR : 0 ≤ c * epsSeq L α α₀ K := mul_nonneg hc.le hεK0
  have hε₀ : 0 < ε₀ := by
    obtain ⟨_, _, _, _, ⟨_, h, _⟩, _⟩ := hθ
    exact h
  have hxk : 0 ≤ xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) := by
    unfold xiK2
    have := cK2_pos d' L N
    positivity
  have hε₁ : ε₀ ≤ ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) := by linarith
  have hKloc : 1 ≤ (2 * bgK1 d' L N + 2) * xiC1 d' := by
    have := bgK1_pos d' L N
    have := one_le_xiC1 d'
    nlinarith
  have hroom0 : ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) ≤ epsSeq L α α₀ K := by
    refine le_trans ?_ hroom
    have h0 : 0 ≤ ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) := by linarith
    calc _ = 1 * (ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K))) := (one_mul _).symm
      _ ≤ ((2 * bgK1 d' L N + 2) * xiC1 d') *
          (ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K))) :=
        mul_le_mul_of_nonneg_right hKloc h0
      _ = _ := by ring
  have hε₀K : ε₀ ≤ epsSeq L α α₀ K := hε₁.trans hroom0
  have hsm0 : (4 * d' + 6) * ((2 * d' + 1) * ε₀) ≤ 1 := by
    refine le_trans ?_ hsmall
    have : (0 : ℝ) ≤ 4 * d' + 6 := by positivity
    have : (0 : ℝ) ≤ 2 * d' + 1 := by positivity
    gcongr
  have hth0 : xiC1 d' * ε₀ ≤ thm73C1 d' L N :=
    le_trans (mul_le_mul_of_nonneg_left hε₀K (by have := one_le_xiC1 d'; linarith)) hth
  have hsm1 : (4 * d' + 6) * ((2 * d' + 1) * (ε₀ + xiK2 d' L N *
      ((N : ℝ) * (c * epsSeq L α α₀ K)))) ≤ 1 := by
    refine le_trans ?_ hsmall
    have : (0 : ℝ) ≤ 4 * d' + 6 := by positivity
    have : (0 : ℝ) ≤ 2 * d' + 1 := by positivity
    gcongr
  have hth1 : xiC1 d' * (ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K))) ≤
      thm73C1 d' L N :=
    le_trans (mul_le_mul_of_nonneg_left hroom0 (by have := one_le_xiC1 d'; linarith)) hth
  have hclose : ∀ w ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K),
      XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1
        (ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)))
        (S.dataUC (fun q => w (e.symm q))) := fun w hw =>
    dataUC_xiCData_of_close S HB ha₁ hθ hsm0 hth0 hR hm1 hδ₂ hstar hK1s hsm (fun q => by
      have := hw (e.symm q)
      simp only [Equiv.apply_symm_apply] at this
      exact this.le)
  have hΛ : ∀ j, AnalyticOnNhd ℂ (fun w : L1Torus d N₀ → ℂ =>
      composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q))))
      (polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K)) := fun j =>
    analyticOnNhd_composedPair S HB (isOpen_polydisc _ _)
      (ψ := fun (w : L1Torus d N₀ → ℂ) q => w (e.symm q))
      (fun q w _ => (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : L1Torus d N₀ => ℂ) (e.symm q)).analyticAt w)
      (fun w hw => xiCData_unionC (hclose w hw)) j
  have hsub : ∀ w ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => c * epsSeq L α α₀ K),
      ∀ j, 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
      (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ).dom j (Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).1
        (composedPairAtC S.a S.ν (Nat.le_succ kS) j (S.dataUC (fun q => w (e.symm q)))).2 := by
    intro w hw j hj1 hjK X hX
    have hjk : j ≤ kS := hjK.trans hK
    rw [hgs j (hjk.trans (Nat.le_succ kS)) hj1 hjK X hX]
    exact composedPair_xiDom_localB_of_xiCData S HB ha₁ (hclose w hw) hsm1 hth1 hc0 hc1
      (hroom.trans (epsSeq_anti L α α₀ hα₀.le hα0 hjK)) hj1 hjk
  have hBc : 0 ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) := (cutConst_pos (d := d) (L := L) hd κ).le
  have hβpos : 0 < betaK d' L K β₀ := by
    rw [betaK_eq_rpow K hd2]
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := hβ₀; positivity
  exact cutoffInteraction_final_class_of_polydisc_subset_levels
    (R := c * epsSeq L α α₀ K) (N₀ := N₀) hT (hK.trans (Nat.le_succ kS)) hE₀
    (fun j _ _ => hΛ j) hsub hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
    (pLog_nonneg hA p (by
      rw [betaK_eq_rpow K hd2]
      have h1 : 1 ≤ (L : ℝ) ^ (((d' : ℝ) - 2) * K) :=
        Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
          (by have : (2 : ℝ) ≤ d' := by exact_mod_cast hd2
              positivity)
      nlinarith)) hβpos hγ
    (cutConst_mul_pLog_lt_epsSeq hd2 hp hBc hA hα₀ hc hα hβ₀ hsize K)

end Composed

end Balaban.Green
