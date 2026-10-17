/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalRadiusClass
public import Balaban.Localization.I5Chain
public import Balaban.SmallField.XiPerturb
public import Balaban.Fluctuation.StepComplex
public import Balaban.Fluctuation.Theorem42WireAct
public import Balaban.Fluctuation.ClassOldBirthConsts
public import Balaban.Fluctuation.StepActivityClassChart
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The polydisc inclusion of the last integral for the class (blocker 5)

The field of the last integral is `φ₀ + β_K^{-1/2} C_fin(s) ψ`, a point of the polydisc of radius
`R = c ε_K` around the critical field `φ₀ = ψ^{(k)}(θ)` (the unit-lattice field of the critical
datum).  A step `S` (`StepSetting`) and an equivalence `e : L1Torus d N₀ ≃ S.U × Fin N` identify
the variable `w : L1Torus d N₀ → ℂ` of the cutoff theorems with the complex old spin
`ψ_w = w ∘ e⁻¹ : S.EC`.  The lift of `w` to the data of the class at level `j` is the composed pair
`Λ_j(w) = composedPairAtC … j (S.dataUC ψ_w)` of (H.2): the datum `(ψ_w, h₀)` of `𝔹_k`
composed down to `𝔹_j`.

* `dataUC_xiCData_of_close`: if the block datum `θ` lies in `Ξ^c_{k+1}(𝔹'; 1, ε₀)`, then for every
  old spin `ψ` with `|ψ - ψ^{(k)}(θ)| ≤ m` the datum `dataUC ψ` lies in
  `Ξ^c_{k+1}(𝔹_k; 1, ε₀ + K₂' N m)` (composition (Ξ3) at `b = 1`, then the perturbation (Ξ2));
* `composedPair_xiDom_of_xiCData`: a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` composes, at every level
  `j ≤ k`, to a pair of `Ξ^c_j(𝔹_j; 1, ε)` (the whole-level chart);
* `analyticOnNhd_composedPair_polydisc`: `Λ_j` is analytic on the polydisc;
* `polydisc_composedPair_mem_xiDom`: `hsub` for terms whose generating set is the whole-level set;
* `cutoffInteraction_final_class_of_polydisc_subset_levels`: the cut-family analyticity for the
  interaction `∑_j ℰ^{(j)}(Λ_j w)` with level-dependent lifts;
* `cutoffInteraction_final_class_polydisc`: the composed theorem.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Fluctuation Balaban.Inhabited Balaban.LargeField.ActionConv

namespace Balaban.Green

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The datum of an old spin near the critical point lies in the chart of `𝔹_k`.**  Let the block
datum `θ = S.D'` lie in `Ξ^c_{k+1}(𝔹'; 1, ε₀)` and let `ψ` be a complex old spin with
`|ψ(q) - ψ^{(k)}(θ)(q)| ≤ m` for all `q`.  Then `dataUC ψ` lies in `Ξ^c_{k+1}(𝔹_k; 1, ε₀ + K₂' N m)`.
The numerical conditions are those of (Ξ3) at `ε₀` and of (Ξ2) with `δ₃ = N m`. -/
theorem dataUC_xiCData_of_close (S : StepSetting d L N₁ m₁ k N ϱ) (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (ha₁ : 0 < S.a₁) {ε₀ m : ℝ}
    (hθ : XiCData S.G' S.a S.ν (k + 1) 1 ε₀ S.D')
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1) (hth : xiC1 d * ε₀ ≤ thm73C1 d L N)
    (hm : 0 ≤ m) (hm1 : (N : ℝ) * m ≤ 1)
    (hδ₂ : xiC1 d * ε₀ + 5 * ((N : ℝ) * m) ≤ bgC1 d L N)
    (hstar : (N : ℝ) * m ≤ deltaStar d L N)
    (hK1s : bgK1 d L N * (xiC1 d * ε₀) ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε₀) + cK2 d L N * ((N : ℝ) * m) < bgC0 d L N)
    {ψ : S.EC} (hψ : ∀ q, ‖ψ q - S.psi0C q‖ ≤ m) :
    XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 (ε₀ + xiK2 d L N * ((N : ℝ) * m))
      (S.dataUC ψ) := by
  have h1 := xiCData_compose_of_one_le (G := stepG d L N₁ m₁ k ϱ) (G' := S.G') (b := 1) le_rfl ha₁
    HB HB (S.hG.precedes S.hG' le_rfl) (fun z _ => (S.hG' z).1) hsmall hth hθ
  rw [one_mul] at h1
  have h2 : XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 ε₀ (S.dataUC S.psi0C) := by
    rw [S.dataUC_psi0C]; exact h1
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h2
  have hδΨc := isLayerConstant_liftC S.hG S.hG' (ψ - S.psi0C)
  have hδΨ : ∀ x ∈ dataSites (stepG d L N₁ m₁ k ϱ), vn (liftC S.hG' (ψ - S.psi0C) x) ≤
      (N : ℝ) * m := fun x _ => vn_le_card_mul hm fun i => hψ (unitPt S.hG' x, i)
  have hP := xiC_perturb HB (by positivity) hm1 (by
      have := hsmall; nlinarith [hth]) hδ₂ hstar hK1s hsm hδΨc hδΨ hX
  refine ⟨Ψ₀, h₀, _, h'', hP, ?_, ?_⟩
  · intro x hx i
    have hx' := hR.1 x hx i
    rw [S.dataUC_Ψ] at hx' ⊢
    show ψ (unitPt S.hG' x, i) = (Ψ₀ x i : ℂ) +
      (Ψ'' x i + (ψ (unitPt S.hG' x, i) - S.psi0C (unitPt S.hG' x, i)))
    linear_combination hx'
  · intro x hx i
    rw [S.dataUC_h]
    have := hR.2 x hx i
    rw [S.dataUC_h] at this
    exact this

/-- **The composition of a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` to the level `j` lies in the whole-level
chart**: for `1 ≤ j ≤ k`, the pair `(ψ_k^{(j)}, h)` of (H.2) lies in `Ξ^c_j(𝔹_j; 1, ε')` for
every `ε' ≥ ε` (composition (Ξ3) at `b = 1`, the level monotonicity, and the rescaling). -/
theorem composedPair_xiDom_of_xiCData (S : StepSetting d L N₁ m₁ k N ϱ)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε ε' : ℝ}
    {D : BgData (stepG d L N₁ m₁ k ϱ) N}
    (hD : XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 ε D)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hth : xiC1 d * ε ≤ thm73C1 d L N)
    (hε : ε ≤ ε') {j : ℕ} (hjk : j ≤ k) :
    XiDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
        (hjk.trans (Nat.le_succ k))) S.a S.ν j ε'
      (composedPairAtC S.a S.ν (Nat.le_succ k) j D).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) j D).2 := by
  have h1 := xiCData_compose_of_one_le (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k + 1) (ϱ := ϱ) j (hjk.trans (Nat.le_succ k))) (G' := stepG d L N₁ m₁ k ϱ) (b := 1)
    le_rfl ha₁ HB HB (levelGS_precedes_at hjk (Nat.le_succ k)) (fun z _ => (S.hG z).1) hsmall hth hD
  rw [one_mul] at h1
  have h2 := xiCData_level_mono (n' := j) (hjk.trans (Nat.le_succ k)) HB.mass h1
  have h3 := xiDom_of_xiCData_of_one_le (le_refl (1 : ℝ)) (ε' := ε') (by nlinarith) h2
  have e : composedPairAtC S.a S.ν (Nat.le_succ k) j D =
      ((composedDataAtC S.a S.ν hjk (Nat.le_succ k) D).Ψ,
        (composedDataAtC S.a S.ν hjk (Nat.le_succ k) D).h) := by
    simp only [composedPairAtC, hjk, ↓reduceDIte]
  rw [e]
  exact h3

end Chart

section Analytic

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The composed pair of the datum of an old spin is analytic in the spin variable.**  If the
coordinates `w ↦ ψ_w(q)` are analytic on an open set `s` and `dataUC ψ_w` lies in the union domain
`𝒟` of Theorem 7.2 for `w ∈ s`, then `w ↦ (ψ_k^{(j)}, h)` of `dataUC ψ_w` is analytic on `s`, for
every level `j` (for `j > k` it is the constant pair `(0, 0)`). -/
theorem analyticOnNhd_composedPair (S : StepSetting d L N₁ m₁ k N ϱ)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν) {s : Set E} (hs : IsOpen s) {ψ : E → S.EC}
    (hψ : ∀ q, AnalyticOnNhd ℂ (fun w => ψ w q) s)
    (hU : ∀ w ∈ s, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (ψ w))) (j : ℕ) :
    AnalyticOnNhd ℂ (fun w => composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (ψ w))) s := by
  by_cases hj : j ≤ k
  · have hD : AnalyticOnNhd ℂ (fun w => ((S.dataUC (ψ w)).Ψ, (S.dataUC (ψ w)).h)) s := by
      intro w hw
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
        (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      · have e : (fun w => (S.dataUC (ψ w)).Ψ x i) = fun w => ψ w (unitPt S.hG' x, i) :=
          funext fun w => S.dataUC_Ψ _ x i
        rw [e]; exact hψ _ w hw
      · have e : (fun w => (S.dataUC (ψ w)).h x i) = fun _ => (S.h₀ i : ℂ) :=
          funext fun w => S.dataUC_h _ x i
        rw [e]; exact analyticAt_const
    have hφ := bgFieldC_analyticOn_raw (G := stepG d L N₁ m₁ k ϱ) HB hs
      (Dd := fun w => S.dataUC (ψ w)) hD hU
    intro w hw
    have e : (fun w => composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (ψ w))) =
        fun w => ((composedDataAtC S.a S.ν hj (Nat.le_succ k) (S.dataUC (ψ w))).Ψ,
          (composedDataAtC S.a S.ν hj (Nat.le_succ k) (S.dataUC (ψ w))).h) := by
      funext w'
      simp only [composedPairAtC, hj, ↓reduceDIte]
    rw [e]
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    · exact analyticAt_composeField (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) j (hj.trans (Nat.le_succ k))) (G' := stepG d L N₁ m₁ k ϱ) S.a
        (fun w => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (ψ w)))
        (fun w => (S.dataUC (ψ w)).Ψ)
        (fun r => analyticAt_pi_iff.1 (hφ w hw) r)
        (fun y j' => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_fst.comp (hD w hw)) y) j')
        x i
    · have e2 : (fun w => (composedDataAtC S.a S.ν hj (Nat.le_succ k) (S.dataUC (ψ w))).h x i) =
          fun _ => if x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) j (hj.trans (Nat.le_succ k))).Ω 1 then (S.h₀ i : ℂ) else 0 := by
        funext w'
        show (if x ∈ _ then (S.dataUC (ψ w')).h x i else 0) = _
        rw [S.dataUC_h]
      rw [e2]; exact analyticAt_const
  · have e : (fun w => composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (ψ w))) =
        fun _ => ((0 : Fld d L N₁ m₁ (k + 1) N), (0 : Fld d L N₁ m₁ (k + 1) N)) := by
      funext w'
      simp only [composedPairAtC, hj, ↓reduceDIte]
    rw [e]
    exact fun _ _ => analyticAt_const

end Analytic

section Composed

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The last integral for the interaction of the class: the polydisc inclusion discharged**
(whole-level charts).  Let `S` be a step with the block datum `θ = S.D'` in
`Ξ^c_{k_S+1}(𝔹'; 1, ε₀)` and `e` an identification of the variable `w : L1Torus d N₀ → ℂ` of the
cutoff theorems with the old spin `w ∘ e⁻¹` of the unit lattice.  The critical field is
`φ₀ = ψ^{(k_S)}(θ) ∘ e` and the lift of `w` to the data of the class at level `j` is the composed
pair `Λ_j(w) = ψ_{k_S}^{(j)}(dataUC (w ∘ e⁻¹)), h` of (H.2).  If the terms of the class use the
whole-level generating sets `𝔹_j = levelGS j` (`hgs`) and the numerical conditions hold (room
`ε₀ + K₂' N c ε_K ≤ ε_K` in the radius, smallness of (Ξ2), (Ξ3)), then the cutoff integral of
`∑_{j ≤ K} ℰ^{(j)}(Λ_j(w))` over the polydisc of radius `c ε_K` around `φ₀` is analytic on the
polydisc of radius `e^κ`.  The lifts are analytic (`analyticOnNhd_composedPair`) and land in the
domains `Ξ^c_j(𝔹_j; 1, ε_j)` of the terms (`composedPair_xiDom_of_xiCData`). -/
theorem cutoffInteraction_final_class_polydisc
    {d' : ℕ} {c α α₀ β₀ A₁ : ℝ} {p : ℕ} {N₁ m₁ kS N : ℕ} [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N)
    {P : Consts} {Tm : Terms d' L N₁ m₁ (kS + 1) N ϱ}
    (hT : SFTermClauses P
      (xiFieldDom S.a S.ν (epsSeq L α α₀) : FieldDom d' L N₁ m₁ (kS + 1) N ϱ) Tm)
    {K : ℕ} (hK : K ≤ kS) (hE₀ : 0 ≤ P.E₀)
    (hgs : ∀ j (hjk : j ≤ kS + 1), 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
      Tm.gs j X = levelGS (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kS + 1) (ϱ := ϱ) j hjk)
    (HB : BgHyp d' L (kS + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε₀ : ℝ}
    (hθ : XiCData S.G' S.a S.ν (kS + 1) 1 ε₀ S.D')
    (hroom : ε₀ + xiK2 d' L N * ((N : ℝ) * (c * epsSeq L α α₀ K)) ≤ epsSeq L α α₀ K)
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
  have hε₀K : ε₀ ≤ epsSeq L α α₀ K := hε₁.trans hroom
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
    le_trans (mul_le_mul_of_nonneg_left hroom (by have := one_le_xiC1 d'; linarith)) hth
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
    exact composedPair_xiDom_of_xiCData S HB ha₁ (hclose w hw) hsm1 hth1
      (hroom.trans (epsSeq_anti L α α₀ hα₀.le hα0 hjK)) hjk
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
