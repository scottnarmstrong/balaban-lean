/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymM
public import Balaban.Inhabited.XiCRawOpenWitness
public import Balaban.Fluctuation.StepComplexJointH
public import Balaban.Fluctuation.StepComplexOffFibreC
public import Balaban.Fluctuation.StepComplexOffFibreE1Loc

/-!
# The neighbourhood part of `hdom` (`StepTowerNewLevelSymDom`)

The premise `hdom` of `densE0_fullJSymGroup`, `densM0_fullJSymGroup` asks that the old composed
pairs of the shifted data lie in the class domain for all shifts near each point of the
interpolation path.  `hdom_of_pathMem` reduces it to the path points themselves: the inequalities
of `XiC` are strict, so the class domain is open in the layer-constant fields
(`xiDom_eventually`); the composed pair is layer-constant (`composedPairAtC_mem_layerSub`) and
continuous in the shift (`analyticAt_PJ`, through the linear homeomorphism
`ψ̂ ↦ β_k^{-1/2} C^{1/2} ψ̂`).  What remains is the membership at the real path points, the open
`OldXiDomC` (class-radius inequalities of `GENERAL.md` §1) for data of any field.
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Matrix Filter Topology

section DomA

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ eps pp : ℝ}
  {a' : ℕ → ℝ} {μ' : ℝ} {ε' : ℕ → ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The composed old pair of any datum lies in the layer-constant fields of its level set. -/
theorem composedPairAtC_mem_layerSub {j : ℕ} (hj : j ≤ k)
    (E : BgData (stepG d L N₁ m₁ k ϱ) N) :
    composedPairAtC S.a S.ν (Nat.le_succ k) j E ∈
      layerSub (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
        (hj.trans (Nat.le_succ k))) := by
  simp only [composedPairAtC, hj, ↓reduceDIte]
  exact ⟨(composedDataAtC S.a S.ν hj (Nat.le_succ k) E).Ψ_layerConst,
    (composedDataAtC S.a S.ν hj (Nat.le_succ k) E).h_layerConst⟩

variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}
variable (Jr : S.JointRep eps pp)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include Jr hC hMX hdm hα hsm in
/-- **The neighbourhood part of `hdom`**: if the old composed pairs of the shifted data at the
points `s β_k^{-1/2} C^{(k)1/2} ψ̂`, `‖ψ̂‖ < p₁`, of the interpolation path lie in the class domain
`Ξ^c_j(𝔹_j; 1, ε'_j)` (`hpath`, the real path points only), then they do for all shifts near each
path point.  The domain is open in the layer-constant fields (`xiDom_eventually`: the inequalities
of `XiC` are strict), the composed pair is a layer-constant continuous (indeed analytic,
`analyticAt_PJ`) function of the shift, and the substitution `ψ' = β_k^{-1/2} C^{1/2} ψ̂` is a
linear homeomorphism. -/
theorem hdom_of_pathMem (hβ : 0 < S.β) (hle : S.p₁ ≤ pp)
    (hBg : BgHyp d L (k + 1) ϱ a' μ') {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hpath : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (s : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (s : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))).2) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)),
        ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2 := by
  intro s hs x hx
  set M := hatCovSqrt S.G' S.a₁ S.ν D with hMdef
  have hdet : IsUnit M.det := by
    rw [hMdef]
    show IsUnit (hatCovSqrt S.G' S.a₁ S.ν (S.withDatumH D).D').det
    rw [(S.withDatumH D).det_hatCovSqrt_of_chart hC hMX hdm hα hsm hD]
    exact (Complex.exp_ne_zero _).isUnit
  obtain ⟨T, Ti, hT, hTTi, hTiT⟩ := S.exists_hatField_clm hβ M hdet
  have hΘ : rawOf D ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hψ₀ : ‖(s : ℂ) • yhat x‖ < pp :=
    calc ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := StepSetting.JointRep.norm_smul_yhat_le (S := S) s x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ < pp := by rw [one_mul]; exact hx.trans_le hle
  have hw₀ : (s : ℂ) • S.hatField M (yhat x) = T ((s : ℂ) • yhat x) := by
    rw [hT, S.hatField_smul']
  have hTi₀ : Ti ((s : ℂ) • S.hatField M (yhat x)) = (s : ℂ) • yhat x := by
    rw [hw₀, hTiT]
  -- the open set of shifts whose preimage is in the ball
  have hUopen : IsOpen {w : S.EC | ‖Ti w‖ < pp} :=
    isOpen_lt (continuous_norm.comp Ti.continuous) continuous_const
  have hUmem : (s : ℂ) • S.hatField M (yhat x) ∈ {w : S.EC | ‖Ti w‖ < pp} := by
    show ‖Ti ((s : ℂ) • S.hatField M (yhat x))‖ < pp
    rw [hTi₀]; exact hψ₀
  rw [Filter.eventually_all_finset]
  intro j hj
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  have hjk' : j ≤ k + 1 := hjk.trans (Nat.le_succ k)
  suffices h : ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField M (yhat x)),
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk')
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2 by
    filter_upwards [h] with w hw hjk''
    exact hw
  -- the composed pair is continuous at the path point
  have hpair : ∀ w ∈ {w : S.EC | ‖Ti w‖ < pp},
      composedPairAtC S.a S.ν (Nat.le_succ k) j
        ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w)) = Jr.PJ j (rawOf D, Ti w) := by
    intro w hw
    have hψ : ∀ p, ‖Ti w p‖ ≤ pp := fun p => (norm_le_pi_norm (Ti w) p).trans (le_of_lt hw)
    have e : S.hatField (hatCovSqrt S.G' S.a₁ S.ν (S.withDatumH D).D') (Ti w) = w :=
      (hT (Ti w)).symm.trans (hTTi w)
    have := Jr.PJ_dataUCH (S.withDatumH D) hD hψ j
    simp only [e] at this
    exact this.symm
  have hcont : ContinuousAt (fun w : S.EC => composedPairAtC S.a S.ν (Nat.le_succ k) j
      ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))) ((s : ℂ) • S.hatField M (yhat x)) := by
    have hψ : ∀ p, ‖Ti ((s : ℂ) • S.hatField M (yhat x)) p‖ ≤ pp := fun p =>
      (norm_le_pi_norm _ p).trans (le_of_lt hUmem)
    have han := Jr.analyticAt_PJ hΘ hψ j
    have hc : ContinuousAt (fun w : S.EC => ((rawOf D, Ti w) :
        RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC))
        ((s : ℂ) • S.hatField M (yhat x)) :=
      continuousAt_const.prodMk Ti.continuous.continuousAt
    refine ContinuousAt.congr (han.continuousAt.comp_of_eq hc rfl) ?_
    filter_upwards [hUopen.mem_nhds hUmem] with w hw
    exact (hpair w hw).symm
  have hmem0 := hpath s hs x hx j hj hjk'
  have hev := xiDom_eventually (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
    (ϱ := ϱ) j hjk') hBg hmem0
  have htend : Tendsto (fun w : S.EC => composedPairAtC S.a S.ν (Nat.le_succ k) j
      ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))) (𝓝 ((s : ℂ) • S.hatField M (yhat x)))
      (𝓝[layerSub (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j hjk')]
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H +
            (s : ℂ) • S.hatField M (yhat x))))) :=
    tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto, Filter.Eventually.of_forall fun w =>
      composedPairAtC_mem_layerSub hjk _⟩
  exact htend.eventually hev

end DomA
end Balaban.Inhabited.StepSym
