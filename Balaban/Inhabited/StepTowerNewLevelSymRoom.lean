/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymDom
public import Balaban.Fluctuation.ClassOldMarksY
public import Balaban.Fluctuation.LocalClassDensityIrrelStepRoom

/-!
# The old composed pairs along the path lie in the old domain (`StepTowerNewLevelSymRoom`)

The membership asked by `hdom_of_pathMem` at the real points of the interpolation path.  At the
path point `s β_k^{-1/2} C^{(k)1/2} ψ̂` the old datum `dataUCH (ψ^{(k)}(D) + w)` is the datum
`flDatumOne` of the chain of the old terms (`flDatumOne_stepG_liftC_H`: the free-field version of
`flDatumOne_stepG_liftC`), for the fluctuation `ψ' = liftC w` in the ball of radius `δ₁`
(`hatLift_mem_flBallLC`).  The chain places its composition into `𝔹_j` in `Ξ^c_j(𝔹_j; 1,
ε + K₂δ₃ + K₂δ_fl)` (`eTerm_chain_of_one_le`), hence in `Ξ_j(𝔹_j; ε'_j)` as soon as the room
`ε + K₂δ₃ + K₂δ_fl ≤ ε'_j` holds.  The composition holds into any term generator `Gj` with the
settings of the chain (`pathDatum_xiCData_of_room`, the core; `pathMem_of_room` is its instance at
`Gj = 𝔹_j`).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Matrix Filter Topology

section RoomA

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}

/-- **`flDatumOne` at a complex tangent, at a block datum with any field**: for a block datum
`H.D'` the chain datum of the tangent `liftC v` is the old datum of the spin `ψ^{(k)}(θ) + v`
(`flDatumOne_stepG_liftC` for the free-field wrapper). -/
theorem flDatumOne_stepG_liftC_H (H : StepSettingH S) (ha : S.a k ≠ 0) (BG₂ κ : ℝ)
    (hP : Precedes (stepG d L N₁ m₁ k ϱ) S.G')
    (hPm : Precedes (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ)) (v : S.EC)
    (hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v)) :
    flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν H.D' (liftC S.hG' v) hz =
      H.dataUCH (H.psi0H + v) := by
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    have ht := congrFun (congrFun (H.compTangent_dataUCH (H.psi0H + v)) x) i
    simp only [compTangent] at ht
    have e : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ x i =
        composeField (stepG d L N₁ m₁ k ϱ) S.G' S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
          H.D'.Ψ x i := rfl
    rw [e] at ht
    show (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν H.D' _ hz).Ψ x i =
      (H.dataUCH (H.psi0H + v)).Ψ x i
    unfold flDatumOne
    rw [flDatum_Ψ, composeField_self S.hG S.a ha]
    have hv : (H.psi0H + v - fun q => (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ (unitRep (G' := S.G') q.1) q.2) = v := by
      funext q
      simp [StepSettingH.psi0H]
    rw [hv] at ht
    linear_combination -ht
  · funext x i
    show (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hP hPm S.a₁ S.ν H.D' _ hz).h x i =
      (H.dataUCH (H.psi0H + v)).h x i
    rw [H.dataUCH_h]
    unfold flDatumOne
    rw [flDatum_h]
    show (if x ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 then H.D'.h x i else 0) = _
    rw [ite_eq_left (S.hG x).1]

end RoomA

section RoomB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc δ₃ δfl r₀ eps pp μ' : ℝ} {a' ε' : ℕ → ℝ}
  {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable (Jr : S.JointRep eps pp)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)

include Jr hC hMX hdm hα hsm hδ₁ in
/-- **The composition of the old datum of a bounded hat variable into a term generator lies in the
chart** (the core of `pathMem_of_room`, at any term generator `Gj`).  For a datum `D` of the chart
and `‖ψ̂‖ ≤ pp`, the old datum `dataUCH (ψ^{(k)}(D) + β_k^{-1/2} C^{1/2} ψ̂)` composed into a term
generator `Gj` with the settings of the chain of the old terms (`BgSetting` for `(𝔹_k, Gj)`,
`FlSetting` for the fluctuation of `𝔹_k`) lies in `Ξ^c_j(Gj; 1, ε + K₂δ₃ + K₂δ_fl)`
(`eTerm_chain_of_one_le` at `b = 1`, for the fluctuation `liftC (C^{1/2} ψ̂)` in the ball of
radius `δ₁`, `hatLift_mem_flBallLC`). -/
theorem pathDatum_xiCData_of_room (hβ : 0 < S.β) {ϱ₂ : ℝ}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂} {j : ℕ}
    (hBj : BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) {ψh : S.EC}
    (hψh : ∀ p, ‖ψh p‖ ≤ pp) :
    XiCData Gj (compWeight L S.a₁) S.ν j 1 (eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
      (composeData hBj.hq (compWeight L S.a₁)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν (bgC0 d L N)
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H +
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) ψh)))
        ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H +
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) ψh))) := by
  have hδ' : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁ := by
    rw [S.norm_betaU_rpow hβ.le]; exact hδ₁
  have hmem := hatLift_mem_flBallLC hC S.hk1 S.hG S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    Jr.hpp hMX hdm hα hsm hδ' hD hψh
  have hmem' : liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) ψh) ∈
      FlBallLC (stepG d L N₁ m₁ k ϱ) δ₁ := hmem
  have ht := triple_one_mem (X₁f := X₁f) hC hD hmem'
  obtain ⟨Fk, -, hFk⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν)
    (N := N) hBj.HBk
  obtain ⟨D', ψ'', hlc, ht22, -, -, -, hX2⟩ :=
    eTerm_chain_of_one_le (b := 1) le_rfl (one_le_scaledC0 d) hBj hF hFk ht
  have ht22' : ((rawOf D, liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) ψh)) :
      RawData d L (N₁ * L ^ m₁) (k + 1) N × _) = (rawOf D', ψ'') := ht22
  have hD'eq : D' = D := BgData.eq_of_raw (congrArg Prod.fst ht22').symm
  have hψeq := (congrArg Prod.snd ht22').symm
  have hD'eq' := hD'eq.symm
  subst hD'eq' hψeq
  have ha : S.a k ≠ 0 :=
    (compWeight_pos (by have := hBj.HBp.hL; omega) hBj.ha₁ S.hk1).ne'
  have hfl := flDatumOne_stepG_liftC_H (S.withDatumH D) ha BG₂ κ hBj.hP hF.hPm
    (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) ψh) hlc
  rw [one_pow, one_mul] at hX2
  exact hfl ▸ hX2

include Jr hC hMX hdm hα hsm hδ₁ in
/-- **The old composed pairs at the real path points lie in the old domain**: the hypothesis
`hpath` of `hdom_of_pathMem`.  For a datum `D` of the chart, `s ∈ [0,1]`, `‖ψ̂‖ < p₁ ≤ pp` and an
old level `1 ≤ j ≤ k`, the composed pair of `ψ^{(k)}(D) + s β_k^{-1/2} C^{1/2} ψ̂` lies in
`Ξ_j(𝔹_j; ε'_j)` when the chain of the old terms is set up at the level (`BgSetting` for
`𝔹_j`, `FlSetting` for the fluctuation of `𝔹_k`, the data of `eTerm_chain_of_one_le`) and the
room `ε + K₂ δ₃ + K₂ δ_fl ≤ ε'_j` holds (`pathDatum_xiCData_of_room` at `Gj = 𝔹_j`). -/
theorem pathMem_of_room (hβ : 0 < S.β) (hle : S.p₁ ≤ pp)
    (ha' : a' = S.a) (hμ' : μ' = S.ν)
    (hB : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hroom : ∀ j ∈ Finset.Icc 1 k, eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ ε' j)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (s : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + (s : ℂ) •
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))).2 := by
  subst ha' hμ'
  intro s hs x hx j hj hjk
  obtain ⟨-, hjk0⟩ := Finset.mem_Icc.1 hj
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hψ₀ : ‖(s : ℂ) • yhat x‖ < pp :=
    calc ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := StepSetting.JointRep.norm_smul_yhat_le (S := S) s x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ < pp := by rw [one_mul]; exact hx.trans_le hle
  have hψh : ∀ p, ‖((s : ℂ) • yhat x) p‖ ≤ pp := fun p =>
    (norm_le_pi_norm _ p).trans hψ₀.le
  have hv : S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) ((s : ℂ) • yhat x) =
      (s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) := S.hatField_smul' _ _ _
  have hX2 := pathDatum_xiCData_of_room Jr hC hMX hdm hα hsm hδ₁ hβ (hB j hj hjk) hF hD hψh
  rw [hv] at hX2
  have hdom := xiDom_of_xiCData_of_one_le (σ := 1) (ε' := ε' j) le_rfl
    (by rw [one_pow, one_mul]; exact hroom j hj) hX2
  simp only [composedPairAtC, hjk0, ↓reduceDIte]
  exact hdom

end RoomB

end Balaban.Inhabited.StepSym
