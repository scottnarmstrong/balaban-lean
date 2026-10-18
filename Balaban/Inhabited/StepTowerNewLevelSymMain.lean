/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymE
public import Balaban.Fluctuation.LocalClassDensityHAnalytic

/-!
# `hDzfull` for the step density (`StepTowerNewLevelSymMain`)

`densE0_fullJSymGroup`: the covariance of the density `𝒟 = densE0` of the new level under
`fullJSymGroup L (k + 1)`, in the exact form of the input `hDzfull` of
`localClass_newLevel_of_expansion_cast`, for the step with generating set `levelGS (k + 1)`.  The
proof reduces to the chart datum `D` of the cut-off (`densE0_eq`) and applies `E0locH_sym`; the
transported datum is again a chart datum (`xiCData_sym_pair`), with cut-off `σ`-transported
(`clipRaw_act_pair`).

`phi_eventuallyEq_of_dom`: the transported `Φ₁` agrees with `Φ₁` near a point of the interpolation
path as soon as the old composed pairs of the shifted data and their transports lie in the domain
of the level sets for all shifts near the point.

Input beyond the landed premises of `densE0_eq`: the old class (clause `eucEloc`, `SFTermClauses`)
and the domain statement `hdom` (the path points of the old composed pairs lie in the domain of the
level sets of the old class, with a neighbourhood).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Matrix Filter Topology

section Main

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ eps pp : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

variable {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} {P : Consts}
  {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}

/-- **The transported `Φ₁` agrees with `Φ₁` near the points of the path**, if the old composed pairs
of the shifted data and their transports lie in the domain of the level sets for all shifts near
the point (`Phi1H_sym` at each such shift). -/
theorem phi_eventuallyEq_of_dom (C : StepClass d L N₁ m₁ k N ϱ)
    (Sy : LatSymm S.G' S.G' σ)
    (Sk : LatSymm (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) σ) (hU : UnitBlockPres σ)
    (hcl : SFTermClauses P Dom C.Tm) (hm : P.m₀ = C.m₀)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (D : BgData S.G' N) {w₀ : S.EC}
    (hdom : ∀ᶠ w in 𝓝 w₀, ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2 ∧
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1)
        (actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2))
    (hdom0 : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).2 ∧
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).1)
        (actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).2)) :
    (S.withDatumH D).Phi1H C =ᶠ[𝓝 w₀]
      fun w => (S.withDatumH (Sy.sym D)).Phi1H C
        (fun r => w ((unitAct S.G' Sy hU).symm r.1, r.2)) := by
  filter_upwards [hdom] with w hw
  have hc : ∀ (E : BgData (stepG d L N₁ m₁ k ϱ) N) (j : ℕ), 1 ≤ j → j ≤ k →
      composedPairAtC S.a S.ν (Nat.le_succ k) j (Sk.sym E) =
        (actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j E).1,
          actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j E).2) :=
    fun E j hj1 hjk => composedPairAtC_sym (a := S.a) (ν := S.ν) hσ Sk hj1 hjk E
  refine (Phi1H_sym C Sy Sk hU hcl hm hσ D w (fun j hj hjk => (hw j hj hjk).1)
    (fun j hj hjk => ?_) (fun j hj hjk => (hdom0 j hj hjk).1) (fun j hj hjk => ?_)).symm
  · obtain ⟨hj1, hjk'⟩ := Finset.mem_Icc.1 hj
    rw [hc _ j hj1 hjk']
    exact (hw j hj hjk).2
  · obtain ⟨hj1, hjk'⟩ := Finset.mem_Icc.1 hj
    rw [hc _ j hj1 hjk']
    exact (hdom0 j hj hjk).2

variable (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- **`hDzfull` for the step density `densE0`** (the covariance of `𝒟 = ℰ₀^{(k+1)}` under the full
level group `fullJSymGroup L (k + 1)`, in the exact form of `localClass_newLevel_of_expansion_cast`,
for the step whose generating set is `levelGS (k + 1)` and `P.eps d L (k + 1) ≤ eps`).

The proof reduces, at the cut-off datum `D` of the chart, to the covariance of `E0locH`
(`E0locH_sym`): the covariance of the background field, of the decoupled square root and logarithm
(through the principal root and logarithm of `𝒜`, which involves no cover), of the interaction
`V^{(k)}`, of the hat measure `ν_{p₁}` and of the old energy.  The old covariance (clause `eucEloc` of
`hcl`) holds on the domain of the level sets only; `hdom` says that the old composed pairs of the
shifted data `ψ^{(k)}(D) + w`, and their transports, lie in that domain for all `w` near the points
`s β_k^{-1/2} C^{(k)1/2} ψ̂`, `‖ψ̂‖ < p₁`, of the interpolation path (`OldXiDomC` of
`GeneralClassPathAnalytic`, with openness, for a datum of any field). -/
theorem densE0_fullJSymGroup (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hcl : SFTermClauses P Dom C.Tm) (hm : P.m₀ = C.m₀)
    (hdom : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)),
        ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2 ∧
        Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (actField r (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1)
          (actField r (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2))
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    (hε : P.eps d L (k + 1) ≤ eps) :
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2 →
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Jr.densE0 C (r y) (actField r q.1, actField r q.2) = Jr.densE0 C y q := by
  intro r hr y q hq hrq
  obtain ⟨Sy⟩ := nonempty_latSymm_of_isLevel (G := S.G') S.hG' (n := k + 1) (j := k + 1)
    le_rfl le_rfl hr
  obtain ⟨Sk⟩ := nonempty_latSymm_of_isLevel (G := stepG d L N₁ m₁ k ϱ) S.hG (n := k)
    (j := k + 1) (Nat.le_succ k) le_rfl hr
  have hU := unitBlockPres_of_fullJ hr
  have hq' : XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 := by
    rw [hG]; exact hq
  obtain ⟨D, hD, hcq⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq'
  have hD' := xiCData_sym_pair Sy hD
  have hcq' : clipRaw S.G' (actField r q.1, actField r q.2) = rawOf (Sy.sym D) := by
    rw [clipRaw_act_pair Sy q, hcq, rawOf_sym_pair Sy D]
  rw [Jr.densE0_eq C hC hMX hdm hα hsm hβ hp₁ hle hD (hE D hD) hcq y,
    Jr.densE0_eq C hC hMX hdm hα hsm hβ hp₁ hle hD' (hE _ hD') hcq' (r y)]
  have hz := mem_blockU_unitAct Sy hU y
  refine E0locH_sym Sy hU C hC hMX hdm hα hsm hp₁ hD hz (fun s hs x hx => ?_)
  refine phi_eventuallyEq_of_dom C Sy Sk hU hcl hm hr D (hdom D hD r hr s hs x hx) ?_
  have h0 := (hdom D hD r hr 0 ⟨le_rfl, zero_le_one⟩ 0 (by simpa using hp₁)).self_of_nhds
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
  exact h0

end Main

end Balaban.Inhabited.StepSym
