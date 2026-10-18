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

`xiDom_act_iff`: the domain `Ξ^c_j(𝔹; 1, ε)` is covariant under lattice symmetries.
`phi_eventuallyEq_of_dom`: the transported `Φ₁` agrees with `Φ₁` near a point of the interpolation
path as soon as the old composed pairs of the shifted data lie in the domain of the level sets for
all shifts near the point.

Input beyond the landed premises of `densE0_eq`: the old class (clause `eucEloc`, `SFTermClauses`)
and the domain statement `hdom` (the old composed pairs along the interpolation path lie in the
domain of the level sets of the old class, with a neighbourhood).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Matrix Filter Topology

section XiAct

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}

/-- **The domain `Ξ^c_j(𝔹; 1, ε)` of the terms is covariant under a lattice symmetry**:
`(σ Ψ, σ h)` lies in the domain of `𝔹'` iff `(Ψ, h)` lies in the domain of `𝔹`. -/
theorem xiDom_act_iff (S : LatSymm G G' σ) {a : ℕ → ℝ} {ν ε : ℝ} {j : ℕ}
    (Ψ h : Fld d L N₁ m₁ K N) :
    XiDom G' a ν j ε (actField σ Ψ) (actField σ h) ↔ XiDom G a ν j ε Ψ h := by
  constructor
  · rintro ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hX⟩
    refine ⟨fun y => Ψ₀ (σ y), h₀, fun y => Ψ'' (σ y), fun y => h'' (σ y), fun x i => ?_,
      fun x i => ?_, ?_⟩
    · have := hΨ (σ x) i
      simpa [actField] using this
    · have := hh (σ x) i
      simpa [actField] using this
    · refine (xiC_sym_iff S a ν).1 ?_
      simpa using hX
  · rintro ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hX⟩
    refine ⟨fun y => Ψ₀ (σ.symm y), h₀, fun y => Ψ'' (σ.symm y), fun y => h'' (σ.symm y),
      fun x i => ?_, fun x i => ?_, xiC_sym S a ν hX⟩
    · simpa [actField] using hΨ (σ.symm x) i
    · simpa [actField] using hh (σ.symm x) i

end XiAct

section Main

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ eps pp : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

variable {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} {P : Consts}
  {a' : ℕ → ℝ} {μ' : ℝ} {ε' : ℕ → ℝ}

/-- The domain of the level sets is covariant under the full group, for the landed domains. -/
theorem xiFieldDom_act_levelGS (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L
      (k + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (Ψ h : Fld d L N₁ m₁ (k + 1) N) :
    (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (actField σ Ψ) (actField σ h) ↔
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) Ψ h := by
  obtain ⟨Sj⟩ := nonempty_latSymm_of_isLevel (G := levelGS (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j hjk) (isLevel_levelGS hj1 hjk) (n := j) (j := k + 1)
    hjk le_rfl hσ
  exact xiDom_act_iff Sj Ψ h

/-- **The transported `Φ₁` agrees with `Φ₁` near the points of the path**, if the old composed pairs
of the shifted data lie in the domain of the level sets of the old class for all shifts near the
point (`Phi1H_sym` at each such shift; the transports lie in the domain by its covariance). -/
theorem phi_eventuallyEq_of_dom (C : StepClass d L N₁ m₁ k N ϱ)
    (Sy : LatSymm S.G' S.G' σ)
    (Sk : LatSymm (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) σ) (hU : UnitBlockPres σ)
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) C.Tm)
    (hm : P.m₀ = C.m₀)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (D : BgData S.G' N) {w₀ : S.EC}
    (hdom : ∀ᶠ w in 𝓝 w₀, ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2)
    (hdom0 : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatumH D).dataUCH (S.withDatumH D).psi0H)).2) :
    (S.withDatumH D).Phi1H C =ᶠ[𝓝 w₀]
      fun w => (S.withDatumH (Sy.sym D)).Phi1H C
        (fun r => w ((unitAct S.G' Sy hU).symm r.1, r.2)) := by
  filter_upwards [hdom] with w hw
  have hc : ∀ (E : BgData (stepG d L N₁ m₁ k ϱ) N) (j : ℕ), 1 ≤ j → j ≤ k →
      composedPairAtC S.a S.ν (Nat.le_succ k) j (Sk.sym E) =
        (actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j E).1,
          actField σ (composedPairAtC S.a S.ν (Nat.le_succ k) j E).2) :=
    fun E j hj1 hjk => composedPairAtC_sym (a := S.a) (ν := S.ν) hσ Sk hj1 hjk E
  refine (Phi1H_sym C Sy Sk hU hcl hm hσ D w (fun j hj hjk => hw j hj hjk)
    (fun j hj hjk => ?_) hdom0 (fun j hj hjk => ?_)).symm
  · obtain ⟨hj1, hjk'⟩ := Finset.mem_Icc.1 hj
    rw [hc _ j hj1 hjk']
    exact (xiFieldDom_act_levelGS hσ hj1 hjk _ _).2 (hw j hj hjk)
  · obtain ⟨hj1, hjk'⟩ := Finset.mem_Icc.1 hj
    rw [hc _ j hj1 hjk']
    exact (xiFieldDom_act_levelGS hσ hj1 hjk _ _).2 (hdom0 j hj hjk)

variable (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- **`hDzfull` for the step density** (the covariance of `𝒟 = ℰ₀^{(k+1)}` under the full
level group `fullJSymGroup L (k + 1)`, in the exact form of `localClass_newLevel_of_expansion_cast`,
for the step whose generating set is `levelGS (k + 1)` and `P.eps d L (k + 1) ≤ eps`).

The proof reduces, at the cut-off datum `D` of the chart, to the covariance of `E0locH`
(`E0locH_sym`): the covariance of the background field, of the decoupled square root and logarithm
(through the principal root and logarithm of `𝒜`, which involves no cover), of the interaction
`V^{(k)}`, of the hat measure `ν_{p₁}` and of the old energy.  The old covariance (clause `eucEloc` of
`hcl`, a premise on the old class) holds on the domain `Ξ^c_j(𝔹_j; 1, ε'_j)` of the level sets
only; `hdom` says that the old composed pairs of the shifted data `ψ^{(k)}(D) + w`, for all `w` near
the points `s β_k^{-1/2} C^{(k)1/2} ψ̂`, `‖ψ̂‖ < p₁`, of the interpolation path, lie in that domain
(the open `OldXiDomC` of `GeneralClassPathAnalytic`, with a neighbourhood, for a datum with any field); their
transports lie in it by the covariance of the domain (`xiDom_act_iff`). -/
theorem densE0_fullJSymGroup (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) C.Tm)
    (hm : P.m₀ = C.m₀)
    (hdom : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)),
        ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2)
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
  refine phi_eventuallyEq_of_dom C Sy Sk hU hcl hm hr D (hdom D hD s hs x hx) ?_
  have h0 := (hdom D hD 0 ⟨le_rfl, zero_le_one⟩ 0 (by simpa using hp₁)).self_of_nhds
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
  exact h0

end Main

end Balaban.Inhabited.StepSym
