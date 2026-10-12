/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionBridge
public import Balaban.Fluctuation.InteractionPoly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential part of the localized interaction (FLUCTUATION §3.3, Proposition 3.3, `V`-part)

`interactionOne` is the interaction potential `V^{(k)}(ψ')` of Lemma 2.3 (b) as a function of the
raw data `Θ` and the tangent `ψ'`.  `vpart_locInt` proves that the potential part of (3.3),
`σ ∫₀¹ ω(t') V'''(σ t' x₀)[w]³ dt'`, is a localized expansion over the domains `Y ⊃ X₁`: the third
derivative of `V` equals that of the energy of the decoupled fluctuation (`interactionV_eq_energy`:
the difference is the quadratic form `½⟨ψ', Δ^{(k)} ψ'⟩`), whose block energies are expanded by
`vblocks_locInt`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section VPart

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {ν : ℝ}

open Classical in
/-- **The interaction potential `V^{(k)}(ψ')` as a function of the raw data and the tangent**
(`0` for unrealizable data).  `Θ = rawOf D'`, `D'` the datum of level `n+1`; `ψ'` the tangent
`D.Ψ - ψ^{(k)}` of a datum `D` of level `n` with the same `h̃`. -/
noncomputable def interactionOne (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K)
    (a₁ ν eps : ℝ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  if h : ∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' ∧ u.1 = rawOf D' then
    if h2 : ∃ D : BgData Hm N, (∀ x i, D.h x i = h.choose.h x i) ∧
        compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose D = u.2 then
      interactionV (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) u.2
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) h2.choose -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose))
    else 0
  else 0

theorem interactionOne_eq (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K)
    {a₁ ν eps : ℝ} {D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D')
    {D : BgData Hm N} (hh : ∀ x i, D.h x i = D'.h x i) :
    interactionOne hG hG' hp a₁ ν eps (rawOf D', compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D) =
      interactionV (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')
        (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D)
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) := by
  classical
  have h : ∃ D'' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D'' ∧ rawOf D' = rawOf D'' :=
    ⟨D', hD, rfl⟩
  have e1 : h.choose = D' := (BgData.eq_of_raw h.choose_spec.2).symm
  have h2 : ∃ D₂ : BgData Hm N, (∀ x i, D₂.h x i = h.choose.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose D₂ =
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D := by
    rw [e1]; exact ⟨D, hh, rfl⟩
  unfold interactionOne
  simp only [h, h2, dite_true]
  have e2 : h2.choose = D := by
    obtain ⟨hh2, ht2⟩ := h2.choose_spec
    have e3 : composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose) h.choose =
        composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' := by rw [e1]
    have hΨ : h2.choose.Ψ = D.Ψ := by
      funext x i
      have := congrFun (congrFun ht2 x) i
      simp only [compTangent, e3] at this
      linear_combination this
    have hhh : h2.choose.h = D.h := by
      funext x i; rw [hh2 x i, hh x i, e1]
    exact BgData.eq_of_raw (Prod.ext hΨ hhh)
  have key : ∀ (A : BgData Gp N) (B : BgData Hm N), A = D' → B = D →
      interactionV (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) A)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) A)
        (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D)
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) B -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) A)) =
      interactionV (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')
        (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D)
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) := by
    rintro A B rfl rfl; rfl
  exact key _ _ e1 e2

theorem isLayerConstant_line {z w : CTorus d L N₁ m₁ K → Fin N → ℂ} (hz : IsLayerConstant Hm z)
    (hw : IsLayerConstant Hm w) (τ : ℂ) : IsLayerConstant Hm (z + τ • w) := by
  intro m h1 h2 x hx x' hx'
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hz m h1 h2 x hx x' hx', hw m h1 h2 x hx x' hx']

theorem isLayerConstant_smul {z : CTorus d L N₁ m₁ K → Fin N → ℂ} (hz : IsLayerConstant Hm z)
    (c : ℂ) : IsLayerConstant Hm (c • z) := by
  intro m h1 h2 x hx x' hx'
  simp only [Pi.smul_apply]
  rw [hz m h1 h2 x hx x' hx']

variable {a₁ c BG κ eps Kc' Cx' c₂ BG₂ δ₁ : ℝ}

/-- **The third derivative of `V^{(k)}` along a line is that of the block energies.** -/
theorem dirS3_interactionOne (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D')
    (hreal : ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {z0 w : CTorus d L N₁ m₁ K → Fin N → ℂ} (hz0 : IsLayerConstant Hm z0)
    (hw : IsLayerConstant Hm w) {r : ℝ} (hr : 0 < r)
    (hline : ∀ τ : ℂ, ‖τ‖ < r → z0 + τ • w ∈ FlBall Hm δ₁)
    (hsmooth : ∀ z, ContDiffAt ℂ 3 (fun τ : ℂ => blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z
      (rawOf D', z0 + τ • w)) 0) :
    dirS3 (interactionOne hG hG' hp a₁ ν eps) w (rawOf D') z0 =
      ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
        dirS3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) w (rawOf D') z0 := by
  classical
  obtain ⟨c0, c1, c2, hq⟩ := deltaForm_line (hG.precedes hG' hp) (compWeight L a₁) ν
    (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
    (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') z0 w
  have heq : ∀ τ : ℂ, ‖τ‖ < r → interactionOne hG hG' hp a₁ ν eps (rawOf D', z0 + τ • w) =
      (∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
        blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w)) -
        (1 / 2) * (c0 + c1 * τ + c2 * τ ^ 2) := by
    intro τ hτ
    obtain ⟨D, hh, hD2, hdisc⟩ := hreal _ (hline τ hτ)
      (isLayerConstant_line hz0 hw τ)
    have hψ : compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D ∈ FlBall Hm δ₁ := by
      rw [hD2]; exact hline τ hτ
    rw [← hD2, interactionOne_eq hG hG' hp hD hh,
      interactionV_eq_energy hC hG hG' hp ha₁ H D' hD hc7 D hh hψ hR hdisc hRs hsmall hnum hnum']
    congr 1
    · exact Finset.sum_congr rfl fun z _ => by
        rw [blockEnergyOne_rawOf hD n z]
    · rw [hD2, ← hq τ]
      rfl
  have hev : (fun τ : ℂ => interactionOne hG hG' hp a₁ ν eps (rawOf D', z0 + τ • w)) =ᶠ[nhds 0]
      fun τ => (∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
        blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w)) -
        (1 / 2) * (c0 + c1 * τ + c2 * τ ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ using heq τ (by simpa using hτ)
  unfold dirS3
  rw [hev.iteratedDeriv_eq]
  have hcdS : ContDiffAt ℂ 3 (fun τ : ℂ => ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
      blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w)) 0 := by
    have := ContDiffAt.sum (𝕜 := ℂ) (s := (Finset.univ : Finset (Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))))
      (f := fun z τ => blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w))
      (x := (0 : ℂ)) (n := 3) (fun z _ => hsmooth z)
    simpa using this
  have hcdP : ContDiffAt ℂ 3 (fun τ : ℂ => (1 / 2 : ℂ) * (c0 + c1 * τ + c2 * τ ^ 2)) 0 := by
    fun_prop
  rw [iteratedDeriv_fun_sub hcdS hcdP, iteratedDeriv_const_mul_field, iteratedDeriv_quad]
  have hsum := iteratedDeriv_sum (𝕜 := ℂ) (I := (Finset.univ : Finset (Torus d (N₁ * L ^ m₁ *
    L ^ (K - (n + 1)))))) (n := 3) (x := (0 : ℂ))
    (f := fun z τ => blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w))
    (fun z _ => hsmooth z)
  have e : (fun τ : ℂ => ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
      blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w)) =
      ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
        fun τ : ℂ => blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D', z0 + τ • w) := by
    funext τ; simp [Finset.sum_apply]
  rw [e, hsum]
  simp

/-- **The potential part of the localized interaction** (Proposition 3.3, the `V`-part): for the
exact interaction potential `V^{(k)}` of Lemma 2.3 (b), `σ ∫₀¹ ω(t') V'''(σ t' x₀)[w]³ dt'` is a
localized expansion over the domains `Y ⊃ X₁`, with the bound
`|σ| M_ω 6 E e^{-2 κ d̃^{cov}_{k+1}(Y)} / r³`.  The directions `x₀, w` are layer-constant. -/
theorem vpart_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ j : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcov : ∀ z, CovSetup Gp (m₀ z) (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀ z) (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne (m₀ z) (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L (m₀ z) m₁ (j z)) E₀ = treeLenCovOne (m₀ z) (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne (m₀ z) (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hZ : ∀ z, readSites Hm n z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z) (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ 𝒴 z then T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => raySrc3 (interactionOne hG hG' hp a₁ ν eps) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ 𝒴 z then Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨𝒴, T, hL⟩ := vblocks_locInt hC hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog hn1
    hp hZ hmar hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
  have hex : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
    intro z
    obtain ⟨Ev, h1', -, -, h4'⟩ := vblock_expansion hC (hcov z) (hX₁ z) hconn hrow (hopt z) (hΔ z)
      hκ₀ hκdec hκ h1 (hlog z) hn1 hp z (hZ z) (hmar z)
    exact ⟨Ev, h1', h4'⟩
  choose Ev hEvsum hEvan using hex
  refine ⟨𝒴, T, (hL.mono_XW (fun xw hxw => hxw.1)).congr_val ?_⟩
  rintro ⟨x₀, w⟩ ⟨hxw, hx0, hw⟩ σ hσ Θ ⟨D', hD, rfl⟩
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hdisc : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ FlBall Hm δ₁ := fun t ht τ hτ => hxw σ hσ t (hreal1 t ht) τ hτ
  have hint : ∀ z, IntervalIntegrable (fun t : ℝ => ω (t : ℂ) * dirS3
      (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) w (rawOf D') ((σ * (t : ℂ)) • x₀))
      MeasureTheory.volume 0 1 := by
    intro z
    refine raySrc3_intervalIntegrable (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      (B := FlBall Hm δ₁)
      (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
        (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z))) (Evs := Ev z) (fun Y => hEvan z Y) ?_ hωc
      ⟨D', hD, rfl⟩ hr hdisc
    intro Θ hΘ ψ' hψ
    obtain ⟨D'', hD'', rfl⟩ := hΘ
    rw [blockEnergyOne_rawOf hD'']
    exact hEvsum z D'' hD'' ψ' hψ
  unfold raySrc3
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun z _ => hint z)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only
  rw [← Finset.mul_sum]
  congr 1
  refine dirS3_interactionOne hC hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum' hD
    (hreal D' hD) (isLayerConstant_smul hx0 _) hw hr (fun τ hτ => hdisc t ht τ hτ.le) ?_
  intro z
  refine contDiffAt_line_of_sum (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
      (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z))) (Evs := Ev z) (fun Y => hEvan z Y) ?_ ⟨D', hD, rfl⟩ hr (fun τ hτ => hdisc t ht τ hτ)
  intro Θ hΘ ψ' hψ
  obtain ⟨D'', hD'', rfl⟩ := hΘ
  rw [blockEnergyOne_rawOf hD'']
  exact hEvsum z D'' hD'' ψ' hψ

end VPart

end Balaban.Localization
