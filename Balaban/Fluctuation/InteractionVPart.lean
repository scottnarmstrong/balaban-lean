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
variable {n : ℕ}

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

end VPart

end Balaban.Localization
