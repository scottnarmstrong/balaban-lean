/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatRay
public import Balaban.Fluctuation.StepTaylor
public import Balaban.Fluctuation.StepComplexAgree
public import Balaban.Fluctuation.StepIdentityInhabited
public import Balaban.Fluctuation.HatLabelsDm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential part of the step exponent is the value of the hat expansion

`interaction_expansion_hat` expands, at the lifted field `hatC x` and the parameter `σ = u`, the
value `val` whose potential part is
`-c_β · u ∫₀¹ (1-t)²/2 · ∂³_τ f(Θ, (u t + τ) ψ̂)|_{τ=0} dt`
with `f = hatFun … (interactionOne …)`, `ψ̂ = hatC x`.  The `u`-ray of the hat variable is the
interpolation `s ψ̂` of the step; since `V^{(k)}(ψ^{(k)} + s ψ')` has vanishing 2-jet at `s = 0`
(`Vk_ray_vanish_of_baseDomain`), Taylor's formula identifies the integral:

`s² · (-β) · raySrc3 f taylorWeight ψ̂ ψ̂ s Θ = -β · V^{(k)}(ψ^{(k)} + s ψ') = W₁(s, ψ̂)`

for the zero class (no old energy), `s ∈ [0,1]` and `ψ̂` in the support of `ν_{p₁}`
(`Wone_zeroClass_eq_hat`).  The extra factor `s²` is the difference between the remainder
`σ ∫ (1-t)²/2 V'''` (weight `σ`) and the Taylor remainder `σ³ ∫ (1-t)²/2 V'''`.

All statements are for the landed (real) `Wone`; they use the real chart block of
`StepComplexAgree` (the substitution `shiftUC = ↑shiftU`), so they hold at a real block datum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ} {pp : ℝ}

/-- For the zero class (no old energy term) `W₁(s, ψ̂) = -β V^{(k)}(ψ^{(k)} + s ψ')`. -/
theorem Wone_zeroClass_eq (s : ℝ) (x : S.E) :
    S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x = -(S.β : ℂ) * S.Vk (S.psiAt s x) := by
  have h0 : ∀ D, EcompAt (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
      (Nat.le_succ k) D = 0 := fun D => EcompAt_zero _ _ _ _ _
  unfold Wone dE
  rw [h0, h0]
  ring

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (R0 : S.RayData pp) (hlt : S.p₁ < pp)
  (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν (S.dataU S.psi0))
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hp₁ : 0 < S.p₁) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hpc : S.p₁ < cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

include hC R0 hlt hbase hD hc7 hR hsmR hMX hdm hα hsm hp₁ hcψ hpc hδ₁ in
/-- **T1: the potential part of the step exponent is the value of the hat expansion.**
For the zero class, `s ∈ [0,1]` and `ψ̂` in the support of `ν_{p₁}` (`χ_fl(ψ̂) = 1`),
`s² · ((-β) · raySrc3 (hatFun … (interactionOne …)) (1-t)²/2 ψ̂ ψ̂ s Θ) = W₁(s, ψ̂)`, with
`Θ = rawOf D'` the raw data of the block datum, `cc = β_k^{-1/2}`, and `raySrc3` the `σ`-ray
integral of the third derivative of the hat expansion (the potential part of `val`). -/
theorem Wone_zeroClass_eq_hat {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    (s : ℂ) ^ 2 * ((-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
      (S.hatC x) (s : ℂ) (rawOf S.D')) = S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R0.hχu
  have hxn : ‖x‖ ≤ S.p₁ := ((chiFl_eq_one_iff hp₁ x).1 hx).le
  set cc : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcc
  set f := interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps with hf
  let Gc : ℂ → ℂ := fun l => hatFun S.G' S.a₁ S.ν eps S.hG' cc f (rawOf S.D', l • yhat x)
  have hreal : ∀ r : ℝ, Gc (r : ℂ) = S.Vk (S.psiAt r x) := fun r => by
    show hatFun S.G' S.a₁ S.ν eps S.hG' cc f (rawOf S.D', (r : ℂ) • yhat x) = _
    rw [← S.VkC_psiAtC_eq_hatFun hD r x, S.psiAtC_eq R0.ha₁ R0.H R0.hδ'0 R0.hδ' R0.hD'R R0.hδ0 hχ
      R0.hfam R0.hsm r x, S.VkC_yhat]
  have hAn : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ Gc (r : ℂ) := by
    intro r hr
    have hb : ∀ p, ‖(r : ℂ) * yhat x p‖ < cψ := fun p => by
      have := S.norm_smul_yhat_le hp₁ hr hx p
      have e : ((r : ℂ) • yhat x) p = (r : ℂ) * yhat x p := rfl
      rw [e] at this
      exact lt_of_le_of_lt this hpc
    have := analyticAt_interactionOne_hatRay hC S.hk1 S.hG S.hG' R0.ha₁ R0.H hc7 hR hsmR hMX hdm
      hα hsm cc hcψ hδ₁ hD (yhat x) (s := (r : ℂ)) hb
    refine this.congr (Filter.Eventually.of_forall fun l => ?_)
    exact (hatFun_rawOf S.hG' cc f hD _).symm
  have hd3 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      dirS3 (hatFun S.G' S.a₁ S.ν eps S.hG' cc f) (S.hatC x) (rawOf S.D')
        (((s : ℂ) * (t : ℂ)) • S.hatC x) =
        iteratedDeriv 3 (fun r : ℝ => S.Vk (S.psiAt r x)) (s * t) := by
    intro t ht
    have hst : s * t ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hs.1 ht.1, by nlinarith [hs.1, hs.2, ht.1, ht.2]⟩
    unfold dirS3
    have e : (fun τ : ℂ => hatFun S.G' S.a₁ S.ν eps S.hG' cc f
        (rawOf S.D', ((s : ℂ) * (t : ℂ)) • S.hatC x + τ • S.hatC x)) =
        fun τ : ℂ => Gc (((s * t : ℝ) : ℂ) + τ) := by
      funext τ
      show _ = hatFun S.G' S.a₁ S.ν eps S.hG' cc f (rawOf S.D', (((s * t : ℝ) : ℂ) + τ) • yhat x)
      rw [add_smul]
      push_cast
      rfl
    rw [e]
    have h1 := congrFun (iteratedDeriv_comp_const_add 3 Gc (((s * t : ℝ)) : ℂ)) 0
    rw [h1, add_zero, ← iteratedDeriv_comp_ofReal 3 Gc (s * t) (hAn _ hst)]
    congr 1
    funext r
    exact hreal r
  have hrs : raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' cc f) taylorWeight (S.hatC x) (S.hatC x)
      (s : ℂ) (rawOf S.D') = (s : ℂ) * ∫ t in (0 : ℝ)..1, taylorWeight (t : ℂ) *
        iteratedDeriv 3 (fun r : ℝ => S.Vk (S.psiAt r x)) (s * t) := by
    unfold raySrc3
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [hd3 t ht]
  have hT := Vk_ray_taylor_of_baseDomain R0 hlt hbase hxn hs
  have hI : ∫ u in (0 : ℝ)..1, taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
      iteratedDeriv 3 (fun r : ℝ => S.Vk (S.psiAt r x)) (u * s)) =
      (s : ℂ) ^ 3 * ∫ t in (0 : ℝ)..1, taylorWeight (t : ℂ) *
        iteratedDeriv 3 (fun r : ℝ => S.Vk (S.psiAt r x)) (s * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [mul_comm u s]
    ring
  rw [S.Wone_zeroClass_eq, hrs, hT, hI]
  ring

end StepSetting

end Balaban.Fluctuation
