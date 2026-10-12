/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepTaylorComplex
import Mathlib.Tactic.Linarith

/-!
# The base-datum domain of the ray identities is a consequence of Theorem 7.3

HAT-RATE §2 asks that the old-spin datum at the critical point lie in the union domain with the
smaller radius `bgC2` (needed by `theorem72_linearResponse`).  This is not an extra premise: the
datum is the composition of `θ` through its background (`dataU_psi0`), and BG Theorem 7.3
(`theorem73_complex_small`) places a composed datum of `𝒟(𝔹'_k)` with radius `thm73C2` in `𝒟(𝔹_k)`
with radius `bgC2`.

Constants: `thm73C3 ≤ thm73C2 ≤ thm73C1` and `bgC2 ≤ bgC1`; `thm73C2 = bgC2 / (2 C₄ K₁)`.  The
landed `RayData` hypothesis `δ' ≤ thm73C3 / 2` already implies `δ' ≤ thm73C2`, so no extra
smallness is needed.

* `baseDomain_of_rayData`: `hbase` under `RayData`.
* `Vk_ray_vanish`, `Vk_ray_taylor`, `completeW_taylor`: the ray identities without `hbase`.
* `baseDomainC_of_chart`, `VkC_ray_vanish`, `VkC_ray_taylor`: the complex chart.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology Asymptotics

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}

/-- **The base-datum domain of HAT-RATE §2 from Theorem 7.3.**  Under `RayData` the datum
`dataU ψ^{(k)}(θ)` lies in `𝒟(𝔹_k)` with radius `bgC2`. -/
theorem baseDomain_of_rayData (R : S.RayData pp) :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν (S.dataU S.psi0) := by
  obtain ⟨-, hDC⟩ := S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R
  have h := theorem73_complex_small R.ha₁ R.H R.H (S.hG.precedes S.hG' (le_refl (k + 1))) hDC
  rw [S.dataU_psi0 R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R, ← S.psiKdC_eq R.H R.hδ'0 R.hδ' R.hD'R]
  exact h

/-- **Order of vanishing along the ray** (HAT-RATE §2), from `RayData` alone. -/
theorem Vk_ray_vanish (R : S.RayData pp) (x : S.E) :
    S.Vk (S.psiAt 0 x) = 0 ∧ deriv (fun s : ℝ => S.Vk (S.psiAt s x)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => S.Vk (S.psiAt s x))) 0 = 0 :=
  Vk_ray_vanish_of_baseDomain R (baseDomain_of_rayData R) x

/-- **The Taylor remainder along the ray** (HAT-RATE §2 (2.3)), from `RayData` alone. -/
theorem Vk_ray_taylor (R : S.RayData pp) (hlt : S.p₁ < pp) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    S.Vk (S.psiAt s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.Vk (S.psiAt r x)) (u * s)) :=
  Vk_ray_taylor_of_baseDomain R hlt (baseDomain_of_rayData R) hx hs

/-- **The exact identity (2.6)** from `RayData`, `StepTermsAnalytic` and `RayInDomain`. -/
theorem completeW_taylor (C : StepClass d L N₁ m₁ k N ϱ) {g : Fld d L N₁ m₁ (k + 1) N}
    {A : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ} (R : S.RayData pp) (hT : StepTermsAnalytic C A μ ε)
    (hD : S.RayInDomain C g A μ ε pp) (hlt : S.p₁ < pp) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    completeW C g s t x = S.Wone C s x + S.Wtwo C g t x :=
  completeW_taylor_of_baseDomain C R hT hD hlt (baseDomain_of_rayData R) hx hs ht

/-! ### The complex chart -/

/-- **The complex base datum from the chart of `θ`** (BG Theorem 7.3, complex data): if `θ` lies in
`𝒟(𝔹'_k)` with radius `thm73C2`, then `dataUC ψ⁰_C` lies in `𝒟(𝔹_k)` with radius `bgC2`. -/
theorem baseDomainC_of_chart (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D') :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν (S.dataUC S.psi0C) := by
  rw [S.dataUC_psi0C]
  exact theorem73_complex_small ha₁ H H (S.hG.precedes S.hG' (le_refl (k + 1))) hD2

/-- Complex ray, order of vanishing, from the chart hypothesis. -/
theorem VkC_ray_vanish (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D') (x : S.E)
    (hray0 : ∀ᶠ s : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N)
      S.ν (S.dataUC (S.psiAtC s x))) :
    S.VkC (S.psiAtC 0 x) = 0 ∧ deriv (fun s : ℝ => S.VkC (S.psiAtC s x)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => S.VkC (S.psiAtC s x))) 0 = 0 :=
  S.VkC_ray_vanish_of_baseDomain ha₁ H hD2 (S.baseDomainC_of_chart ha₁ H hD2) x hray0

/-- Complex ray, cubic Taylor remainder, from the chart hypothesis. -/
theorem VkC_ray_taylor (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D') (x : S.E)
    (hray : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtC s x))) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    S.VkC (S.psiAtC s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtC r x)) (u * s)) :=
  S.VkC_ray_taylor_of_baseDomain ha₁ H hD2 (S.baseDomainC_of_chart ha₁ H hD2) x hray hs

end StepSetting

/-! ### Non-vacuity -/

open Balaban Balaban.Inhabited Balaban.Localization.I5Inhabited in
/-- **Non-vacuity.**  At the witness step of `exists_witness_rayInDomain`, `RayData` holds, hence
`baseDomain_of_rayData` applies (no extra smallness: the witness `δ'` satisfies
`δ' ≤ thm73C3 / 2`, part of `RayData`), and the unconditional identities hold. -/
theorem Vk_ray_taylor_unconditional_witness :
    ∃ (m₁ : ℕ) (β δ : ℝ), 0 < β ∧ Nonempty ((witnessSetting m₁ β δ).RayData 2) ∧
      InUnionDomainC (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (bgC0 3 3 2) (bgC2 3 3 2)
        (witnessSetting m₁ β δ).ν
        ((witnessSetting m₁ β δ).dataU (witnessSetting m₁ β δ).psi0) ∧
      ∀ x : (witnessSetting m₁ β δ).E,
        (witnessSetting m₁ β δ).Vk ((witnessSetting m₁ β δ).psiAt 0 x) = 0 ∧
        deriv (fun s : ℝ => (witnessSetting m₁ β δ).Vk ((witnessSetting m₁ β δ).psiAt s x)) 0
          = 0 := by
  obtain ⟨m₁, β, δ, hβ, -, -, ⟨R⟩, -⟩ := exists_witness_rayInDomain
  exact ⟨m₁, β, δ, hβ, ⟨R⟩, StepSetting.baseDomain_of_rayData R, fun x =>
    ⟨(StepSetting.Vk_ray_vanish R x).1, (StepSetting.Vk_ray_vanish R x).2.1⟩⟩

end Balaban.Fluctuation
