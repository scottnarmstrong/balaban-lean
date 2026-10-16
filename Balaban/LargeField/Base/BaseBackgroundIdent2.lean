/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBackgroundIdent

/-!
# The first step's sector data meet the smallness of the decoupled identification

`c₇ d L N BG κ ≤ bgC1 d L N` (`c7_le_bgC1`), so the first step's good-region radius `δ₀`
(the datum lies in `Ψ̃(4 d L δ₀)`) is admissible for the identification of the first step's
background with the level-one decoupled one as soon as `4 d L δ₀ ≤ c₇`.  Here `δ₀` is the free
small parameter of the cube test; no landed first-step result fixes it beyond `4 d L δ₀ ≤ bgC1`.
The torus `1 * n` of `baseSectorDatum` is identified with `N₁ L^{m₁}` for `n = N₁ L^{m₁}`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

open Classical in
/-- **The first step's sector data meet the smallness `δ ≤ c₇`.**  If the radius satisfies
`4 d L δ₀ ≤ c₇ d L N BG κ`, every coarse field with a passing cube product has its lifted datum in
the real domain `Ψ̃(δ)` with `δ = 4 d L δ₀ ≤ c₇`. -/
theorem baseSectorDatum_inDomainR_c7 {d N L n : ℕ} [NeZero L] [NeZero n]
    (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0)) (BG κ : ℝ)
    (hΛ7 : 4 * d * L * δ₀ ≤ c7 d L N BG κ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    InDomainR (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
      (if regimeB then ν else 0) (4 * d * L * δ₀) (baseSectorDatum ϱ θ h) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N := hΛ7.trans (c7_le_bgC1 d L N BG κ)
  have hsmall : 4 * d * L * δ₀ ≤ 1 / 1024 :=
    (approxDelta_le d L (bgC1_facts d L N hd0 hΛ1).1).1
  exact inDomainR_base H (baseSectorSpinSupport_of_product_ne_zero ϱ regimeB ν δ₀ hδ h hh θ φ hp)
    hsmall

section Transport

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L]

/-- The data types over `single` at equal base sides are equal. -/
theorem bgData_single_eq {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (e : N₀ = N₀') (ϱ : ℝ) :
    BgData (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ) N =
      BgData (GeneratingSet.single (d := d) (L := L) (N₀ := N₀') (k := 1) ϱ) N := by
  subst e
  rfl

/-- The real domain `Ψ̃(δ)` is transported along an equality of base sides. -/
theorem inDomainR_cast {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (e : N₀ = N₀') {ϱ ν δ : ℝ}
    {D : BgData (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ) N}
    (hD : InDomainR (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ) ν δ D) :
    InDomainR (GeneratingSet.single (d := d) (L := L) (N₀ := N₀') (k := 1) ϱ) ν δ
      (cast (bgData_single_eq e ϱ) D) := by
  subst e
  exact hD

open Classical in
/-- **The first step's background is the decoupled background at `s ≡ 1`, for
`baseSectorDatum` itself.**  The datum `baseSectorDatum` lives on the torus `1 * n`; for
`n = N₁ L^{m₁}` it is carried to the step torus `N₁ L^{m₁}` by the equality `1 * n = N₁ L^{m₁}`
(`cast`), and for a coarse field `θ` with a passing cube product and `4 d L δ₀ ≤ c₇` the real
minimizer `(bgField, bgMult)` of the transported datum solves `Dec2.IsDecBg` of the cover at
`s ≡ 1`. -/
theorem baseSectorDatum_decBg_one {n : ℕ} [NeZero n] (e : 1 * n = N₁ * L ^ m₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN₁ : 5 < N₁)
    (regimeB : Prop) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ 2 ≤ 1) (δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c BG) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hΛ7 : 4 * d * L * δ₀ ≤ c7 d L N BG κ)
    (hνB : (if regimeB then ν else 0) = ν)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    let D : BgData (GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1)
        (Inhabited.LevelStep.rhoSepG d L m₁)) N :=
      cast (bgData_single_eq e _) (baseSectorDatum (Inhabited.LevelStep.rhoSepG d L m₁) θ h)
    Dec2.IsDecBg (coverOf (GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1)
      (Inhabited.LevelStep.rhoSepG d L m₁))) (GeneratingSet.single (d := d) (L := L)
      (N₀ := N₁ * L ^ m₁) (k := 1) (Inhabited.LevelStep.rhoSepG d L m₁)) (compWeight L 1) ν
      (rho4 d L N BG κ) (fun _ => 1) D
      (bgField _ (compWeight L 1) ν D) (bgMult _ (compWeight L 1) ν D) := by
  intro D
  have HB : BgHyp d L 1 (Inhabited.LevelStep.rhoSepG d L m₁) (compWeight L 1)
      (if regimeB then ν else 0) := by
    rw [hνB]
    exact Inhabited.LevelStep.bgHyp_lvG (k := 0) hd hL
      (Inhabited.LevelStep.bgR0_le_rhoSepG m₁ hd hL) hν0 (by simpa using hν)
  have hD := baseSectorDatum_inDomainR_c7 (Inhabited.LevelStep.rhoSepG d L m₁) (compWeight L 1)
    regimeB ν δ₀ hδ h hh HB BG κ hΛ7 θ φ hp
  rw [hνB] at hD
  have hδ0 : 0 < 4 * (d : ℝ) * L * δ₀ := by
    have : 0 < d := by omega
    positivity
  exact baseSingle_decBg_one hd hL hM hN₁ hν0 hν hS hκ hMκ hδ0 hΛ7 (inDomainR_cast e hD)

end Transport

end Balaban.LargeField.Base
