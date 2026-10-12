/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem I-4a: the constants of the fixed point argument for a general Green family

The constants of Proposition 5.1 (`cA`, `cTau`, `c6`, `deltaStar`, `cK2` of
`Balaban/Background/Contraction.lean`) with the Green constant `greenSupConst d L` replaced by a
number `B` and the polydisc radius `γ₁` by `Γ`.  `coreHyp'_small` verifies the numerical conditions
of `CoreHyp` for `δ₀, δ₁ ≤ δ_*`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Constants

variable (d L N : ℕ) [NeZero L] (B Γ : ℝ)

/-- `τ = 1 / (15 A (B+1)²)`. -/
noncomputable def cTau' : ℝ := 1 / (15 * cA d L N * (B + 1) ^ 2)
/-- `c_N = 5 A (B+1) C_F + 5/2`. -/
noncomputable def cN' : ℝ := 5 * cA d L N * (B + 1) * cF d L + 5 / 2
/-- The radius `c₆`. -/
noncomputable def c6' : ℝ := min (Γ / 4) (2 * cTau' d L N B / 9)
/-- The smallness `δ_*`. -/
noncomputable def deltaStar' : ℝ :=
  min (min (cTau' d L N B / 3) (Γ / 4)) (min (min 1 (c6' d L N B Γ / (2 * cN' d L N B)))
    (cTau' d L N B / (3 * cF d L)))
/-- The constant `K₂`. -/
noncomputable def cK2' : ℝ := (B + 1) * (cF d L + 3 * cN' d L N B) + 2 * cN' d L N B
/-- The bound for `|𝒩(0)|₂` with the family constant `B`. -/
noncomputable def selfBound' (δ₀ Fb Gb : ℝ) : ℝ :=
  coreBound N B (commKConst d L N) (2 * d + 8) δ₀ Fb Gb

variable {d L N B Γ}

omit [NeZero L] in
theorem cTau'_pos (hB0 : 0 ≤ B) : 0 < cTau' d L N B := by
  have := Balaban.Background.cA_ge d L N
  unfold cTau'; positivity

omit [NeZero L] in
theorem cTau'_spec (hB0 : 0 ≤ B) : 15 * cA d L N * (B + 1) ^ 2 * cTau' d L N B = 1 := by
  have := Balaban.Background.cA_ge d L N
  unfold cTau'; field_simp

omit [NeZero L] in
theorem cN'_pos (hB0 : 0 ≤ B) : 0 < cN' d L N B := by
  have := Balaban.Background.cA_ge d L N; have := Balaban.Background.cF_pos d L
  unfold cN'; positivity

omit [NeZero L] in
theorem c6'_pos (hB0 : 0 ≤ B) (hΓ : 0 < Γ) : 0 < c6' d L N B Γ := by
  have := cTau'_pos (d := d) (L := L) (N := N) hB0
  unfold c6'; positivity

omit [NeZero L] in
theorem deltaStar'_pos (hB0 : 0 ≤ B) (hΓ : 0 < Γ) : 0 < deltaStar' d L N B Γ := by
  have := cTau'_pos (d := d) (L := L) (N := N) hB0
  have := c6'_pos (d := d) (L := L) (N := N) hB0 hΓ
  have := cN'_pos (d := d) (L := L) (N := N) hB0; have := Balaban.Background.cF_pos d L
  unfold deltaStar'; positivity

omit [NeZero L] in
theorem selfBound'_le (hB0 : 0 ≤ B) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N B Γ) (hδ₁ : δ₁ ≤ deltaStar' d L N B Γ) :
    selfBound' d L N B δ₀ (cF d L * δ₁) (5 * δ₁) ≤ cN' d L N B * δ₁ := by
  have hB1 : (1 : ℝ) ≤ B + 1 := by linarith
  have hτ := (cTau'_pos (d := d) (L := L) (N := N) hB0)
  have hA := Balaban.Background.cA_ge d L N
  have hcF := Balaban.Background.cF_pos d L
  have hs1 : deltaStar' d L N B Γ ≤ cTau' d L N B / 3 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hs3 : deltaStar' d L N B Γ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs5 : deltaStar' d L N B Γ ≤ cTau' d L N B / (3 * cF d L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hFb : cF d L * δ₁ ≤ cTau' d L N B / 3 := by
    have : δ₁ ≤ cTau' d L N B / (3 * cF d L) := hδ₁.trans hs5
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hFb0 : 0 ≤ cF d L * δ₁ := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hK0 : (0 : ℝ) ≤ commKConst d L N := by unfold commKConst; positivity
  have hz0 : (0 : ℝ) ≤ N * (2 * d + 8) := by positivity
  have hKA : commKConst d L N ≤ cA d L N := by unfold cA; linarith
  have hNA : (N : ℝ) ≤ cA d L N := by unfold cA; linarith
  have hzA : (N : ℝ) * (2 * d + 8) ≤ cA d L N := by unfold cA; linarith
  have hBB : B ≤ (B + 1) := by linarith
  have hBF : (B + 1) * (cF d L * δ₁) ≤ 1 := by
    have hBt : (B + 1) * cTau' d L N B ≤ 1 / 15 := by
      have h1 : 0 ≤ cA d L N * (B + 1) - 1 := by nlinarith
      have := (cTau'_spec (d := d) (L := L) (N := N) hB0)
      nlinarith [mul_nonneg h1 (mul_nonneg (by linarith : 0 ≤ (B + 1)) hτ.le)]
    nlinarith
  have hself := arith_self (A := cA d L N) (B1 := (B + 1)) (B := B)
    (Fb := cF d L * δ₁) (Gb := 5 * δ₁) (δ₀ := δ₀) (x := N) (y := commKConst d L N)
    (e := 2 * d + 8) (δ₁ := δ₁) (CF := cF d L) hA hB1 hB0 hBB hNA hKA hzA h0
    (hδ₀.trans hs3) hFb0 hBF rfl rfl
  unfold selfBound' coreBound
  unfold cN'
  exact hself

omit [NeZero L] in
theorem coreHyp'_small (hB0 : 0 ≤ B) (hΓ : 0 < Γ) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N B Γ) (hδ₁ : δ₁ ≤ deltaStar' d L N B Γ) :
    CoreHyp N B (commKConst d L N) (2 * d + 8) Γ δ₀ (cF d L * δ₁)
      (5 * δ₁) (c6' d L N B Γ) := by
  have hB1 : (1 : ℝ) ≤ B + 1 := by linarith
  have hτ := (cTau'_pos (d := d) (L := L) (N := N) hB0)
  have hA := Balaban.Background.cA_ge d L N
  have hcF := Balaban.Background.cF_pos d L
  have hcN := (cN'_pos (d := d) (L := L) (N := N) hB0)
  have hc6 := (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ)
  have hs1 : deltaStar' d L N B Γ ≤ cTau' d L N B / 3 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hs2 : deltaStar' d L N B Γ ≤ Γ / 4 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hs3 : deltaStar' d L N B Γ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs4 : deltaStar' d L N B Γ ≤ c6' d L N B Γ / (2 * cN' d L N B) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs5 : deltaStar' d L N B Γ ≤ cTau' d L N B / (3 * cF d L) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hc6a : c6' d L N B Γ ≤ Γ / 4 := min_le_left _ _
  have hc6b : c6' d L N B Γ ≤ 2 * cTau' d L N B / 9 := min_le_right _ _
  have hFb : cF d L * δ₁ ≤ cTau' d L N B / 3 := by
    have : δ₁ ≤ cTau' d L N B / (3 * cF d L) := hδ₁.trans hs5
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hFb0 : 0 ≤ cF d L * δ₁ := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hK0 : (0 : ℝ) ≤ commKConst d L N := by unfold commKConst; positivity
  have hz0 : (0 : ℝ) ≤ N * (2 * d + 8) := by positivity
  have hNA : (N : ℝ) ≤ cA d L N := by unfold cA; linarith
  have hKA : commKConst d L N ≤ cA d L N := by unfold cA; linarith
  have hzA : (N : ℝ) * (2 * d + 8) ≤ cA d L N := by unfold cA; linarith
  have hBB : B ≤ (B + 1) := by linarith
  refine ⟨hc6.le, by linarith, by positivity, ?_, ?_⟩
  · exact arith_lip (A := cA d L N) (B1 := (B + 1)) (B := B) (Fb := cF d L * δ₁)
      (δ₀ := δ₀) (ρ := c6' d L N B Γ) (τ := cTau' d L N B) (x := N) (y := commKConst d L N)
      (z := N * (2 * d + 8)) hA hB1 hB0 hBB ((cTau'_spec (d := d) (L := L) (N := N) hB0)) hτ.le hN0 hK0 hz0 hNA hKA hzA
      hFb0 h0 hc6.le hFb (hδ₀.trans hs1) (by linarith)
  · have := selfBound'_le hB0 h0 h1 hδ₀ hδ₁
    unfold selfBound' at this
    have hδ' : δ₁ ≤ c6' d L N B Γ / (2 * cN' d L N B) := hδ₁.trans hs4
    rw [le_div_iff₀ (by positivity)] at hδ'
    nlinarith

end Constants

section Data

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The standing hypotheses of the localization setting give the hypotheses of the Green's
function bounds of BACKGROUND.md §1. -/
theorem DGSetting.toGreen (S : DGSetting G a ν) : GreenSetting G a ν where
  hd := S.hd
  hL := S.hL
  mass := S.mass
  massLe := S.massLe
  weights := S.weights
  sep := by
    have hε : 0 < agmonRate d := agmonRate_pos (by have := S.hd; omega)
    have h1 := S.one_lt_rho
    have h := S.sep
    have : agmonRate d / 16 * (ϱ - 1) ≤ agmonRate d / 2 / 2 * (ϱ - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

/-- The Green family of `G_s`: `α ↦ G_s(α)`, with the parameters `s` extended by `1`. -/
noncomputable def decG (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (s : DecParams G) : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  fun α => Gs G a ν α (extS G s)

variable (G a ν) in
/-- The hypotheses (P1)--(P4) of Theorem I-4a (LOCALIZATION.md §3.2), in the mode `ιU`: the
defect hypothesis (P4) is only present in mode U (`ιU = true`).  The smallness of `δ₀, δ₁` is a
separate hypothesis of the theorems. -/
structure DecHyp (ιU : Bool) (α₀ : G.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) (δ₀ δ₁ : ℝ) : Prop where
  green : GreenSetting G a ν
  δ₀_nn : 0 ≤ δ₀
  δ₁_nn : 0 ≤ δ₁
  δ₀_le : δ₀ ≤ 1
  smooth : IsSmoothField G δ₀ φ₀
  phiBd : ∀ x ∈ G.Ω 1, vn (φ₀ x) ≤ 3 / 2
  alpha0 : ∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α₀ x‖ ≤ δ₀
  f₁_bd : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖f₁ (x, i)‖ ≤ δ₁
  dPsi : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁
  g0 : ιU = true → ∀ x : G.Ω 1, ‖gdef G φ₀ x‖ ≤ δ₁
  gl : ιU = true → ∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
    ‖negLap (zeroExt (G.Ω 1) (gdef G φ₀)) (x : CTorus d L N₁ m₁ K)‖ ≤ δ₁

variable {ιU : Bool} {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
  {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}

/-- The data of Theorem I-4a give the `Setup` of the abstract core, in either mode, for
`H₀ = H_D(α₀)`. -/
theorem DecHyp.setup (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) :
    Setup G (dirichletOperator G a ν α₀) ιU (commKConst d L N) (2 * d + 8) α₀ φ₀
      (pertSource G a δΨ f₁) δ₀ (cF d L * δ₁) (5 * δ₁) where
  δ₀_nn := H.δ₀_nn
  Fb_nn := by have := Balaban.Background.cF_pos d L; have := H.δ₁_nn; positivity
  Gb_nn := by have := H.δ₁_nn; positivity
  Kc_nn := by unfold commKConst; positivity
  Rc_nn := by positivity
  phiBd := H.phiBd
  alpha0 := H.alpha0
  Fs_bd := pertSource_bound H.green H.δ₁_nn H.dPsi H.f₁_bd
  g_bd := fun h x => Hg_bound H.green H.alpha0 H.δ₀_le H.δ₁_nn (H.g0 h) (H.gl h) x
  comm_bd := fun hV hs x => commK_bound (by have := H.green.hd; omega)
    (by have := H.green.hL; omega) H.green.weights ν α₀ H.smooth H.δ₀_nn hV hs x
  R_bd := fun hV hW hv hw x => Rvec_bound H.green.weights H.green.mass H.green.massLe
    (fun y => (H.alpha0 y).trans H.δ₀_le) hV hW hv hw x

variable (G a ν) in
/-- The fixed point equation of Theorem I-4a: `δα = 𝒩_s(δα)`, with
`δφ(δα) = G_s(α₀ + δα)(F_s - δα φ₀)`. -/
def DecFixed (s : DecParams G) (ιU : Bool) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) : Prop :=
  Nmap G (dirichletOperator G a ν α₀) ιU φ₀ Fs (dphi G (decG G a ν s) α₀ φ₀ Fs δα) = δα

end Data

section Exists

variable {d L : ℕ} [NeZero L]

theorem pertSource_zero {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (a : ℕ → ℝ) : pertSource G a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) 0 = 0 := by
  funext p
  simp [pertSource, qStar, boundaryTerm]

theorem Nmap_zero_zero {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    Nmap G H₀ false φ₀ 0 0 = 0 := by
  funext x
  have hc : ∀ i, Multiscale.comp G (0 : G.Ω 1 × Fin N → ℂ) i = 0 := fun i => rfl
  simp [Nmap, Rvec, Rsc, hc]

/-- **Theorem I-4a (a), (c) for one parameter `s`**: existence, uniqueness in the ball
`|δα|₂ ≤ c₆` and the bounds, in both modes.  The family `G_s` is the decoupled Green's operator;
the constants are `famConst d L B_G κ₁`. -/
theorem i4a_exists_unique {cstar BG : ℝ} (hF : FamSpec d L cstar BG) :
    ∀ {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : DecParams G}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {ιU : Bool} {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
        {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ},
      DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁ →
      δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) →
      δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) →
      ∃ δα : G.Ω 1 → ℂ,
        DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα ∧
        Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small G δα (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα)
          (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : G.Ω 1 → ℂ, Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα' → δα' = δα) ∧
        (ιU = false → δΨ = 0 → f₁ = 0 → δα = 0 ∧
          dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα = 0) := by
  obtain ⟨-, hBG, Hfam⟩ := hF
  intro N₁ m₁ K N _ ϱ G a ν S κ hκ hM s hs ιU α₀ φ₀ δΨ f₁ δ₀ δ₁ H hδ₀ hδ₁
  obtain ⟨hfam, hsup⟩ := Hfam G S hκ hM hs N
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB1 : 1 ≤ B := famConst_ge_one hBG κ hd0
  have hB0 : 0 ≤ B := by linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  obtain ⟨δα, hsmall, hfix, hsb, hstar, huniq⟩ := prop51_core hfam H.setup hC
  have hsb' := selfBound'_le (d := d) (L := L) (N := N) hB0 H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  have hcN := cN'_pos (d := d) (L := L) (N := N) hB0
  have hF := Balaban.Background.cF_pos d L
  have hδ1 := H.δ₁_nn
  have hr2 : δ₀ + 2 * coreBound N B (commKConst d L N) (2 * d + 8) δ₀ (cF d L * δ₁) (5 * δ₁) ≤ Γ := by
    linarith [hC.poly, hC.self, hC.ρ_nn]
  have hcb : coreBound N B (commKConst d L N) (2 * d + 8) δ₀ (cF d L * δ₁) (5 * δ₁) ≤ cN' d L N B * δ₁ :=
    hsb'
  have hK : 2 * cN' d L N B * δ₁ ≤ cK2' d L N B * δ₁ := by
    unfold cK2'
    nlinarith [mul_nonneg (by linarith : 0 ≤ B + 1) (mul_nonneg hF.le hδ1),
      mul_nonneg hcN.le hδ1, mul_nonneg (mul_nonneg (by linarith : 0 ≤ B + 1) hcN.le) hδ1]
  have hsmall2 : Small G δα (cK2' d L N B * δ₁) := fun x => by
    refine (hsb x).trans ?_
    nlinarith
  have hdp : SupBounds G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα)
      (cK2' d L N B * δ₁) := by
    have hFs := Fsrc_bd H.setup hsb
    have hX : 0 ≤ cF d L * δ₁ + 3 / 2 * (2 * coreBound N B (commKConst d L N) (2 * d + 8) δ₀
        (cF d L * δ₁) (5 * δ₁)) := by
      have := coreBound_nonneg (N := N) hB0 H.setup.Kc_nn H.setup.Rc_nn H.δ₀_nn H.setup.Fb_nn
        H.setup.Gb_nn
      have := H.setup.Fb_nn
      positivity
    have := hsup (α := α₀ + δα) (H.setup.poly hsb hr2) _ hX hFs
    refine this.mono ?_
    unfold cK2'
    calc B * (cF d L * δ₁ + 3 / 2 * (2 * coreBound N B (commKConst d L N) (2 * d + 8) δ₀
          (cF d L * δ₁) (5 * δ₁)))
        ≤ (B + 1) * (cF d L * δ₁ + 3 * (cN' d L N B * δ₁)) := by
          refine mul_le_mul (by linarith) (by linarith) hX (by linarith)
      _ ≤ _ := by nlinarith [mul_nonneg hcN.le hδ1, mul_nonneg hF.le hδ1,
            mul_nonneg (mul_nonneg hcN.le hδ1) hB0]
  refine ⟨δα, hfix, hsmall, hsmall2, hdp, fun δα' hs' hf' => huniq δα' hs' hf', ?_⟩
  intro hι hΨ hf
  subst hι hΨ hf
  rw [pertSource_zero] at *
  -- zero is a fixed point in the ball
  have hz : Small G (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) := by
    intro x; have := (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le; simp [this]
  have h0 : DecFixed G a ν s false α₀ φ₀ 0 0 := by
    unfold DecFixed dphi
    have : Fsrc φ₀ (0 : G.Ω 1 × Fin N → ℂ) (0 : G.Ω 1 → ℂ) = 0 := by
      funext p; simp [Fsrc]
    rw [this, Matrix.mulVec_zero]
    exact Nmap_zero_zero G _ φ₀
  have e0 : δα = 0 := (huniq 0 hz h0).symm
  refine ⟨e0, ?_⟩
  subst e0
  unfold dphi
  have : Fsrc φ₀ (0 : G.Ω 1 × Fin N → ℂ) (0 : G.Ω 1 → ℂ) = 0 := by
    funext p; simp [Fsrc]
  rw [this, Matrix.mulVec_zero]

end Exists

end Balaban.Localization
