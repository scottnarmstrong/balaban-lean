/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSolve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-4a (b): at `s = 1` the decoupled system is the system of Proposition 5.1

For `s = 1` one has `G_1(A) = G_D(A)` (`Gs_one`), so the map `𝒩_1` is the map `𝒩` of BG (5.2)
and, in mode U, the fixed point of `𝒩_1` in the ball is the solution of the perturbed system
(P-1), (P-2); conversely every solution of (P-1), (P-2) with `|δα|₂` in the ball is that fixed point.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The identity `G_1 = G_D`** (the conclusion of `Gs_one` with the constant `c`). -/
def OneSpec (d L : ℕ) [NeZero L] (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → c ≤ (L : ℝ) ^ m₁ →
      IsUnit (1 - Kcal G a ν α (fun _ => 1)) ∧
      Gs G a ν α (fun _ => 1) = (dirichletOperator G a ν α)⁻¹

theorem OneSpec.mono_c {d L : ℕ} [NeZero L] {c c' : ℝ} (h : OneSpec d L c) (hc : c ≤ c') :
    OneSpec d L c' :=
  ⟨h.1.trans hc, by
    intro N₁ m₁ K _ ϱ G a ν S α hα hM
    exact h.2 G S hα (hc.trans hM)⟩

theorem oneSpec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) : ∃ c : ℝ, OneSpec d L c := by
  obtain ⟨c, hc, H⟩ := Gs_one (d := d) (L := L) hd hL
  refine ⟨c, hc, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα hM
  exact H G S hα hM

theorem extS_one (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    extS G (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext P
  unfold extS
  split_ifs <;> rfl

/-- At `s = 1` the family `G_s(α)` is `H_D(α)⁻¹` on admissible potentials. -/
theorem decG_one {c : ℝ} (h1 : OneSpec d L c) (S : DGSetting G a ν) (hM : c ≤ (L : ℝ) ^ m₁)
    {α : G.Ω 1 → ℂ} (hα : AdmPot G α) :
    decG G a ν (fun _ => 1) α = greenD G a ν α := by
  unfold decG greenD
  rw [extS_one]
  exact (h1.2 G S hα hM).2

/-- A solution of (P-1), (P-2) is a fixed point of `𝒩` (the `G_D`-specific step, converse of
`perturbed_of_fixed`). -/
theorem fixed_of_perturbed (S : GreenSetting G a ν) {α₀ : G.Ω 1 → ℂ}
    {φ₀ : Torus d (N₁ * L ^ m₁ * L ^ K) → Fin N → ℂ} {Fs δφ' : G.Ω 1 × Fin N → ℂ}
    {δα' : G.Ω 1 → ℂ} (hα' : Small G (α₀ + δα') (gamma1 d))
    (hP' : IsPerturbed G a ν α₀ φ₀ Fs δφ' δα') :
    δφ' = dphi G (greenD G a ν) α₀ φ₀ Fs δα' ∧
      Nmap G (dirichletOperator G a ν α₀) true φ₀ Fs
        (dphi G (greenD G a ν) α₀ φ₀ Fs δα') = δα' := by
  obtain ⟨hP1', hP2'⟩ := hP'
  have hdφ := (isPerturbed_dphi_iff S hα' δφ').1 hP1'
  have hu' := fun x => (constraint_iff_u φ₀ δφ' x).1 (hP2' x)
  have hz : (dirichletOperator G a ν (α₀ + 2 * δα') *ᵥ fun y => 2 * ∑ i, φ₀ y i * δφ' (y, i) +
      ∑ i, δφ' (y, i) * δφ' (y, i) + gdef G φ₀ y) = 0 := by
    funext x
    have hu0 : (fun y : G.Ω 1 => 2 * ∑ i, φ₀ y i * δφ' (y, i) + ∑ i, δφ' (y, i) * δφ' (y, i) +
      gdef G φ₀ y) = 0 := funext hu'
    rw [hu0]; simp
  refine ⟨hdφ, ?_⟩
  funext x
  have := identity52 a ν α₀ δα' φ₀ Fs δφ' hP1' x
  rw [congrFun hz x] at this
  rw [← hdφ]
  have h2 : (2 : ℂ) * (Nmap G (dirichletOperator G a ν α₀) true φ₀ Fs δφ' x - δα' x) = 0 := by
    simpa using this.symm
  have := (mul_eq_zero.1 h2).resolve_left (by norm_num)
  exact sub_eq_zero.1 this

/-- **Theorem I-4a (b), `s = 1`, mode U.**  Under the hypotheses of `i4a_exists_unique`, the
fixed point `δα` of `𝒩_1` in the ball `|δα|₂ ≤ c₆` solves (P-1), (P-2) of Proposition 5.1 with
`δφ = dphi δα`, and it is the only solution of (P-1), (P-2) with `|δα'|₂ ≤ c₆`. -/
theorem i4a_one {cstar BG c1 : ℝ} (hF : FamSpec d L cstar BG) (h1 : OneSpec d L c1)
    (hc1 : c1 ≤ cstar) {κ : ℝ} (hκ : 0 ≤ κ)
    (S : DGSetting G a ν) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : G.Ω 1 × Fin N → ℂ}
    {δ₀ δ₁ : ℝ} (H : DecHyp G a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ δα : G.Ω 1 → ℂ,
      DecFixed G a ν (fun _ => 1) true α₀ φ₀ (pertSource G a δΨ f₁) δα ∧
      IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁)
        (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα) δα ∧
      Small G δα (cK2' d L N (famConst d L BG κ) * δ₁) ∧
      ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
        IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ' δα' →
        Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
        δφ' = dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα ∧ δα' = δα := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hE : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by unfold N0; positivity)
  have hMc : c1 ≤ (L : ℝ) ^ m₁ := by
    refine le_trans hc1 (le_trans ?_ hM)
    have := h1.1; nlinarith [hF.1]
  have hs1 : ∀ P, ‖(fun _ : cubeIdx G => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using Real.one_le_exp hκ
  obtain ⟨δα, hfix, hsmall, hsm, -, huniq, -⟩ := i4a_exists_unique hF G S hκ hM hs1 H hδ₀ hδ₁
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hF.2.1 κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  have hγ : Γ ≤ gamma1 d := by have := gamma1_pos hd0; rw [hΓdef]; linarith
  -- the equality of the two Green families on the ball
  have hfam : ∀ δα' : G.Ω 1 → ℂ, Small G δα' (c6' d L N B Γ) →
      dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα' =
        dphi G (greenD G a ν) α₀ φ₀ (pertSource G a δΨ f₁) δα' := by
    intro δα' hs
    have hsm' : Small G (α₀ + δα') Γ := H.setup.poly hs (by linarith [hC.poly, hC.ρ_nn])
    unfold dphi
    rw [decG_one h1 S hMc (admPot_of_small hd0 hsm')]
  have hfixG : Nmap G (dirichletOperator G a ν α₀) true φ₀ (pertSource G a δΨ f₁)
      (dphi G (greenD G a ν) α₀ φ₀ (pertSource G a δΨ f₁) δα) = δα := by
    rw [← hfam δα hsmall]; exact hfix
  have hpoly : δ₀ + 2 * c6' d L N B Γ ≤ gamma1 d := by linarith [hC.poly]
  have hP := perturbed_of_fixed H.green H.alpha0 hC.ρ_nn hpoly hsmall hfixG
  refine ⟨δα, hfix, by rw [hfam δα hsmall]; exact hP, hsm, ?_⟩
  intro δφ' δα' hP' hs'
  have hα' : Small G (α₀ + δα') (gamma1 d) := fun x =>
    ((Small.add H.alpha0 hs') x).trans (by linarith [hC.poly, hC.ρ_nn])
  obtain ⟨hδφ, hfix'⟩ := fixed_of_perturbed H.green hα' hP'
  have hfix1 : DecFixed G a ν (fun _ => 1) true α₀ φ₀ (pertSource G a δΨ f₁) δα' := by
    unfold DecFixed; rw [hfam δα' hs']; exact hfix'
  have := huniq δα' hs' hfix1
  refine ⟨?_, this⟩
  rw [hδφ, this, hfam δα hsmall]

end Balaban.Localization
