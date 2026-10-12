/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Solve
public import Balaban.Localization.DecoupledOne

/-!
# Theorem I-4a (b): at `s = 1` the decoupled system is the system of Proposition 5.1

For a cover `C` and an operator `H`.  `OneSpec` is the identity `G_1 = G_D` of `Gs_one`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}


/-- **The identity `G_1 = G_D`** (the conclusion of `Gs_one` with the constant `c`). -/
def OneSpec (d L : ℕ) [NeZero L] (Kc Cx c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → c ≤ (L : ℝ) ^ m₁ →
      IsUnit (1 - Kcal C H a ν α (fun _ => 1)) ∧
      Gs C H a ν α (fun _ => 1) = (dirichletOperator H a ν α)⁻¹

theorem OneSpec.mono_c {d L : ℕ} [NeZero L] {c c' : ℝ} (h : OneSpec d L Kc Cx c) (hc : c ≤ c') :
    OneSpec d L Kc Cx c' :=
  ⟨h.1.trans hc, by
    intro N₁ m₁ K _ ϱ C H a ν S α hα hM
    exact h.2 C H S hα (hc.trans hM)⟩

theorem oneSpec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) : ∃ c : ℝ, OneSpec d L Kc Cx c := by
  obtain ⟨c, hc, Hh⟩ := Gs_one (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨c, hc, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα hM
  exact Hh C H S hα hM

omit [NeZero N₁] [NeZero L] in
theorem extS_one (C : DecCover d L N₁ m₁ K) :
    extS C (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext P
  unfold extS
  split_ifs <;> rfl


/-- At `s = 1` the family `G_s(α)` is `H_D(α)⁻¹` on admissible potentials. -/
theorem decG_one {c : ℝ} (h1 : OneSpec d L Kc Cx c) (S : CoverBase C H a ν Kc Cx) (hM : c ≤ (L : ℝ) ^ m₁)
    {α : H.Ω 1 → ℂ} (hα : AdmPot H α) :
    decG C H a ν (fun _ => 1) α = greenD H a ν α := by
  unfold decG greenD
  rw [extS_one C]
  exact (h1.2 C H S hα hM).2

/-- **Theorem I-4a (b), `s = 1`, mode U.**  Under the hypotheses of `i4a_exists_unique`, the
fixed point `δα` of `𝒩_1` in the ball `|δα|₂ ≤ c₆` solves (P-1), (P-2) of Proposition 5.1 with
`δφ = dphi δα`, and it is the only solution of (P-1), (P-2) with `|δα'|₂ ≤ c₆`. -/
theorem i4a_one {cstar BG c1 : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (h1 : OneSpec d L Kc Cx c1)
    (hc1 : c1 ≤ cstar) {κ : ℝ} (hκ : 0 ≤ κ)
    (S : CoverBase C H a ν Kc Cx) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {α₀ : H.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : H.Ω 1 × Fin N → ℂ}
    {δ₀ δ₁ : ℝ} (Hh : DecHyp H a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ δα : H.Ω 1 → ℂ,
      DecFixed C H a ν (fun _ => 1) true α₀ φ₀ (pertSource H a δΨ f₁) δα ∧
      IsPerturbed H a ν α₀ φ₀ (pertSource H a δΨ f₁)
        (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα) δα ∧
      Small H δα (cK2' d L N (famConst d L BG κ) * δ₁) ∧
      ∀ (δφ' : H.Ω 1 × Fin N → ℂ) (δα' : H.Ω 1 → ℂ),
        IsPerturbed H a ν α₀ φ₀ (pertSource H a δΨ f₁) δφ' δα' →
        Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
        δφ' = dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα ∧ δα' = δα := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hE : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by unfold N0; positivity)
  have hMc : c1 ≤ (L : ℝ) ^ m₁ := by
    refine le_trans hc1 (le_trans ?_ hM)
    have := h1.1; nlinarith [hF.1]
  have hs1 : ∀ P, ‖(fun _ : C.cubeIdx => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using Real.one_le_exp hκ
  obtain ⟨δα, hfix, hsmall, hsm, -, huniq, -⟩ := i4a_exists_unique hF C H S hκ hM hs1 Hh hδ₀ hδ₁
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hF.2.1 κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  have hγ : Γ ≤ gamma1 d := by have := gamma1_pos hd0; rw [hΓdef]; linarith
  -- the equality of the two Green families on the ball
  have hfam : ∀ δα' : H.Ω 1 → ℂ, Small H δα' (c6' d L N B Γ) →
      dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα' =
        dphi H (greenD H a ν) α₀ φ₀ (pertSource H a δΨ f₁) δα' := by
    intro δα' hs
    have hsm' : Small H (α₀ + δα') Γ := Hh.setup.poly hs (by linarith [hC.poly, hC.ρ_nn])
    unfold dphi
    rw [decG_one h1 S hMc (admPot_of_small hd0 hsm')]
  have hfixG : Nmap H (dirichletOperator H a ν α₀) true φ₀ (pertSource H a δΨ f₁)
      (dphi H (greenD H a ν) α₀ φ₀ (pertSource H a δΨ f₁) δα) = δα := by
    rw [← hfam δα hsmall]; exact hfix
  have hpoly : δ₀ + 2 * c6' d L N B Γ ≤ gamma1 d := by linarith [hC.poly]
  have hP := perturbed_of_fixed Hh.green Hh.alpha0 hC.ρ_nn hpoly hsmall hfixG
  refine ⟨δα, hfix, by rw [hfam δα hsmall]; exact hP, hsm, ?_⟩
  intro δφ' δα' hP' hs'
  have hα' : Small H (α₀ + δα') (gamma1 d) := fun x =>
    ((Small.add Hh.alpha0 hs') x).trans (by linarith [hC.poly, hC.ρ_nn])
  obtain ⟨hδφ, hfix'⟩ := fixed_of_perturbed Hh.green hα' hP'
  have hfix1 : DecFixed C H a ν (fun _ => 1) true α₀ φ₀ (pertSource H a δΨ f₁) δα' := by
    unfold DecFixed; rw [hfam δα' hs']; exact hfix'
  have := huniq δα' hs' hfix1
  refine ⟨?_, this⟩
  rw [hδφ, this, hfam δα hsmall]


end Balaban.Localization.Dec2
