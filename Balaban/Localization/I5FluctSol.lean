/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation field `δφ(ψ', s)` and multiplier `δα(ψ', s)` (Theorem I-4a, mode P)

For a pair `(C, H⁻)` and data `e = (φ₀, α₀, δΨ, f₁)` the fluctuation multiplier is the unique
fixed point of `𝒩_s` in the ball `|δα|₂ ≤ c₆` (`IsFlSol`; `fl_exists_unique`), and the
fluctuation field is `δφ = G_s(α₀ + δα)(F_s - δα φ₀)` (`flField`).  They are defined only through
the `∃!` theorem (`flMult_spec`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Sol

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱm : ℝ}
variable {C : DecCover d L N₁ m₁ K} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ}

variable (C Hm a ν) in
/-- **`δα` solves the fixed point equation of Theorem I-4a (mode P) for the data `e` in the ball
of radius `ρ`.** -/
def IsFlSol (ρ : ℝ) (s : Dec2.DecParams C) (e : Edat Hm N) (δα : Hm.Ω 1 → ℂ) : Prop :=
  Small Hm δα ρ ∧ Dec2.DecFixed C Hm a ν s false e.2.1 e.1 (pertSource Hm a e.2.2.1 e.2.2.2) δα

variable (C Hm a ν) in
open Classical in
/-- **The fluctuation multiplier** `δα(s)` (`0` if there is no unique solution in the ball;
`fl_exists_unique` shows that there is one for the data of Theorem I-4a). -/
noncomputable def flMult (ρ : ℝ) (s : Dec2.DecParams C) (e : Edat Hm N) : Hm.Ω 1 → ℂ :=
  if h : ∃! δα, IsFlSol C Hm a ν ρ s e δα then h.exists.choose else 0

variable (C Hm a ν) in
/-- **The fluctuation field** `δφ(s) = G_s(α₀ + δα)(F_s - δα φ₀)`. -/
noncomputable def flField (ρ : ℝ) (s : Dec2.DecParams C) (e : Edat Hm N) : Hm.Ω 1 × Fin N → ℂ :=
  dphi Hm (Dec2.decG C Hm a ν s) e.2.1 e.1 (pertSource Hm a e.2.2.1 e.2.2.2)
    (flMult C Hm a ν ρ s e)

theorem flMult_spec {ρ : ℝ} {s : Dec2.DecParams C} {e : Edat Hm N} {δα : Hm.Ω 1 → ℂ}
    (h : IsFlSol C Hm a ν ρ s e δα) (hu : ∀ δα', IsFlSol C Hm a ν ρ s e δα' → δα' = δα) :
    flMult C Hm a ν ρ s e = δα := by
  classical
  have Hh : ∃! δα, IsFlSol C Hm a ν ρ s e δα := ⟨δα, h, hu⟩
  unfold flMult
  simp only [Hh, ↓reduceDIte]
  exact Hh.unique Hh.exists.choose_spec h

/-- **Theorem I-4a (a), mode P, for the fluctuation data**: for `s` with `|s_P| ≤ e^κ` and data
satisfying the strict inequalities, the fluctuation multiplier exists and is unique in the ball,
and satisfies the bounds. -/
theorem fl_exists_unique {cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    (S : Dec2.CoverBase C Hm a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : Dec2.DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {e : Edat Hm N} {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hle : δ₀ ≤ 1) (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (he : StrictDataM Hm N false δ₀ δ₁ e) :
    ∃ δα : Hm.Ω 1 → ℂ,
      IsFlSol C Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) s e δα ∧
      (∀ δα', IsFlSol C Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) s e δα' →
        δα' = δα) ∧
      Small Hm δα (cK2' d L N (famConst d L BG κ) * δ₁) ∧
      SupBounds Hm (dphi Hm (Dec2.decG C Hm a ν s) e.2.1 e.1 (pertSource Hm a e.2.2.1 e.2.2.2) δα)
        (cK2' d L N (famConst d L BG κ) * δ₁) := by
  have Hh : DecHyp Hm a ν false e.2.1 e.1 e.2.2.1 e.2.2.2 δ₀ δ₁ :=
    StrictDataM.hyp S.toOpSetting.toGreen h0 h1 hle he
  obtain ⟨δα, hfix, hsm, hsK, hdp, huniq, -⟩ :=
    Dec2.i4a_exists_unique hF C Hm S hκ hM hs Hh hδ₀ hδ₁
  exact ⟨δα, ⟨hsm, hfix⟩, fun δα' h' => huniq δα' h'.1 h'.2, hsK, hdp⟩

theorem flField_spec {cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    (S : Dec2.CoverBase C Hm a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : Dec2.DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {e : Edat Hm N} {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hle : δ₀ ≤ 1) (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (he : StrictDataM Hm N false δ₀ δ₁ e) :
    IsFlSol C Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) s e
        (flMult C Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) s e) ∧
      Small Hm (flMult C Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) s e)
        (cK2' d L N (famConst d L BG κ) * δ₁) ∧
      SupBounds Hm (flField C Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) s e)
        (cK2' d L N (famConst d L BG κ) * δ₁) := by
  obtain ⟨δα, hsol, hu, hsm, hsup⟩ := fl_exists_unique hF S hκ hM hs h0 h1 hle hδ₀ hδ₁ he
  have e1 := flMult_spec hsol hu
  unfold flField
  rw [e1]
  exact ⟨hsol, hsm, hsup⟩

end Sol

end Balaban.Localization
