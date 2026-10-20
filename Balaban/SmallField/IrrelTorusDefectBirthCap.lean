/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectBirthSurrogate

/-!
# The level-only surrogate with the cap `e² ν̄`

In `IsSFFamily2.exists_levelOnly` the birth mass `μ_j` of a level `j` had to satisfy the extra
premise `μ_j ≤ ν̄ L⁻²ᵏ`.  Along the flow the birth mass is at most `e² ν_k L^{-2(k-j)}`
(`physMass_mul_sq_le_exp_nuIdeal`), so the surrogate regime `ν'_k = ν_j L^{2(k-j)}` has
`ν'_k ≤ e² ν̄`.  `IsSFFamily2.exists_levelOnly_cap` takes the surrogate constants with `ν̄` replaced
by `e² ν̄`; they are admissible when `e² ν̄ ≤ 7/8 L⁻²`, a condition on the choice of the constants only
(author ruling R6).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The birth mass of a level, rescaled to the scale `k`, is at most `e²` times the running mass. -/
theorem levelOnly_nu_le {P : Consts} (hP : P.Admissible d L) (hL : 2 ≤ L) {β ν a : ℕ → ℝ}
    (h : CoeffBounds d L k P β ν a) {j : ℕ} (hjk : j ≤ k) :
    ν j * (L : ℝ) ^ (2 * (k - j)) ≤ Real.exp 2 * ν k := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 := physMass_mul_sq_le_exp_nuIdeal hP hL h hjk
  rw [physMass_mul_sq] at h1
  have h2 : (0 : ℝ) < (L : ℝ) ^ (2 * (k - j)) := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2.le
  refine h3.trans (le_of_eq ?_)
  unfold nuIdeal
  rw [show 2 * (k - j) = (k - j) * 2 by ring, pow_mul]
  field_simp

/-- The term clauses survive an increase of `c₉` and any change of `ν̄`. -/
theorem SFTermClauses.of_c9_le_νbar {N₁ : ℕ} [NeZero N₁] {P : Consts}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
    (hT : SFTermClauses P Dom Tm) {c ν : ℝ} (hc : P.c₉ ≤ c) :
    SFTermClauses { P with c₉ := c, νbar := ν } Dom Tm where
  gs_spec := hT.gs_spec
  analyticE := hT.analyticE
  analyticM := hT.analyticM
  rotE := hT.rotE
  pavingGS := hT.pavingGS
  eucE := hT.eucE
  eucEloc := hT.eucEloc
  rotM := hT.rotM
  eucM := hT.eucM
  eucMloc := hT.eucMloc
  localE := hT.localE
  localM := hT.localM
  boundE := hT.boundE
  boundM := by
    intro j hj1 hjk x X hX hx Ψ h g h1 hg
    refine lt_of_lt_of_le (hT.boundM j hj1 hjk x X hX hx Ψ h g h1 hg) ?_
    have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (inv_nonneg.2 (pow_nonneg hL.le _)) _))
      (Real.exp_pos _).le

section Surrogate

variable {P : Consts} {Rg : Regime L} {β a Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- **A level `j` of a member of `IsSFFamily2` on the birth domains is a member on the complete
domains of a regime of the mass `μ_j`, with no premise on the flow** (`IsSFFamily2.exists_levelOnly`
with the constants `ν̄` replaced by `e² ν̄`).  Only the condition `e² ν̄ ≤ 7/8 L⁻²` on the constants
is needed. -/
theorem IsSFFamily2.exists_levelOnly_cap
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hL : 2 ≤ L) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hνbar : Real.exp 2 * P.νbar ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹) :
    ∃ (Rg' : Regime L) (β' : ℕ → ℝ) (Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ),
      Rg'.ν k = Rg.ν j * (L : ℝ) ^ (2 * (k - j)) ∧
      (∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j ∧ (Tm' N₁).M j = (Tm N₁).M j ∧
        (Tm' N₁).gs = (Tm N₁).gs) ∧
      IsSFFamily2 { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } Rg' β' a
        (completeXiDom { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } Rg' a) Tm'
        (fun _ _ _ _ _ => 0) Ek := by
  classical
  have hadm := hF.admissible
  have hν_j : 0 < Rg.ν j := hF.coeff.nu_pos_of_le hadm hL hjk
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνk'pos : 0 < Rg.ν j * (L : ℝ) ^ (2 * (k - j)) := by positivity
  have hνk'le : Rg.ν j * (L : ℝ) ^ (2 * (k - j)) ≤ Real.exp 2 * P.νbar :=
    (levelOnly_nu_le hadm hL hF.coeff hjk).trans
      (mul_le_mul_of_nonneg_left hF.coeff.nu_le (Real.exp_pos 2).le)
  choose Tm' hE hM hgs hE0 hM0 using fun (N₁ : ℕ) [NeZero N₁] =>
    exists_levelOnly_terms (Tm N₁) j
  let Rg' : Regime L := ⟨Rg.kZero, nuComplete L k (Rg.ν j * (L : ℝ) ^ (2 * (k - j)))⟩
  have hRgν : Rg'.ν k = Rg.ν j * (L : ℝ) ^ (2 * (k - j)) := nuComplete_self k _
  have hmass : Rg'.sfBgMass k = physMass L j (Rg.ν j) := by
    show physMass L k (Rg'.ν k) = _
    rw [hRgν, physMass_levelOnly j k hjk]
  have hdom : ∀ (N₁ : ℕ) [NeZero N₁] (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ)
      (Ψ h : Fld d L N₁ m₁ k N),
      (completeXiDom { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } Rg' a N₁).dom j G Ψ h ↔
        (birthXiDom P Rg a N₁).dom j G Ψ h := by
    intro N₁ _ G Ψ h
    show XiDom G (aIdeal L k (a k)) (Rg'.sfBgMass k) j _ Ψ h ↔
      XiDom G (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ h
    rw [hmass]
    exact Iff.rfl
  have hc9 : P.noChi.c₉ ≤ |P.c₉| + 1 := by
    show P.c₉ ≤ _
    have := le_abs_self P.c₉
    linarith
  have hclauses : ∀ (N₁ : ℕ) [NeZero N₁], SFTermClauses
      { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar }
      (completeXiDom { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } Rg' a N₁) (Tm' N₁) := by
    intro N₁ _
    exact SFTermClauses.levelOnly ((hF.torus N₁).terms.noChi.of_c9_le_νbar hc9) (hdom N₁) (hE N₁)
      (hM N₁) (hgs N₁) (hE0 N₁) (hM0 N₁) hadm.E₀_nonneg (by positivity)
  refine ⟨Rg', betaComplete d L P (Rg.ν j * (L : ℝ) ^ (2 * (k - j))), Tm', hRgν,
    fun N₁ _ => ⟨hE N₁, hM N₁, hgs N₁⟩, ?_⟩
  · refine
      { admissible := ?_
        coeff := ?_
        torus := fun N₁ _ _ => ?_
        torusIndep := ?_
        renorm := fun i hi1 hik => ?_ }
    · exact ⟨hadm.γ_pos, hadm.γ_lt, hadm.α₁_pos, hadm.α₁_lt, hadm.α₀_pos, hadm.κ_pos,
        by have := hadm.νbar_pos; positivity, hνbar, hadm.c₈_pos, hadm.E₀_nonneg⟩
    · have hC : CoeffBounds d L k { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } β Rg.ν a :=
        ⟨hF.coeff.flow, hF.coeff.beta_gt, hF.coeff.nu_pos, hF.coeff.nu_le.trans (le_mul_of_one_le_left hadm.νbar_pos.le (Real.one_le_exp (by norm_num))),
          hF.coeff.a_ge,
          hF.coeff.a_lt⟩
      exact coeffBounds_complete_of (P := { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar })
        ⟨hadm.γ_pos, hadm.γ_lt, hadm.α₁_pos, hadm.α₁_lt, hadm.α₀_pos, hadm.κ_pos,
          by have := hadm.νbar_pos; positivity, hνbar, hadm.c₈_pos, hadm.E₀_nonneg⟩ hC hνk'pos hνk'le
    · refine
        { density := ?_
          terms := hclauses N₁
          gsStrong := ?_ }
      · intro Ψ₀ h₀ g D _ _ _
        have hX : ¬ Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg'.sfBgMass k) k 1
            ({ P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar }.p
              (betaComplete d L P (Rg.ν j * (L : ℝ) ^ (2 * (k - j))) k) /
              Real.sqrt (betaComplete d L P (Rg.ν j * (L : ℝ) ^ (2 * (k - j))) k)) Ψ₀ h₀ := by
          show ¬ Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg'.sfBgMass k) k 1
            (0 / _) Ψ₀ h₀
          rw [zero_div]
          exact fun h => lt_irrefl _ h.2.1
        rw [ite_eq_right_iff.2 fun h => absurd h hX]
        simp
      · intro i hi1 hik X hX
        have := (hF.torus N₁).gsStrong i hi1 hik X hX
        rwa [← hgs N₁] at this
    · exact TorusIndep.levelOnly hF.torusIndep hE hE0
    · by_cases hij : i = j
      · subst hij
        exact RenormCond.levelOnly (hF.renorm i hi1 hik)
          (fun _ => nuIdeal_pos' hF.coeff.nu_pos i) hE
      · exact RenormCond.levelOnly_zero _ (fun N₁ _ => hE0 N₁ i hij)


end Surrogate

end Balaban.SmallField.Def6v2
