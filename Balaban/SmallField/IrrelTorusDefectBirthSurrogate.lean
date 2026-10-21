/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectBirthTerms
public import Balaban.SmallField.Def6v2Birth

/-!
# A level `j` of the birth-mass family is a member of the complete regime of its birth mass

A member of `IsSFFamily2` on the birth domains `birthXiDom` has, at the level `j`, the chart
`Ξᶜ_j(G; aIdeal L k (a k), μ_j, 1, ε_j)` of the birth mass `μ_j = ν_j L⁻²ʲ`.  The family `T'` that has
the terms of `T` at the level `j` and vanishing terms elsewhere is a member of `IsSFFamily2` on the
complete domains of the regime `Rg'` whose running mass at `k` is `ν'_k = ν_j L^{2(k-j)}`
(`ν'_k L⁻²ᵏ = μ_j`, `nuIdeal L k ν'_k j = ν_j`), with the characteristic radius `0` and a larger
`c₉`.  Every result on the complete regime which reads the terms at the level `j` only thus holds
for the terms of the birth family at the level `j` (author ruling R6).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The terms of a level, extended by zero to the other levels. -/
theorem exists_levelOnly_terms {N₁ : ℕ} [NeZero N₁] (T : Terms d L N₁ m₁ k N ϱ)
    (j : ℕ) :
    ∃ T' : Terms d L N₁ m₁ k N ϱ, T'.E j = T.E j ∧ T'.M j = T.M j ∧ T'.gs = T.gs ∧
      (∀ i, i ≠ j → ∀ y X Ψ h, T'.E i y X Ψ h = 0) ∧
      (∀ i, i ≠ j → ∀ x X Ψ h g, T'.M i x X Ψ h g = 0) := by
  classical
  refine ⟨⟨fun i y X Ψ h => if i = j then T.E i y X Ψ h else 0,
    fun i x X Ψ h g => if i = j then T.M i x X Ψ h g else 0, T.gs⟩, ?_, ?_, rfl, ?_, ?_⟩
  · funext y X Ψ h; simp
  · funext x X Ψ h g; simp
  · intro i hi y X Ψ h; simp [hi]
  · intro i hi x X Ψ h g; simp [hi]

theorem physMass_mul_sq_eq_pow (j k : ℕ) (hjk : j ≤ k) (ν : ℝ) :
    physMass L j ν * ((L : ℝ) ^ k) ^ 2 = ν * (L : ℝ) ^ (2 * (k - j)) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
  unfold physMass
  rw [Nat.add_sub_cancel_left, show 2 * t = t * 2 by ring, pow_mul, pow_add]
  field_simp

theorem physMass_levelOnly (j k : ℕ) (hjk : j ≤ k) (ν : ℝ) :
    physMass L k (ν * (L : ℝ) ^ (2 * (k - j))) = physMass L j ν := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 := physMass_mul_sq_eq_pow (L := L) j k hjk ν
  have h2 : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  have h3 := physMass_mul_sq (L := L) k (ν * (L : ℝ) ^ (2 * (k - j)))
  exact mul_right_cancel₀ h2.ne' (h3.trans h1.symm)

/-- The term clauses survive an increase of `c₉`. -/
theorem SFTermClauses.of_c9_le {N₁ : ℕ} [NeZero N₁] {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom Tm) {c : ℝ} (hc : P.c₉ ≤ c) :
    SFTermClauses { P with c₉ := c } Dom Tm where
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

/-- **A level `j` of a member of `IsSFFamily2` on the birth domains is a member of `IsSFFamily2` on
the complete domains of a regime of the mass `μ_j`.**  The regime `Rg'` has the running mass
`ν'_k = ν_j L^{2(k-j)}` at `k` (so `ν'_k L⁻²ᵏ = μ_j = ν_j L⁻²ʲ` and `nuIdeal L k ν'_k j = ν_j`); the
family `T'` has the terms and generating sets of `T` at the level `j` and vanishing terms at every
other level; the constants are those of `P` with the characteristic radius `0` and `c₉` replaced by
`|c₉| + 1`.  The cap `μ_j ≤ ν̄ L⁻²ᵏ` on the birth mass is the coefficient bound `ν'_k ≤ ν̄` of the
class `Rg'`. -/
theorem IsSFFamily2.exists_levelOnly
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hL : 2 ≤ L) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hcap : physMass L j (Rg.ν j) ≤ P.νbar * ((L : ℝ) ^ k)⁻¹ ^ 2) :
    ∃ (Rg' : Regime L) (β' : ℕ → ℝ) (Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ),
      Rg'.ν k = Rg.ν j * (L : ℝ) ^ (2 * (k - j)) ∧
      (∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j ∧ (Tm' N₁).M j = (Tm N₁).M j ∧
        (Tm' N₁).gs = (Tm N₁).gs) ∧
      IsSFFamily2 { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } Rg' β' a
        (completeXiDom { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } Rg' a) Tm'
        (fun _ _ _ _ _ => 0) Ek := by
  classical
  have hadm := hF.admissible
  have hν_j : 0 < Rg.ν j := hF.coeff.nu_pos_of_le hadm hL hjk
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνk'pos : 0 < Rg.ν j * (L : ℝ) ^ (2 * (k - j)) := by positivity
  have hνk'le : Rg.ν j * (L : ℝ) ^ (2 * (k - j)) ≤ P.νbar := by
    have h1 := physMass_mul_sq_eq_pow (L := L) j k hjk (Rg.ν j)
    have h2 : 0 < ((L : ℝ) ^ k) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hcap h2.le
    rw [h1] at h3
    refine h3.trans (le_of_eq ?_)
    rw [inv_pow]; field_simp
  choose Tm' hE hM hgs hE0 hM0 using fun (N₁ : ℕ) [NeZero N₁] =>
    exists_levelOnly_terms (Tm N₁) j
  let Rg' : Regime L := ⟨Rg.kZero, nuComplete L k (Rg.ν j * (L : ℝ) ^ (2 * (k - j)))⟩
  have hRgν : Rg'.ν k = Rg.ν j * (L : ℝ) ^ (2 * (k - j)) := nuComplete_self k _
  have hmass : Rg'.sfBgMass k = physMass L j (Rg.ν j) := by
    show physMass L k (Rg'.ν k) = _
    rw [hRgν, physMass_levelOnly j k hjk]
  have hdom : ∀ (N₁ : ℕ) [NeZero N₁] (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ)
      (Ψ h : Fld d L N₁ m₁ k N),
      (completeXiDom { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } Rg' a N₁).dom j G Ψ h ↔
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
      { P with p := fun _ => 0, c₉ := |P.c₉| + 1 }
      (completeXiDom { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } Rg' a N₁) (Tm' N₁) := by
    intro N₁ _
    exact SFTermClauses.levelOnly ((hF.torus N₁).terms.noChi.of_c9_le hc9) (hdom N₁) (hE N₁)
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
        hadm.νbar_pos, hadm.νbar_le, hadm.c₈_pos, hadm.E₀_nonneg⟩
    · have hC : CoeffBounds d L k { P with p := fun _ => 0, c₉ := |P.c₉| + 1 } β Rg.ν a :=
        ⟨hF.coeff.flow, hF.coeff.beta_gt, hF.coeff.nu_pos, hF.coeff.nu_le, hF.coeff.a_ge,
          hF.coeff.a_lt⟩
      exact coeffBounds_complete_of (P := { P with p := fun _ => 0, c₉ := |P.c₉| + 1 })
        ⟨hadm.γ_pos, hadm.γ_lt, hadm.α₁_pos, hadm.α₁_lt, hadm.α₀_pos, hadm.κ_pos,
          hadm.νbar_pos, hadm.νbar_le, hadm.c₈_pos, hadm.E₀_nonneg⟩ hC hνk'pos hνk'le
    · refine
        { density := ?_
          terms := hclauses N₁
          gsStrong := ?_
          hat := ?_ }
      · intro Ψ₀ h₀ g D _ _ _
        have hX : ¬ Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg'.sfBgMass k) k 1
            ({ P with p := fun _ => 0, c₉ := |P.c₉| + 1 }.p
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
      · intro i hi1 hik X hX
        have := (hF.torus N₁).hat i hi1 hik X hX
        rwa [← hgs N₁] at this
    · exact TorusIndep.levelOnly hF.torusIndep hE hE0
    · by_cases hij : i = j
      · subst hij
        exact RenormCond.levelOnly (hF.renorm i hi1 hik)
          (fun _ => nuIdeal_pos' hF.coeff.nu_pos i) hE
      · exact RenormCond.levelOnly_zero _ (fun N₁ _ => hE0 N₁ i hij)

end Surrogate

end Balaban.SmallField.Def6v2
