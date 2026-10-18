/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectBirthNu
public import Balaban.SmallField.Def6v2Renorm

/-!
# Level-`j` terms: the term clauses on a field domain that is only read at the level `j`

The filed torus defect at the level `j` reads the terms `ℰ^{(j)}`, `ℳ^{(j)}` and the field domain at
the level `j` only.  If `T'` has the terms of `T` at the level `j` and vanishing terms at every other
level, the clauses `SFTermClauses` and `TorusIndep` of `T'` on a field domain `Dom'` follow
from those of `T` on a field domain `Dom` which agrees with `Dom'` at the level `j`.  This lets the
terms of a level born at the mass `μ_j = ν_j L⁻²ʲ` be compared with the complete regime of the mass
`μ_j` (author ruling R6).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Clauses

variable {P : Consts} {Dom Dom' : FieldDom d L N₁ m₁ k N ϱ} {Tm Tm' : Terms d L N₁ m₁ k N ϱ}
  {j : ℕ}

theorem Eloc_levelOnly_eq (hE : Tm'.E j = Tm.E j) (m₀ : ℕ) :
    Eloc m₀ Tm' j = Eloc m₀ Tm j := by
  funext y ψ h
  simp only [Eloc, hE]

theorem Mloc_levelOnly_eq (hM : Tm'.M j = Tm.M j) (m₀ : ℕ) :
    Mloc m₀ Tm' j = Mloc m₀ Tm j := by
  funext y ψ h g
  simp only [Mloc, hM]

theorem Eloc_levelOnly_zero {i : ℕ} (hE0 : ∀ y X Ψ h, Tm'.E i y X Ψ h = 0) (m₀ : ℕ) :
    Eloc m₀ Tm' i = fun _ _ _ => 0 := by
  funext y ψ h
  simp [Eloc, hE0]

theorem Mloc_levelOnly_zero {i : ℕ} (hM0 : ∀ x X Ψ h g, Tm'.M i x X Ψ h g = 0) (m₀ : ℕ) :
    Mloc m₀ Tm' i = fun _ _ _ _ => 0 := by
  funext y ψ h g
  simp [Mloc, hM0]

/-- **The term clauses of a level-only family.** `Tm'` has the terms and generating sets of `Tm`
at the level `j` and vanishing terms at every other level; `Dom'` agrees with `Dom` at the level
`j`. -/
theorem SFTermClauses.levelOnly (hT : SFTermClauses P Dom Tm)
    (hDom : ∀ G Ψ h, Dom'.dom j G Ψ h ↔ Dom.dom j G Ψ h)
    (hE : Tm'.E j = Tm.E j) (hM : Tm'.M j = Tm.M j) (hgs : Tm'.gs = Tm.gs)
    (hE0 : ∀ i, i ≠ j → ∀ y X Ψ h, Tm'.E i y X Ψ h = 0)
    (hM0 : ∀ i, i ≠ j → ∀ x X Ψ h g, Tm'.M i x X Ψ h g = 0)
    (hP0 : 0 ≤ P.E₀) (hP9 : 0 < P.c₉) : SFTermClauses P Dom' Tm' where
  gs_spec := by
    intro i hi1 hik X hX
    rw [hgs]
    exact hT.gs_spec i hi1 hik X hX
  analyticE := by
    intro i hi1 hik y X hX hy
    by_cases hij : i = j
    · subst hij
      simp only [hE]
      exact (hT.analyticE i hi1 hik y X hX hy).mono fun p hp => (hDom _ _ _).1 (by
        simpa only [hgs, Set.mem_ofPred_eq] using hp)
    · have : (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm'.E i y X p.1 p.2) =
          fun _ => 0 := by
        funext p; exact hE0 i hij y X _ _
      rw [this]
      exact analyticOnNhd_const
  analyticM := by
    intro i hi1 hik x X hX hx
    by_cases hij : i = j
    · subst hij
      simp only [hM]
      refine (hT.analyticM i hi1 hik x X hX hx).mono fun p hp => ⟨(hDom _ _ _).1 ?_, hp.2⟩
      simpa only [hgs] using hp.1
    · have : (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
          Tm'.M i x X p.1 p.2.1 p.2.2) = fun _ => 0 := by
        funext p; exact hM0 i hij x X _ _ _
      rw [this]
      exact analyticOnNhd_const
  rotE := by
    intro i hi1 hik y X hX hy R hR Ψ h h1 h2
    by_cases hij : i = j
    · subst hij
      simp only [hE]
      exact hT.rotE i hi1 hik y X hX hy R hR Ψ h (by simpa only [hgs] using (hDom _ _ _).1 h1)
        (by simpa only [hgs] using (hDom _ _ _).1 h2)
    · rw [hE0 i hij, hE0 i hij]
  pavingGS := by
    intro i hi1 hik X hX r hr n
    simp only [hgs]
    exact hT.pavingGS i hi1 hik X hX r hr n
  eucE := by
    intro i hi1 hik y X hX hy r hr Ψ h h1 h2
    by_cases hij : i = j
    · subst hij
      simp only [hE]
      exact hT.eucE i hi1 hik y X hX hy r hr Ψ h
        (by simpa only [hgs] using (hDom _ _ _).1 h1) (by simpa only [hgs] using (hDom _ _ _).1 h2)
    · rw [hE0 i hij, hE0 i hij]
  eucEloc := by
    intro i hi1 hik y r hr Ψ h h1 h2
    by_cases hij : i = j
    · subst hij
      rw [Eloc_levelOnly_eq hE]
      exact hT.eucEloc i hi1 hik y r hr Ψ h ((hDom _ _ _).1 h1) ((hDom _ _ _).1 h2)
    · rw [Eloc_levelOnly_zero (hE0 i hij)]
  rotM := by
    intro i hi1 hik x X hX hx R hR Ψ h g hg1 hg2 h1 h2
    by_cases hij : i = j
    · subst hij
      simp only [hM]
      exact hT.rotM i hi1 hik x X hX hx R hR Ψ h g hg1 hg2
        (by simpa only [hgs] using (hDom _ _ _).1 h1) (by simpa only [hgs] using (hDom _ _ _).1 h2)
    · rw [hM0 i hij, hM0 i hij]
      simp
  eucM := by
    intro i hi1 hik x X hX hx r hr Ψ h g h1 h2
    by_cases hij : i = j
    · subst hij
      simp only [hM]
      exact hT.eucM i hi1 hik x X hX hx r hr Ψ h g
        (by simpa only [hgs] using (hDom _ _ _).1 h1) (by simpa only [hgs] using (hDom _ _ _).1 h2)
    · rw [hM0 i hij, hM0 i hij]
  eucMloc := by
    intro i hi1 hik x r hr Ψ h g h1 h2
    by_cases hij : i = j
    · subst hij
      rw [Mloc_levelOnly_eq hM]
      exact hT.eucMloc i hi1 hik x r hr Ψ h g ((hDom _ _ _).1 h1) ((hDom _ _ _).1 h2)
    · rw [Mloc_levelOnly_zero (hM0 i hij)]
  localE := by
    intro i y X Ψ Ψ' h h' hloc
    by_cases hij : i = j
    · subst hij
      simp only [hE]
      exact hT.localE i y X Ψ Ψ' h h' hloc
    · rw [hE0 i hij, hE0 i hij]
  localM := by
    intro i x X Ψ Ψ' h h' g g' hloc
    by_cases hij : i = j
    · subst hij
      simp only [hM]
      exact hT.localM i x X Ψ Ψ' h h' g g' hloc
    · rw [hM0 i hij, hM0 i hij]
  boundE := by
    intro i hi1 hik y X hX hy Ψ h h1
    by_cases hij : i = j
    · subst hij
      simp only [hE]
      exact hT.boundE i hi1 hik y X hX hy Ψ h (by simpa only [hgs] using (hDom _ _ _).1 h1)
    · rw [hE0 i hij, norm_zero]
      positivity
  boundM := by
    intro i hi1 hik x X hX hx Ψ h g h1 hg
    by_cases hij : i = j
    · subst hij
      simp only [hM]
      exact hT.boundM i hi1 hik x X hX hx Ψ h g (by simpa only [hgs] using (hDom _ _ _).1 h1) hg
    · rw [hM0 i hij]
      have : vn (0 : Fin N → ℂ) = 0 := by simp [vn]
      rw [this]
      have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
      exact mul_pos (mul_pos hP9 (Real.rpow_pos_of_pos (inv_pos.2 (pow_pos hL _)) _))
        (Real.exp_pos _)

theorem Edens_levelOnly_eq (hE : Tm'.E j = Tm.E j) (m₀ : ℕ) :
    Edens m₀ Tm' j = Edens m₀ Tm j := by
  funext ψ h
  simp only [Edens, Eloc_levelOnly_eq hE]

theorem Edens_levelOnly_zero {i : ℕ} (hE0 : ∀ y X Ψ h, Tm'.E i y X Ψ h = 0) (m₀ : ℕ) :
    Edens m₀ Tm' i = fun _ _ => 0 := by
  funext ψ h
  simp only [Edens, Eloc_levelOnly_zero hE0, Finset.sum_const_zero]

end Clauses

section Family

variable {P : Consts} {Tm Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ} {j : ℕ}

theorem TorusIndep.levelOnly (hT : TorusIndep P.m₀ Tm)
    (hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j)
    (hE0 : ∀ (N₁ : ℕ) [NeZero N₁] (i : ℕ), i ≠ j → ∀ y X Ψ h, (Tm' N₁).E i y X Ψ h = 0) :
    TorusIndep P.m₀ Tm' where
  E_eq := by
    intro i hi1 hik y X' hy ψ h N₂ N₃ _ _ hnw₂ hnw₃ hp₂ hp₃
    by_cases hij : i = j
    · subst hij
      simp only [hE]
      exact hT.E_eq i hi1 hik y X' hy ψ h N₂ N₃ hnw₂ hnw₃ hp₂ hp₃
    · rw [hE0 N₂ i hij, hE0 N₃ i hij]

theorem Eseq_levelOnly_eq (hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j) (m₀ : ℕ) :
    Eseq (L := L) (m₁ := m₁) (k := k) m₀ Tm' j = Eseq m₀ Tm j := by
  funext y X' ψ h n
  simp only [Eseq, hE]

theorem ElocInf_levelOnly_eq (hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j) (m₀ : ℕ) :
    ElocInf (L := L) (m₁ := m₁) (k := k) m₀ Tm' j = ElocInf m₀ Tm j := by
  funext y ψ h
  simp only [ElocInf, Einf, Eseq_levelOnly_eq hE]

theorem ElocInf_levelOnly_zero {i : ℕ}
    (hE0 : ∀ (N₁ : ℕ) [NeZero N₁] y X Ψ h, (Tm' N₁).E i y X Ψ h = 0) (m₀ : ℕ)
    (y : Fin d → ℤ) (ψ h : InfFld d N) :
    ElocInf (L := L) (m₁ := m₁) (k := k) m₀ Tm' i y ψ h = 0 := by
  have hs : ∀ (y : Fin d → ℤ) (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N),
      Einf (L := L) (m₁ := m₁) (k := k) m₀ Tm' i y X' ψ h = 0 := by
    intro y X' ψ h
    refine stabVal_eq (c := 0) (Filter.Eventually.of_forall fun n => ?_)
    simp only [Eseq, hE0]
  simp [ElocInf, hs]

/-- **The renormalization conditions of a level-only family.** -/
theorem RenormCond.levelOnly {νk νk' : ℝ} (hR : RenormCond P.m₀ k νk Tm j)
    (hν : 0 < nuIdeal L k νk' j → 0 < nuIdeal L k νk j)
    (hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j) :
    RenormCond P.m₀ k νk' Tm' j where
  val := by
    intro i₀
    rw [ElocInf_levelOnly_eq hE]
    exact hR.val i₀
  dh := by
    intro i₀ hpos
    rw [ElocInf_levelOnly_eq hE]
    exact hR.dh i₀ (hν hpos)
  dpsi := by
    intro i₀
    rw [ElocInf_levelOnly_eq hE]
    exact hR.dpsi i₀
  moment := by
    intro i₀ i₁ hne
    have := hR.moment i₀ i₁ hne
    simpa only [momentSum, Edens_levelOnly_eq (hE _)] using this

theorem RenormCond.levelOnly_zero {i : ℕ} (νk : ℝ)
    (hE0 : ∀ (N₁ : ℕ) [NeZero N₁] y X Ψ h, (Tm' N₁).E i y X Ψ h = 0) :
    RenormCond P.m₀ k νk Tm' i where
  val := by
    intro i₀
    exact ElocInf_levelOnly_zero hE0 _ _ _ _
  dh := by
    intro i₀ _
    have : (fun h : Fin N → ℂ => ElocInf (L := L) (m₁ := m₁) (k := k) P.m₀ Tm' i 0
        (constInf (Pi.single i₀ 1)) (constInf h)) = fun _ => 0 :=
      funext fun h => ElocInf_levelOnly_zero hE0 _ _ _ _
    rw [this]
    simp
  dpsi := by
    intro i₀
    have : (fun t : ℂ => ElocInf (L := L) (m₁ := m₁) (k := k) P.m₀ Tm' i 0
        (constInf ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ))) (constInf (Pi.single i₀ 1))) =
        fun _ => 0 :=
      funext fun t => ElocInf_levelOnly_zero hE0 _ _ _ _
    rw [this]
    simp
  moment := by
    intro i₀ i₁ _
    have : ∀ n : ℕ, haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
        momentSum P.m₀ (Tm' (n + 1)) i i₀ i₁ = 0 := by
      intro n
      simp only [momentSum, Edens_levelOnly_zero (hE0 _), D2]
      simp
    simp only [this]
    exact tendsto_const_nhds

end Family

end Balaban.SmallField.Def6v2
