/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.GeneralClassWitness
public import Balaban.Fluctuation.GeneralClassPathAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A non-zero class member matched to the step witness (package `GeneralClassWitness`, step side)

The step is `witnessSetting m₁ β δ` of `StepRegWitness` (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`,
torus index `k + 1 = 2`, `ϱ = rhoSep m₁`, `a₁ = 1`, `ν = 0`, `h₀ = e₀`), so the path scale is the
single `j = 1 = k`.  The class is `witClass m₁`: the terms `qTerms` of `GeneralClassWitness` at the
level `j₀ = 1`, with energy `c · avg_z h(z)·h(z)` on the whole-torus polymer and source part zero
(`cj = 0`), on the torus of index `2`; field domain `boundedFieldDom` (`‖h(x)‖ ≤ 2`).

Inventory of `ClassParamMatch` (`m₀_eq`, `terms_eq`, `weights_eq`, `mass_eq`) and `StepClass`
(`m₀`, `Tm`, `Ek`) at this pairing: `C.m₀ = P.m₀ = 0`; `C.Tm = qTerms …` (the same term as the
`IsSF2` member); `C.Ek = 0` (the `Ek` of the member); `S.a = compWeight 3 1 = aIdeal 3 2 (a 2)` for
`a = compWeight 3 1` (`compWeight_eq_aIdeal`); `S.ν = 0 = Rg.sfBgMass 2` for the zero regime.
None of these fields forces the terms to vanish or `k = 0`.  They are equalities of parameters.

What holds, and in which form:

* `isSF2_witClass` (T2): `IsSF2` at the step torus; the energy term is not identically zero
  (`E_qTerms_const_ne_zero`).
* `classParamMatch_witClass` (T3): `ClassParamMatch` with all four fields.
* `oldXiDomC_witClass` (T4): `OldXiDomC` on `boundedFieldDom`.  `k = 1`, so the statement is **not**
  vacuous (the scale `j = 1` occurs).  The domain is the bounded-field domain, **not** the source
  chart `Ξ^c_j(𝔹_j; 1, ε_j)` (`xiFieldDom` / `completeXiDom`); for the chart the statement is the
  open package GENERAL-OLD-XIDOM-C, which is not proved here: the composed datum of the path would
  have to be shown to lie in the chart, which `rayInDomain_dom_of_xiCData` reduces to `XiCData`
  of the composed datum, not available at this step.  The proof uses that along the whole path the
  composed field `h` is the constant `h₀` (`composedPairAtC_h`).
* `edens_ne_zero_along_path` (T6): at every point of the path the old energy `ℰ^{(1)}` is
  non-zero (the value is `|aligned sites| · c · h₀·h₀ = |aligned sites| · c`).
* `witClass_pathAnalytic` (T5): the three predicates `EdensAnalyticOnPath`, `MlocAnalyticOnPath`,
  `FlocAnalyticOnPath` for this `(S, C)`, from the three landed theorems.

`classRegular_of_isSF2` is not instantiated: it requires `IsSF2` on `completeXiDom` and `RayInDomain`
(the chart `XiDom` along the real ray), which is the same open domain problem (and on
`completeXiDom` at the mass `0` of this witness the bound `‖h‖ ≤ 2` of `vn_le_two_of_xiDom`, which
needs a positive mass, is not available).  The old terms are given directly on the torus of index
`k + 1`; the lift of terms of index `k` (OLD-TERMS-LIFT) is not used.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Finset Set

section General

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Along the whole path the composed field `h` is the constant `h₀`** of the step, at every
scale `1 ≤ j ≤ k`. -/
theorem composedPairAtC_h (S : StepSetting d L N₁ m₁ k N ϱ) (s : ℝ) (x : S.E) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 k) :
    (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))).2 =
      fun _ i => (S.h₀ i : ℂ) := by
  have hj' := Finset.mem_Icc.1 hj
  unfold composedPairAtC
  simp only [hj'.2, ↓reduceDIte]
  funext z i
  show (if z ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
      (hj'.2.trans (Nat.le_succ k))).Ω 1 then (S.dataUC (S.psiAtC s x)).h z i else 0) = _
  have hz : z ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
      (hj'.2.trans (Nat.le_succ k))).Ω 1 := by
    simp [levelGS, hj'.1]
  simp only [hz, ↓reduceIte, S.dataUC_h]

/-- **`OldXiDomC` on the bounded-field domain**: if the step field `h₀` has `‖h₀‖ ≤ 2`, the
composed path data lie in `boundedFieldDom` for every class (the composed `h` is `h₀`). -/
theorem oldXiDomC_boundedFieldDom (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (h : vn (fun i => (S.h₀ i : ℂ)) ≤ 2) :
    S.OldXiDomC C (boundedFieldDom d L N₁ m₁ (k + 1) N ϱ) := by
  intro s _ x _ j hj X _
  show ∀ z, vn ((composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x))).2 z) ≤ 2
  intro z
  rw [composedPairAtC_h S s x hj]
  exact h

end General

section Witness

variable (m₁ : ℕ)

/-- The constants of the witness class: `E₀ = 1`, `c₉ = 1`, the others `0`. -/
def witConsts : Consts := ⟨0, 0, 0, 1, 0, 1, 0, 0, 0, fun _ => 0, 0⟩

/-- The terms of the witness class on the torus of index `2` (`d = L = 3`, `N₁ = 6`, `N = 2`):
`qTerms` with the energy at the level `1`, source part zero. -/
noncomputable def witTerms : Terms 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁) :=
  qTerms 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁) witConsts (fun _ => 0) 1

/-- The step class of the witness: the terms `witTerms`, `m₀ = 0`, `Ek = 0`. -/
noncomputable def witClass : StepClass 3 3 6 m₁ 1 2 (rhoSep m₁) := ⟨witConsts.m₀, witTerms m₁, 0⟩

/-- The zero regime (`ν ≡ 0`). -/
def witRegime : Regime 3 := ⟨0, fun _ => 0⟩

theorem witRegime_mass : witRegime.sfBgMass (1 + 1) = 0 := by
  simp [witRegime, Regime.sfBgMass, sfBgMassAt, physMass]

theorem bgHyp_wit : BgHyp 3 3 (1 + 1) (rhoSep m₁)
    (aIdeal 3 (1 + 1) (compWeight 3 1 (1 + 1))) (witRegime.sfBgMass (1 + 1)) := by
  rw [← compWeight_eq_aIdeal (by norm_num) (by norm_num) 1, witRegime_mass]
  exact bgHyp_rho m₁

/-- **T2: a non-zero member of the class on the step torus.**  `IsSF2` for `witTerms` on the
bounded-field domain at the torus index `k + 1 = 2` of the step witness. -/
theorem isSF2_witClass :
    IsSF2 witConsts witRegime (fun _ => 1) (compWeight 3 1)
      (boundedFieldDom 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁)) (witTerms m₁)
      (rho2 witConsts witRegime (fun _ => 1) (compWeight 3 1) (witTerms m₁) 0) 0 := by
  refine isSF2_qTerms (by norm_num [witConsts]) (by norm_num [witConsts]) (fun _ => le_rfl)
    (fun j => ?_) (fun j => ?_) (fun j _ _ Ψ h hd => hd) (bgHyp_wit m₁)
  · simp only [mul_zero, witConsts, one_mul]
    positivity
  · simp only [witConsts, one_mul]
    positivity

theorem qCore_unit : qCore (fun i => ((unitVec hN2 i : ℝ) : ℂ)) = 1 := by
  have h : ((∑ i, unitVec hN2 i * unitVec hN2 i : ℝ) : ℂ) = 1 := by
    have := sum_sq_unitVec hN2
    simp only [sq] at this
    rw [this]; simp
  unfold qCore
  push_cast at h
  exact h

/-- **The energy term of the witness is not identically zero**: at the constant unit field. -/
theorem witTerms_E_ne_zero (y : CTorus 3 3 6 m₁ (1 + 1)) (Ψ : Fld 3 3 6 m₁ (1 + 1) 2) :
    (witTerms m₁).E 1 y Set.univ Ψ (constFld (fun i => (unitVec hN2 i : ℂ))) ≠ 0 := by
  refine E_qTerms_const_ne_zero (by norm_num [witConsts]) y Ψ ?_
  rw [qCore_unit]; exact one_ne_zero

/-- **T3: `ClassParamMatch` at the step witness**, all four fields. -/
theorem classParamMatch_witClass (β δ : ℝ) :
    Nonempty (ClassParamMatch (witnessSetting m₁ β δ) (witClass m₁) witConsts witRegime
      (compWeight 3 1) (witTerms m₁)) :=
  ⟨⟨rfl, rfl, compWeight_eq_aIdeal (by norm_num) (by norm_num) 1, witRegime_mass.symm⟩⟩

/-- **T4: `OldXiDomC` on the bounded-field domain** (the domain of `isSF2_witClass`).  Not
vacuous (`k = 1`, the scale `j = 1` occurs); the domain is not the source chart (see the module
documentation). -/
theorem oldXiDomC_witClass (β δ : ℝ) :
    (witnessSetting m₁ β δ).OldXiDomC (witClass m₁)
      (boundedFieldDom 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁)) := by
  refine oldXiDomC_boundedFieldDom _ _ ?_
  have h1 : vn (fun i => ((unitVec hN2 i : ℝ) : ℂ)) ^ 2 = 1 := by
    rw [vn_sq]; simpa [sq] using sum_sq_unitVec hN2
  have h0 := vn_nonneg (fun i => ((unitVec hN2 i : ℝ) : ℂ))
  show vn (fun i => ((unitVec hN2 i : ℝ) : ℂ)) ≤ 2
  nlinarith

/-- **The old energy is non-zero along the whole path** (T6): at every point `(s, x)`,
`s ∈ [0, 1]`, `‖x‖ ≤ p₁`, the density `ℰ^{(1)}` of the witness class at the composed datum is
not zero. -/
theorem edens_ne_zero_along_path (β δ : ℝ) {s : ℝ} (x : (witnessSetting m₁ β δ).E) :
    Edens (witClass m₁).m₀ (witClass m₁).Tm 1
      (composedPairAtC (witnessSetting m₁ β δ).a (witnessSetting m₁ β δ).ν (Nat.le_succ 1) 1
        ((witnessSetting m₁ β δ).dataUC ((witnessSetting m₁ β δ).psiAtC s x))).1
      (composedPairAtC (witnessSetting m₁ β δ).a (witnessSetting m₁ β δ).ν (Nat.le_succ 1) 1
        ((witnessSetting m₁ β δ).dataUC ((witnessSetting m₁ β δ).psiAtC s x))).2 ≠ 0 := by
  classical
  rw [composedPairAtC_h (witnessSetting m₁ β δ) s x (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩)]
  unfold Edens
  have hloc : ∀ y (ψ : Fld 3 3 6 m₁ (1 + 1) 2),
      Eloc (witClass m₁).m₀ (witClass m₁).Tm 1 y ψ (fun _ i => ((witnessSetting m₁ β δ).h₀ i : ℂ))
        = ((cQ 3 3 6 m₁ (1 + 1) witConsts 1 : ℝ) : ℂ) := by
    intro y ψ
    show Eloc witConsts.m₀ (qTerms 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁) witConsts (fun _ => 0) 1) 1 y ψ
      (constFld (fun i => ((unitVec hN2 i : ℝ) : ℂ))) = _
    rw [Eloc_qTerms, qAvg_const]
    simp only [↓reduceIte]
    rw [qCore_unit, mul_one]
  simp only [hloc]
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ ?_
  · have hne : ((Finset.univ : Finset (CTorus 3 3 6 m₁ (1 + 1))).filter
        (Aligned (3 ^ 1))).Nonempty :=
      ⟨cbase (3 ^ 1) (0 : CTorus 3 3 6 m₁ (1 + 1)), by simpa using aligned_cbase _⟩
    exact_mod_cast hne.card_pos.ne'
  · have : 0 < cQ 3 3 6 m₁ (1 + 1) witConsts 1 := by
      unfold cQ witConsts; positivity
    exact_mod_cast this.ne'

/-- **T5: the three path-analyticity predicates for the witness pair `(S, C)`**, for every source
`g` with `‖g‖₁ < 1`, from the three landed theorems. -/
theorem witClass_pathAnalytic (β δ : ℝ) :
    (witnessSetting m₁ β δ).EdensAnalyticOnPath (witClass m₁) ∧
    ∀ g : Fld 3 3 6 m₁ (1 + 1) 2, l1 g < 1 →
      (witnessSetting m₁ β δ).FlocAnalyticOnPath (witClass m₁) g ∧
      ∀ y i, (witnessSetting m₁ β δ).MlocAnalyticOnPath (witClass m₁) g y i := by
  obtain ⟨hm⟩ := classParamMatch_witClass m₁ β δ
  have hd := oldXiDomC_witClass m₁ β δ
  have h := isSF2_witClass m₁
  exact ⟨edensAnalyticOnPath_of_oldXiDomC hm h hd, fun g hg =>
    ⟨flocAnalyticOnPath_of_oldXiDomC hm h hd hg, fun y i =>
      mlocAnalyticOnPath_of_oldXiDomC hm h hd hg y i⟩⟩

end Witness

end Balaban.Fluctuation
