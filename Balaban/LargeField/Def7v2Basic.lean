/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Variants
public import Balaban.LargeField.Def7Basic

/-!
# Def-7 v2, part 7: consequences (Lemma II.6.3 and the restriction facts) -- DRAFT

The consequence lemmas of `Def7Basic` / `Def7Counts` on the second version.  **They are insensitive
to the small-field mass and to the correction term**: Lemma II.6.3 (a) (`Rep.opBound_of_data`),
(c) (`Rep.tau_le_Gpost`, `Rep.p2_le_Gpost(_flat)`) and (d) (`Rep.rg_ripe`, `Rep.lf2Hyp`,
`Rep.budget_of_LF2`, `Rep.budgetFlat_of_budget`, `gpost_eq_gpre`) are statements about the
large-field part `F.lf nK : Rep …` of a representation (histories, step and kept data, budgets);
the second version changes only `form` (D1), `sfData` (D2), `bdry` (D7) and adds `corr`, so these
lemmas apply to `F.lf nK` of an `IsRep2` verbatim; the wrappers below only read the clause (D6) of
`IsRep2`.  Nothing in the derivation is sensitive; the only change is in the restriction facts:

* `IsRep2.mem_repClass2`;
* `D2SF2.toFlat2`, (D9) ⇒ (D9♭) is `D9Coeff.toFlat` (unchanged);
* `IsRep2.toFlat` (Lemma IV.2.1): `IsRep2_{k₀}` implies `IsRep2^♭_{k₀}` for the same
  representation (the form clause, `corr`, `bdry` are the same; (D2) ⇒ (D2♭) is `toFlat2`);
* `D7Bdry2.toD7Bdry`, `IsRepCorr`-comparison: see `Def7v2Class`, `Def7v2Form`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7
  RegionHistory

section SF

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P6 : Def6.Consts} {k0 : ℕ}
  {sf : SFData d L m₁ k N ϱ}

/-- **(D2) ⇒ (D2♭), second version** (§II.6.3 (iii), audit P2-01): the mass range `ν_k ≤ ν̄`
implies `ν_k ≤ 1`.  Insensitive to the mass of the regime (the coefficient bounds of
`IsSFFamily2` are those of Def-6). -/
theorem D2SF2.toFlat2 (h : D2SF2 P6 k0 sf (fun _ => 1)) : SFFlat2 P6 k0 sf := by
  obtain ⟨ρsf, hF⟩ := h.sfClass
  exact
    { admissible := hF.admissible
      coeff :=
        { flow := hF.coeff.flow
          beta_gt := hF.coeff.beta_gt
          nu_pos := hF.coeff.nu_pos
          nu_le := hF.coeff.nu_le.trans (nuBar_le_one hF.admissible)
          a_ge := hF.coeff.a_ge
          a_lt := hF.coeff.a_lt }
      torus := ⟨ρsf, fun N₁ _ => hF.torus N₁⟩
      torusIndep := hF.torusIndep
      renorm := hF.renorm
      rTerms := h.rTerms }

end SF

section Class

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {β ν : ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
  {k : ℕ} {ϱ : ℝ} {hM6 : M = S.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ K}
  {F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ}
  {ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
    (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ}
  {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N} {vc : CorrCoef S.d}

/-- A represented density family lies in the class `𝓡2_k(𝖼)`. -/
theorem IsRep2.mem_repClass2 (h : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc) :
    ρ ∈ RepClass2 S R k0 K M N geo cs P P6 C7 β ν hv rH k ϱ hM6 hkK :=
  ⟨F, St, vc, h⟩

/-- **Lemma II.6.3 (c), first inequality, on the second version**: under (D6) of `IsRep2`,
`G_k(Z) ≥ τ_{k+1}` for every history of the representation on the torus `n_K`. -/
theorem IsRep2.tau_le_Gpost (h : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (G : S.Good) (nK : ℕ) [NeZero nK] {A : LabHist S (sides S.L K nK) R k0 K}
    (hA : A ∈ (F.lf nK).hist) (c : PostComp A k) : S.tau (k + 1) ≤ (F.lf nK).Gpost A k c.1 :=
  (F.lf nK).tau_le_Gpost G (h.budget nK) hA c

/-- **Lemma II.6.3 (c) on the second version**: `G_k(Z) ≥ 2 p₂(β_k)`. -/
theorem IsRep2.p2_le_Gpost (h : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (G : S.Good) {a ε : ℝ} {nRun : ℕ → ℝ} (hrun : RunningHyp S.d S.L β ν a ε P.beta nRun)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (h3 : 3 ≤ lamHat S.d S.L β a 0) (nK : ℕ)
    [NeZero nK] {A : LabHist S (sides S.L K nK) R k0 K} (hA : A ∈ (F.lf nK).hist)
    (c : PostComp A k) : 2 * p2Run S.A2 S.p2 P.beta k ≤ (F.lf nK).Gpost A k c.1 :=
  (F.lf nK).p2_le_Gpost G (h.budget nK) hrun hlam h3 hA c

/-- **Lemma II.6.3 (c) for `IsRepFlat2`**: `G_k(Z) ≥ p₂(β_{k₀})`. -/
theorem IsRepFlat2.p2_le_Gpost_flat {khat : ℕ}
    (h : IsRepFlat2 S R k0 K M N geo cs P P6 C7 β ν hv rH k khat hM6 hkK F ρ St vc)
    (G : S.Good) {a ε : ℝ} {nRun : ℕ → ℝ} (hrun : RunningHyp S.d S.L β ν a ε P.beta nRun)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (h3 : 3 ≤ lamHat S.d S.L β a 0) (nK : ℕ)
    [NeZero nK] {A : LabHist S (sides S.L K nK) R k0 K} (hA : A ∈ (F.lf nK).hist)
    (c : PostComp A k) : p2Run S.A2 S.p2 P.beta k0 ≤ (F.lf nK).Gpost A k c.1 :=
  (F.lf nK).p2_le_Gpost_flat G (h.budget nK) hrun hlam h3 hA c

/-- **Lemma II.6.3 (d) on the second version**: the abstract history of LF-2 of a history of the
representation (insensitive to the second version: it reads only `pin`). -/
noncomputable def IsRep2.lf2Hyp
    (h : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (B : BudgetSetup S P) (ok : S.Ok) (hKtop : K ≤ k + 1) (nK : ℕ) [NeZero nK]
    (A : LabHist S (sides S.L K nK) R k0 K) (hA : A ∈ (F.lf nK).hist) : LF2Hyp S (sides S.L K nK) k0 K :=
  (F.lf nK).lf2Hyp B ok (h.pin nK) hKtop A hA

/-- **Lemma IV.2.1 (transfer), second version: `IsRep2_{k₀}` implies `IsRepFlat2_{k₀}`** for the
same representation, under the conditions of LF-2 and a horizon `K ≤ k₀ + 1`, with the a priori
horizon `khat`.  Not sensitive to the second version: `form`, `corr`, `bdry` are the same
clauses, (D2) ⇒ (D2♭) is `D2SF2.toFlat2`, (D9) ⇒ (D9♭) is `D9Coeff.toFlat`, (D6) ⇒ (H6♭) is
`Rep.budgetFlat_of_budget`. -/
theorem IsRep2.toFlat (h : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hk : k = k0) (G : S.Good) (B : BudgetSetup S P) (hK : K ≤ k + 1) {khat : ℕ} (hk0 : k0 ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    IsRepFlat2 S R k0 K M N geo cs P P6 C7 β ν hv rH k khat hM6 hkK F ρ St vc where
  range := hk.ge
  coh := h.coh
  field := h.field
  complete := h.complete
  form := h.form
  corr := h.corr
  sfData := h.sfData.toFlat2
  pin := h.pin
  opBound := h.opBound
  budget := fun nK _ => (F.lf nK).budgetFlat_of_budget G B (h.pin nK) hK (Nat.lt_succ_self k) hk
    hk0 hH1 hH2 (h.budget nK)
  bdry := h.bdry
  coherent := h.coherent
  coeff := h.coeff.toFlat (by obtain ⟨_, hF⟩ := h.sfData.sfClass; exact hF.admissible)

end Class

end Balaban.LargeField.Def7v2
