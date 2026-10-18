/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.ClassStep
public import Balaban.LargeField.R.RFieldProjection
public import Balaban.LargeField.Operators.StepVacuumR5
import Mathlib.Tactic.Linarith

/-!
# The operation `R` of the spine from three sub-inputs

`rInput_of_parts` proves `RInput` (`Spine/ClassStep.lean`) from three named sub-inputs, following
LFR Theorem III.10.8 and Lemma III.8.4 (P7 Theorem 2, (1.3)-(1.7), (3.1)-(3.29)) with the
representation of the output as a gas of removed clusters (ruling R4).

The output of `R` on a member of `ℛ^pre_k` is a representation that has the following parts.
* The **small-field data** are those of the input plus one new term `ℛ''_m` of the remainders at
  the index `m = m₀ + m₁` (P7 (3.28)-(3.29)): `sf' = sf + ℛ''` (`sfAddRem`). Its coefficients,
  masses, normalizations, `E_k` and terms `Tm` are those of the input, so `Coh`, `FieldClauses`,
  `D1CorrLim` and `D9Coeff` and the running constants are carried over (`coh_addRem`, ...); `D8SF`
  and the bound of (D2) are those of the input plus those of `ℛ''` (`d8SF_addRem`,
  `sfData_of_remainder_added`).
* The **histories** `𝔄'` are a complete set at `(k, k + 1)` (the outcome `removed` / `kept ϰ` of
  every ripe component is recorded; `IsComplete k (k + 1)`).
* The **step data** `SD` are those of the input. The **kept data** `κK`, `KD` and the histories are
  new (pinned exponent at the scale `k`, the bounds `ϰ₄`, `ϰ₅` of the kept outcomes of Theorem III.8.9,
  the budget `(H6′)` with the kept exponents).
* The **boundary terms** `ℬ'` are those of the gas of removed clusters: the heavy objects are the
  removed clusters, their couplings are decorated by the removed members they meet,
  `b_X(S) = ℬ(X, 𝔸′ ∪ S) - ℬ̂(X; 𝔸′) + ℬ′_X(S)` (P7 (3.22)-(3.27)).

The sub-inputs are statements about the output data, quantified over the input record, because
no landed operator constructs the output representation (the pieces of `Balaban/LargeField/R/` are
for abstract gases, kernels and normalizations).
* `RVacuumInput` (the vacuum constants, R5, R5′; P6 (3.2)): a member of `ℛ^pre_k` has a record of the same density
  whose step data carry the vacuum constants of the flow (`VacuumTied`, `StepData.VacuumTie`). It is
  asked of the input because `IsRepPre2` does not carry the tie.
* `RKeptInput` (the kept data; LFR Lemma III.10.5, Definition III.10.6, Theorem III.8.9 (a), (b)):
  for a member of `ℛ^pre_k` there are histories complete at `(k, k + 1)` and kept data (`κK`, `KD`)
  for the same step data with the pinned exponents (`D4Pin (k + 1)`), the operator bound at `k + 1`
  (`D5Bound`), the budget (`D6Budget`) and torus coherent (`KeptOutput`).
* `RGasInput` (the gas; LFR Theorem III.10.8 (b), (c), Lemma III.8.4, P7 (3.10)-(3.29)): for a
  vacuum tied record and such kept data there are boundary terms `ℬ'`, a term `ℛ''` and a density `ρ'` such that `ℛ''` has the
  bound of (D2) with the allowance `1/2` at `m` and is torus coherent, `ρ'` has the form (D1) of the
  output, the boundary terms satisfy (D7), the output is torus coherent, and `∫ ρ' = ∫ ρ`
  (`GasOutput`).

Proved here: the carrying over of the small-field clauses along `sf' = sf + ℛ''`
(`coh_addRem`, `field_addRem`, `corr_addRem`, `coeff_addRem`, `d8SF_addRem`), the form of the
output family (`repFamPost`), and the assembly (the output is in `ℛ_k` with the same running
constants, `IsComplete`, `sfData_of_remainder_added`).

The open sub-sub-inputs of `RGasInput` (window bound of the removed histories, the small factor
(3.10″), the vacuum constants, ℬ′, the kept bounds) are listed in `notes/phase1/SPINE.md`, section
"RInput sub-inputs". The three sub-inputs need the exemption of the seven inputs (rule 10), as `RInput`
does. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### The small-field data of the output: `sf' = sf + ℛ''`
-/

section SF

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The term `ℛ''` that `R` adds to the remainders `ℛ^{(k)}_n` (P7 (3.28)-(3.29)), as a family of
functions on every Def-6 torus. -/
abbrev RemTerm (d L m₁ k N : ℕ) : Type :=
  ∀ (N₁ : ℕ) [NeZero N₁], ℕ → Set (Localization.CTorus d L N₁ m₁ k) → Def6.Fld d L N₁ m₁ k N →
    Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ

/-- The small-field data with the remainders `ℛ^{(k)}_n + ℛ''_n`. -/
def sfAddRem (sf : SFData d L m₁ k N ϱ) (Rpp : RemTerm d L m₁ k N) : SFData d L m₁ k N ϱ :=
  { sf with Rt := fun N₁ _ nn X ψ hh g => sf.Rt N₁ nn X ψ hh g + Rpp N₁ nn X ψ hh g }

/-- The small-field data with the remainders `ℛ''_n` alone. -/
def sfWithRem (sf : SFData d L m₁ k N ϱ) (Rpp : RemTerm d L m₁ k N) : SFData d L m₁ k N ϱ :=
  { sf with Rt := Rpp }

/-- `D8SF` of the sum: the clause on `Tm` of the input and the sum of the two clauses on the
remainders. -/
theorem d8SF_addRem {m₀ : ℕ} {sf : SFData d L m₁ k N ϱ} {Rpp : RemTerm d L m₁ k N}
    (h : D8SF m₀ sf) (h' : D8SF m₀ (sfWithRem sf Rpp)) : D8SF m₀ (sfAddRem sf Rpp) where
  M_eq := h.M_eq
  R_eq := fun nn X' ψ hh g N₁ N₂ _ _ a1 a2 a3 a4 => by
    have e1 := h.R_eq nn X' ψ hh g N₁ N₂ a1 a2 a3 a4
    have e2 := h'.R_eq nn X' ψ hh g N₁ N₂ a1 a2 a3 a4
    simp only [sfAddRem, sfWithRem] at e1 e2 ⊢
    rw [e1, e2]

/-- `D1CorrLim` is carried over to `sf + ℛ''`. -/
theorem corr_addRem {m₀ : ℕ} {sf : SFData d L m₁ k N ϱ} {Rpp : RemTerm d L m₁ k N}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d} (h : D1CorrLim m₀ sf St hv vc) :
    D1CorrLim m₀ (sfAddRem sf Rpp) St hv vc where
  src_pos := h.src_pos
  v1_lim := h.v1_lim
  v2_lim := h.v2_lim

/-- `D9Coeff` is carried over to `sf + ℛ''`. -/
theorem coeff_addRem {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    {Rpp : RemTerm d L m₁ k N} (h : D9Coeff P6 k0 sf) : D9Coeff P6 k0 (sfAddRem sf Rpp) where
  beta_gt := h.beta_gt
  nu_pos := h.nu_pos
  nu_le := h.nu_le
  k_le := h.k_le

end SF

section Carry

variable {S : Setting} {R : ℕ → ℝ} {k0 M : ℕ} [NeZero S.L] {N : ℕ} {cs : OpConsts}
  {P : BudgetConsts} {P6 : Def6.Consts} {C7 : Consts7} {β ν : ℝ} {k : ℕ} {ϱ : ℝ}
  {sf : SFData S.d S.L C7.m₁ k N ϱ} {Rpp : RemTerm S.d S.L C7.m₁ k N}

/-- `Coh` is carried over to `sf + ℛ''`: it does not read the remainders. -/
theorem coh_addRem (h : Coh S R k0 M cs P P6 C7 β ν k sf) :
    Coh S R k0 M cs P P6 C7 β ν k (sfAddRem sf Rpp) where
  M_eq := h.M_eq
  M_pow := h.M_pow
  lam_eq := h.lam_eq
  R_eq := h.R_eq
  k0_eq := h.k0_eq
  a_free := h.a_free
  beta_cs := h.beta_cs
  beta_P := h.beta_P
  z_cs := h.z_cs
  nu_cs := h.nu_cs
  delta_cs := h.delta_cs
  p0_cs := h.p0_cs
  B0_cs := h.B0_cs

/-- `FieldClauses` is carried over to `sf + ℛ''`. -/
theorem field_addRem {hv : EuclideanSpace ℝ (Fin N)} (h : FieldClauses S k0 k cs sf hv) :
    FieldClauses S k0 k cs (sfAddRem sf Rpp) hv where
  h_unit := h.h_unit
  mu_eq := h.mu_eq
  muBg_eq := h.muBg_eq
  muAct_eq := h.muAct_eq

end Carry

/-!
### The output family
-/

section Post

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {k m₁ : ℕ} {ϱ : ℝ}

/-- The boundary terms `ℬ^{(k)}(X, 𝔸; ψ, ψ', h, g)` of a representation on one torus (the type of
the field `Rep.B`). -/
abbrev BTerms (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M]
    [NeZero S.L] (N k : ℕ) : Type :=
  LabHist S n R k0 K → Finset (Torus S.d (n k)) → MultiFieldC S n M K N → MultiFieldC S n M K N →
    (Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ

/-- **The family of the output of `R`**: the small-field data `sf + ℛ''`, and on every torus the
large-field part `lf₁` (histories, kept data, step data) with the boundary terms replaced by `ℬ'`. -/
def repFamPost (F : RepFam S R k0 K M N geo cs P k m₁ ϱ)
    (lf₁ : ∀ (nK : ℕ) [NeZero nK], Rep S (sides S.L K nK) R k0 K M N (geo nK) cs P k)
    (B' : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k)
    (Rpp : RemTerm S.d S.L m₁ k N) : RepFam S R k0 K M N geo cs P k m₁ ϱ where
  sf := sfAddRem F.sf Rpp
  lf := fun nK _ => { lf₁ nK with B := B' nK }

end Post

/-!
### The input record
-/

/-- `PreClassAt` is the existence of a record (`PreRec`, `Spine/ClassStep.lean`). -/
theorem preClassAt_iff {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k r : ℕ} [NeZero T.M] [NeZero T.L]
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ} :
    PreClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r ρ νk ↔
      Nonempty (PreRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r ρ νk) := Iff.rfl

/-- **The vacuum constants of the step data are those of the flow** (R5, R5′; P6 (3.2), P5 (3.18)):
for every torus, the constants `vacE`, `vacEpp`, `vacEppp` of the creating step of every localized
history are `E_k`, `E_k + δ″_k`, `E_k + δ‴_k`, the offsets not depending on `E_k` (`StepData.VacuumTie`).
The boundary factor of a step is then `b_k = b⁰_k − (E_k |Z_k^c ∖ Ω_{k+1}|_k + E″_k |Ω_{k+1} ∖ Ω″_{k+1}|_k +
E‴_k |Ω″_{k+1} ∩ Z_{k+1}|_k)` with `b⁰_k` bounded by constants free of `E`. -/
def VacuumTied {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7} {PB : BudgetConsts}
    {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf k r : ℕ}
    [NeZero T.M] [NeZero T.L] {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}
    (rec : PreRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r ρ νk) : Prop :=
  ∀ (nK : ℕ) [NeZero nK], ∃ dpp dppp : ℕ → ℝ,
    (rec.F.lf nK).SD.VacuumTie Set.univ rec.F.sf.E dpp dppp

/-!
### The output data and the two sub-inputs
-/

section Outputs

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {k m₁ : ℕ} {ϱ : ℝ}

/-- The zero boundary terms. -/
def bZero : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k :=
  fun _ _ _ _ _ _ _ _ => 0

/-- The zero remainder term. -/
def remZero : RemTerm S.d S.L m₁ k N := fun _ _ _ _ _ _ _ => 0

/-- **The output of the kept half of `R`** on a family with the large-field part `lf₁`: on every
torus the pinned exponents `D4Pin (k + 1)` (the exponent `κ_k` of a kept component is the pre-`R`
exponent `κ^pre_k`), the operator bound `D5Bound` at `k + 1` (the bound (1.26) of the kept
operators with the exponent `κ_k - C_R λ_k^{2d+1} + γ(ϰ)`, LFR Theorem III.8.9 (a), (b)), the budget
`D6Budget` (H6′), and the torus coherence of the step and kept data (the family `F` with these
data and no boundary terms is `LFCoherent`). -/
def KeptOutput (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k m₁ ϱ)
    (lf₁ : ∀ (nK : ℕ) [NeZero nK], Rep S (sides S.L K nK) R k0 K M N (geo nK) cs P k) : Prop :=
  (∀ (nK : ℕ) [NeZero nK],
    D4Pin (k + 1) (lf₁ nK) ∧ D5Bound (k + 1) hkK (lf₁ nK) ∧ D6Budget (lf₁ nK)) ∧
  LFCoherent (repFamPost F lf₁ bZero remZero)

/-- **The output of the gas half of `R`** (the new boundary terms `ℬ'`, the new remainder `ℛ''`,
the density `ρ' = R ρ`), for the input density `ρ` with the family `F`, the kept data `lf₁`:
* `ℛ''` satisfies the bounds of (D2) at the index `m = m₀ + m₁` with the allowance `1/2` (the other
  half of the allowance of `IsRepPre2`, P7 (3.28)-(3.29)) and is torus coherent (`D8SF`);
* `ρ'` has the form (D1) of the output family;
* the boundary terms satisfy (D7), the post-`R` record;
* the output family is torus coherent;
* `∫ ρ' = ∫ ρ` on every torus and every source of the unit `ℓ¹` ball (P7 (1.7)). -/
def GasOutput {P6 : Def6.Consts} {C7 : Consts7} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (vc : CorrCoef S.d)
    (ρ ρ' : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ)
    (lf₁ : ∀ (nK : ℕ) [NeZero nK], Rep S (sides S.L K nK) R k0 K M N (geo nK) cs P k)
    (B' : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k)
    (Rpp : RemTerm S.d S.L C7.m₁ k N) : Prop :=
  (∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 F.sf.β F.sf.ν F.sf.a N₁ (Rpp N₁)
    (fun nn => if nn = P6.m₀ + C7.m₁ then 1 / 2 else 0)) ∧
  D8SF P6.m₀ (sfWithRem F.sf Rpp) ∧
  (∀ (nK : ℕ) [NeZero nK], D1Form2 ((repFamPost F lf₁ B' Rpp).ctx hM6 hkK nK) vc
    ((repFamPost F lf₁ B' Rpp).lf nK) hv (ρ' nK)) ∧
  (∀ (nK : ℕ) [NeZero nK], D7Bdry2Post (fineFrame S (sides S.L K nK) K hM6) (sides_hnn S.L K nK)
    hkK ((repFamPost F lf₁ B' Rpp).lf nK) (fun A => (A.H.step k).Z) (repFamPost F lf₁ B' Rpp).weights cs.mu
    (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0 P6.κ hv rH) ∧
  LFCoherent (repFamPost F lf₁ B' Rpp) ∧
  ∀ (nK : ℕ) [NeZero nK] (g : GIdx S (sides S.L K nK) M K N → ℂ), g ∈ l1Ball _ →
    ∫ ψ, ρ' nK ψ g = ∫ ψ, ρ nK ψ g

end Outputs

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A4-2v, the vacuum constants (R5, R5′; P6 (3.2), P5 (3.18), LFR proof of Theorem IV.1.1).**
For `1 ≤ k ≤ k₀`, every member of `ℛ^pre_k` with (I.2) up to `k` and torus coherent has the same density as
a record whose step data carry the vacuum constants of the flow (`VacuumTied`). The kernels are not changed:
`b⁰_k` is `b_k` plus the vacuum term of the flow, and the content is that `b⁰_k` is bounded by constants free
of `E` (`StepData.b0_bound`; W965 normalization, W968 vacuum). -/
def RVacuumInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
  ∀ _rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk,
    ∃ rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk, VacuumTied rec

/-- **A4-2a, the kept half of `R` (LFR Lemma III.10.5, Definition III.10.6, Theorem III.8.9 (a), (b);
P7 (1.3)-(1.6)).** For `1 ≤ k ≤ k₀`, a member of `ℛ^pre_k` with (I.2) up to `k` and torus coherent
has, on every torus, histories complete at `(k, k + 1)` (the outcome, removed or kept with a label,
of every ripe component is recorded) and kept data for the step data of the input with the pinned
exponents, the operator bound at `k + 1`, the budget, and torus coherent (`KeptOutput`). The new
kept data are the bounds `ϰ₄`, `ϰ₅` of the kept outcomes (Lemma III.5.3 for the ripe components,
Theorem III.8.9 (a), (b)) and the pin `κ_k = κ^pre_k`. -/
def RKeptInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
  ∀ rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk,
    ∃ lf₁ : ∀ (nK : ℕ) [NeZero nK], Rep 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
      (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N
      (rec.geo nK) rec.cs rec.P k,
      (∀ (nK : ℕ) [NeZero nK],
        IsComplete k (k + 1) (lf₁ nK).hist ∧ (lf₁ nK).SD = (rec.F.lf nK).SD) ∧
      KeptOutput rec.hkK rec.F lf₁

/-- **A4-2b, the gas half of `R` (LFR Theorem III.10.8 (b), (c), Lemma III.8.4; P7 (3.1)-(3.29);
ruling R4).** For `1 ≤ k ≤ k₀`, a member `ρ` of `ℛ^pre_k` with (I.2) up to `k` and torus coherent, and
kept data as in `RKeptInput`, there are new boundary terms `ℬ'`, a new remainder `ℛ''` and the density
`ρ' = R ρ` (`GasOutput`): the ripe components that are removed are summed as a gas of removed clusters
(the heavy objects), whose couplings are decorated by the removed members they meet,
`b_X(S) = ℬ(X, 𝔸′ ∪ S) - ℬ̂(X; 𝔸′) + ℬ′_X(S)` (P7 (3.22)-(3.27)), and whose activities are bounded
through the small factor (3.10″) of the removed operators (the window bound with the cancellation
identity, the vacuum constants of the step data); the gas gives the new term `ℛ''_m` and the new
boundary terms; `∫ R ρ = ∫ ρ`. -/
def RGasInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
  ∀ rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk,
  VacuumTied rec →
  ∀ lf₁ : (∀ (nK : ℕ) [NeZero nK], Rep 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
      (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N
      (rec.geo nK) rec.cs rec.P k),
    (∀ (nK : ℕ) [NeZero nK],
      IsComplete k (k + 1) (lf₁ nK).hist ∧ (lf₁ nK).SD = (rec.F.lf nK).SD) →
    KeptOutput rec.hkK rec.F lf₁ →
    ∃ (B' : ∀ (nK : ℕ) [NeZero nK], BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N k)
      (Rpp : RemTerm d (T κ c₉).L (C7 κ c₉).m₁ k N)
      (ρ' : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]),
      GasOutput (hv := h) (rH := rH κ c₉) rec.hM6 rec.hkK rec.F rec.vc ρ ρ' lf₁ B' Rpp

/-- **`RInput` from its three sub-inputs** (LFR Theorem III.10.8, Lemma III.8.4). The vacuum half
(`RVacuumInput`) gives a record of the same density with the vacuum constants of the flow. The kept half gives
the large-field part `lf₁`, the gas half the boundary terms `ℬ'`, the remainder `ℛ''` and the
density `ρ'`. The output family is `repFamPost`: its small-field data are `sf + ℛ''`, so `Coh`,
`FieldClauses`, `D1CorrLim`, `D9Coeff` and the running constants are those of the input, `D8SF` is
the sum (`d8SF_addRem`) and (D2) is `sfData_of_remainder_added` (the allowance `1/2` of the input plus
the allowance `1/2` of `ℛ''` at `m`); `complete` is the completeness of the histories of the kept half;
the form, (D7), the coherence and the integral are those of the gas half; `D4Pin`, `D5Bound` and
`D6Budget` are those of the kept half (they do not read the boundary terms). The threshold is the
larger of the two thresholds. -/
theorem rInput_of_parts (hV : RVacuumInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hK : RKeptInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hG : RGasInput d N T P6 C7 PB cs₀ M1 c rH ϱ) : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₀, hβ₀⟩ := hV κ hκ c₉ hc₉
  obtain ⟨β₁, hβ₁⟩ := hK κ hκ c₉ hc₉
  obtain ⟨β₂, hβ₂⟩ := hG κ hκ c₉ hc₉
  refine ⟨max β₀ (max β₁ β₂), fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk hρ => ?_⟩
  obtain ⟨rec₀⟩ := preClassAt_iff.1 hρ
  obtain ⟨rec, hvac⟩ :=
    hβ₀ β (le_of_max_le_left hβ) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec₀
  obtain ⟨lf₁, hlf, hker⟩ :=
    hβ₁ β (le_of_max_le_left (le_of_max_le_right hβ)) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec
  obtain ⟨B', Rpp, ρ', hRpp, hD8, hform, hbdry, hcoh, hint⟩ :=
    hβ₂ β (le_of_max_le_right (le_of_max_le_right hβ)) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec
      hvac lf₁ hlf hker
  refine ⟨ρ', ?_, hint⟩
  refine ⟨rec.hM6, rec.hkK, rec.R, rec.geo, rec.cs, rec.P, repFamPost rec.F lf₁ B' Rpp, rec.St,
    rec.vc, rec.geoTie, rec.tie_aKer, rec.tie_Cpsi, rec.tie_Cb, rec.tie_aw, rec.tie_c1,
    rec.tie_c2, rec.tie_H0, ?_, rec.β0, rec.ν0, rec.νk, rec.run, hcoh, rec.Ev, rec.vac⟩
  exact
    { coh := coh_addRem rec.pre.coh
      field := field_addRem rec.pre.field
      complete := fun nK _ => (hlf nK).1
      form := hform
      corr := corr_addRem rec.pre.corr
      sfData := sfData_of_remainder_added rec.pre.sfData rfl rfl rfl rfl rfl Rpp
        (fun _ _ _ _ _ _ _ => rfl) hRpp
      pin := fun nK _ => (hker.1 nK).1
      opBound := fun nK _ => (hker.1 nK).2.1
      budget := fun nK _ => (hker.1 nK).2.2
      bdry := hbdry
      coherent := d8SF_addRem rec.pre.coherent hD8
      coeff := coeff_addRem rec.pre.coeff }

end Inputs

end Balaban.RootFSpine
