/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.SFStep
public import Balaban.Spine.SFVacuumRatio
public import Balaban.Spine.RStep
public import Balaban.Spine.Transfer
public import Balaban.LargeField.Def7Counts
public import Balaban.LargeField.Def7WitData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The large-field half of the step from a sub-spine (A4-1h)

`lfStepInput_of_parts` proves the sub-input `LFStepInput` of the small-field step (A4-1h,
`Spine/SFStep.lean`; LF-3 (b)–(d), (h), LFR Theorem IV.1.1; P5 §§2–3, P6 §§2–3) from named parts,
each one clause of the source's construction, at general `d, N` on the class carriers.

**The construction map.** As for the small-field half (`Φ`, `ΦE`), the parts are properties of one
construction: the clause (D1) of the step density holds only for the histories, kernels and
boundary terms that the step constructs, and the other clauses (bounds, coherence) do not determine
these data. So the sub-spine takes the large-field data created by the step as a map `Λ`
(`LFStepMap`): for every record `rec` of `ℛ_k` the data `LFStepRaw` on every torus of the family
(the histories `𝔄'`, the step kernels `(K_j, b_j)`, the boundary terms `ℬ^{(k+1)}`, the vacuum
normalization `s`). A `Rep` also contains proofs ((S0)–(S2) are fields of `StepData`), so the map
gives the data, and a part asserts that step data with these kernels exist.

**Maps, definitions and existentials** (rule: what the source defines by a formula is a map, what it
only asserts to exist is an existential inside the part):
* maps, fields of `LFStepRaw`: the histories (LF-3 (c): the histories of `rep` followed by every step
  record and the hull closure), the step kernels (LF-3 (d): the quiet kernels and the kernels of
  P5 (2.47)·P6 (3.2) with the local background, the boundary factors of P6 (2.32)–(2.33), (3.3)),
  the boundary terms `ℬ^{(k+1)}` (LFR Lemma IV.1.5: the three kinds of P5 p. 512, P6 pp. 14–15), the
  normalization `s = L^d E_k - e₀/|T^{(k+1)}_1|` (`Spine/SFVacuum.lean`);
* defined here (formulas whose clauses are then proved, not asked): the operator constants
  `cs' = succOpConsts` and the budget constants `P' = succBudgetConsts` (those of `rec` at the scales
  `≤ k`, the running constants of the image `Φ rec.F.sf` at `k + 1`, LFR §II.1.1), and the kept data
  `succKD` with the exponents of `rec` ("no kept data are created by a step": the kept data of `rec`
  restricted to the scales `≤ k`, `KeptData.upTo`, which is (S3) at `cs'`);
* existentials inside a part: the Gaussian witnesses of (S1), the remainder `b⁰` and the offsets
  `δ″, δ‴` of the vacuum constants (inside `LFStepDataInput`: read by no other part; `b⁰` is
  determined by `b_vac`), the proofs of (S0)–(S2) (the structure `StepData`), and the coefficient
  data `St', vc'` (P1 (3.106)–(3.110): thermodynamic limits that the source asserts to exist, inside
  `LFCorrInput`; the form clause is asked for every `vc'` with `D1CorrLim`, which determines `vc'` at
  the scales the form reads).

**The parts** (statements below; sources in the docstrings; status in `notes/phase1/SPINE.md`):
* `LFHistInput` (LF-3 (c)): the histories are complete up to `k + 1`;
* `LFStepDataInput` (row (g1); Lemmas IV.1.3, IV.1.4, IV.1.6, Lemma II.5.14; R5, R5′): step data
  (S0)–(S2) with the kernels of the map, tied to the vacuum flow extended by `ΦE`;
* `LFBdryInput` (row (g2); Lemma IV.1.5): (D7) of the boundary terms at the physical field;
* `LFBdrySrcInput` (row (g5); blocker 2, leaf 5): (D7) at the other fields of the pinned ball;
* `LFFormInput` (row (g3); P5 (1.8), (1.26), P5 §§2–3, P6 §§2–3): (D1) of the step density;
* `LFOpBoundInput` (row (g3), (D5)): **proved** from `LFSignInput` (`z_j > 0`) by LFR Lemma
  II.6.3 (a) (`Rep.opBound_of_data`), `lfOpBoundInput_of_signs`;
* `LFPinInput` (row (g4), (D4)): the kept exponents are pinned;
* `LFBudgetInput` (row (g4), (D6)): **proved** from `LFPinInput` and the prefix by LF-2 (i) on the
  counter history truncated at `k + 1` (`Rep.budgetPre_of_LF2_trunc`), `lfBudgetInput_of_pin`;
* `LFCoherenceInput` (row (h); LF-3 (h), D-IV.9): `LFCoherent` of the successor;
* `LFCorrInput` (row (h); P1 (3.110)): the coefficient data of the image exist.
The kept data (row (g1), (S3)) are not a part: `succKD` is proved to be kept data.

**Proved in the assembly**: the existential package of `LFStepInput`; `cs'`, `P'` and their seven
ties to the outer constants; `Coh` and `FieldClauses` at `k + 1` (`coh_succ`, `field_succ`); (D2),
(D8), (D9) from the hypotheses on the image; (D7) of `IsRepPre2` from the physical-field and the
pinned-ball parts (`D7Bdry.toD7Bdry2_of_ball`); the vacuum tie of the chosen step data with
`vacExt rec.Ev k (ΦE …)`.

**The SF→LF interface (watch item of W1096).** The step does not need the interface clause of
`IsRep2WithInterface`: under the landed field clauses (ruling R2) the backgrounds of the actions of
both halves are complete (`muBg_eq_sfBgMass_of_fieldClauses`: `cs.muBg j` is the small-field solver
mass `sfBgMass j`; the main action of a step reads `cs.muBg (k + 1)`), so the chord of
`SFtoLFInterface` (the action at `lfBgMass` minus the action at `sfBgMass`) is no term of an exponent
of `IsRepPre2`; the mass `cs.mu` (zero below `k₀`) enters only the sharp characteristic functions.
What the step reads from its input in the region that becomes large-field is (D1) and (D2) of the
input. Two range clauses of the input that the class does not carry are asked by the parts instead:
the vacuum tie of the input's step data at the old steps (in `LFStepDataInput`; it is the estimate of
A4-2v, `VacuumB0Bound`, blocked on ruling R10: `norm_stepVacuumTerm_le_of_stepData`) and `z_j > 0` at
the old scales (in `LFSignInput`).

Rule 10: `LFStepRaw` is inhabited (`LFStepRaw.zero`), `Matches` (`LFStepRaw.matches_zero`) and
`D7BdryBall` (`d7BdryBall_of_hist_eq_empty`) are satisfiable;
the parts and the combinators `LFImageInput`, `RepRec.SuccFams` need the exemption of the spine inputs.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Multiscale
  Balaban.Background RegionHistory

namespace Balaban.RootFSpine

/-!
### The large-field data created by a step
-/

section Raw

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- **The large-field data created by a step**, at the scale `k` on the tori of a family, without the
proofs that `Rep` carries (LFR Definition II.6.1; LF-3 (c), (d)): on every torus `n_K` the histories
`𝔄`, the step kernels and boundary factors `(K_j, b_j)(Z', 𝔞)` and the boundary terms `ℬ^{(k)}`; and
the vacuum normalization `s` of the step density that they represent. The kept data and their
exponents are not created by a step: those of the successor are the input's (`KeptData.upTo`). -/
structure LFStepRaw (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N k : ℕ) where
  /-- the histories `𝔄` -/
  hist : ∀ (nK : ℕ) [NeZero nK], Finset (LabHist S (sides S.L K nK) R k0 K)
  /-- the step kernels and boundary factors -/
  ker : ∀ (nK : ℕ) [NeZero nK] (j : ℕ) (a : LocalHistory S (sides S.L K nK) M K),
    LFKernel (OutT N R a (j + 1)) (NewCfg N a j) (EuclideanSpace ℝ (Fin N))
      (GIdx S (sides S.L K nK) M K N)
  /-- the boundary terms `ℬ^{(k)}(X, 𝔸)` -/
  B : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k
  /-- the vacuum normalization of the step density -/
  s : ℝ

namespace LFStepRaw

variable {k : ℕ}

/-- **The zero data** (rule 10): no histories, zero kernels, zero boundary terms. -/
noncomputable def zero : LFStepRaw S R k0 K M N k where
  hist := fun _ _ => ∅
  ker := fun _ _ _ _ => zeroKer _ _ _ _
  B := fun _ _ _ _ _ _ _ _ => 0
  s := 0

instance : Nonempty (LFStepRaw S R k0 K M N k) := ⟨zero⟩

variable (D : LFStepRaw S R k0 K M N k)
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}

/-- The representation on the torus `n_K` with the data of `D`, the kept exponents `κK`, the step
data `SD` and the kept data `KD`. -/
def rep (nK : ℕ) [NeZero nK] (κK : ℕ → LocalHistory S (sides S.L K nK) M K → ℝ)
    (SD : StepData k0 (geo nK) cs N (kappaStepLoc (K := K) S P M))
    (KD : KeptData k0 (geo nK) cs N κK S.lam) :
    Rep S (sides S.L K nK) R k0 K M N (geo nK) cs P k where
  hist := D.hist nK
  κK := κK
  SD := SD
  KD := KD
  B := D.B nK

/-- The step data on every torus carry the kernels of `D` (the other data of `StepData` are read by
no clause of `IsRepPre2` or `LFCoherent` other than (S0)–(S2) themselves: the operators read the step
data only through `ker`, `preOpTop_congr`). -/
def Matches (SD : ∀ (nK : ℕ) [NeZero nK], StepData k0 (geo nK) cs N (kappaStepLoc (K := K) S P M)) :
    Prop :=
  ∀ (nK : ℕ) [NeZero nK], (SD nK).ker = D.ker nK

/-- **`Matches` is satisfiable** (rule 10): the zero data are carried by the zero step data (horizon
`K ≤ 1`, `C_b = 0`). -/
theorem matches_zero (hK : K ≤ 1) (hCb : cs.Cb = 0) :
    (zero : LFStepRaw S R k0 K M N k).Matches (geo := geo) (P := P)
      (fun nK _ => zeroStepData (geo nK) cs hK hCb _) :=
  fun _ _ => rfl

/-- The family of representations with the small-field data `sf` and, on every torus, the data of
`D` with the kept exponents `κK`, the step data `SD` and the kept data `KD`. -/
def fam {m₁ : ℕ} {ϱ : ℝ} (sf : SFData S.d S.L m₁ k N ϱ)
    (κK : ∀ (nK : ℕ) [NeZero nK], ℕ → LocalHistory S (sides S.L K nK) M K → ℝ)
    (SD : ∀ (nK : ℕ) [NeZero nK], StepData k0 (geo nK) cs N (kappaStepLoc (K := K) S P M))
    (KD : ∀ (nK : ℕ) [NeZero nK], KeptData k0 (geo nK) cs N (κK nK) S.lam) :
    RepFam S R k0 K M N geo cs P k m₁ ϱ where
  sf := sf
  lf := fun nK _ => D.rep nK (κK nK) (SD nK) (KD nK)

end LFStepRaw

end Raw

/-!
### The constants of the successor
-/

section Consts

/-- A sequence of scale `k` followed by `e` at `k + 1` takes the values of `f` at `j ≤ k + 1` if it
agrees with `f` at `j ≤ k` and `e = f (k + 1)`. -/
theorem vacExt_eq_of_le_succ {E f : ℕ → ℝ} {k j : ℕ} {e : ℝ} (hE : ∀ i, i ≤ k → E i = f i)
    (he : e = f (k + 1)) (hj : j ≤ k + 1) : vacExt E k e j = f j := by
  by_cases h : j ≤ k
  · rw [vacExt_of_le _ h]
    exact hE j h
  · obtain rfl : j = k + 1 := by omega
    rw [vacExt_succ]
    exact he

/-- `δ_j` reads the coupling at `j` only. -/
theorem deltaRun_congr {A0 a : ℝ} {p0 : ℕ} {b b' : ℕ → ℝ} {j : ℕ} (h : b j = b' j) :
    deltaRun A0 p0 a b j = deltaRun A0 p0 a b' j := by
  simp only [deltaRun, pZero, runLam, h]

/-- `p₀(β_j)` reads the coupling at `j` only. -/
theorem pZero_congr {A0 a : ℝ} {p0 : ℕ} {b b' : ℕ → ℝ} {j : ℕ} (h : b j = b' j) :
    pZero A0 p0 a b j = pZero A0 p0 a b' j := by
  simp only [pZero, runLam, h]

variable {S : Setting} [NeZero S.L] {m₁ N : ℕ} {ϱ : ℝ}

/-- **The operator constants of the successor** (LFR §II.1.1, Definition II.1.1): those of `cs` (the
input's) at the scales `j ≤ k`; at `k + 1` the running constants of the small-field data `sf'` of the
scale `k + 1` (the coupling `β_{k+1}`, the mass `ν_{k+1}`, `z_{k+1}`, the tolerances `δ_{k+1}`, `p₀(β_{k+1})`
computed from `β_{k+1}`, the cutoff mass `bgMass` (zero below `k₀`), the background and action masses
`ν_{k+1} L^{-2(k+1)}`, ruling R2), kept beyond `k + 1` (`vacExt`; never read at the scale `k + 1`); the
non-running constants (`a_n`, `C_ψ`, `a`, `C_b`, `B₀`) are those of `cs`. -/
noncomputable def succOpConsts (S : Setting) [NeZero S.L] (k0 : ℕ) (A0 : ℝ) (cs : OpConsts) (k : ℕ)
    (sf' : SFData S.d S.L m₁ (k + 1) N ϱ) : OpConsts where
  aw := cs.aw
  mu := vacExt cs.mu k (bgMass k0 S.L sf'.ν (k + 1))
  muBg := vacExt cs.muBg k (sf'.ν (k + 1) / (S.L : ℝ) ^ (2 * (k + 1)))
  muAct := vacExt cs.muAct k (sf'.ν (k + 1) / (S.L : ℝ) ^ (2 * (k + 1)))
  nu := vacExt cs.nu k (sf'.ν (k + 1))
  delta := vacExt cs.delta k (deltaRun A0 S.p0 cs.aKer sf'.β (k + 1))
  p0 := vacExt cs.p0 k (pZero A0 S.p0 cs.aKer sf'.β (k + 1))
  Cpsi := cs.Cpsi
  beta := vacExt cs.beta k (sf'.β (k + 1))
  z := vacExt cs.z k (sf'.z (k + 1))
  aKer := cs.aKer
  Cb := cs.Cb
  B0 := cs.B0

/-- **The budget constants of the successor**: `c₁, c₂, H₀` of `P`, the couplings of `P` at the
scales `j ≤ k` and `β_{k+1}` of `sf'` after. -/
noncomputable def succBudgetConsts (P : BudgetConsts) (k : ℕ) (sf' : SFData S.d S.L m₁ (k + 1) N ϱ) :
    BudgetConsts where
  c1 := P.c1
  c2 := P.c2
  H0 := P.H0
  beta := vacExt P.beta k (sf'.β (k + 1))

variable {R : ℕ → ℝ} {k0 M : ℕ} {cs : OpConsts} {P : BudgetConsts} {P6 : Def6.Consts}
  {C7 : Consts7} {β ν : ℝ} {k : ℕ} {sf : SFData S.d S.L C7.m₁ k N ϱ}
  {sf' : SFData S.d S.L C7.m₁ (k + 1) N ϱ}

/-- **`Coh` at the successor**: the coherence of the constants of the successor with its small-field
data `sf'`, which keep the couplings, masses and field renormalizations of `sf` at the scales `j ≤ k`
and whose kernel coefficients follow the free flow up to `k + 1`, from the coherence of the input. -/
theorem coh_succ (hcoh : Coh S R k0 M cs P P6 C7 β ν k sf) (hβ : ∀ j, j ≤ k → sf'.β j = sf.β j)
    (hν : ∀ j, j ≤ k → sf'.ν j = sf.ν j) (hz : ∀ j, j ≤ k → sf'.z j = sf.z j)
    (ha : ∀ j, 1 ≤ j → j ≤ k + 1 → sf'.a j = compWeight S.L cs.aKer j) :
    Coh S R k0 M (succOpConsts S k0 C7.A0 cs k sf') (succBudgetConsts P k sf') P6 C7 β ν (k + 1)
      sf' where
  M_eq := hcoh.M_eq
  M_pow := hcoh.M_pow
  lam_eq := hcoh.lam_eq
  R_eq := hcoh.R_eq
  k0_eq := hcoh.k0_eq
  a_free := ha
  beta_cs := fun _ hj =>
    vacExt_eq_of_le_succ (fun i hi => (hcoh.beta_cs i hi).trans (hβ i hi).symm) rfl hj
  beta_P := fun _ hj =>
    vacExt_eq_of_le_succ (fun i hi => (hcoh.beta_P i hi).trans (hβ i hi).symm) rfl hj
  z_cs := fun _ hj => vacExt_eq_of_le_succ (fun i hi => (hcoh.z_cs i hi).trans (hz i hi).symm) rfl hj
  nu_cs := fun _ hj =>
    vacExt_eq_of_le_succ (fun i hi => (hcoh.nu_cs i hi).trans (hν i hi).symm) rfl hj
  delta_cs := fun _ hj => vacExt_eq_of_le_succ
    (fun i hi => (hcoh.delta_cs i hi).trans (deltaRun_congr (hβ i hi).symm)) rfl hj
  p0_cs := fun _ hj => vacExt_eq_of_le_succ
    (fun i hi => (hcoh.p0_cs i hi).trans (pZero_congr (hβ i hi).symm)) rfl hj
  B0_cs := hcoh.B0_cs

/-- **The field clauses at the successor** (ruling R2): the masses of the successor's constants. -/
theorem field_succ {hv : EuclideanSpace ℝ (Fin N)} (hf : FieldClauses S k0 k cs sf hv)
    (hν : ∀ j, j ≤ k → sf'.ν j = sf.ν j) :
    FieldClauses S k0 (k + 1) (succOpConsts S k0 C7.A0 cs k sf') sf' hv where
  h_unit := hf.h_unit
  mu_eq := fun _ hj => vacExt_eq_of_le_succ
    (fun i hi => (hf.mu_eq i hi).trans (by simp only [LargeField.bgMass, hν i hi])) rfl hj
  muBg_eq := fun _ hj => vacExt_eq_of_le_succ (f := fun j => sf'.ν j / (S.L : ℝ) ^ (2 * j))
    (fun i hi => (hf.muBg_eq i hi).trans (by rw [hν i hi])) rfl hj
  muAct_eq := fun _ hj => vacExt_eq_of_le_succ (f := fun j => sf'.ν j / (S.L : ℝ) ^ (2 * j))
    (fun i hi => (hf.muAct_eq i hi).trans (by rw [hν i hi])) rfl hj

/-- **The background of the large-field actions is the small-field one** (the SF→LF watch item;
ruling R2): under the field clauses the background mass `cs.muBg j` of the large-field operators is
the small-field solver mass `sfBgMass j` (`ν_j L^{-2j}`, complete backgrounds) of the regime
`(k₀, ν)`, at every scale `j ≤ k`. The chord of `SFtoLFInterface` compares the actions at `lfBgMass`
and `sfBgMass`; no exponent of the class is evaluated at `lfBgMass`. -/
theorem muBg_eq_sfBgMass_of_fieldClauses {hv : EuclideanSpace ℝ (Fin N)}
    (h : FieldClauses S k0 k cs sf hv) {j : ℕ} (hj : j ≤ k) :
    cs.muBg j = (⟨k0, sf.ν⟩ : Regime S.L).sfBgMass j := by
  rw [h.muBg_eq j hj]
  show _ = sf.ν j * ((S.L : ℝ) ^ j)⁻¹ ^ 2
  rw [pow_mul, div_eq_mul_inv, inv_pow, ← pow_mul, ← pow_mul, mul_comm j 2]

end Consts

/-!
### The kept data of the successor
-/

section Kept

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs cs' : OpConsts}

/-- **`χ^{dom}` at the scale `j` reads the tolerances `δ_i` (`i ≤ j`), the radii `p₀(β_i)` (`i < j`)
and `C_ψ` only** (Definition II.3.4, P5 (1.24)–(1.25)). -/
theorem chiDomAt_congr {j : ℕ} (hδ : ∀ i, i ≤ j → cs'.delta i = cs.delta i)
    (hp : ∀ i, i < j → cs'.p0 i = cs.p0 i) (hC : cs'.Cpsi = cs.Cpsi) (H : RegionHistory S n R k0 K)
    (Z : H.Comp j) {A : Set (InternalVars (H.localHistory M K j Z) j)}
    (o : OutT N R (H.localHistory M K j Z) j) (x : SubCfg N (H.localHistory M K j Z) j A) :
    ChiDomAt geo cs' H j Z o x ↔ ChiDomAt geo cs H j Z o x := by
  unfold ChiDomAt ChiDomProp
  rw [hC]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi y hy hy' => ?_, fun i hi1 hi y hy hy' hy'' => ?_, fun i hi y hy => ?_⟩
    · rw [← hδ i hi.le]
      exact h1 i hi y hy hy'
    · rw [← hδ i hi]
      exact h2 i hi1 hi y hy hy' hy''
    · rw [← hp i hi]
      exact h3 i hi y hy
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi y hy hy' => ?_, fun i hi1 hi y hy hy' hy'' => ?_, fun i hi y hy => ?_⟩
    · rw [hδ i hi.le]
      exact h1 i hi y hy hy'
    · rw [hδ i hi]
      exact h2 i hi1 hi y hy hy' hy''
    · rw [hp i hi]
      exact h3 i hi y hy

/-- **The kept data restricted to the scales `≤ k`, at other constants** ((S3) of the step: "no kept
data are created by a step", LFR proof of Theorem IV.1.1): the kept variables, `C_dec` and `γ` of
`KD`, the kept kernels of `KD` at the scales `≤ k` and zero kernels above. At constants `cs'` whose
tolerances `δ_i`, radii `p₀(β_i)` (`i ≤ k`) and `C_ψ` are those of `cs` these are kept data (S3):
`χ^{dom}` at the scales `≤ k` reads nothing else (`chiDomAt_congr`), and a zero kernel satisfies
(1.26) (`kerBound_of_K_zero`). -/
noncomputable def _root_.Balaban.LargeField.KeptData.upTo {κ : ℕ → LocalHistory S n M K → ℝ}
    {lamHat : ℕ → ℝ} (KD : KeptData k0 geo cs N κ lamHat) (k : ℕ) (cs' : OpConsts)
    (hδ : ∀ i, i ≤ k → cs'.delta i = cs.delta i) (hp : ∀ i, i ≤ k → cs'.p0 i = cs.p0 i)
    (hC : cs'.Cpsi = cs.Cpsi) : KeptData k0 geo cs' N κ lamHat where
  datum := fun j a ϰ =>
    { Ikeep := (KD.datum j a ϰ).Ikeep
      contains := (KD.datum j a ϰ).contains
      ker := if j ≤ k then (KD.datum j a ϰ).ker else zeroKer _ _ _ _ }
  Cdec := KD.Cdec
  gam := KD.gam
  one_le_Cdec := KD.one_le_Cdec
  sum_inv_Cdec := KD.sum_inv_Cdec
  gam_ge := KD.gam_ge
  b_supp := fun j a ϰ o x hv g g' hg => by
    by_cases hj : j ≤ k
    · simp only [hj, ↓reduceIte]
      exact KD.b_supp j a ϰ o x hv g g' hg
    · simp only [hj, ↓reduceIte]
      rfl
  rot_K := fun j a ϰ ρ o x hv => by
    by_cases hj : j ≤ k
    · simp only [hj, ↓reduceIte]
      exact KD.rot_K j a ϰ ρ o x hv
    · simp only [hj, ↓reduceIte]
      rfl
  rot_b := fun j a ϰ ρ o x hv g => by
    by_cases hj : j ≤ k
    · simp only [hj, ↓reduceIte]
      exact KD.rot_b j a ϰ ρ o x hv g
    · simp only [hj, ↓reduceIte]
      rfl
  euclid_I := fun j σ a a' hI hk ϰ p => KD.euclid_I j σ a a' hI hk ϰ p
  euclid_K := fun j σ a a' hI hk ϰ o o' x x' hv ho hx => by
    by_cases hj : j ≤ k
    · simp only [hj, ↓reduceIte]
      exact KD.euclid_K j σ a a' hI hk ϰ o o' x x' hv ho hx
    · simp only [hj, ↓reduceIte]
      rfl
  euclid_b := fun j σ a a' hI hk ϰ o o' x x' hv g g' ho hx hg => by
    by_cases hj : j ≤ k
    · simp only [hj, ↓reduceIte]
      exact KD.euclid_b j σ a a' hI hk ϰ o o' x x' hv g g' ho hx hg
    · simp only [hj, ↓reduceIte]
      rfl
  bound := fun H hH j Z hj1 hj0 hrip ϰ => by
    by_cases hj : j ≤ k
    · obtain ⟨hvan, hb⟩ := KD.bound H hH j Z hj1 hj0 hrip ϰ
      simp only [hj, ↓reduceIte]
      exact ⟨fun o x hv hd => hvan o x hv fun h' => hd ((chiDomAt_congr
        (fun i hi => hδ i (hi.trans hj)) (fun i hi => hp i (hi.le.trans hj)) hC H Z o x).2 h'), hb⟩
    · simp only [hj, ↓reduceIte]
      exact ⟨fun _ _ _ _ => rfl, kerBound_of_K_zero _ _ _ (fun _ _ _ => rfl) _⟩

end Kept

/-!
### (D7) at the pinned ball
-/

section Ball

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **(D7) at the complex fields of the pinned ball** (the clauses `analytic`, `bound` of `D7Bdry2`
at the fields `h ∈ hSetB2 hv rH` other than the physical field `hC hv`; blocker 2, leaf 5: the
source enters the boundary terms through `ν_j h`, and the bound on a complex neighbourhood of the
physical field is the activity bound on the transverse source radius). -/
structure D7BdryBall {m₀ m₁ : ℕ} (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K)
    (rep : Rep S n R k0 K M N geo cs P k) (Zof : LabHist S n R k0 K → Set (Torus S.d (n k)))
    (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ) (hv : EuclideanSpace ℝ (Fin N)) (rH : ℝ) : Prop where
  analytic : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A), ∀ h ∈ hSetB2 hv rH, h ≠ hC hv →
    AnalyticOnNhd ℂ
      (fun p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ) =>
        rep.B A X (extK p.1) (extK p.2.1) h p.2.2)
      {p | H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))}
  bound : ∀ A ∈ rep.hist, ∀ X ∈ bdryDomsPre Fr A k (Zof A), ∀ h ∈ hSetB2 hv rH, h ≠ hC hv →
    ∀ p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ),
      H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)) →
      ‖rep.B A X (extK p.1) (extK p.2.1) h p.2.2‖ <
        fac * Real.exp (-rate * d7SizePre Fr A k X)

variable {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {hnn : ∀ i, i < K → n i = S.L * n (i + 1)}
  {hkK : k ≤ K} {rep : Rep S n R k0 K M N geo cs P k}
  {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
  {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}

/-- `D7BdryBall` holds when there are no histories (rule 10). -/
theorem d7BdryBall_of_hist_eq_empty (h : rep.hist = ∅) :
    D7BdryBall Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv rH where
  analytic := fun A hA => by simp [h] at hA
  bound := fun A hA => by simp [h] at hA

/-- **(D7) of the pre-`R` class, second version, from (D7) at the physical field and at the other
fields of the pinned ball.** -/
theorem _root_.Balaban.LargeField.Def7.D7Bdry.toD7Bdry2_of_ball (h : D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv)
    (hb : D7BdryBall Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv rH) :
    D7Bdry2 Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv rH where
  loc_field := h.loc_field
  loc_hist := h.loc_hist
  real := h.real
  analytic := fun A hA X hX h' hh' => by
    by_cases e : h' = hC hv
    · subst e
      exact h.analytic A hA X hX _ rfl
    · exact hb.analytic A hA X hX h' hh' e
  bound := fun A hA X hX h' hh' => by
    by_cases e : h' = hC hv
    · subst e
      exact h.bound A hA X hX _ rfl
    · exact hb.bound A hA X hX h' hh' e
  rot := h.rot
  euclid := h.euclid
  support := h.support

end Ball

/-!
### The vacuum constants of step data
-/

section Vacuum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {κs : ℕ → LocalHistory S n M K → ℝ}

/-- **The vacuum term of step data is bounded on `χ^new`** (the obstruction of A4-2v for every
`StepData`): since `b_k = b⁰_k - (vacuum term)` and both `b_k` and `b⁰_k` are bounded by
`(C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|_{k+1}`, the vacuum term of the step data's own constants is
bounded by twice that. The first region of the vacuum term contains the whole torus outside the
component (`compl_fineSet_subset_vacuumRegion`), so step data tied to a flow with `E_k ≠ 0` exist on
large tori only after ruling R10 localizes that region. -/
theorem norm_stepVacuumTerm_le_of_stepData (SD : StepData k0 geo cs N κs)
    (H : RegionHistory S n R k0 K) (hH : H.Admissible) (k : ℕ) (Z' : H.Comp (k + 1))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) (hχ : ChiNewAt geo cs H k Z' o x) :
    ‖(stepVacuumTerm (H.localHistory M K (k + 1) Z') k
        (SD.vacE k (H.localHistory M K (k + 1) Z')) (SD.vacEpp k (H.localHistory M K (k + 1) Z'))
        (SD.vacEppp k (H.localHistory M K (k + 1) Z')) : ℂ)‖ ≤
      2 * ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k}) := by
  have h1 := SD.b0_bound H hH k Z' o x hv g hg hχ
  have h2 := SD.b_bound H hH k Z' o x hv g hg hχ
  have e := SD.b_vac k (H.localHistory M K (k + 1) Z') o x hv g
  have h3 := norm_sub_le (SD.b0 k (H.localHistory M K (k + 1) Z') o x hv g)
    ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g)
  have e' : SD.b0 k (H.localHistory M K (k + 1) Z') o x hv g -
      (SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g =
      (stepVacuumTerm (H.localHistory M K (k + 1) Z') k
        (SD.vacE k (H.localHistory M K (k + 1) Z')) (SD.vacEpp k (H.localHistory M K (k + 1) Z'))
        (SD.vacEppp k (H.localHistory M K (k + 1) Z')) : ℂ) := by
    rw [e]; ring
  rw [e'] at h3
  linarith

end Vacuum

/-!
### The successor of a record
-/

section Succ

variable {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7} {PB : BudgetConsts}
  {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ}
  [NeZero T.M] [NeZero T.L] {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}

namespace RepRec

variable (rec : RepRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k ρ νk)
  (sf' : SFData d T.L C7.m₁ (k + 1) N ϱ)

/-- The operator constants of the successor of `rec` with the small-field data `sf'`
(`succOpConsts`: those of `rec` at the scales `≤ k`, the running constants of `sf'` at `k + 1`). -/
noncomputable def succCs : OpConsts :=
  succOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 rec.cs k sf'

/-- The budget constants of the successor of `rec` with the small-field data `sf'`. -/
noncomputable def succP : BudgetConsts :=
  succBudgetConsts (S := 𝒮[d, T, β, cs₀.aKer]) rec.P k sf'

/-- **The kept data of the successor** on the torus `n_K` ((S3): no kept data are created by a step):
the kept data of `rec` restricted to the scales `≤ k` (`KeptData.upTo`), at the constants of the
successor, which are those of `rec` at the scales `≤ k`. Their exponents are those of `rec`. -/
noncomputable def succKD (nK : ℕ) [NeZero nK] :
    KeptData (kZero d T.L β ν) (rec.geo nK) (rec.succCs sf') N (rec.F.lf nK).κK
      (Setting.lam 𝒮[d, T, β, cs₀.aKer]) :=
  (rec.F.lf nK).KD.upTo k (rec.succCs sf') (fun _ hi => vacExt_of_le _ hi)
    (fun _ hi => vacExt_of_le _ hi) rfl

/-- **The successor families**: `Q` holds for the family with the small-field data `sf'` and, on
every torus, the histories, kernels and boundary terms of `D`, the kept data `succKD` with the
exponents of `rec`, and any step data at the constants of the successor that carry the kernels of
`D` (`LFStepRaw.Matches`). The clauses of `IsRepPre2` and `LFCoherent` read the step data only through
their kernels, so a statement of this form is a statement about `sf'`, `D` and `rec`. -/
def SuccFams (D : LFStepRaw 𝒮[d, T, β, cs₀.aKer] rec.R (kZero d T.L β ν) (kf + 1) T.M N (k + 1))
    (Q : RepFam 𝒮[d, T, β, cs₀.aKer] rec.R (kZero d T.L β ν) (kf + 1) T.M N rec.geo
      (rec.succCs sf') (rec.succP sf') (k + 1) C7.m₁ ϱ → Prop) : Prop :=
  ∀ SD : ∀ (nK : ℕ) [NeZero nK], StepData (kZero d T.L β ν) (rec.geo nK) (rec.succCs sf') N
      (kappaStepLoc (K := kf + 1) 𝒮[d, T, β, cs₀.aKer] (rec.succP sf') T.M),
    D.Matches SD → Q (D.fam sf' (fun nK _ => (rec.F.lf nK).κK) SD (rec.succKD sf'))

/-- The couplings of a record are positive at the scales `j ≤ k` ((I.2)). -/
theorem sfBeta_pos {j : ℕ} (hj : j ≤ k) : 0 < rec.F.sf.β j := by
  obtain ⟨γ, hγ, -, hβj⟩ := rec.run.beta_eq j hj
  rw [hβj]
  have := rec.run.hβ
  have hL : (0 : ℝ) < T.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.L)
  positivity

/-- The couplings of an image that keeps those of the record at the scales `j ≤ k` and satisfies
(D2) at `k + 1` (whose coefficient bounds give `β_{k+1} > 0`, `CoeffBounds.beta_succ_ge`) are
positive at the scales `j ≤ k + 1`. -/
theorem imageBeta_pos {fac : ℕ → ℝ} (hD2 : D2SF2 P6 (kZero d T.L β ν) sf' fac)
    (hβ : ∀ j, j ≤ k → sf'.β j = rec.F.sf.β j) {j : ℕ} (hj : j ≤ k + 1) : 0 < sf'.β j := by
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · rw [hβ j (by omega)]
    exact rec.sfBeta_pos (by omega)
  · obtain rfl : j = k + 1 := by omega
    obtain ⟨_, hsf⟩ := hD2.sfClass
    have hL : 1 ≤ T.L := Nat.pos_of_ne_zero (NeZero.ne T.L)
    exact (hsf.coeff.beta_succ_ge hL (by rw [hβ k le_rfl]; exact rec.sfBeta_pos le_rfl)).1

end RepRec

end Succ

/-!
### The parts
-/

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
  (ΦE : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ)

/-- **The large-field step map** (a parameter of the sub-spine, defined by the provider): for every
record `rec` of `ℛ_k` (constants `κ, c₉`, couplings `β, ν`, unit field `h`, horizon `kf`, density
`ρ`), the large-field data of the successor at the scale `k + 1` on the tori of the family of `rec`
(LF-3 (c), (d); LFR Lemma IV.1.5; P5 §§2–3, P6 §§2–3). -/
abbrev LFStepMap :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk),
    LFStepRaw 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] rec.R (kZero d (T κ c₉).L β ν) (kf + 1)
      (T κ c₉).M N (k + 1)

/-- **The form of the parts**: a property `Q` of every record `rec` of `ℛ_k`, `1 ≤ k < k₀`, for
`β ≥ β₀(κ, c₉)`, `0 < ν ≤ 7/8 L⁻²`, every unit field `h` and the horizon `kf`, whose small-field
image `Φ rec.F.sf` satisfies the hypotheses of `LFStepInput`: (D2) with the allowance `preFac`,
(D8), (D9), the free flow of `a_j` up to `k + 1`, and the running constants of `rec` at `j ≤ k`. -/
def LFImageInput (Q : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
    [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (k : ℕ)
    (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk → k + 1 ≤ kf + 1 → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk),
    D2SF2 (P6 κ c₉) (kZero d (T κ c₉).L β ν) (Φ κ c₉ β ν k rec.F.sf)
      (preFac ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) →
    D8SF (P6 κ c₉).m₀ (Φ κ c₉ β ν k rec.F.sf) →
    D9Coeff (P6 κ c₉) (kZero d (T κ c₉).L β ν) (Φ κ c₉ β ν k rec.F.sf) →
    (∀ j, 1 ≤ j → j ≤ k + 1 →
      (Φ κ c₉ β ν k rec.F.sf).a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j) →
    (∀ j, j ≤ k → (Φ κ c₉ β ν k rec.F.sf).β j = rec.F.sf.β j ∧
      (Φ κ c₉ β ν k rec.F.sf).ν j = rec.F.sf.ν j ∧ (Φ κ c₉ β ν k rec.F.sf).z j = rec.F.sf.z j) →
    ∀ hkK' : k + 1 ≤ kf + 1, Q κ c₉ β ν h kf k ρ νk rec hkK'

/-- **The histories of the successor (LF-3 (c); LFR Definition I.3.1, (R8)).** On every torus the
histories of the map are a complete set of the histories up to the scale `k + 1` (without an
`R`-record at `k + 1`): every history agrees up to `k + 1` with exactly one of them. -/
def LFHistInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec _ =>
    ∀ (nK : ℕ) [NeZero nK], IsComplete (k + 1) (k + 1) ((Λ κ c₉ β ν h kf k ρ νk rec).hist nK)

/-- **The step data of the successor (row (g1); LF-3 (d); LFR Lemma II.5.14 (quiet steps), Lemma
IV.1.3 (the local background, the terms `Δ(Y)` of `b_k`), Lemma IV.1.4 ((S1)–(S2) of the kernels of
P5 (2.47)·P6 (3.2) with the witness `χ'^{(k)c}(𝖯)χ'^{(k)}(…)`), Lemma IV.1.6 (rotation form), (S0)
from P6 (2.32)–(2.33), (3.3); the vacuum constants: R5, R5′, P6 (3.2), P4 (2.1), (2.41), (2.63)).** On
every torus there are step data (S0)–(S2) at the constants of the successor whose kernels are those
of the map, and whose vacuum constants are those of the flow `E_0, …, E_k` of `rec` extended by the
new constant `ΦE` (`vacExt`), with offsets `δ″, δ‴`. At the old steps `j < k` the kernels are those of
`rec` (the composition of (D1)), so the tie there is the estimate `VacuumB0Bound` of the input's step
data on its flow (A4-2v), which exists only after ruling R10 (`norm_stepVacuumTerm_le_of_stepData`).
The witnesses of (S1), `b⁰` and the offsets are existential (read by no other part). -/
def LFStepDataInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec _ =>
    ∀ (nK : ℕ) [NeZero nK], ∃ SD : StepData (kZero d (T κ c₉).L β ν) (rec.geo nK)
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)) N
        (kappaStepLoc (K := kf + 1) 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (rec.succP (Φ κ c₉ β ν k rec.F.sf)) (T κ c₉).M),
      SD.ker = (Λ κ c₉ β ν h kf k ρ νk rec).ker nK ∧
      ∃ dpp dppp : ℕ → ℝ, SD.VacuumTie Set.univ
        (vacExt rec.Ev k (ΦE κ c₉ β ν k rec.F.sf rec.Ev)) dpp dppp

/-- **The boundary terms at the physical field (row (g2); LFR Lemma IV.1.5; P5 p. 512, P6 pp. 14–15,
34).** On every torus the boundary terms `ℬ^{(k+1)}` of the map satisfy (D7) of the pre-`R` class at
the physical field (`D7Bdry`: locality in the fields and in the history, reality, analyticity and the
bound `B_st e^{-(3κ/2) d^cov}` on the H7 domain, covariance, support): the new terms of the
fluctuation integral and of the renormalization, the terms `Δ(Y)` of Lemma IV.1.3 meeting
`Z^c_{k+1}`, and the old terms whose domains meet `Ω_{k+1}` re-expanded (blocker 3: old terms across a
new hole). -/
def LFBdryInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec hkK' =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D7Bdry (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (sides (T κ c₉).L (kf + 1) nK) (kf + 1) rec.hM6) (sides_hnn (T κ c₉).L (kf + 1) nK)
        hkK' (F'.lf nK) (fun A => A.H.F.Zpre (k + 1)) F'.weights
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉))
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).nu (C7 κ c₉).Bst (3 / 2 * (P6 κ c₉).κ) h

/-- **The boundary terms at the other fields of the pinned ball (row (g5); blocker 2, leaf 5;
`notes/phase1/Q13-YM.md` §§2, 5; ruling R2).** On every torus the boundary terms of the map are
analytic on the H7 domain and bounded by `B_st e^{-(3κ/2) d^cov}` at every complex field `h'` of the
pinned ball `‖h' - h‖ < r_h` other than `h` (`D7BdryBall`): the activity bound at a complex source. -/
def LFBdrySrcInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec hkK' =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D7BdryBall (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (sides (T κ c₉).L (kf + 1) nK) (kf + 1) rec.hM6) (sides_hnn (T κ c₉).L (kf + 1) nK)
        hkK' (F'.lf nK) (fun A => A.H.F.Zpre (k + 1)) F'.weights
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉))
        (rec.succCs (Φ κ c₉ β ν k rec.F.sf)).nu (C7 κ c₉).Bst (3 / 2 * (P6 κ c₉).κ) h (rH κ c₉)

/-- **The form of the step density (row (g3); LFR proof of Theorem IV.1.1 (c), (D1); P5 (2.1)–(2.14),
(2.42)–(2.48), §3 (Propositions 3.1–3.4, (3.18)), P6 §2 ((2.11)–(2.33)), (3.3); P5 (1.8) for the
correction).** On every torus the step density `ρ' = e^{-s|T^{(k+1)}_1|} z^{N|T^{(k+1)}|}(T^{(k)}ρ)(z·)`
(`stepDensity`, with the Gaussian constant `β_k a L^{d-2}`, `z = z_{k+1}` of the image and the
normalization `s` of the map) is the sum over the histories of the map of the pre-`R` terms of the
successor (`D1PreForm2`), for the coefficient data `vc'` of P5 (1.8) defined by the limits
`D1CorrLim` of the image. -/
def LFFormInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec hkK' =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (St' : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ (k + 1) N)
        (vc' : CorrCoef d), D1CorrLim (P6 κ c₉).m₀ (Φ κ c₉ β ν k rec.F.sf) St' h vc' →
      ∀ (nK : ℕ) [NeZero nK], D1PreForm2 (F'.ctx rec.hM6 hkK' nK) vc' (F'.lf nK) h
        (stepDensity d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k
          (rec.F.sf.β k * (cs₀ κ c₉).aKer * ((T κ c₉).L : ℝ) ^ (d - 2))
          ((Φ κ c₉ β ν k rec.F.sf).z (k + 1)) (Λ κ c₉ β ν h kf k ρ νk rec).s ρ nK)

/-- **The operator bound of the successor (row (g3), (D5)).** On every torus the localized operators
of the successor satisfy (1.26) at every scale `≤ k + 1` (`D5Bound`). It follows from the step and
kept data by LFR Lemma II.6.3 (a) given the signs of the running constants
(`lfOpBoundInput_of_signs`). -/
def LFOpBoundInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec hkK' =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK' (F'.lf nK)

/-- **The field renormalizations are positive (P1 (1.11), P4 (4.1); LF-3: "there are
`z_{k+1} > 0`").** The image has `z_j > 0` at the scales `1 ≤ j ≤ k + 1` (at `j ≤ k` these are the
`z_j` of `rec`; the class does not carry their sign). -/
def LFSignInput : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν _ _ _ _ k _ _ rec _ =>
    ∀ j, 1 ≤ j → j ≤ k + 1 → 0 < (Φ κ c₉ β ν k rec.F.sf).z j

/-- **The pinned exponents of the successor (row (g4), (D4); LF-3 proof of Theorem IV.1.1, (D4)).**
On every torus the exponent `κ_j` of a kept component of a history of the map, at the scales
`1 ≤ j ≤ k` carrying an `R`-record, is its pre-`R` exponent `κ^pre_j` (`D4Pin (k + 1)`): the kept data
and the histories up to `k` are those of `rec`. -/
def LFPinInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec _ =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F'.lf nK)

/-- **The budget of the successor (row (g4), (D6); LF-2 (i), LFR Theorem I.5.4 (i)).** On every torus
every component of `Z^pre_{k+1}` of a history of the map satisfies (H6′)^pre (`D6Pre`). It follows
from the pinned exponents and the prefix by LF-2 (i) on the counter history truncated at `k + 1`
(`lfBudgetInput_of_pin`). -/
def LFBudgetInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec _ =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D6Pre (F'.lf nK)

/-- **The torus coherence of the successor (row (h); LF-3 (h), D-IV.9, LFR proof of Theorem IV.1.1
(D8)).** The successor family is `LFCoherent`: its step kernels, kept data and boundary terms are
given by the same formulas on `ℤ^d` (for the old data: (D8) of `rec`; for the new kernels: the local
background `bgLocPiece`; for `ℬ^{(k+1)}`: the localization expansions). -/
def LFCoherenceInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h kf _ _ k ρ νk rec _ =>
    rec.SuccFams (Φ κ c₉ β ν k rec.F.sf) (Λ κ c₉ β ν h kf k ρ νk rec) fun F' => LFCoherent F'

/-- **The coefficient data of the image (row (h); P1 (3.106)–(3.110), P5 (1.8); CLASS-RULINGS-2
item 6).** The source-form terms `St'` of the image and the thermodynamic limits `vc'` of their
local coefficients exist (`D1CorrLim`). -/
def LFCorrInput : Prop :=
  LFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ fun κ c₉ β ν h _ _ _ k _ _ rec _ =>
    ∃ (St' : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ (k + 1) N)
      (vc' : CorrCoef d), D1CorrLim (P6 κ c₉).m₀ (Φ κ c₉ β ν k rec.F.sf) St' h vc'

end Inputs

/-!
### The assembly
-/

section Assembly

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}
  {Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)}
  {ΦE : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ}

/-- **The large-field half of the step from its parts** (LFR Theorem IV.1.1 (b)–(d), (h)). For a
record `rec` of `ℛ_k` and its image `Φ rec.F.sf`:
* the step data on every torus are chosen by `LFStepDataInput` (their kernels are those of the map
  `Λ rec`); the kept data are those of `rec` (`succKD`, (S3) proved); the successor family is
  `⟨Φ rec.F.sf, Λ rec with these data⟩`;
* the constants are `succCs`, `succP` (those of `rec` at the scales `≤ k`, the running constants of
  the image at `k + 1`), whose ties to the outer constants are those of `rec`, and whose `Coh`,
  `FieldClauses` at `k + 1` are `coh_succ`, `field_succ` (with the ties of the image at `j ≤ k`);
* `IsRepPre2`: (D2), (D8), (D9) are the hypotheses on the image; completeness `LFHistInput`; (D1)
  `LFFormInput` for the coefficient data of `LFCorrInput`; (D4) `LFPinInput`; (D5) `LFOpBoundInput`;
  (D6) `LFBudgetInput`; (D7) of the second version from `LFBdryInput` and `LFBdrySrcInput`
  (`D7Bdry.toD7Bdry2_of_ball`);
* `LFCoherent` is `LFCoherenceInput`; the vacuum tie with `vacExt rec.Ev k (ΦE …)` is that of the
  chosen step data.
The threshold is the largest of the ten thresholds. -/
theorem lfStepInput_of_parts (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hH : LFHistInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hS : LFStepDataInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ ΦE Λ)
    (hB : LFBdryInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hBs : LFBdrySrcInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hF : LFFormInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hO : LFOpBoundInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hP : LFPinInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hG : LFBudgetInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hC : LFCoherenceInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hc : LFCorrInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ) :
    LFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ ΦE := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₁, h₁⟩ := hH κ hκ c₉ hc₉
  obtain ⟨b₂, h₂⟩ := hS κ hκ c₉ hc₉
  obtain ⟨b₄, h₄⟩ := hB κ hκ c₉ hc₉
  obtain ⟨b₅, h₅⟩ := hBs κ hκ c₉ hc₉
  obtain ⟨b₆, h₆⟩ := hF κ hκ c₉ hc₉
  obtain ⟨b₇, h₇⟩ := hO κ hκ c₉ hc₉
  obtain ⟨b₈, h₈⟩ := hP κ hκ c₉ hc₉
  obtain ⟨b₉, h₉⟩ := hG κ hκ c₉ hc₉
  obtain ⟨b₁₀, h₁₀⟩ := hC κ hκ c₉ hc₉
  obtain ⟨b₁₁, h₁₁⟩ := hc κ hκ c₉ hc₉
  refine ⟨max (max (max b₁ b₂) (max b₄ b₅)) (max (max b₆ b₇) (max b₈ (max b₉ (max b₁₀ b₁₁)))),
    ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK'
  simp only [max_le_iff] at hβ
  obtain ⟨⟨⟨hb₁, hb₂⟩, hb₄, hb₅⟩, ⟨hb₆, hb₇⟩, hb₈, hb₉, hb₁₀, hb₁₁⟩ := hβ
  choose SD hSDker hSDtie using
    h₂ β hb₂ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK'
  have hM : (Λ κ c₉ β ν h kf k ρ νk rec).Matches SD := fun nK _ => hSDker nK
  obtain ⟨St', vc', hcorr⟩ :=
    h₁₁ β hb₁₁ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK'
  refine ⟨rec.succCs (Φ κ c₉ β ν k rec.F.sf), rec.succP (Φ κ c₉ β ν k rec.F.sf),
    fun nK _ => (Λ κ c₉ β ν h kf k ρ νk rec).rep nK (rec.F.lf nK).κK (SD nK)
      (rec.succKD (Φ κ c₉ β ν k rec.F.sf) nK), St', vc',
    (Λ κ c₉ β ν h kf k ρ νk rec).s, rec.tie_aKer, rec.tie_Cpsi, rec.tie_Cb, rec.tie_aw, rec.tie_c1,
    rec.tie_c2, rec.tie_H0, ?_,
    h₁₀ β hb₁₀ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM,
    fun nK _ => hSDtie nK⟩
  exact
    { coh := coh_succ rec.rep.coh (fun j hj => (hcst j hj).1) (fun j hj => (hcst j hj).2.1)
        (fun j hj => (hcst j hj).2.2) fun j hj1 hj => (hafree j hj1 hj).trans (by rw [rec.tie_aKer])
      field := field_succ rec.rep.field fun j hj => (hcst j hj).2.1
      complete := h₁ β hb₁ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK'
      form := h₆ β hb₆ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM
        St' vc' hcorr
      corr := hcorr
      sfData := hD2
      pin := h₈ β hb₈ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM
      opBound := h₇ β hb₇ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM
      budget := h₉ β hb₉ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM
      bdry := fun nK _ =>
        (h₄ β hb₄ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM
          nK).toD7Bdry2_of_ball
        (h₅ β hb₅ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK)
      coherent := hD8
      coeff := hD9 }

/-- **(D5) of the successor from the signs of its running constants** (LFR Lemma II.6.3 (a), "(D4)
implies (D5)", `Rep.opBound_of_data`): the step and kept data of the successor carry (S1)–(S3) by
their types, so the localized operators of every scale satisfy (1.26) once `z_{j+1} > 0` and
`β_j a L^{d-2} ≥ 0` at every scale. The constants of the successor are frozen after `k + 1`; the
couplings are positive by (I.2) of `rec` at `j ≤ k` and by the coefficient bounds (H.6) of the image
at `k + 1` (`imageBeta_pos`), `a > 1` by (I.2); the field renormalizations by `LFSignInput`. -/
theorem lfOpBoundInput_of_signs (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hz : LFSignInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ) :
    LFOpBoundInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hz κ hκ c₉ hc₉
  refine ⟨b, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK'
    _ _ _ _ => ?_⟩
  have hz' := hb β hβ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK'
  refine Rep.opBound_of_data _ (fun j => ?_) (fun j => ?_) (k + 1) hkK'
  · show 0 < vacExt rec.cs.z k ((Φ κ c₉ β ν k rec.F.sf).z (k + 1)) (j + 1)
    by_cases hj : j + 1 ≤ k
    · rw [vacExt_of_le _ hj, rec.rep.coh.z_cs _ hj, ← (hcst _ hj).2.2]
      exact hz' _ (by omega) (by omega)
    · simp only [vacExt, hj, ↓reduceIte]
      exact hz' _ (by omega) le_rfl
  · show 0 ≤ vacExt rec.cs.beta k ((Φ κ c₉ β ν k rec.F.sf).β (k + 1)) j * rec.cs.aKer *
      ((T κ c₉).L : ℝ) ^ (d - 2)
    have hβj : 0 < vacExt rec.cs.beta k ((Φ κ c₉ β ν k rec.F.sf).β (k + 1)) j := by
      by_cases hj : j ≤ k
      · rw [vacExt_of_le _ hj, rec.rep.coh.beta_cs _ hj]
        exact rec.sfBeta_pos hj
      · simp only [vacExt, hj, ↓reduceIte]
        exact rec.imageBeta_pos (Φ κ c₉ β ν k rec.F.sf) hD2 (fun i hi => (hcst i hi).1) le_rfl
    have ha : 0 < rec.cs.aKer := by rw [rec.tie_aKer]; linarith [rec.run.ha1]
    have hL : (0 : ℝ) < (T κ c₉).L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
    positivity

/-- **(D6) of the successor from the pinned exponents and the prefix** (LF-2 (i); LFR Theorem I.5.4
(i), Lemma II.6.3 (d); "(D6) for `rep'` is LF-2 (i)"). The counter history of a history of the
successor, truncated at `k + 1` (`Rep.budgetPre_of_LF2_trunc`), satisfies the hypotheses of LF-2:
(B) by Lemma B (`BudgetSetupTo`: (I.2) up to `k + 1`, the analytic conditions (Λ15)–(Λ17′) at the a
priori `λ̂_j`, the budget constants of the prefix) and (Rg) by the pinned exponents (`LFPinInput`);
the setting is `Good` by the typing clauses of the prefix (`exists_good_lamHat`). (I.2) up to
`k + 1` for the image: (I.2) of `rec` up to `k`, the ties of the image at `j ≤ k`, the coefficient
bounds (H.6) of the image at `k + 1` and the rate of the prefix (`runningHypTo_succ_of_coeffBounds`). -/
theorem lfBudgetInput_of_pin {δ : ℝ} (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hP : LFPinInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ) :
    LFBudgetInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b, hb⟩ := hP κ hκ c₉ hc₉
  obtain ⟨hL3, ha1, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hTok, hθ, -, hH0, hc1, hLM, hcv⟩, -,
    hq⟩ := hA1 κ hκ c₉ hc₉
  obtain ⟨x₀, hx₀⟩ := exists_good_lamHat ({ T κ c₉ with d := d } : Typing) hTok hθ
  have hd3 : 3 ≤ d := hTok.three_le_d
  have hL2 : 2 ≤ (T κ c₉).L := by omega
  set Xa : ℝ := max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * ((T κ c₉).p0 : ℝ))))))
    (max ((PB κ c₉).c2 + 2)
      (3 + 2 * (thetaOf d (T κ c₉).L + 1 + 1 / (PB κ c₉).H0))) with hXa
  refine ⟨max b (Real.exp (max x₀ Xa)), ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hD2 hD8 hD9 hafree hcst hkK' SD hM nK _
  have hpin := hb β (le_of_max_le_left hβ) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2 hD8 hD9
    hafree hcst hkK' SD hM nK
  have hβe : Real.exp (max x₀ Xa) ≤ β := le_of_max_le_right hβ
  have hβ0 : 0 < β := lt_of_lt_of_le (Real.exp_pos _) hβe
  have hlog : max x₀ Xa ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hβe
  have hlogβa : Real.log β ≤ Real.log (β * (cs₀ κ c₉).aKer) :=
    Real.log_le_log hβ0 (by nlinarith)
  have hG := hx₀ β (cs₀ κ c₉).aKer (by linarith [le_max_left x₀ Xa])
  have hθ0 : 0 ≤ thetaOf d (T κ c₉).L := by
    unfold thetaOf
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by have : (2 : ℝ) ≤ (T κ c₉).L := by exact_mod_cast hL2
                           linarith))
  have hK : ∀ j, AnalyticLamAt (analyticK d (T κ c₉).L (T κ c₉).p0 (PB κ c₉).H0 (PB κ c₉).c2)
      (lamHat d (T κ c₉).L β (cs₀ κ c₉).aKer j) := by
    intro j
    apply analyticK_at (by omega) hL2 hH0
    have : 0 ≤ (j : ℝ) * thetaOf d (T κ c₉).L := mul_nonneg (Nat.cast_nonneg _) hθ0
    unfold lamHat
    linarith [le_max_right x₀ Xa]
  have hrun : RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) (Φ κ c₉ β ν k rec.F.sf).β
      (Φ κ c₉ β ν k rec.F.sf).ν (k + 1) := by
    obtain ⟨_, hsf⟩ := hD2.sfClass
    exact runningHypTo_succ_of_coeffBounds hsf.admissible hq hsf.coeff
      ((hcst 0 (Nat.zero_le k)).1.trans rec.β0) ((hcst 0 (Nat.zero_le k)).2.1.trans rec.ν0)
      (runningHypTo_congr rec.run (fun j hj => (hcst j hj).1) (fun j hj => (hcst j hj).2.1))
  let B : BudgetSetupTo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (rec.succP (Φ κ c₉ β ν k rec.F.sf))
      (k + 1) :=
    { β := β
      ν := ν
      a := (cs₀ κ c₉).aKer
      ε := 1 / 20
      nuRun := (Φ κ c₉ β ν k rec.F.sf).ν
      K := analyticK d (T κ c₉).L (T κ c₉).p0 (PB κ c₉).H0 (PB κ c₉).c2
      lam_eq := fun _ => rfl
      Kd := rfl
      KL := rfl
      Kp0 := rfl
      KH0 := rec.tie_H0.symm
      Kc2 := rec.tie_c2.symm
      lam_cond := hK
      H0_nonneg := by
        show 0 ≤ rec.P.H0
        rw [rec.tie_H0]
        exact hH0.le
      c1_nonneg := by
        show 0 ≤ rec.P.c1
        rw [rec.tie_c1]
        exact hc1
      L_le_M := hLM
      cv_ge := by
        show ((T κ c₉).M : ℝ) ^ d * (rec.P.H0 + rec.P.c1 + 3) ≤ (T κ c₉).cv
        rw [rec.tie_H0, rec.tie_c1]
        exact hcv
      run := runningHypTo_congr hrun (fun _ hj => vacExt_eq_of_le_succ
        (fun i hi => (rec.rep.coh.beta_P i hi).trans (hcst i hi).1.symm) rfl hj)
        (fun _ _ => rfl) }
  exact Rep.budgetPre_of_LF2_trunc _ hG B hpin hkK' le_rfl (by omega) (by omega) le_rfl

/-- **The large-field half of the step from its parts and the prefix**: `lfStepInput_of_parts`, with
(D5) from the signs of the field renormalizations (`lfOpBoundInput_of_signs`, LFR Lemma II.6.3 (a))
and (D6) from the pinned exponents and the prefix (`lfBudgetInput_of_pin`, LF-2 (i)). -/
theorem lfStepInput_of_prefix {δ : ℝ} (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hH : LFHistInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hS : LFStepDataInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ ΦE Λ)
    (hB : LFBdryInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hBs : LFBdrySrcInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hF : LFFormInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hz : LFSignInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ)
    (hP : LFPinInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hC : LFCoherenceInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hc : LFCorrInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ) :
    LFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ ΦE :=
  lfStepInput_of_parts Λ hH hS hB hBs hF (lfOpBoundInput_of_signs Λ hz) hP
    (lfBudgetInput_of_pin hA1 Λ hP) hC hc

end Assembly

end Balaban.RootFSpine
