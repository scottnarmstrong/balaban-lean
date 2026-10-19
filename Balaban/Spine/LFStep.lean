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
construction: the clause (D1) of the step density holds only for the histories, kernels, kept data
and boundary terms that the step constructs, and the other clauses (bounds, coherence) do not
determine these data. So the sub-spine takes the large-field data of the successor as a map `Λ`
(`LFStepMap`): for every record `rec` of `ℛ_k` the raw data `LFStepRaw` on every torus of the family
(the histories `𝔄'`, the exponents `κ_j` of the kept bound, the step kernels `(K_j, b_j)`, the kept
data, the boundary terms `ℬ^{(k+1)}`, the vacuum normalization `s`). A `Rep` also contains proofs
((S0)–(S3) are fields of `StepData`, `KeptData`), so the map gives the data, and the parts assert
that step and kept data with these data exist (LFR Lemma IV.1.4, Lemma II.5.14, (S0), (S3)).

**Maps and existentials** (rule: what the source defines by a formula is a map, what it only asserts
to exist is an existential inside the part):
* maps, fields of `LFStepRaw`: the histories (LF-3 (c): the histories of `rep` followed by every step
  record and the hull closure), the step kernels (LF-3 (d): the quiet kernels and the kernels of
  P5 (2.47)·P6 (3.2) with the local background, the boundary factors of P6 (2.32)–(2.33), (3.3)),
  the kept data and their exponents (no kept data are created by a step: those of `rep`, pinned to
  `κ^pre`), the boundary terms `ℬ^{(k+1)}` (LFR Lemma IV.1.5: the three kinds of P5 p. 512, P6
  pp. 14–15), the normalization `s = L^d E_k - e₀/|T^{(k+1)}_1|` (`Spine/SFVacuum.lean`);
* defined here: the operator constants `cs' = succOpConsts` and the budget constants
  `P' = succBudgetConsts` (the running constants of the image `Φ rec.F.sf`, LFR §II.1.1), so that
  `Coh`, `FieldClauses` and the ties to the outer constants are proved, not asked;
* existentials inside a part: the Gaussian witnesses of (S1), the remainder `b⁰` and the offsets
  `δ″, δ‴` of the vacuum constants (inside `LFStepDataInput`: read by no other part; `b⁰` is
  determined by `b_vac`), the proofs of (S0)–(S3) (the structures `StepData`, `KeptData`), and the
  coefficient data `St', vc'` (P1 (3.106)–(3.110): thermodynamic limits that the source asserts to
  exist, inside `LFCorrInput`; the form clause is asked for every `vc'` with `D1CorrLim`, which
  determines `vc'` at the scales the form reads).

**The parts** (statements below; sources in the docstrings; status in `notes/phase1/SPINE.md`):
* `LFHistInput` (LF-3 (c)): the histories are complete up to `k + 1`;
* `LFStepDataInput` (row (g1); Lemmas IV.1.3, IV.1.4, IV.1.6, Lemma II.5.14; R5, R5′): step data
  (S0)–(S2) with the kernels of the map, tied to the vacuum flow extended by `ΦE`;
* `LFKeptInput` (row (g1), (S3)): kept data with the kept data of the map;
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

Rule 10: `LFStepRaw` is inhabited (`LFStepRaw.zero`), `D7BdryBall` is (`d7BdryBall_of_hist_eq_empty`);
the parts and the combinators `LFImageInput`, `RepRec.SuccFams` need the exemption of the spine inputs.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Multiscale
  Balaban.Background RegionHistory

namespace Balaban.RootFSpine

/-!
### The raw large-field data of the successor
-/

section Raw

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- **The large-field data of a representation at the scale `k` on the tori of a family**, without
the proofs that `Rep` carries (LFR Definition II.6.1): on every torus `n_K` the histories `𝔄`, the
exponents `κ_j(Z, 𝔞)` of the kept bound, the step kernels and boundary factors `(K_j, b_j)(Z', 𝔞)`,
the kept data (the variables `I''` and kernels, `C_dec`, `γ_j`), the boundary terms `ℬ^{(k)}`; and
the vacuum normalization `s` of the step density that the data represent. -/
structure LFStepRaw (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N k : ℕ) where
  /-- the histories `𝔄` -/
  hist : ∀ (nK : ℕ) [NeZero nK], Finset (LabHist S (sides S.L K nK) R k0 K)
  /-- the exponents `κ_j(Z, 𝔞)` of the kept bound -/
  κK : ∀ (nK : ℕ) [NeZero nK], ℕ → LocalHistory S (sides S.L K nK) M K → ℝ
  /-- the step kernels and boundary factors -/
  ker : ∀ (nK : ℕ) [NeZero nK] (j : ℕ) (a : LocalHistory S (sides S.L K nK) M K),
    LFKernel (OutT N R a (j + 1)) (NewCfg N a j) (EuclideanSpace ℝ (Fin N))
      (GIdx S (sides S.L K nK) M K N)
  /-- the kept variables and kernels -/
  datum : ∀ (nK : ℕ) [NeZero nK] (j : ℕ) (a : LocalHistory S (sides S.L K nK) M K), Fin 5 →
    KeptDatum N R a j
  /-- the numbers `C_dec(ϰ)` -/
  Cdec : ∀ (nK : ℕ) [NeZero nK], Fin 5 → ℝ
  /-- the kept exponents `γ_j(ϰ)` -/
  gam : ∀ (nK : ℕ) [NeZero nK], ℕ → Fin 5 → ℝ
  /-- the boundary terms `ℬ^{(k)}(X, 𝔸)` -/
  B : ∀ (nK : ℕ) [NeZero nK], BTerms S (sides S.L K nK) R k0 K M N k
  /-- the vacuum normalization of the step density -/
  s : ℝ

namespace LFStepRaw

variable {k : ℕ}

/-- **The zero data** (rule 10): no histories, zero kernels, kept data with all variables kept and
zero kernels, zero boundary terms. -/
noncomputable def zero : LFStepRaw S R k0 K M N k where
  hist := fun _ _ => ∅
  κK := fun _ _ _ _ => 0
  ker := fun _ _ _ _ => zeroKer _ _ _ _
  datum := fun _ _ _ _ _ =>
    { Ikeep := Set.univ
      contains := fun _ _ => Set.mem_univ _
      ker := zeroKer _ _ _ _ }
  Cdec := fun _ _ _ => 1
  gam := fun _ _ _ _ => 0
  B := fun _ _ _ _ _ _ _ _ => 0
  s := 0

instance : Nonempty (LFStepRaw S R k0 K M N k) := ⟨zero⟩

variable (D : LFStepRaw S R k0 K M N k)
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}

/-- The representation on the torus `n_K` with the data of `D`, the step data `SD` and the kept
data `KD`. -/
def rep (nK : ℕ) [NeZero nK] (SD : StepData k0 (geo nK) cs N (kappaStepLoc (K := K) S P M))
    (KD : KeptData k0 (geo nK) cs N (D.κK nK) S.lam) :
    Rep S (sides S.L K nK) R k0 K M N (geo nK) cs P k where
  hist := D.hist nK
  κK := D.κK nK
  SD := SD
  KD := KD
  B := D.B nK

/-- The step data and the kept data on every torus carry the data of `D`: the kernels `ker`, the
kept data `datum`, `C_dec`, `γ` (the other data of `StepData`, `KeptData` are read by no clause of
`IsRepPre2` or `LFCoherent` other than (S0)–(S3) themselves). -/
def Matches (SD : ∀ (nK : ℕ) [NeZero nK], StepData k0 (geo nK) cs N (kappaStepLoc (K := K) S P M))
    (KD : ∀ (nK : ℕ) [NeZero nK], KeptData k0 (geo nK) cs N (D.κK nK) S.lam) : Prop :=
  ∀ (nK : ℕ) [NeZero nK], (SD nK).ker = D.ker nK ∧ (KD nK).datum = D.datum nK ∧
    (KD nK).Cdec = D.Cdec nK ∧ (KD nK).gam = D.gam nK

/-- The family of representations with the small-field data `sf` and, on every torus, the data of
`D` with the step data `SD` and the kept data `KD`. -/
def fam {m₁ : ℕ} {ϱ : ℝ} (sf : SFData S.d S.L m₁ k N ϱ)
    (SD : ∀ (nK : ℕ) [NeZero nK], StepData k0 (geo nK) cs N (kappaStepLoc (K := K) S P M))
    (KD : ∀ (nK : ℕ) [NeZero nK], KeptData k0 (geo nK) cs N (D.κK nK) S.lam) :
    RepFam S R k0 K M N geo cs P k m₁ ϱ where
  sf := sf
  lf := fun nK _ => D.rep nK (SD nK) (KD nK)

end LFStepRaw

end Raw

/-!
### The constants of the successor
-/

section Consts

/-- **A sequence frozen after the scale `r`**: `f_j` for `j ≤ r`, `f_r` beyond (the class at the
scale `r` reads its running constants only at the scales `≤ r`). -/
def frozenAfter (f : ℕ → ℝ) (r : ℕ) : ℕ → ℝ := fun j => f (min j r)

theorem frozenAfter_of_le (f : ℕ → ℝ) {r j : ℕ} (h : j ≤ r) : frozenAfter f r j = f j := by
  simp [frozenAfter, Nat.min_eq_left h]

variable {S : Setting} [NeZero S.L] {m₁ r N : ℕ} {ϱ : ℝ}

/-- **The operator constants of the successor** (LFR §II.1.1, Definition II.1.1): the running
constants of the small-field data `sf` of the scale `r` (couplings `β_j`, masses, `ν_j`, `z_j`, the
tolerances `δ_j` and `p₀(β_j)` computed from `β_j`), frozen after `r`; the cutoff mass is `bgMass`
(zero below `k₀`), the background and action masses are the physical `ν_j L^{-2j}` (ruling R2); the
non-running constants (`a_n`, `C_ψ`, `a`, `C_b`, `B₀`) are those of `cs`. -/
noncomputable def succOpConsts (S : Setting) [NeZero S.L] (k0 : ℕ) (A0 : ℝ) (cs : OpConsts)
    (sf : SFData S.d S.L m₁ r N ϱ) : OpConsts where
  aw := cs.aw
  mu := frozenAfter (bgMass k0 S.L sf.ν) r
  muBg := frozenAfter (fun j => sf.ν j / (S.L : ℝ) ^ (2 * j)) r
  muAct := frozenAfter (fun j => sf.ν j / (S.L : ℝ) ^ (2 * j)) r
  nu := frozenAfter sf.ν r
  delta := frozenAfter (deltaRun A0 S.p0 cs.aKer sf.β) r
  p0 := frozenAfter (pZero A0 S.p0 cs.aKer sf.β) r
  Cpsi := cs.Cpsi
  beta := frozenAfter sf.β r
  z := frozenAfter sf.z r
  aKer := cs.aKer
  Cb := cs.Cb
  B0 := cs.B0

/-- **The budget constants of the successor**: `c₁, c₂, H₀` of `P` and the couplings of `sf`, frozen
after `r`. -/
noncomputable def succBudgetConsts (P : BudgetConsts) (sf : SFData S.d S.L m₁ r N ϱ) :
    BudgetConsts where
  c1 := P.c1
  c2 := P.c2
  H0 := P.H0
  beta := frozenAfter sf.β r

variable {R : ℕ → ℝ} {k0 M : ℕ} {cs : OpConsts} {P : BudgetConsts} {P6 : Def6.Consts}
  {C7 : Consts7} {β ν : ℝ} {k : ℕ} {sf : SFData S.d S.L C7.m₁ k N ϱ}
  {sf' : SFData S.d S.L C7.m₁ (k + 1) N ϱ}

/-- **`Coh` at the successor**: the coherence of the constants of the successor with its small-field
data `sf'` (whose kernel coefficients follow the free flow up to `k + 1`), from the coherence of
the input (the typing and a priori data, `B₀`). -/
theorem coh_succ (hcoh : Coh S R k0 M cs P P6 C7 β ν k sf)
    (ha : ∀ j, 1 ≤ j → j ≤ k + 1 → sf'.a j = compWeight S.L cs.aKer j) :
    Coh S R k0 M (succOpConsts S k0 C7.A0 cs sf') (succBudgetConsts P sf') P6 C7 β ν (k + 1) sf'
    where
  M_eq := hcoh.M_eq
  M_pow := hcoh.M_pow
  lam_eq := hcoh.lam_eq
  R_eq := hcoh.R_eq
  k0_eq := hcoh.k0_eq
  a_free := ha
  beta_cs := fun _ hj => frozenAfter_of_le _ hj
  beta_P := fun _ hj => frozenAfter_of_le _ hj
  z_cs := fun _ hj => frozenAfter_of_le _ hj
  nu_cs := fun _ hj => frozenAfter_of_le _ hj
  delta_cs := fun _ hj => frozenAfter_of_le (deltaRun C7.A0 S.p0 cs.aKer sf'.β) hj
  p0_cs := fun _ hj => frozenAfter_of_le (pZero C7.A0 S.p0 cs.aKer sf'.β) hj
  B0_cs := hcoh.B0_cs

/-- **The field clauses at the successor** (ruling R2): the masses of the successor's constants. -/
theorem field_succ {hv : EuclideanSpace ℝ (Fin N)} (hf : FieldClauses S k0 k cs sf hv) :
    FieldClauses S k0 (k + 1) (succOpConsts S k0 C7.A0 cs sf') sf' hv where
  h_unit := hf.h_unit
  mu_eq := fun _ hj => frozenAfter_of_le (bgMass k0 S.L sf'.ν) hj
  muBg_eq := fun _ hj => frozenAfter_of_le (fun j => sf'.ν j / (S.L : ℝ) ^ (2 * j)) hj
  muAct_eq := fun _ hj => frozenAfter_of_le (fun j => sf'.ν j / (S.L : ℝ) ^ (2 * j)) hj

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
theorem D7Bdry.toD7Bdry2_of_ball (h : D7Bdry Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv)
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

end Balaban.RootFSpine
