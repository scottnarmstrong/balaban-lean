/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.StepDensity
public import Balaban.Spine.SFStepClauses
public import Balaban.Spine.RootF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field step of the spine from a sub-spine

`sfStepInput_of_parts` proves the sub-input `SFStepInput` of the class step (A4-1,
`Spine/ClassStep.lean`; LF-3, LFR Theorem IV.1.1 (a)–(e), (h); P5 Theorem 1, P6 Theorem 1, P4
Theorem 1) from nine sub-inputs at general `d, N` on the class carriers.

**The construction maps.** The parts of the step are properties of one construction, so they are
stated for two maps, parameters of the sub-spine that the provider defines: the small-field step
`Φ` (the image of the small-field data of `ℛ_k` under I-9: SF Theorems 5.1–5.3 with the new level
computed on the local generating set of each polymer, ruling R8) and the vacuum constant `ΦE` of
the step. A part stated as "there are small-field data with property X" and another as "for all
small-field data with property X, there is the large-field data" could not be combined: the
properties are bounds and do not determine the data, and the large-field half (the form (D1) of the
step density) holds only for the data the step constructs. With the maps fixed, each part is a
separate statement about them, true for the maps of the source.

**The step density** is `stepDensity` (`Spine/StepDensity.lean`): `ρ' = e^{-s|T^{(k+1)}_1|} S^{(k)} T^{(k)} ρ`
with the Gaussian `t_k` of constant `β_k a L^{d-2}`, the field renormalization `z_{k+1}` of the image
and the vacuum normalization `s` of the step. `∫ ρ' = e^{-s|T^{(k+1)}_1|} ∫ ρ` is proved
(`integralStep_stepDensity`) from the integrability of `ρ`.

The sub-inputs (statements below; status in `notes/phase1/SPINE.md`, "SFStepInput sub-inputs"):
* A4-1a `SFInheritInput`: the image keeps `β_j, ν_j, z_j, a_j` and the terms of the levels `j ≤ k`
  (pulled back to the tori of scale `k + 1`), `a_{k+1}` follows the free flow, `z_{k+1} > 0`;
* A4-1b `SFNewLevelInput`: the term clauses, the generating sets and torus independence of the new
  level `k + 1` on its birth domain;
* A4-1c `SFRenormInput`: (H.6) and (H.5) at `k + 1` (the counterterm system `ξ^{(k)}`);
* A4-1d `SFDensityInput`: the density (H.1) at `k + 1` is real;
* A4-1e `SFRemainderInput`: P5 H4 for `ℛ^{(k+1)}` with `½ β_{k+1}^{-m-1}`;
* A4-1f `SFCoherenceInput`: (D8) of the new level and of `ℛ^{(k+1)}`;
* A4-1g `SFVacuumInput`: the vacuum constant `E_{k+1}` is bounded by `C_b (log β_{k+1} + 1)`;
* A4-1h `LFStepInput`: the large-field half, the representation of the step density in `ℛ^pre_{k+1}`
  with the small-field data `Φ rec.F.sf`;
* A4-1i `StepIntegrableInput`: the members of `ℛ_k` are integrable.

Proved here: the small-field clauses (D2), (D8), (D9) of the successor (`sfSucc_clauses`,
`Spine/SFStepClauses.lean`: the inherited levels by the landed splice theorems on the birth domains),
(I.2) up to `k`, `β_0 = β`, `ν_0 = ν`, the ties of the scales `j ≤ k` asked by `SFStepInput`, the vacuum
flow up to `k + 1`, `k + 1 ≤ k̂_f + 1`, and the integral. Inhabitation (rule 10): `sfClassAt_witness`;
the nine sub-inputs need the exemption of the spine inputs.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale

namespace Balaban.RootFSpine

/-!
### The small-field half of a member of `ℛ_k`
-/

/-- **The small-field half of a member of `ℛ_k`** (the premises of the small-field step: LFR
(A-IV.2) and Definition II.6.2, clauses (D2), (D8), (D9)): the data `sf` of scale `k` satisfy (D2)
of `IsRep2` (`IsSFFamily2` on the birth domains, P5 H4 for `ℛ^{(k)}`), the small-field half of (D8),
(D9) for the a priori regime index `k₀ = kZero d L β ν`, their kernel coefficients follow the free
flow `a_j = compWeight L a j` (`Coh.a_free`), and their running coefficients start from the bare
couplings and satisfy (I.2) up to `k`. -/
def SFClassAt (d N L : ℕ) [NeZero L] (P6 : Def6.Consts) (m₁ : ℕ) (ϱ a β ν : ℝ) (k : ℕ)
    (sf : SFData d L m₁ k N ϱ) : Prop :=
  D2SF2 P6 (kZero d L β ν) sf (fun _ => 1) ∧ D8SF P6.m₀ sf ∧ D9Coeff P6 (kZero d L β ν) sf ∧
    (∀ j, 1 ≤ j → j ≤ k → sf.a j = compWeight L a j) ∧ sf.β 0 = β ∧ sf.ν 0 = ν ∧
    RunningHypTo d L β ν a (1 / 20) sf.β sf.ν k

/-- (I.2) up to `k` depends only on the running coefficients at the scales `j ≤ k`. -/
theorem runningHypTo_congr {d L : ℕ} {β ν a ε : ℝ} {βs νs βs' νs' : ℕ → ℝ} {k : ℕ}
    (h : RunningHypTo d L β ν a ε βs νs k) (hβ : ∀ j, j ≤ k → βs' j = βs j)
    (hν : ∀ j, j ≤ k → νs' j = νs j) : RunningHypTo d L β ν a ε βs' νs' k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hγ, hδ⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun j hj => (hβ j hj).symm ▸ hγ j hj,
    fun j hj => (hν j hj).symm ▸ hδ j hj⟩

/-- The small-field data of a record of `ℛ_k` satisfy `SFClassAt`. -/
theorem RepRec.sfClassAt {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}
    (rec : RepRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k ρ νk) :
    SFClassAt d N T.L P6 C7.m₁ ϱ cs₀.aKer β ν k rec.F.sf :=
  ⟨rec.rep.sfData, rec.rep.coherent, rec.rep.coeff,
    fun j hj1 hjk => (rec.rep.coh.a_free j hj1 hjk).trans (by rw [rec.tie_aKer]), rec.β0, rec.ν0,
    rec.run⟩

open Balaban.LargeField.Def7.Wit Balaban.LargeField.Def7v2.Wit in
/-- **`SFClassAt` is inhabited** (rule 10): the small-field data of the landed witness of `IsRep2`
(`d = L = 3`, `N = 2`, `k = 1`, `ν = 1/(27β)`). -/
theorem sfClassAt_witness :
    ∃ sf : @SFData 3 typing.L wC7.m₁ 1 2 ⟨by norm_num [typing, typing0]⟩ (Background.bgR0 3 3),
      @SFClassAt 3 2 typing.L ⟨by norm_num [typing, typing0]⟩ wP6 wC7.m₁ (Background.bgR0 3 3)
        (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer wβ wν₀ 1 sf := by
  have : NeZero typing.L := ⟨by norm_num [typing, typing0]⟩
  have : NeZero typing.M := ⟨by norm_num [typing, typing0]⟩
  obtain ⟨ρ, νk, ⟨rec⟩⟩ := repClassAt_witness 0
  exact ⟨_, rec.sfClassAt⟩

/-!
### The sub-inputs
-/

/-- **The extended vacuum flow**: the flow `E_j` of a record of scale `k` followed, at the scale
`k + 1`, by the new vacuum constant `e` (and constant `e` beyond, which is never read). -/
def vacExt (E : ℕ → ℝ) (k : ℕ) (e : ℝ) : ℕ → ℝ := fun j => if j ≤ k then E j else e

theorem vacExt_of_le {E : ℕ → ℝ} {k j : ℕ} (e : ℝ) (h : j ≤ k) : vacExt E k e j = E j := by
  simp [vacExt, h]

theorem vacExt_succ (E : ℕ → ℝ) (k : ℕ) (e : ℝ) : vacExt E k e (k + 1) = e := by
  simp [vacExt]

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
  (ΦE : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ)

/-- **The form of the small-field sub-inputs**: a property `Q` of the image `Φ sf` of the small-field
data `sf` of every member of `ℛ_k`, `1 ≤ k < k₀`, for `β ≥ β₀(κ, c₉)`, `0 < ν ≤ 7/8 L⁻²`. The map
`Φ` is the small-field step of the source (I-9: SF Theorems 5.1–5.3, P4 Theorem 1, P5 Theorem 1),
a parameter of the sub-spine. -/
def SFImageInput (Q : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 → ∀ [NeZero (T κ c₉).L],
  ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
  ∀ sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉),
    SFClassAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉) (cs₀ κ c₉).aKer β ν k sf →
    Q κ c₉ β ν k sf (Φ κ c₉ β ν k sf)

/-- **A4-1a, the inherited data (I-9, inherited part; ruling R6; the free flow (II.1)).** The image
keeps the running constants `β_j, ν_j, z_j, a_j` and the terms `ℰ^{(j)}, ℳ^{(j)}` with their
generating sets at the levels `j ≤ k`, transported to the tori of scale `k + 1`
(`liftOldTermsFam`, along `oldTorusEquiv`); the new kernel coefficient follows the free flow,
`a_{k+1} = a (1 - L⁻²)/(1 - L^{-2(k+1)})`, and the new field renormalization is positive. -/
def SFInheritInput : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ fun κ c₉ _ _ k _ sf sf' =>
    (∀ j, j ≤ k → sf'.β j = sf.β j ∧ sf'.ν j = sf.ν j ∧ sf'.z j = sf.z j ∧ sf'.a j = sf.a j) ∧
    sf'.a (k + 1) = compWeight (T κ c₉).L (cs₀ κ c₉).aKer (k + 1) ∧ 0 < sf'.z (k + 1) ∧
    ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ k →
      (sf'.Tm N₂).E j = (liftOldTermsFam sf.Tm N₂).E j ∧
        (sf'.Tm N₂).M j = (liftOldTermsFam sf.Tm N₂).M j ∧
        (sf'.Tm N₂).gs j = (liftOldTermsFam sf.Tm N₂).gs j

/-- **A4-1b, the new level (the fluctuation integral on the local generating set of each polymer;
P3 (4.44)–(4.47), P4 Proposition 4.1, ruling R8).** On every Def-6 torus the terms of the new level
`k + 1` (`newLevelTerms`) satisfy the term clauses (H.2)–(H.4), (H.7) on the birth domain of the
level, their generating sets satisfy the strong specification `𝔹_{k+1}(X)`, and they are torus
independent (P4 (H.4)). -/
def SFNewLevelInput : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ fun κ c₉ β ν k _ _ sf' =>
    (∀ (N₂ : ℕ) [NeZero N₂], ReadTorus (T κ c₉).L (P6 κ c₉).m₀ N₂ →
      SFTermClauses (P6 κ c₉)
        (sfDom (P6 κ c₉) (kZero d (T κ c₉).L β ν) sf' N₂) (newLevelTerms (sf'.Tm N₂))) ∧
    (∀ (N₂ : ℕ) [NeZero N₂], ReadTorus (T κ c₉).L (P6 κ c₉).m₀ N₂ → ∀ (X : Set (CTorus d (T κ c₉).L N₂ (C7 κ c₉).m₁ (k + 1))),
      IsPolyDom (P6 κ c₉).m₀ (k + 1) X →
        GsSpec.GsSpecStrong (k + 1) le_rfl X ((sf'.Tm N₂).gs (k + 1) X)) ∧
    TorusIndep (P6 κ c₉).m₀ (fun N₂ _ => newLevelTerms (sf'.Tm N₂))

/-- **A4-1c, the renormalization (the counterterm system `ξ^{(k)}` and the densities `D_E`, `D_M`;
P4 (4.14)–(4.22), (5.28), conditions (H.5), (H.6); `rg_step_infty`).** The coefficients of the image
satisfy the coefficient bounds (H.6) at `k + 1` (the flow `β_{k+1} = β_k L^{d-2}/(1 + ξ₃)`,
`ν_{k+1} = ν_k L² (1 + ξ₃)/(1 + ξ₂)` with `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}`, `β_{k+1} > B L^{(k+1)(d-2)}`,
`0 < ν_{k+1} ≤ ν̄`, the window of `a_{k+1}`), and the new level satisfies the renormalization
conditions (H.5) at `k + 1`. -/
def SFRenormInput : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ fun κ c₉ _ _ k _ _ sf' =>
    CoeffBounds d (T κ c₉).L (k + 1) (P6 κ c₉) sf'.β sf'.ν sf'.a ∧
    RenormCondAlong (P6 κ c₉).m₀ (k + 1) (sf'.ν (k + 1)) sf'.Tm (k + 1)
      (torusSeq (T κ c₉).L (P6 κ c₉).m₀) (fun n => torusSeq_ne_zero (P6 κ c₉).m₀ n)

/-- **A4-1d, the density of the new small-field class is real (P4 (H.1) at `k + 1`).** On every
Def-6 torus, at the real fields realized by a datum `D` inside the small-field region `Ξ_{k+1}` and
for real sources of `ℓ¹` norm `< 1`, the exponential of the exponent (H.1) of the image (`expo2`,
the action at the complete background and the composites `ℰ_{k+1}`, `ℱ_{k+1}`) is real. With the
term clauses this gives the density clause of `IsSF2` (`exists_isSF2_of_real`). -/
def SFDensityInput : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ fun κ c₉ β ν k _ _ sf' =>
    ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus (T κ c₉).L (P6 κ c₉).m₀ N₂ →
      ∀ (Ψ₀ : CTorus d (T κ c₉).L N₂ (C7 κ c₉).m₁ (k + 1) → Fin N → ℝ)
      (h₀ : Fin N → ℝ) (g : CTorus d (T κ c₉).L N₂ (C7 κ c₉).m₁ (k + 1) → Fin N → ℝ)
      (D : BgData (topGS d (T κ c₉).L N₂ (C7 κ c₉).m₁ (k + 1) (ϱ κ c₉)) N),
      Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
      Xi (topGS d (T κ c₉).L N₂ (C7 κ c₉).m₁ (k + 1) (ϱ κ c₉))
          (aIdeal (T κ c₉).L (k + 1) (sf'.a (k + 1)))
          ((⟨kZero d (T κ c₉).L β ν, sf'.ν⟩ : Regime (T κ c₉).L).sfBgMass (k + 1)) (k + 1) 1
          ((P6 κ c₉).p (sf'.β (k + 1)) / Real.sqrt (sf'.β (k + 1))) Ψ₀ h₀ →
      (Complex.exp (expo2 (P6 κ c₉) ⟨kZero d (T κ c₉).L β ν, sf'.ν⟩ sf'.β sf'.a (sf'.Tm N₂)
        (sf'.E N₂) D (fun x i => (g x i : ℂ)))).im = 0

/-- **A4-1e, the remainder terms `ℛ^{(k+1)}_n` (P5 Propositions 3.1–3.4, LFR Lemma IV.1.8).** On
every Def-6 torus the terms `ℛ^{(k+1)}_n` of the image satisfy P5 H4 at the scale `k + 1` with the
pre-`R` allowance `½ β_{k+1}^{-m-1}` at `n = m` (`preFac`). -/
def SFRemainderInput : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ fun κ c₉ _ _ _ _ _ sf' =>
    ∀ (N₂ : ℕ) [NeZero N₂], RTermsH4 (ϱ := ϱ κ c₉) (P6 κ c₉) sf'.β sf'.ν sf'.a N₂ (sf'.Rt N₂)
      (preFac ((P6 κ c₉).m₀ + (C7 κ c₉).m₁))

/-- **A4-1f, the torus coherence of the new small-field data (D8 at `k + 1`, LFR Theorem IV.1.1 (h),
D-IV.9; the exact two-torus agreement of the new level, W1089 `e0CoeffFamily_value_fromTowerG_core_twoTorus`,
W1090 `coreE0_unique`).** The new level `ℳ^{(k+1)}` and the terms `ℛ^{(k+1)}_n` of the image are the
same on two tori for polymers that wind around neither (`D8SF` of the image with its levels `j ≤ k`
emptied; the inherited levels are `liftOldTermsFam_M_eq_of_d8`). -/
def SFCoherenceInput : Prop :=
  SFImageInput d N T P6 C7 cs₀ ϱ Φ fun κ c₉ _ _ _ _ _ sf' =>
    D8SF (P6 κ c₉).m₀ { sf' with Tm := fun N₂ _ => newLevelTerms (sf'.Tm N₂) }

/-- **A4-1g, the vacuum constant of the step (P4 (2.1), (2.41), (2.63); rulings R5, R5′;
`Fluctuation/VacuumFlow.lean`).** `ΦE` is the vacuum constant `E_{k+1}` of the scale `k + 1`
produced by the step from the small-field data and the vacuum flow `E_j, j ≤ k` of the input (with
the vacuum normalization of the step, `stepDensity`, which keeps the flow of order `log β`). For a flow
with `|E_j| ≤ C_b (log β_j + 1)` at `j ≤ k`, the new constant satisfies the same bound at `k + 1`. -/
def SFVacuumInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 → ∀ [NeZero (T κ c₉).L],
  ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
  ∀ sf : SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉),
    SFClassAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉) (cs₀ κ c₉).aKer β ν k sf →
    ∀ Ev : ℕ → ℝ, VacuumFlowTo (cs₀ κ c₉).Cb Ev sf.β k →
      |ΦE κ c₉ β ν k sf Ev| ≤
        (cs₀ κ c₉).Cb * (Real.log ((Φ κ c₉ β ν k sf).β (k + 1)) + 1)

/-- **A4-1h, the large-field half of the step (LF-3 (b)–(d), (h); P5 §§2–3, P6 §§2–3; LFR Lemmas
IV.1.2–IV.1.6, LF-2 (i) for the budget, Lemma IV.1.5 for (D7)).** For `1 ≤ k < k₀`, a record `rec`
of `ℛ_k` whose small-field image `Φ rec.F.sf` satisfies the small-field clauses of `ℛ^pre_{k+1}`
((D2) with the allowance `preFac`, (D8), (D9), the free flow of `a_j` up to `k + 1`) and keeps the
running constants at the scales `j ≤ k`: on the tori of the family there are operator and budget
constants `cs', P'` (with the outer constants of the prefix), large-field data `lf'` at `k + 1`,
coefficient data `St', vc'` and a vacuum normalization `s` such that the family `⟨Φ rec.F.sf, lf'⟩`
represents the step density `stepDensity … (β_k a L^{d-2}) z_{k+1} s ρ` in `ℛ^pre_{k+1}`
(`IsRepPre2`: histories of `ρ` followed by every step record and the hull closure; the quiet kernels
and the kernels of P5 (2.47)·P6 (3.2) with the local background and the boundary factors; the
boundary terms `ℬ^{(k+1)}` with `3κ/2` and `B_st`; (H6′)^pre; the coefficient data of P5 (1.8)) and
is torus coherent (`LFCoherent`). **The vacuum tie (R5, R5′; P4 (2.1), (2.41), (2.63)):** the step data
of `lf'` carry the vacuum constants of the extended flow `E_0, …, E_k, ΦE` (`vacExt`; the new constant
`E_{k+1}` is the one of A4-1g): on every torus `StepData.VacuumTie` with offsets `δ″, δ‴` free of the
flow. The step data are the ones whose boundary exponent `b_k` is bounded (`IsRepPre2`), so `ΦE = 0`
satisfies the tie only if the source's vacuum energy is zero. -/
def LFStepInput : Prop :=
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
    ∀ hkK' : k + 1 ≤ kf + 1,
    ∃ (cs' : OpConsts) (P' : BudgetConsts)
      (lf' : ∀ (nK : ℕ) [NeZero nK], Rep 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N
        (rec.geo nK) cs' P' (k + 1))
      (St' : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ (k + 1) N)
      (vc' : CorrCoef d) (s : ℝ),
      cs'.aKer = (cs₀ κ c₉).aKer ∧ cs'.Cpsi = (cs₀ κ c₉).Cpsi ∧ cs'.Cb = (cs₀ κ c₉).Cb ∧
      cs'.aw = (cs₀ κ c₉).aw ∧ P'.c1 = (PB κ c₉).c1 ∧ P'.c2 = (PB κ c₉).c2 ∧
      P'.H0 = (PB κ c₉).H0 ∧
      IsRepPre2 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] rec.R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N rec.geo cs' P' (P6 κ c₉) (C7 κ c₉) β ν h (rH κ c₉) (k + 1) rec.hM6 hkK'
        ⟨Φ κ c₉ β ν k rec.F.sf, lf'⟩
        (stepDensity d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k
          (rec.F.sf.β k * (cs₀ κ c₉).aKer * ((T κ c₉).L : ℝ) ^ (d - 2))
          ((Φ κ c₉ β ν k rec.F.sf).z (k + 1)) s ρ) St' vc' ∧
      LFCoherent (⟨Φ κ c₉ β ν k rec.F.sf, lf'⟩ : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] rec.R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N rec.geo cs' P' (k + 1) (C7 κ c₉).m₁
        (ϱ κ c₉)) ∧
      ∀ (nK : ℕ) [NeZero nK], ∃ dpp dppp : ℕ → ℝ, (lf' nK).SD.VacuumTie Set.univ
        (vacExt rec.Ev k (ΦE κ c₉ β ν k rec.F.sf rec.Ev)) dpp dppp

/-- **A4-1i, the densities of `ℛ_k` are integrable (the premise of P1 (1.11), `∫ T ρ = ∫ ρ`).** For
`1 ≤ k < k₀`, every member of `ℛ_k` is integrable in the field of the `k`-blocks on every torus of the
family, for every source of the unit `ℓ¹` ball. -/
def StepIntegrableInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk →
    ∀ (nK : ℕ) [NeZero nK]
      (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
        (kf + 1) N → ℂ), g ∈ LargeField.l1Ball _ → Integrable (fun ψ => ρ nK ψ g)

end Inputs

/-!
### The assembly
-/

section Assembly

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}

/-- **The small-field step from its sub-inputs** (LFR Theorem IV.1.1). For a record `rec` of `ℛ_k`,
`1 ≤ k < k₀`, the small-field data of the successor are the image `sf' = Φ rec.F.sf`; the small-field
clauses of `ℛ^pre_{k+1}` ((D2), (D8), (D9)) follow from the input class and the sub-inputs A4-1a–f
(`sfSucc_clauses`: the inherited levels by the landed splice theorems on the birth domains, the new
level, the renormalization, the density, the remainders and the coherence from the sub-inputs); the
large-field half A4-1h gives the representation of the step density with these small-field data;
the vacuum flow is extended by the vacuum constant `E_{k+1}` of A4-1g; (I.2) up to `k`, `β_0 = β`,
`ν_0 = ν` and the ties of the scales `j ≤ k` are those of the input (A4-1a); `∫ ρ' = c ∫ ρ` is
`integralStep_stepDensity` with the integrability A4-1i. The threshold is the largest of the nine
thresholds and `2` (`k₀ ≤ k̂_f` needs `β > 1`, `kZero_le_of_isHorizon`). The typing facts `d ≥ 3`,
`L ≥ 3`, `ϱ ≥ R₀(d, L)` are those of the background theory on the birth domains (clauses of
`PrefixInput`). -/
theorem sfStepInput_of_parts (hd : 3 ≤ d) (hL : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → 3 ≤ (T κ c₉).L)
    (hϱ : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → bgR0 d (T κ c₉).L ≤ ϱ κ c₉)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
    (ΦE : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ)
    (hI : SFInheritInput d N T P6 C7 cs₀ ϱ Φ) (hNw : SFNewLevelInput d N T P6 C7 cs₀ ϱ Φ)
    (hRn : SFRenormInput d N T P6 C7 cs₀ ϱ Φ) (hDn : SFDensityInput d N T P6 C7 cs₀ ϱ Φ)
    (hRt : SFRemainderInput d N T P6 C7 cs₀ ϱ Φ) (hCo : SFCoherenceInput d N T P6 C7 cs₀ ϱ Φ)
    (hV : SFVacuumInput d N T P6 C7 cs₀ ϱ Φ ΦE) (hLF : LFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ ΦE)
    (hInt : StepIntegrableInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    SFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₁, h₁⟩ := hI κ hκ c₉ hc₉
  obtain ⟨b₂, h₂⟩ := hNw κ hκ c₉ hc₉
  obtain ⟨b₃, h₃⟩ := hRn κ hκ c₉ hc₉
  obtain ⟨b₄, h₄⟩ := hDn κ hκ c₉ hc₉
  obtain ⟨b₅, h₅⟩ := hRt κ hκ c₉ hc₉
  obtain ⟨b₆, h₆⟩ := hCo κ hκ c₉ hc₉
  obtain ⟨b₇, h₇⟩ := hV κ hκ c₉ hc₉
  obtain ⟨b₈, h₈⟩ := hLF κ hκ c₉ hc₉
  obtain ⟨b₉, h₉⟩ := hInt κ hκ c₉ hc₉
  refine ⟨max (max (max b₁ b₂) (max b₃ b₄)) (max (max b₅ b₆) (max (max b₇ b₈) (max b₉ 2))), ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec
  simp only [max_le_iff] at hβ
  obtain ⟨⟨⟨hb₁, hb₂⟩, hb₃, hb₄⟩, ⟨hb₅, hb₆⟩, ⟨hb₇, hb₈⟩, hb₉, hb2⟩ := hβ
  have hsf := rec.sfClassAt
  obtain ⟨hcst, hfree', hz, hTm⟩ := h₁ β hb₁ ν hν hνL k hk1 hk rec.F.sf hsf
  obtain ⟨hnew, hgsnew, hTInew⟩ := h₂ β hb₂ ν hν hνL k hk1 hk rec.F.sf hsf
  obtain ⟨hC', hR'⟩ := h₃ β hb₃ ν hν hνL k hk1 hk rec.F.sf hsf
  have hreal := h₄ β hb₄ ν hν hνL k hk1 hk rec.F.sf hsf
  have hRtm := h₅ β hb₅ ν hν hνL k hk1 hk rec.F.sf hsf
  have hD8n := h₆ β hb₆ ν hν hνL k hk1 hk rec.F.sf hsf
  have hEv := h₇ β hb₇ ν hν hνL k hk1 hk rec.F.sf hsf rec.Ev rec.vac
  obtain ⟨hD2', hD8', hD9'⟩ := sfSucc_clauses hd (hL κ hκ c₉ hc₉) (hϱ κ hκ c₉ hc₉) hk1 hk rec.rep.sfData
    rec.rep.coherent hsf.2.2.2.1 rec.run hcst hfree' hTm hnew hgsnew hTInew hC' hR' hreal hRtm hD8n
  have hkK' : k + 1 ≤ kf + 1 := by
    have h1 : (1 : ℝ) < β := by linarith
    have := kZero_le_of_isHorizon (d := d) (L := (T κ c₉).L) (by omega)
      (by have := hL κ hκ c₉ hc₉; omega) h1 hν hkf
    omega
  have hafree : ∀ j, 1 ≤ j → j ≤ k + 1 →
      (Φ κ c₉ β ν k rec.F.sf).a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j := by
    intro j hj1 hjk
    by_cases hj : j ≤ k
    · rw [(hcst j hj).2.2.2]; exact hsf.2.2.2.1 j hj1 hj
    · obtain rfl : j = k + 1 := by omega
      exact hfree'
  obtain ⟨cs', P', lf', St', vc', s, o1, o2, o3, o4, o5, o6, o7, hpre, hcoh', hvt⟩ :=
    h₈ β hb₈ ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hD2' hD8' hD9' hafree
      (fun j hj => ⟨(hcst j hj).1, (hcst j hj).2.1, (hcst j hj).2.2.1⟩) hkK'
  have hβk : 0 < rec.F.sf.β k := by
    obtain ⟨γ, hγ, -, hβk⟩ := rec.run.beta_eq k le_rfl
    rw [hβk]
    have := rec.run.hβ
    have hL0 : (0 : ℝ) < (T κ c₉).L := by exact_mod_cast (by have := hL κ hκ c₉ hc₉; omega : 0 < (T κ c₉).L)
    positivity
  have hcK : 0 < rec.F.sf.β k * (cs₀ κ c₉).aKer * ((T κ c₉).L : ℝ) ^ (d - 2) := by
    have ha := rec.run.ha1
    have hL0 : (0 : ℝ) < (T κ c₉).L := by exact_mod_cast (by have := hL κ hκ c₉ hc₉; omega : 0 < (T κ c₉).L)
    have : (0 : ℝ) < (cs₀ κ c₉).aKer := by linarith
    positivity
  refine ⟨_, (Φ κ c₉ β ν k rec.F.sf).ν (k + 1),
    { hM6 := rec.hM6
      hkK := hkK'
      R := rec.R
      geo := rec.geo
      cs := cs'
      P := P'
      F := ⟨Φ κ c₉ β ν k rec.F.sf, lf'⟩
      St := St'
      vc := vc'
      geoTie := rec.geoTie
      tie_aKer := o1
      tie_Cpsi := o2
      tie_Cb := o3
      tie_aw := o4
      tie_c1 := o5
      tie_c2 := o6
      tie_H0 := o7
      pre := hpre
      β0 := (hcst 0 (Nat.zero_le k)).1.trans rec.β0
      ν0 := (hcst 0 (Nat.zero_le k)).2.1.trans rec.ν0
      νk := rfl
      run := runningHypTo_congr rec.run (fun j hj => (hcst j hj).1) (fun j hj => (hcst j hj).2.1)
      coh := hcoh'
      Ev := vacExt rec.Ev k (ΦE κ c₉ β ν k rec.F.sf rec.Ev)
      vac := fun j hj => by
        by_cases hjk : j ≤ k
        · rw [vacExt_of_le _ hjk, (hcst j hjk).1]
          exact rec.vac j hjk
        · obtain rfl : j = k + 1 := by omega
          rw [vacExt_succ]
          exact hEv
      zpos := fun j hj1 hjk => by
        by_cases hjk' : j ≤ k
        · rw [show (Φ κ c₉ β ν k rec.F.sf).z j = rec.F.sf.z j from (hcst j hjk').2.2.1]
          exact rec.zpos j hj1 hjk'
        · obtain rfl : j = k + 1 := by omega
          exact hz }, fun j hj => ⟨(hcst j hj).1, (hcst j hj).2.1, (hcst j hj).2.2.2,
      (hcst j hj).2.2.1, vacExt_of_le _ hj⟩,
    fun nK _ => hvt nK,
    integralStep_stepDensity s hcK hz ρ (h₉ β hb₉ ν hν hνL h hh kf hkf k hk1 hk ρ νk ⟨rec⟩)⟩

/-- **The small-field step from its sub-inputs and the prefix**: `sfStepInput_of_parts`, the typing
facts `d ≥ 3`, `L ≥ 3` and `ϱ ≥ R₀(d, L)` being clauses of `PrefixInput`. -/
theorem sfStepInput_of_prefix {δ : ℝ} (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
    (ΦE : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ)
    (hI : SFInheritInput d N T P6 C7 cs₀ ϱ Φ) (hNw : SFNewLevelInput d N T P6 C7 cs₀ ϱ Φ)
    (hRn : SFRenormInput d N T P6 C7 cs₀ ϱ Φ) (hDn : SFDensityInput d N T P6 C7 cs₀ ϱ Φ)
    (hRt : SFRemainderInput d N T P6 C7 cs₀ ϱ Φ) (hCo : SFCoherenceInput d N T P6 C7 cs₀ ϱ Φ)
    (hV : SFVacuumInput d N T P6 C7 cs₀ ϱ Φ ΦE) (hLF : LFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ ΦE)
    (hInt : StepIntegrableInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    SFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  sfStepInput_of_parts (hA1 1 one_pos 1 one_pos).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.three_le_d
    (fun κ hκ c₉ hc₉ => (hA1 κ hκ c₉ hc₉).1)
    (fun κ hκ c₉ hc₉ => (hA1 κ hκ c₉ hc₉).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    Φ ΦE hI hNw hRn hDn hRt hCo hV hLF hInt

end Assembly

end Balaban.RootFSpine
