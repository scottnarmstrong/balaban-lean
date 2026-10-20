/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.SFStepClauses
public import Balaban.Spine.SFStep
public import Balaban.Spine.FrozenStep
public import Balaban.Spine.Witness

/-!
# The small-field clauses of the frozen step (A4f-1, part 1)

The frozen small-field step `ℛ♭_k → ℛ♭_{k+1}`, `max(k₀, 1) ≤ k < k̂_f`, runs on the complete backgrounds
at every scale. Its small-field half is the sub-spine of `Spine/SFStep.lean` at the flat class:

* `SFFlatClassAt`: the small-field half of a member of `ℛ♭_k` (the analogue of `SFClassAt`: (D2♭)
  `SFFlat2`, (D8), (D9♭) `D9Flat`, the free flow of `a_j`, `β_0 = β`, `ν_0 = ν`, (I.2) up to `k`, and the
  mass bound `ν_k ≤ 9/10` of `FlatRep`); `FlatRep.sfFlatClassAt` reads it off a record of `ℛ♭_k`;
  `sfFlatClassAt_witness` is its inhabitation (rule 10);
* `sfFlatSucc_clauses`: the clauses (D2♭), (D8), (D9♭) of the successor at the scale `k + 1`, the
  instance of the class-independent core `sfSucc_core` (`Spine/SFStepClauses.lean`) at the constants
  `massOne P6` of the coefficient bounds and the allowance `1` of the remainders (no operation `R`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale

namespace Balaban.RootFSpine

/-- **The small-field half of a member of `ℛ♭_k`** (the premises of the frozen small-field step: LFR
Definition II.6.3 (iii)–(iv) and (A-IV.2)): the data `sf` of scale `k` satisfy (D2♭) `SFFlat2`, the
small-field half of (D8), (D9♭), their kernel coefficients follow the free flow `a_j = compWeight L a j`,
their running coefficients start from the bare couplings and satisfy (I.2) up to `k`, and the running
mass is at most `9/10` (the mass bound of `FlatRep`). -/
def SFFlatClassAt (d N L : ℕ) [NeZero L] (P6 : Def6.Consts) (m₁ : ℕ) (ϱ a β ν : ℝ) (k : ℕ)
    (sf : SFData d L m₁ k N ϱ) : Prop :=
  SFFlat2 P6 (kZero d L β ν) sf ∧ D8SF P6.m₀ sf ∧ D9Flat P6 sf ∧
    (∀ j, 1 ≤ j → j ≤ k → sf.a j = compWeight L a j) ∧ sf.β 0 = β ∧ sf.ν 0 = ν ∧
    RunningHypTo d L β ν a (1 / 20) sf.β sf.ν k ∧ sf.ν k ≤ 9 / 10

/-- The small-field data of a record of `ℛ♭_k` satisfy `SFFlatClassAt`. -/
theorem FlatRep.sfFlatClassAt {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ kf + 1} {R : ℕ → ℝ}
    {geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M}
    {cs : OpConsts} {P : BudgetConsts}
    {F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N} {vc : CorrCoef d}
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}
    (hF : FlatRep d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k hM6 hkK R geo cs P F St vc ρ νk) :
    SFFlatClassAt d N T.L P6 C7.m₁ ϱ cs₀.aKer β ν k F.sf := by
  obtain ⟨-, h1, -, -, -, -, -, -, hrep, hβ0, hν0, hνk, hrun, -, hX⟩ := hF
  refine ⟨hrep.sfData, hrep.coherent, hrep.coeff,
    fun j hj1 hjk => (hrep.coh.a_free j hj1 hjk).trans (by rw [h1]), hβ0, hν0, hrun, ?_⟩
  rw [hνk]
  exact hX

open Balaban.LargeField.Def7.Wit Balaban.LargeField.Def7v2.Wit in
/-- **`SFFlatClassAt` is inhabited** (rule 10): the small-field data of the landed witness of
`IsRepFlat2` (`d = L = 3`, `N = 2`, `k = 1`, `ν = 1/(27β)`). -/
theorem sfFlatClassAt_witness (rH : ℝ) :
    ∃ sf : @SFData 3 typing.L wC7.m₁ 1 2 ⟨by norm_num [typing, typing0]⟩ (Background.bgR0 3 3),
      @SFFlatClassAt 3 2 typing.L ⟨by norm_num [typing, typing0]⟩ wP6 wC7.m₁ (Background.bgR0 3 3)
        (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer wβ wν₀ 1 sf := by
  have : NeZero typing.L := ⟨by norm_num [typing, typing0]⟩
  have : NeZero typing.M := ⟨by norm_num [typing, typing0]⟩
  obtain ⟨ρ, νk, hM6, hkK, R, geo, cs, P, F, St, vc, hF⟩ := flatClassAt_witness rH
  exact ⟨_, hF.sfFlatClassAt⟩

section Succ

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The small-field clauses of the frozen successor at the scale `k + 1`** (the small-field half
of LF-5: LFR Theorem IV.2.2 (a)–(f); P4 Theorem 1 at the complete backgrounds). The clauses
(D2♭), (D8), (D9♭) of `IsRepFlat2` at `k + 1` from those of the input and the clauses of the new
level; `sfSucc_clauses` for the class `ℛ♭`. -/
theorem sfFlatSucc_clauses {P6 : Def6.Consts} {k0 : ℕ} {a β ν : ℝ}
    {sf : SFData d L m₁ k N ϱ} {sf' : SFData d L m₁ (k + 1) N ϱ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hk1 : 1 ≤ k)
    (hcl : SFFlat2 P6 k0 sf) (hD8 : D8SF P6.m₀ sf) (hνk910 : sf.ν k ≤ 9 / 10)
    (hfree : ∀ j, 1 ≤ j → j ≤ k → sf.a j = compWeight L a j)
    (hrun : RunningHypTo d L β ν a (1 / 20) sf.β sf.ν k)
    (hcst : ∀ j, j ≤ k → sf'.β j = sf.β j ∧ sf'.ν j = sf.ν j ∧ sf'.z j = sf.z j ∧
      sf'.a j = sf.a j)
    (hfree' : sf'.a (k + 1) = compWeight L a (k + 1))
    (hTm : ∀ (N₂ : ℕ) [NeZero N₂] (j : ℕ), j ≤ k →
      (sf'.Tm N₂).E j = (liftOldTermsFam sf.Tm N₂).E j ∧
        (sf'.Tm N₂).M j = (liftOldTermsFam sf.Tm N₂).M j ∧
        (sf'.Tm N₂).gs j = (liftOldTermsFam sf.Tm N₂).gs j)
    (hnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ →
      SFTermClauses P6 (sfDom P6 k0 sf' N₂) (newLevelTerms (sf'.Tm N₂)))
    (hgsnew : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (X : Set (CTorus d L N₂ m₁ (k + 1))),
      IsPolyDom P6.m₀ (k + 1) X → GsSpec.GsSpecStrong (k + 1) le_rfl X ((sf'.Tm N₂).gs (k + 1) X))
    (hTInew : TorusIndep P6.m₀ (fun N₂ _ => newLevelTerms (sf'.Tm N₂)))
    (hC' : CoeffBounds d L (k + 1) (massOne P6) sf'.β sf'.ν sf'.a)
    (hR' : RenormCondAlong P6.m₀ (k + 1) (sf'.ν (k + 1)) sf'.Tm (k + 1) (torusSeq L P6.m₀)
      (fun n => torusSeq_ne_zero P6.m₀ n))
    (hreal : ∀ (N₂ : ℕ) [NeZero N₂], ReadTorus L P6.m₀ N₂ → ∀ (Ψ₀ : CTorus d L N₂ m₁ (k + 1) → Fin N → ℝ) (h₀ : Fin N → ℝ)
      (g : CTorus d L N₂ m₁ (k + 1) → Fin N → ℝ) (D : BgData (topGS d L N₂ m₁ (k + 1) ϱ) N),
      Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
      Xi (topGS d L N₂ m₁ (k + 1) ϱ) (aIdeal L (k + 1) (sf'.a (k + 1)))
        ((⟨k0, sf'.ν⟩ : Regime L).sfBgMass (k + 1)) (k + 1) 1
        (P6.p (sf'.β (k + 1)) / Real.sqrt (sf'.β (k + 1))) Ψ₀ h₀ →
      (Complex.exp (expo2 P6 ⟨k0, sf'.ν⟩ sf'.β sf'.a (sf'.Tm N₂) (sf'.E N₂) D
        (fun x i => (g x i : ℂ)))).im = 0)
    (hRt : ∀ (N₂ : ℕ) [NeZero N₂],
      RTermsH4 (ϱ := ϱ) P6 sf'.β sf'.ν sf'.a N₂ (sf'.Rt N₂) (fun _ => 1))
    (hD8new : D8SF P6.m₀ { sf' with Tm := fun N₂ _ => newLevelTerms (sf'.Tm N₂) }) :
    SFFlat2 P6 k0 sf' ∧ D8SF P6.m₀ sf' ∧ D9Flat P6 sf' := by
  obtain ⟨ρsf, hρsf⟩ := hcl.torus
  obtain ⟨⟨ρ', hρ'⟩, hTI, hren, hD8'⟩ := sfSucc_core (hd := hd) (hL := hL) (hϱ := hϱ) (hk1 := hk1)
    (hadm := hcl.admissible) (hC := hcl.coeff) (hνk910 := hνk910)
    (htorOld := fun N₂ _ hN => hρsf N₂ hN) (hTIold := hcl.torusIndep)
    (hrenOld := hcl.renorm) (hD8 := hD8) (hfree := hfree) (hrun := hrun) (hcst := hcst)
    (hfree' := hfree') (hTm := hTm) (hnew := hnew) (hgsnew := hgsnew) (hTInew := hTInew)
    (hR' := hR') (hreal := hreal) (hD8new := hD8new)
  exact ⟨⟨hcl.admissible, hC', ⟨ρ', hρ'⟩, hTI, hren, hRt⟩, hD8',
    ⟨hC'.beta_gt, hC'.nu_pos, hC'.nu_le⟩⟩

end Succ

end Balaban.RootFSpine
