/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Coherence
public import Balaban.Background.ExistenceSetup
public import Balaban.Frozen.Model.PartitionFunction
public import Balaban.Flow.RunningCoefficients
public import Balaban.Frozen.Geometry.IsPolymer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# The inputs of the Root-F spine

Named obligations, stated over the landed classes of the large-field reconstruction
(`notes/phase1/LF-RECONSTRUCTION.md`, cited **LFR**; Part IV): the class `IsRep2` (`ℛ_k`, Definition
II.6.2 second version, which contains the small-field class `IsSFFamily2` as its clause (D2)) and
the frozen-regime class `IsRepFlat2` (`ℛ♭_k`, §II.6.3). Each `…Input` below is a proposition of the
papers in our recorded reading; none of them is proved here. They are used as hypotheses only by
`Balaban.RootFSpine.rootF_of_spine` (`Balaban/Spine/RootF.lean`) and by the theorems that will
discharge them. The list and the status of each input are in `notes/phase1/SPINE.md`.

## The constants

The inputs share the constants of the prefix of LFR §I.1.4, which depend on `κ, c₉` only and are
fixed before `β₀`. They are passed as functions of `(κ, c₉)` (the choice of the provider): `T` (the
typing constants `d, L, M, R_base, θ_±, α, p₀, p₂, A₂, …`; Root-F's `L, M` are `T.L, T.M`), `P6`
(the Def-6 constants `γ, α₁, κ, E₀, c₈, c₉, …`), `C7` (`m₁, A₀, A₁, B₀, B_st`), `PB` (`c₁, c₂, H₀`
of the budget), `cs₀` (the non-running operator constants: the kernel constant `a`, `C_ψ`, `C_b`,
the weights `a_n`), `M1, c` (the unit `M₁` of the generating sets and `M = c M₁`), `rH` (the radius
of the pinned field ball) and `ϱ` (the separation of the generating sets). The running constants
(`β_j, ν_j, z_j, E_j`, the masses, the tolerances) are not fixed in advance: they are part of the
representation of each density (`Coh` ties them to its small-field data) and are produced by the
steps (LFR Theorem IV.3.2 (d)); the class predicates ask (I.2) for them up to the current scale
(`RunningHypTo`) and pin them to the bare couplings at scale `0` (`β_0 = β`, `ν_0 = ν`). The a
priori setting at `β` is `𝒮[d, T, β, a] = (T with d, λ̂_j = log(β a) + 1 + j θ)` (`lamHat`, D-IV.2);
the regime index is the a priori `k₀ = kZero d L β ν` (D-IV.11) and the horizon is `k̂_f`
(`IsHorizon`, D-IV.1): the flow runs on the tori of side `ℓ = M n_K L^K`, `K = k̂_f + 1`, and
Root-F's `kf` is `k̂_f`.

## The inputs (A-numbers of `notes/phase1/ROOTASM2.md`)

* `PrefixInput` (A1): the constant conditions that every class member needs (`L ≥ 3`, the window of
  the kernel constant `a`, `M = c M₁ = L^{m₀+m₁}` with `c ≥ 14`, the admissibility of the Def-6
  constants, `c₉, B₀ > 0`, `C_b ≥ 0`) and the ties of the class constants to Root-F's `δ, κ, c₉`
  (LFR rows 1, 5, 10).
* `BaseStepInput` (A3, LF-6): the first step `ρ₀ ↦ ρ₁` lands in `ℛ₁` (or `ℛ♭₁` if `k₀ = 0`) with
  `∫ ρ₁ = c Z(g)`.
* `ClassStepInput` (A4, LF-3 + LF-4): `ℛ_k → ℛ_{k+1}` for `1 ≤ k < k₀`, `∫ ρ_{k+1} = c ∫ ρ_k`.
* `TransferInput` (A4, Lemma IV.2.1): `ℛ_{k₀} ⊂ ℛ♭_{k₀}`.
* `FrozenStepInput` (A4, LF-5): `ℛ♭_k → ℛ♭_{k+1}` for `k₀ ≤ k < k_f`, `∫ ρ_{k+1} = c ∫ ρ_k`.
* `LastIntegralInput` (A6, LF-8 (a)): `∫ ρ_{k_f} = exp(E + ⟨g, h⟩ + ∑_j ∑_X p_j(X; g))` with
  scale-`j` activities `p_j` in the observable form of Root-F (`ObservableActivities`).
* `KfZeroInput` (A7, LF-8 (b)): the same for `Z(g)` itself when `ν > 7/8 L⁻²`, at scale `1`.

The two-torus agreement (A11) is not a separate source statement. Its input is the torus coherence
(D8) of the class: the small-field half is the landed clause `D8SF` of `IsRep2`/`IsRepFlat2`, the
large-field half is `LFCoherent` (`Spine/Coherence.lean`, LFR D-IV.9), a conjunct of
`RepClassAt`/`FlatClassAt`. The base and step inputs (A3, A4) produce it; the last integral (A6)
consumes it, and its output is the agreement conjunct of `ObservableActivities` (LFR Theorem IV.5.3
item 7); A7 states the agreement directly. The rate, support and amplitude ties of A9, A10 are the
bound and support conjuncts of `ObservableActivities` (LFR Theorem IV.5.3 items 2, 3, 5), with the
class constants tied to Root-F's by `PrefixInput`.

`ObservableActivities` is the conjunction of its clauses on each admissible torus
(`ActSupportAt`, `ActAnalyticAt`, `ActLocalAt`, `ActBoundAt`) and the two-torus agreement
`ActAgree`; `FlatClassAt` is the existence of witnesses of its body `FlatRep`. The sub-spine of the
last integral (`Spine/LastIntegral.lean`) states its sub-inputs with these pieces. -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-- The a priori setting of the large-field class at the coupling `β`: the typing constants `T` with
dimension `d` and the a priori sequence `λ̂_j = log(β a) + 1 + j θ` (LFR D-IV.2; `Coh.lam_eq`
requires exactly this sequence, with `a` the kernel constant). -/
scoped macro "𝒮[" dd:term ", " T:term ", " β:term ", " a:term "]" : term =>
  `(Setting.mk { $T with d := $dd } (lamHat $dd (Typing.L $T) $β $a))

/-- The densities at scale `k` of the flow on the tori with `n_K` top cubes (side `ℓ = M n_K L^K`):
`ρ(ψ_k; g)` on the field `ψ_k` of the `k`-blocks, with the source `g : 𝕋_ℓ × {1, …, N} → ℂ`. -/
scoped macro "𝒟[" d:term ", " N:term ", " T:term ", " β:term ", " a:term ", "
    K:term ", " k:term "]" : term =>
  `(∀ (nK : ℕ) [NeZero nK],
    (BlockAt 𝒮[$d, $T, $β, $a] (sides (Typing.L $T) $K nK) (Typing.M $T) $K $k →
      EuclideanSpace ℝ (Fin $N)) →
    (GIdx 𝒮[$d, $T, $β, $a] (sides (Typing.L $T) $K nK) (Typing.M $T) $K $N → ℂ) → ℂ)

/-!
### The clauses of the observable form, and the body of the frozen-regime class
-/

/-- **Support on one torus** (the first clause of `ObservableActivities`, top scale `J`): on `𝕋_ℓ`
the increment of `p_j(X; ·)` vanishes unless `1 ≤ j ≤ J` and `X` is a scale-`j` polymer
(`IsPolymer d ℓ (M L^j)`). -/
def ActSupportAt (d N L M J ℓ : ℕ) [NeZero ℓ]
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ j X, ¬ (j ∈ Finset.Icc 1 J ∧ IsPolymer d ℓ (M * L ^ j) X) → ∀ g, p ℓ j X g = p ℓ j X 0

/-- **Analyticity on one torus** (the second clause of `ObservableActivities`): on `𝕋_ℓ`,
`p_j(X; ·)` is analytic on the unit `ℓ¹` ball. -/
def ActAnalyticAt (d N ℓ : ℕ) [NeZero ℓ]
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ j X, AnalyticOnNhd ℂ (p ℓ j X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}

/-- **Locality on one torus** (the third clause of `ObservableActivities`): on `𝕋_ℓ`,
`p_j(X; g)` depends on `g|_X` only. -/
def ActLocalAt (d N ℓ : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ j X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) → p ℓ j X g = p ℓ j X g'

/-- **The bound on one torus** (the fourth clause of `ObservableActivities`, top scale `J`): on
`𝕋_ℓ` and for `1 ≤ j ≤ J`, the increment is at most
`(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}` on the unit `ℓ¹` ball. -/
def ActBoundAt (d N L M : ℕ) (κ c₉ δ : ℝ) (J ℓ : ℕ) [NeZero ℓ]
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ j ∈ Finset.Icc 1 J, ∀ X (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
    ‖p ℓ j X g - p ℓ j X 0‖ ≤ c₉ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
      * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)

/-- **The two-torus agreement** (the last clause of `ObservableActivities`): the increments on two
admissible tori (`M L^{kf+1} ∣ ℓ, ℓ'`) agree on the images of a finite set `A ⊂ ℤ^d` in the common
quarter box `|y_μ| < min(ℓ, ℓ')/4`. -/
def ActAgree (d N L M kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
    ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
      a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
      p ℓ j (A.image fun y μ => (y μ : ZMod ℓ))
          (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) -
          p ℓ j (A.image fun y μ => (y μ : ZMod ℓ)) 0 =
        p ℓ' j (A.image fun y μ => (y μ : ZMod ℓ'))
          (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) -
          p ℓ' j (A.image fun y μ => (y μ : ZMod ℓ')) 0

/-- **The body of `FlatRep` with the scale of (I.2) and the last clause as parameters.** It is
`FlatRep` with (I.2) asked up to a scale `r` (`RunningHypTo`) instead of `k`, and with the closing
clause `νk ≤ 9/10` replaced by `X F.sf.β F.sf.ν F.sf.a`, a clause on the running couplings, masses and
kernel constants of the representation.
`FlatRep` is the case `r = k`, `X = (νk ≤ 9/10)`. The frozen step (`Spine/FrozenStep.lean`) states
its small-field output with `r = k` at the scale `k + 1` and `X = (ν_k = the input mass)`. -/
def FlatRepGen (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k r : ℕ)
    (X : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    [NeZero T.M] [NeZero T.L] (hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1)
    (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N) (vc : CorrCoef d)
    (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) : Prop :=
  (∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = M1 ∧ (geo nK).c = c) ∧
    cs.aKer = cs₀.aKer ∧ cs.Cpsi = cs₀.Cpsi ∧ cs.Cb = cs₀.Cb ∧ cs.aw = cs₀.aw ∧
    P.c1 = PB.c1 ∧ P.c2 = PB.c2 ∧ P.H0 = PB.H0 ∧
    IsRepFlat2 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P P6 C7 β ν h rH k
      kf hM6 hkK F ρ St vc ∧
    F.sf.β 0 = β ∧ F.sf.ν 0 = ν ∧ F.sf.ν k = νk ∧
    RunningHypTo d T.L β ν cs₀.aKer (1 / 20) F.sf.β F.sf.ν r ∧ LFCoherent F ∧ X F.sf.β F.sf.ν F.sf.a

/-- **The body of `FlatClassAt` for given witnesses** `hM6, hkK, R, geo, cs, P, F, St, vc`: the
representation `F` of `ρ` in `ℛ♭_k` (`IsRepFlat2`, horizon `k̂ = kf`) on the tori of the horizon
`K = kf + 1`, with the outer constants of the prefix, `β_0 = β`, `ν_0 = ν`, `ν_k = νk`, (I.2) up to
`k` (`RunningHypTo`), the large-field half of (D8) (`LFCoherent`) and the mass bound
`ν_k ≤ 9/10`. The mass bound is the form in which the flow gives (D9♭): at the first frozen scale
`ν_{k₀} ≤ e^{2ε}/β_{k₀}` (I.2), and `ν_{k+1} = ν_k L² (1+ξ₃)/(1+ξ₂) ≤ (7/8) e^{c_ξ/β}` for
`k < k_f` (LFR Theorem IV.2.2 (D9♭); the base step gives the same for `ν₁`), which is at most
`9/10` for `β ≥ β₀`. With (I.2) (`ν_j = ν L^{2j} δ_j`, `|log δ_j| ≤ 1/20`) it gives
`ν_j L^{-2j} L^{2k} ≤ e^{1/10} · 9/10 ≤ 1` at every level `j ≤ k`, the standing mass hypothesis of
the background theory at the stopping scale (`Spine/InheritedBound.lean`). -/
def FlatRep (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k : ℕ)
    [NeZero T.M] [NeZero T.L] (hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1)
    (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N) (vc : CorrCoef d)
    (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) : Prop :=
  FlatRepGen d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k k (fun _ _ _ => νk ≤ 9 / 10) hM6 hkK R geo cs P F
    St vc ρ νk

/-- **The vacuum flow up to a scale** (P4 (2.1), (2.41), (2.63); rulings R5, R5′): the scale-indexed
vacuum constants `E_j`, `j ≤ r`, satisfy `|E_j| ≤ C (log β_j + 1)`. The class predicates carry such a
flow with the constant `C_b` of the bound (S0) (`OpConsts.Cb`), which LFR Theorem IV.1.1 (f) defines
from the vacuum constants among others; the step data of the creating steps are tied to it
(`VacuumTied`, `Spine/RStep.lean`). The flow is indexed by the scale, unlike the constant
`SFData.E`, which is indexed by the Def-6 torus. -/
def VacuumFlowTo (C : ℝ) (E βs : ℕ → ℝ) (r : ℕ) : Prop :=
  ∀ j, j ≤ r → |E j| ≤ C * (Real.log (βs j) + 1)

/-- The zero flow satisfies the bound when its right side is nonnegative (rule 10). -/
theorem vacuumFlowTo_zero {C : ℝ} {βs : ℕ → ℝ} {r : ℕ}
    (h : ∀ j, j ≤ r → 0 ≤ C * (Real.log (βs j) + 1)) : VacuumFlowTo C (fun _ => 0) βs r :=
  fun j hj => by simpa using h j hj

/-- **The a priori horizon `k̂_f`** (LFR (I.1), D-IV.1): the least `k` with `ν L^{2k+2} ≥ 1`.
Root-F's `kf` is `k̂_f`; the flow runs on the tori with `M L^{k̂_f + 1} ∣ ℓ`. -/
def IsHorizon (L : ℕ) (ν : ℝ) (kf : ℕ) : Prop :=
  1 ≤ ν * (L : ℝ) ^ (2 * kf + 2) ∧ ∀ k < kf, ν * (L : ℝ) ^ (2 * k + 2) < 1

/-- **The data of a member of the class `ℛ_k` at the constants of the prefix** (LFR Definition
II.6.2, second version `IsRep2`; regime `k ≤ k₀`; the body of `RepClassAt`, with its witnesses as
fields, so that the step inputs can speak about them): `ρ` has a representation `F` on the tori of the horizon `K = kf + 1` for
the a priori setting `𝒮[d, T, β, a]`, the a priori regime index `kZero d L β ν`, the outer constants
`P6, C7` and the outer parts `cs₀, PB, M1, c` of the operator, budget and geometric constants, whose
running small-field coefficients start from the bare couplings (`β_0 = β`, `ν_0 = ν`) and satisfy
(I.2) up to the scale `k` (`RunningHypTo`, `ε = 1/20`, LFR (A-IV.2)), and whose large-field data are
torus coherent (`LFCoherent`, the large-field half of (D8), LFR D-IV.9; the small-field half is the
clause `coherent` of `IsRep2`); `νk` is its running mass `ν_k` at scale `k`; it carries a vacuum
flow `E_j`, `j ≤ k`, with `|E_j| ≤ C_b (log β_j + 1)` (`VacuumFlowTo`, rulings R5, R5′). -/
structure RepRec (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k : ℕ)
    [NeZero T.M] [NeZero T.L] (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) where
  hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)
  hkK : k ≤ kf + 1
  R : ℕ → ℝ
  geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M
  cs : OpConsts
  P : BudgetConsts
  F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ
  St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N
  vc : CorrCoef d
  geoTie : ∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = M1 ∧ (geo nK).c = c
  tie_aKer : cs.aKer = cs₀.aKer
  tie_Cpsi : cs.Cpsi = cs₀.Cpsi
  tie_Cb : cs.Cb = cs₀.Cb
  tie_aw : cs.aw = cs₀.aw
  tie_c1 : P.c1 = PB.c1
  tie_c2 : P.c2 = PB.c2
  tie_H0 : P.H0 = PB.H0
  rep : IsRep2 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P P6 C7 β ν h rH k
    hM6 hkK F ρ St vc
  β0 : F.sf.β 0 = β
  ν0 : F.sf.ν 0 = ν
  νk : F.sf.ν k = νk
  run : RunningHypTo d T.L β ν cs₀.aKer (1 / 20) F.sf.β F.sf.ν k
  coh : LFCoherent F
  /-- the scale-indexed vacuum flow `E_j` (rulings R5, R5′) -/
  Ev : ℕ → ℝ
  vac : VacuumFlowTo cs₀.Cb Ev F.sf.β k

/-- **The class `ℛ_k` at the constants of the prefix**: the existence of a record `RepRec`. -/
def RepClassAt (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k : ℕ)
    [NeZero T.M] [NeZero T.L] (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) : Prop :=
  Nonempty (RepRec d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k ρ νk)

/-- **The frozen-regime class `ℛ♭_k` at the constants of the prefix** (LFR §II.6.3, second version
`IsRepFlat2`; regime `k₀ ≤ k ≤ k_f`, horizon `k̂ = kf`), with the same conventions as `RepClassAt`.
-/
def FlatClassAt (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k : ℕ)
    [NeZero T.M] [NeZero T.L] (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) : Prop :=
  ∃ (hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1) (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N) (vc : CorrCoef d),
    FlatRep d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k hM6 hkK R geo cs P F St vc ρ νk

/-- **The normalization `∫ ρ_k dψ_k = c Z(g)`** (LFR Theorem IV.3.2 (c), P1 (1.11), P7 (1.7)): on
every torus of the family (side `ℓ = M n_K L^K`) and every source of the unit `ℓ¹` ball, the
Lebesgue integral of the density over the fields of the `k`-blocks is a positive constant
(independent of `g`) times the partition function of Root-F. -/
def IntegralIsZ (d N : ℕ) (T : Typing) (β ν a : ℝ) (h : EuclideanSpace ℝ (Fin N)) (K k : ℕ)
    [NeZero T.M] [NeZero T.L] (ρ : 𝒟[d, N, T, β, a, K, k]) : Prop :=
  ∃ C : ℕ → ℝ, (∀ nK, 0 < C nK) ∧ ∀ (nK : ℕ) [NeZero nK]
    (g : GIdx 𝒮[d, T, β, a] (sides T.L K nK) T.M K N → ℂ), g ∈ l1Ball _ →
      ∫ ψ, ρ nK ψ g = (C nK : ℂ) * partitionFunction d N (T.M * sides T.L K nK K * T.L ^ K) β ν h
        (fun x i => g (x, i))

/-- **One step preserves the integral up to a positive constant** (`∫ T ρ = ∫ ρ`, P1 (1.11);
`∫ R ρ = ∫ ρ`, P7 (1.7); `S` is a linear change of variables): on every torus of the family and
every source of the unit `ℓ¹` ball, `∫ ρ' dψ_{k+1} = c ∫ ρ dψ_k` with `c > 0` independent of `g`. -/
def IntegralStep (d N : ℕ) (T : Typing) (β a : ℝ) (K k : ℕ) [NeZero T.M] [NeZero T.L]
    (ρ : 𝒟[d, N, T, β, a, K, k]) (ρ' : 𝒟[d, N, T, β, a, K, k + 1]) : Prop :=
  ∃ C : ℕ → ℝ, (∀ nK, 0 < C nK) ∧ ∀ (nK : ℕ) [NeZero nK]
    (g : GIdx 𝒮[d, T, β, a] (sides T.L K nK) T.M K N → ℂ), g ∈ l1Ball _ →
      ∫ ψ, ρ' nK ψ g = (C nK : ℂ) * ∫ ψ, ρ nK ψ g

/-- **Activities in the observable form of Root-F** (LFR Definition IV.5.2 and Theorem IV.5.3 items
2–5, 7; the device of P7 (4.15)–(4.17), ARCH (F3)), scales `1 ≤ j ≤ J`. Only the increments
`p_j(X; g) - p_j(X; 0)` enter `log (Z(g)/Z(0))`, and only they are constrained. On every admissible
torus (`M L^{kf+1} ∣ ℓ`): the increment vanishes unless `X` is a scale-`j` polymer
(`IsPolymer d ℓ (M L^j) X`); `p_j(X; ·)` is analytic on the unit `ℓ¹` ball and depends on `g|_X`
only; the increment is bounded there by `(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}`. The
increments of two admissible tori agree on the images of a finite set `A ⊂ ℤ^d` in the box
`|y_μ| < min(ℓ, ℓ')/4` (P4 (H.4), (D8), PE (f)). The factor `1/2` pays the Cauchy estimate of the
derivative on the half ball (`norm_kf0Deriv_le_two`). -/
def ObservableActivities (d N L M : ℕ) (κ c₉ δ : ℝ) (J kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    ActSupportAt d N L M J ℓ p ∧ ActAnalyticAt d N ℓ p ∧ ActLocalAt d N ℓ p ∧
      ActBoundAt d N L M κ c₉ δ J ℓ p) ∧
  ActAgree d N L M kf p

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The typing conditions of LF-2 that the transfer and the background theory read**, for one
pair `κ, c₉`: the typing `T = Ty κ c₉` with dimension `d` is `Typing.Ok`;
`θ₋ ≤ (d-2) log L ≤ θ₊` ((H-λ), first part); `c_H ≥ d(d-2) log L / 2` ((H-λ), the window of LFR
Lemma IV.3.3 (c)); and for Lemma B: `H₀ > 0`, `c₁ ≥ 0`, `L ≤ M`, `c_v ≥ M^d (H₀ + c₁ + 3)`. -/
def TypingClauses (d : ℕ) (Ty : ℝ → ℝ → Typing) (PB : ℝ → ℝ → BudgetConsts) (κ c₉ : ℝ) :
    Prop :=
  ({ Ty κ c₉ with d := d } : Typing).Ok ∧
    ((Ty κ c₉).θm ≤ thetaOf d (Ty κ c₉).L ∧ thetaOf d (Ty κ c₉).L ≤ (Ty κ c₉).θp) ∧
    (d : ℝ) * ((d : ℝ) - 2) / 2 * Real.log (Ty κ c₉).L ≤ (Ty κ c₉).cH ∧
    0 < (PB κ c₉).H0 ∧ 0 ≤ (PB κ c₉).c1 ∧ (Ty κ c₉).L ≤ (Ty κ c₉).M ∧
    ((Ty κ c₉).M : ℝ) ^ d * ((PB κ c₉).H0 + (PB κ c₉).c1 + 3) ≤ (Ty κ c₉).cv

/-- **The coefficient step at one pair `κ, c₉` (LFR Theorem IV.3.2 (d); prefix row 10).** The
Def-6 constants satisfy `c₈ q ≤ (1 - q)/20` with `q = L^{-2γ}`, i.e. `ε = c₈ q/(1 - q) ≤ 1/20`. -/
def FlowRateAt (κ c₉ : ℝ) : Prop :=
  (P6 κ c₉).c₈ * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ ≤
    1 / 20 * (1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ)

/-- **A1 (the prefix; LFR §I.1.4).** For every `κ, c₉ > 0` the constants of the prefix satisfy every
condition that a member of the classes needs, so that a wrong choice cannot empty them:
* row 3: `L ≥ 3` (Root-F's `2 ≤ L` follows);
* the kernel constant `a = cs₀.aKer`: `1 < a < 3/2` (`RunningHypTo`, (I.2)) and
  `9/10 ≤ a (1 - L⁻²)²` (with `a_k = a (1 - L⁻²)/(1 - L^{-2k})` (`Coh.a_free`), the window
  `9/10 (1 - L⁻²)⁻¹ ≤ a_k < 3/2` of (H.6) (`CoeffBounds.a_ge`, `a_lt`) at every scale);
* row 6: `M = c M₁` with `c ≥ 14`, `M₁ ≥ 1` (`Geo`) and `M = L^{m₀ + m₁}` (`Coh.M_pow`);
* the Def-6 constants are admissible (`IsSFFamily2.admissible`), `c₉^{flow} > 0` (the strict bound
  (H.7)), `B₀ > 0` (the strict bound (D7)), `C_b ≥ 0` (the bound (S0) of `b_k`);

and the ties of the class constants to Root-F's (LFR D-IV.7, rows 1, 5, 10): `δ ≤ γ - α₁`,
`κ_flow ≥ C_{d,L} (κ + 1)` with `C_{d,L} = 3^{d+1} L^{2d+1}`, and `c₉^{flow} ≤ (c₉/2) e^{-κ_flow}`;

and the constant conditions of the typing and of the background theory (`TypingClauses`: the typing
is `Typing.Ok` in dimension `d`, the windows of (H-λ), the conditions of Lemma B on `H₀, c₁, M, c_v`;
and `R₀(d, L) ≤ ϱ`, the separation of the generating sets, `bgR0`);

and the coefficient rate (row 10, `c₈ ∈ (0, c₈′]`): `FlowRateAt`, `c₈ q ≤ (1 - q)/20`). -/
def PrefixInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    3 ≤ (T κ c₉).L ∧
    1 < (cs₀ κ c₉).aKer ∧ (cs₀ κ c₉).aKer < 3 / 2 ∧
    9 / 10 ≤ (cs₀ κ c₉).aKer * (1 - (((T κ c₉).L : ℝ) ^ 2)⁻¹) ^ 2 ∧
    (T κ c₉).M = c κ c₉ * M1 κ c₉ ∧ 14 ≤ c κ c₉ ∧ 1 ≤ M1 κ c₉ ∧
    (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁) ∧
    (P6 κ c₉).Admissible d (T κ c₉).L ∧ 0 < (P6 κ c₉).c₉ ∧ 0 < (C7 κ c₉).B0 ∧
    0 ≤ (cs₀ κ c₉).Cb ∧
    δ ≤ (P6 κ c₉).γ - (P6 κ c₉).α₁ ∧
    (3 : ℝ) ^ (d + 1) * ((T κ c₉).L : ℝ) ^ (2 * d + 1) * (κ + 1) ≤ (P6 κ c₉).κ ∧
    (P6 κ c₉).c₉ ≤ c₉ / 2 * Real.exp (-(P6 κ c₉).κ) ∧
    TypingClauses d T PB κ c₉ ∧ Background.bgR0 d (T κ c₉).L ≤ ϱ κ c₉ ∧
    FlowRateAt T P6 κ c₉

/-- **A3 (the base step, LF-6; LFR Theorem II.7.10 (a), (b); P4 (2.42)–(2.54), pp. 691–694; P5 p.
487).** For `β ≥ β₀`, `0 < ν ≤ 7/8 L⁻²` (so that `k_f ≥ 1`), every unit field `h` and the horizon
`kf = k̂_f`: the density `ρ₁ = S^{(0)} T^{(0)} ρ₀` of the first step has a representation in `ℛ₁` if
`k₀ ≥ 1` (regime (A)) and in `ℛ♭₁` if `k₀ = 0` (regime (B)), and `∫ ρ₁ dψ₁ = c Z(g)` on every torus
of the family. Membership includes `β_0 = β`, `ν_0 = ν`, (I.2) at the scales `0, 1` (LF-7 (d)) and
the torus coherence (D8) of both halves (Theorem II.7.10 (d): every datum is given by the same
formula on `ℤ^d`). -/
def BaseStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
    (1 ≤ kZero d (T κ c₉).L β ν →
      ∃ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, 1]) (νk : ℝ),
        RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf 1 ρ νk ∧
        IntegralIsZ d N (T κ c₉) β ν (cs₀ κ c₉).aKer h (kf + 1) 1 ρ) ∧
    (kZero d (T κ c₉).L β ν = 0 →
      ∃ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, 1]) (νk : ℝ),
        FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf 1 ρ νk ∧
        IntegralIsZ d N (T κ c₉) β ν (cs₀ κ c₉).aKer h (kf + 1) 1 ρ)

/-- **A4 (one full step below `k₀`: LF-3 + LF-4; LFR Theorem IV.1.1 (P5 Theorem 1, P6 Theorem 1, P5
p. 499) followed by Theorem III.10.8 (P5 Theorem 2 = P7 Theorem 2, P7 (1.3)–(1.7), pp. 497–529)).**
For `1 ≤ k < k₀`, every `ρ ∈ ℛ_k` has `ρ' = R^{(k+1)} S^{(k)} T^{(k)} ρ ∈ ℛ_{k+1}` with
`∫ ρ' = c ∫ ρ`. The hypothesis carries the premises of LF-3 and LF-4: (A-IV.2) through `β_0 = β`,
`ν_0 = ν` and (I.2) up to `k`, and (D8) of both halves (D-IV.9). The conclusion asks the same of
`ρ'`: running constants extended by the step (LF-7 (d)), (D8) by the locality of the constructions
(Theorem IV.1.1 (h), Theorem III.10.8 (D8)). The small-field part of the step (P4 Theorem 1 for
`IsSFFamily2`, the clause (D2) of `ℛ_{k+1}`) is a cited input of LF-3. It is not split off, because
no landed operator states the relation between the two small-field data. -/
def ClassStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk →
    ∃ (ρ' : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k + 1]) (νk' : ℝ),
      RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf (k + 1) ρ' νk' ∧
      IntegralStep d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k ρ ρ'

/-- **A4 (the transfer at `k₀`; LFR Lemma IV.2.1, P5 p. 490, LF-2 (iv)).** If `k₀ ≥ 1`, every member
of `ℛ_{k₀}` (with running mass `ν_{k₀}`) is a member of `ℛ♭_{k₀}` with the same density and the same
running mass (the representation is re-read: (D2) to (D2♭), (D9) to (D9♭), (H6′) to (H6♭); (D8),
`β_0 = β` and (I.2) are unchanged). Its landed half is `IsRep2.toFlat`, which needs the torus
horizon `K ≤ k₀ + 1`; at `K = k̂_f + 1` it needs LF-2 (ii) with the counter history truncated at
`k + 1` (`notes/phase1/SPINE.md`, item 4). -/
def TransferInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  1 ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, kZero d (T κ c₉).L β ν]) (νk : ℝ),
    RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf (kZero d (T κ c₉).L β ν) ρ νk →
    FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf (kZero d (T κ c₉).L β ν) ρ νk

/-- **A4 (one frozen step: LF-5; LFR Theorem IV.2.2, P5/P6 Theorem 4 repaired, P6 p. 21).** For
`max(k₀, 1) ≤ k < kf` and `ρ ∈ ℛ♭_k` whose running mass has not reached the stopping threshold
(`ν_k ≤ 7/8 L⁻²`, i.e. `k < k_f`), `ρ' = S^{(k)} T^{(k)} ρ ∈ ℛ♭_{k+1}` with `∫ ρ' = c ∫ ρ`. As for
`ClassStepInput`, hypothesis and conclusion carry `β_0 = β`, `ν_0 = ν`, (I.2) up to the scale and
(D8); the budget (H6♭) at `K = k̂_f + 1` needs LF-2 (ii) truncated at `k + 1`. -/
def FrozenStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → kZero d (T κ c₉).L β ν ≤ k → k < kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk →
    νk * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
    ∃ (ρ' : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k + 1]) (νk' : ℝ),
      FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf (k + 1) ρ' νk' ∧
      IntegralStep d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k ρ ρ'

/-- **A6 (the last integral, LF-8 (a); LFR Theorem IV.4.1 (IV.4.2), P7 (4.9)–(4.17), pp. 529–533, P9
(4.4)–(4.7), p. 516; in the observable form of LFR Definition IV.5.2 and Theorem IV.5.3).** For
`1 ≤ k ≤ kf` and `ρ ∈ ℛ♭_k` at the stopping scale (`ν_k > 7/8 L⁻²`, so `k = k_f`):
`∫ ρ dψ_k = exp(-E_{k+1,0} |T^{(k+1)}| + ⟨g, h⟩ + ∑_{j=1}^{k+1} ∑_X p_j(X; g))` on every torus of
the family, where for `j ≤ k` the activity is `p_j(X; g) = ∑_{x ∈ X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩`
(the (H.7) terms of the class at the constant configuration) and for `j = k + 1` it collects
`ℳ^{(k+1)}_0`, the polymer terms `ℛ^{(k+1)}_n` and `𝒫^{(k+1)}` regrouped by the scale-`(k+1)`
polymer `Ȳ` of their domain; the activities satisfy `ObservableActivities` with top scale `k + 1`.
The hypothesis is that of Theorem IV.4.1: a member of `ℛ♭_k` with (A-IV.2) (`β_0 = β`, `ν_0 = ν`,
(I.2) up to `k`) and the torus coherence (D8) of both halves. The agreement conjunct of the
conclusion is Theorem IV.5.3 item 7, derived in the source from (D8) and the locality of the last
integral; the bounds use the ties of `PrefixInput`. -/
def LastIntegralInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk →
    7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
    ∃ (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ c₉ δ (k + 1) kf p ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ l1Ball _ →
        ∫ ψ, ρ nK ψ g = Complex.exp (E nK + ∑ x, ∑ i, g (x, i) * (h i : ℂ)
          + ∑ j ∈ Finset.Icc 1 (k + 1), ∑ X,
            p ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1)) j X
              (fun x i => g (x, i)))

/-- **A7 (the case `k_f = 0`, LF-8 (b); LFR Proposition IV.4.3, superseded by
`notes/phase1/LF-BASE-KF0.md`; no source treats this case).** For `β ≥ β₀`, `7/8 L⁻² < ν ≤ 1`, every
unit field `h` and `kf = k̂_f`: on every admissible torus `Z(g) = exp(E_ℓ + ⟨g, h⟩ + ∑_X p_1(X; g))`
on the unit `ℓ¹` ball, with scale-`1` activities in the observable form (`ObservableActivities` with
top scale `1`). This is the one-scale input `KF0OneScaleInput` of
`Correlations/KF0RootFPartial.lean` with the Root-F amplitude. -/
def KfZeroInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 7 / 8 < ν * ((T κ c₉).L : ℝ) ^ 2 → ν ≤ 1 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
    ∃ (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ c₉ δ 1 kf p ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], (T κ c₉).M * (T κ c₉).L ^ (kf + 1) ∣ ℓ →
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          partitionFunction d N ℓ β ν h g =
            Complex.exp (E ℓ + ∑ x, ∑ i, g x i * (h i : ℂ) + ∑ X, p ℓ 1 X g)

end Inputs

end Balaban.RootFSpine
