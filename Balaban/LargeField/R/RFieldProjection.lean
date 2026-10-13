/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Variants
public import Balaban.LargeField.R.RHistoryLabels
public import Balaban.LargeField.R.D7BoundTransport

/-!
# The pre-`R` and post-`R` class records: what is shared and what is left to prove

Package (1) of `notes/phase1/VMOD-37.md` §3.  **This file does not construct the operation `R` or
prove any of the seven changed fields in the physical case; it fixes, in Lean, what remains to be
proved (`OPEN-R-PRESERVES-ISREP2`).**

## T1.  The twelve fields (read off `Def7v2Variants.lean:42-67`, `Def7v2Class.lean:281-307`)

| field | in `IsRepPre2` | in `IsRep2` | reads |
| --- | --- | --- | --- |
| `coh` | `Coh … k F.sf` | same | `F.sf` (+ constants `S R k0 M cs P P6 C7 β ν`) |
| `field` | `FieldClauses … F.sf hv` | same | `F.sf` (+ `cs`, `hv`) |
| `corr` | `D1CorrLim m₀ F.sf St hv vc` | same | `F.sf`, `St`, `hv`, `vc` |
| `coherent` | `D8SF m₀ F.sf` | same | `F.sf` |
| `coeff` | `D9Coeff P6 k0 F.sf` | same | `F.sf`, `P6`, `k0` |
| `complete` | `IsComplete k k (F.lf nK).hist` | `IsComplete k (k+1) …` | `F.lf nK` (history set only) |
| `form` | `D1PreForm2 (F.ctx …) vc (F.lf nK) hv (ρ nK)` | `D1Form2 …` | `F.sf` (in `ctx`), `F.lf nK`, `ρ`, `vc`, `hv` |
| `sfData` | `D2SF2 P6 k0 F.sf (preFac (m₀+m₁))` | `D2SF2 P6 k0 F.sf (fun _ => 1)` | `F.sf`, `P6`, `k0` |
| `pin` | `D4Pin k (F.lf nK)` | `D4Pin (k+1) (F.lf nK)` | `F.lf nK` |
| `opBound` | `D5Bound k hkK (F.lf nK)` | `D5Bound (k+1) hkK (F.lf nK)` | `F.lf nK`, `cs` (in `rep`) |
| `budget` | `D6Pre (F.lf nK)` | `D6Budget (F.lf nK)` | `F.lf nK` (`Gpre`/`Gpost`, `bk`, `postBook`) |
| `bdry` | `D7Bdry2 … (Zpre k) … F.weights … C7.Bst (3/2 P6.κ)` | `D7Bdry2Post … ((step k).Z) … C7.B0 P6.κ` | `F.lf nK`, `F.weights` (= `F.sf.a k`), `cs`, `P6`, `C7` |

The component `F.ctx` is built from `F.sf` and constants only (`RepFam.ctx`), `F.weights` from
`F.sf.a k` only, and `F.lf nK` is the large-field part.  So five fields (`coh`, `field`, `corr`,
`coherent`, `coeff`) have literally the same type in both records and read `F.sf` (and `St`, `vc`,
`hv`, the constants); seven change.

## T2.  Copy lemmas

Formulation: two families `F F' : RepFam …` of the same type and the single hypothesis
`hsf : F'.sf = F.sf`.  The field types mention `F.sf` as an explicit argument of a predicate (no
dependent position), so the proofs are `hsf ▸ _`; no `HEq`, no `cast`.  The physical post family is
a structure update `{ F with lf := … }` for which `hsf` is `rfl`.

## T3.  The field `sfData`

`D2SF2 … (preFac m)` and `D2SF2 … (fun _ => 1)` differ only in the factor of the bound of the
remainder term at the index `m = m₀+m₁` (`1/2` before `R`, `1` after).  (i) For unchanged `sf` the
pre statement implies the post statement (`sfData_of_pre`, using `0 ≤ β_k`).  (ii) In the physical
case `R` adds a term `R''` to `sf.Rt` at the index `m` (P7 (3.28)-(3.29)) and nothing else
changes; `sfData_of_remainder_added` states the exact obligation (`OPEN-R-RM-H4`): the added term
satisfies `RTermsH4` with the factor `1/2` at `m` and `0` elsewhere, and then the updated data
satisfies `D2SF2 … (fun _ => 1)`.

## T4.  The assembly

`isRep2_of_isRepPre2_of_fields` builds `IsRep2` from `IsRepPre2` and the seven obligations
`hcomplete hform hsfData hpin hopBound hbudget hbdry`, each with exactly the type of the `IsRep2`
field.  Connections to the landed partial results (each obligation in its listed form):

* `complete` (OPEN-R-HISTORY-ENUM): `complete_succ_of_enum` is `RHistoryLabels.isComplete_succ_of_enum`
  with the pre field; the constructor of `F'` must supply, for each `A` of the pre set and each
  `f ∈ Realized k A`, exactly one `B ∈ (F'.lf nK).hist` with `B.Agree k k A`, `B.outcomeAt k = f`.
  `exists_enum` gives some set with this property, not the physical one.
* `pin` (OPEN-R-TOP-PIN): `pin_succ_iff` (`d4Pin_succ_iff`): `D4Pin (k+1)` is `D4Pin k` plus the
  scale-`k` pin `κ_k = κ^pre_k` at the kept non-removed components.
* `bdry` (OPEN-R-D7-PHYSICAL): `d7Post_bound_of_avoid_of_gas` gives only the `bound` field, from
  the pre record, the coefficient identity on labels avoiding `removedSet` and the gas bound on the
  others; the per-label transfers `real_of_avoid`, `analytic_of_avoid`, `loc_field_of_avoid`,
  `rot_of_avoid`, `post_support_of_avoid` give `real`, `analytic`, `loc_field`, `rot`, `support`
  label by label.  `loc_hist`, `euclid` and the new gas labels remain.  The seven fields of
  `D7Bdry2Post` therefore do not reduce to fewer top-level obligations; the list stays.
* `opBound`, `budget`, `form`, `sfData`: no landed transfer (`flow_counter` consumes `budget`,
  `smallFactor_ge` bounds exponents of the kept outcomes only).

## T5.  No removal

If `A.H.rem k = ∅` for every history of the family, with `F' = F`, `ρ' = ρ`: `coh field corr
coherent coeff` follow (copy), and `bdry` follows under `0 ≤ B_st ≤ B₀`, `0 ≤ κ`
(`d7Bdry2Post_of_pre_of_rem_empty`); see `isRep2_of_isRepPre2_of_no_removal` for the residual hypotheses.
`complete` does not follow: `IsComplete k (k+1)` quantifies over all labelled histories, including
those with a removed outcome at scale `k`, whatever the family says about `rem`.  `pin` needs the
scale-`k` label identity; `opBound` (`locOp` at `k` uses the kept data `keptOp` at ripe components,
`preOpTop` does not) and `form` (`postOp` and the index type `PostComp` against `preOpTop` and
`Comp`) differ even when `rem k = ∅`; `budget` needs the strict inequality `k < t*` of the post
book and `Gpost = Gpre` at the kept ripe components, which uses the kept exponents.

## T6.  Non-vacuity

`IsRepPre2` is inhabited: `Wit.nonempty_isRepPre2` (`Def7v2InhabitedFam.lean`), `Wit.wIsRepPre2`;
`IsRep2` by `Wit.nonempty_isRep2`, `Wit.wIsRep2`.  The two witnesses have the same small-field data
(`rfl`), and `Inhabited/RFieldProjectionWitness.lean` applies the assembly to them.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.LargeField.Def7 RegionHistory

section NoRemovalBdry

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁}
  {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
  {aw μs ε ε1 νs : ℕ → ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
  {rep : Rep S n R k0 K M N geo cs P k}

/-- Without removal the post region of a history is the raw region. -/
theorem step_Z_eq_Zpre_of_rem_empty (A : LabHist S n R k0 K) (h : A.H.rem k = ∅) :
    (A.H.step k).Z = A.H.F.Zpre k := by
  rw [A.H.Z_eq k, h]; simp

/-- **(T5, `bdry`) The pre record `D7Bdry2` gives the post record `D7Bdry2Post` when nothing is
removed at scale `k`**, for `0 ≤ B_st ≤ B₀` and `0 ≤ κ` (the rate `3κ/2` is at least `κ`). -/
theorem d7Bdry2Post_of_pre_of_rem_empty {κ Bst B0 : ℝ}
    (hin : D7Bdry2 Fr hnn hkK rep (fun A => A.H.F.Zpre k) aw μs ε ε1 νs Bst ((3 / 2) * κ) hv rH)
    (hκ : 0 ≤ κ) (hBst : 0 ≤ Bst) (hBB : Bst ≤ B0)
    (hrem : ∀ A ∈ rep.hist, A.H.rem k = ∅) :
    D7Bdry2Post Fr hnn hkK rep (fun A => (A.H.step k).Z) aw μs ε ε1 νs B0 κ hv rH := by
  have hmem : ∀ A ∈ rep.hist, ∀ X : Finset (Torus S.d (n k)),
      X ∈ bdryDomsPost Fr A k (A.H.step k).Z ↔ X ∈ bdryDomsPre Fr A k (A.H.F.Zpre k) :=
    fun A hA X => by
      rw [bdryDomsPost_eq_bdryDomsPre_of_rem_empty Fr _ (hrem A hA),
        step_Z_eq_Zpre_of_rem_empty A (hrem A hA)]
  exact
    { loc_field := fun A hA X hX => hin.loc_field A hA X ((hmem A hA X).1 hX)
      loc_hist := fun A hA A' hA' X hX hX' =>
        hin.loc_hist A hA A' hA' X ((hmem A hA X).1 hX) ((hmem A' hA' X).1 hX')
      real := fun A hA X hX => hin.real A hA X ((hmem A hA X).1 hX)
      analytic := fun A hA X hX => hin.analytic A hA X ((hmem A hA X).1 hX)
      bound := fun A hA X hX h' hh p hp => by
        rw [d7Size_eq_d7SizePre_of_rem_empty Fr X (hrem A hA)]
        refine (hin.bound A hA X ((hmem A hA X).1 hX) h' hh p hp).trans_le ?_
        have hs := d7SizePre_nonneg Fr A k X
        calc Bst * Real.exp (-(3 / 2 * κ) * d7SizePre Fr A k X)
            ≤ Bst * Real.exp (-κ * d7SizePre Fr A k X) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hBst
              nlinarith
          _ ≤ B0 * Real.exp (-κ * d7SizePre Fr A k X) :=
              mul_le_mul_of_nonneg_right hBB (Real.exp_pos _).le
      rot := fun A hA X hX => hin.rot A hA X ((hmem A hA X).1 hX)
      euclid := fun A hA A' hA' σ hσ hlab X hX =>
        hin.euclid A hA A' hA' σ hσ hlab X ((hmem A hA X).1 hX)
      support := fun A hA X hX hnv => by
        have hOm := A.H.omegaPost_eq_OmegaCube_of_rem_empty (hrem A hA)
        rw [hOm, step_Z_eq_Zpre_of_rem_empty A (hrem A hA)] at hX
        exact hin.support A hA X hX
          (fun hp => hnv ((fineValid_iff_fineValidPre_of_rem_empty Fr X (hrem A hA)).2 hp)) }

end NoRemovalBdry

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts}
  {P : BudgetConsts} {P6 : Def6.Consts} {C7 : Consts7} {β ν : ℝ}
  {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ} {k : ℕ} {ϱ : ℝ}
  {hM6 : M = S.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ K}
  {F F' : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ}
  {ρ ρ' : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ}
  {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N} {vc : CorrCoef S.d}

/-! ### T2: the five copy lemmas -/

section Copy

/-- `coh` is copied along `F'.sf = F.sf`. -/
theorem coh_of_sf_eq (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf) : Coh S R k0 M cs P P6 C7 β ν k F'.sf :=
  hsf ▸ hpre.coh

/-- `field` is copied along `F'.sf = F.sf`. -/
theorem field_of_sf_eq (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf) : FieldClauses S k0 k cs F'.sf hv :=
  hsf ▸ hpre.field

/-- `corr` is copied along `F'.sf = F.sf` (same `St`, `vc`, `hv`). -/
theorem corr_of_sf_eq (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf) : D1CorrLim P6.m₀ F'.sf St hv vc :=
  hsf ▸ hpre.corr

/-- `coherent` is copied along `F'.sf = F.sf`. -/
theorem coherent_of_sf_eq
    (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf) : D8SF P6.m₀ F'.sf :=
  hsf ▸ hpre.coherent

/-- `coeff` is copied along `F'.sf = F.sf`. -/
theorem coeff_of_sf_eq (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf) : D9Coeff P6 k0 F'.sf :=
  hsf ▸ hpre.coeff

end Copy

/-! ### T3: the small-field data -/

section SFData

variable {d L m₁ : ℕ} [NeZero L] {k N : ℕ} {ϱ : ℝ}

/-- `RTermsH4` is monotone in the factor, when `β_k ≥ 0` (the bound is
`fac n · β_k^{-n-1} e^{-κ size}`). -/
theorem rTermsH4_mono {P6 : Def6.Consts} {β ν a : ℕ → ℝ} {N₁ : ℕ} [NeZero N₁]
    {Rt : ℕ → Set (Localization.CTorus d L N₁ m₁ k) → Def6.Fld d L N₁ m₁ k N →
      Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ} {fac fac' : ℕ → ℝ}
    (hβ : 0 ≤ β k) (hfac : ∀ nn, fac nn ≤ fac' nn)
    (h : RTermsH4 (ϱ := ϱ) P6 β ν a N₁ Rt fac) : RTermsH4 (ϱ := ϱ) P6 β ν a N₁ Rt fac' where
  analytic := h.analytic
  loc := h.loc
  rot := h.rot
  euc := h.euc
  bound := fun nn hn1 hn2 X hX ψ hh g hψ hh' hg =>
    (h.bound nn hn1 hn2 X hX ψ hh g hψ hh' hg).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hfac nn) (pow_nonneg (inv_nonneg.2 hβ) _))
        (Real.exp_pos _).le)

/-- **(i) For unchanged `sf`, the pre statement implies the post statement** (the allowance `1/2`
at the index `m` is smaller than `1`; `0 ≤ β_k`). -/
theorem sfData_of_pre {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ} {m : ℕ}
    (hβ : 0 ≤ sf.β k) (h : D2SF2 P6 k0 sf (preFac m)) : D2SF2 P6 k0 sf (fun _ => 1) where
  sfClass := h.sfClass
  rTerms := fun N₁ _ =>
    rTermsH4_mono hβ (fun nn => by unfold preFac; split_ifs <;> norm_num) (h.rTerms N₁)

/-- The sum of two families of remainder terms satisfies `RTermsH4` with the sum of the factors. -/
theorem rTermsH4_add {P6 : Def6.Consts} {β ν a : ℕ → ℝ} {N₁ : ℕ} [NeZero N₁]
    {Rt Rt' : ℕ → Set (Localization.CTorus d L N₁ m₁ k) → Def6.Fld d L N₁ m₁ k N →
      Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ} {fac fac' : ℕ → ℝ}
    (h : RTermsH4 (ϱ := ϱ) P6 β ν a N₁ Rt fac) (h' : RTermsH4 (ϱ := ϱ) P6 β ν a N₁ Rt' fac') :
    RTermsH4 (ϱ := ϱ) P6 β ν a N₁ (fun nn X ψ hh g => Rt nn X ψ hh g + Rt' nn X ψ hh g)
      (fun nn => fac nn + fac' nn) where
  analytic := fun nn hn1 hn2 X hX => (h.analytic nn hn1 hn2 X hX).add (h'.analytic nn hn1 hn2 X hX)
  loc := fun nn X ψ ψ' hh hh' g g' hloc => by
    simp only [h.loc nn X ψ ψ' hh hh' g g' hloc, h'.loc nn X ψ ψ' hh hh' g g' hloc]
  rot := fun nn X Rm hR ψ hh g => by
    simp only [h.rot nn X Rm hR, h'.rot nn X Rm hR]
  euc := fun nn X r hr ψ hh g => by
    simp only [h.euc nn X r hr, h'.euc nn X r hr]
  bound := fun nn hn1 hn2 X hX ψ hh g hψ hh' hg => by
    refine (norm_add_le _ _).trans ?_
    have h1 := h.bound nn hn1 hn2 X hX ψ hh g hψ hh' hg
    have h2 := h'.bound nn hn1 hn2 X hX ψ hh g hψ hh' hg
    linarith

/-- **(ii) The physical case of `sfData`** (`OPEN-R-RM-H4`, P7 (3.28)-(3.29)).  The new small-field
data `sf'` differs from `sf` only by the remainder terms: `sf'.Rt N₁ nn X = sf.Rt N₁ nn X +
Rpp N₁ nn X`, where the added term `Rpp` (the term `R''` of P7) satisfies the bounds of P5 H4 with
the factor `1/2` at the index `m = m₀ + m₁` and `0` at every other index (the other half of the
allowance); the hypothesis `hRpp` is that statement.  Conclusion: the post statement `D2SF2 … 1`
for `sf'`. -/
theorem sfData_of_remainder_added {P6 : Def6.Consts} {k0 : ℕ} {sf sf' : SFData d L m₁ k N ϱ}
    (hpre : D2SF2 P6 k0 sf (preFac (P6.m₀ + m₁)))
    (hβ' : sf'.β = sf.β) (hν' : sf'.ν = sf.ν) (ha' : sf'.a = sf.a) (hE' : sf'.E = sf.E)
    (hTm' : sf'.Tm = sf.Tm)
    (Rpp : ∀ (N₁ : ℕ) [NeZero N₁], ℕ → Set (Localization.CTorus d L N₁ m₁ k) →
      Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → Def6.Fld d L N₁ m₁ k N → ℂ)
    (hRt' : ∀ (N₁ : ℕ) [NeZero N₁] nn X ψ hh g,
      sf'.Rt N₁ nn X ψ hh g = sf.Rt N₁ nn X ψ hh g + Rpp N₁ nn X ψ hh g)
    (hRpp : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (Rpp N₁)
      (fun nn => if nn = P6.m₀ + m₁ then 1 / 2 else 0)) :
    D2SF2 P6 k0 sf' (fun _ => 1) := by
  have hdom : sfDom P6 k0 sf' = sfDom P6 k0 sf := by
    unfold sfDom; rw [hν', ha']
  refine ⟨?_, fun N₁ _ => ?_⟩
  · obtain ⟨ρsf, hρ⟩ := hpre.sfClass
    refine ⟨ρsf, ?_⟩
    rw [hdom, hβ', hν', ha', hE', hTm']
    exact hρ
  · have hsum := rTermsH4_add (hpre.rTerms N₁) (hRpp N₁)
    have hfun : (fun nn => preFac (P6.m₀ + m₁) nn + (if nn = P6.m₀ + m₁ then (1 / 2 : ℝ) else 0)) =
        fun _ => 1 := by
      funext nn; unfold preFac; split_ifs <;> norm_num
    rw [hfun] at hsum
    have hRt'' : sf'.Rt N₁ = fun nn X ψ hh g => sf.Rt N₁ nn X ψ hh g + Rpp N₁ nn X ψ hh g := by
      funext nn X ψ hh g; exact hRt' N₁ nn X ψ hh g
    rw [hRt'', hβ', hν', ha']
    exact hsum

end SFData

/-! ### T4: the assembly -/

section Assembly

/-- **The assembly (`OPEN-R-PRESERVES-ISREP2` reduced to seven obligations).**  From a pre-`R`
record for `F, ρ`, a post family `F'` with the same small-field data (`F'.sf = F.sf`), and one
hypothesis for each of the seven changed fields, with exactly the type of the `IsRep2` field,
the post-`R` record for `F', ρ'`.  The five unchanged fields are transported
(`coh_of_sf_eq`, …, `coeff_of_sf_eq`).  This file does not construct the operation `R` or prove
any of the seven hypotheses in the physical case; it fixes, in Lean, what remains to be proved. -/
theorem isRep2_of_isRepPre2_of_fields
    (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf)
    (hcomplete : ∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (F'.lf nK).hist)
    (hform : ∀ (nK : ℕ) [NeZero nK], D1Form2 (F'.ctx hM6 hkK nK) vc (F'.lf nK) hv (ρ' nK))
    (hsfData : D2SF2 P6 k0 F'.sf (fun _ => 1))
    (hpin : ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F'.lf nK))
    (hopBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F'.lf nK))
    (hbudget : ∀ (nK : ℕ) [NeZero nK], D6Budget (F'.lf nK))
    (hbdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry2Post (fineFrame S (sides S.L K nK) K hM6)
      (sides_hnn S.L K nK) hkK (F'.lf nK)
      (fun A => (A.H.step k).Z) F'.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0
      P6.κ hv rH) :
    IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F' ρ' St vc where
  coh := coh_of_sf_eq hpre hsf
  field := field_of_sf_eq hpre hsf
  complete := hcomplete
  form := hform
  corr := corr_of_sf_eq hpre hsf
  sfData := hsfData
  pin := hpin
  opBound := hopBound
  budget := hbudget
  bdry := hbdry
  coherent := coherent_of_sf_eq hpre hsf
  coeff := coeff_of_sf_eq hpre hsf

/-- (a) `complete`: from the pre field and the enumeration of the outcomes
(`isComplete_succ_of_enum`).  The constructor of `F'` must supply, for each history `A` of the pre
set and each realized outcome assignment `f`, exactly one history of the post set that agrees
with `A` at `(k,k)` and has outcome `f` at scale `k`. -/
theorem complete_succ_of_enum
    (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc) (nK : ℕ)
    [NeZero nK]
    (henum : ∀ A ∈ (F.lf nK).hist, ∀ f ∈ Realized k A,
      ∃! B, B ∈ (F'.lf nK).hist ∧ B.Agree k k A ∧ B.outcomeAt k = f) :
    IsComplete k (k + 1) (F'.lf nK).hist :=
  isComplete_succ_of_enum (hpre.complete nK) henum

/-- (b) `pin`: `D4Pin (k+1)` is `D4Pin k` plus the scale-`k` pin (`d4Pin_succ_iff`). -/
theorem pin_succ_of_pin (nK : ℕ) [NeZero nK] (h0 : D4Pin k (F'.lf nK))
    (hk' : ∀ A ∈ (F'.lf nK).hist, ∀ Z : A.H.Comp k, IsKept A.H k Z → Z.1 ∉ A.H.rem k →
      (F'.lf nK).κK k (A.H.localHistory M K k Z) = (F'.lf nK).kappaPreH A k Z) :
    D4Pin (k + 1) (F'.lf nK) :=
  (d4Pin_succ_iff (F'.lf nK) k).2 ⟨h0, fun _ => hk'⟩

/-- **The assembly with the landed history and pin transports**: as
`isRep2_of_isRepPre2_of_fields`, with `hcomplete` replaced by the enumeration hypothesis (a) and
`hpin` by `D4Pin k` for the post histories and the scale-`k` pin (b). -/
theorem isRep2_of_isRepPre2_of_enum_of_pin
    (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hsf : F'.sf = F.sf)
    (henum : ∀ (nK : ℕ) [NeZero nK], ∀ A ∈ (F.lf nK).hist, ∀ f ∈ Realized k A,
      ∃! B, B ∈ (F'.lf nK).hist ∧ B.Agree k k A ∧ B.outcomeAt k = f)
    (hform : ∀ (nK : ℕ) [NeZero nK], D1Form2 (F'.ctx hM6 hkK nK) vc (F'.lf nK) hv (ρ' nK))
    (hsfData : D2SF2 P6 k0 F'.sf (fun _ => 1))
    (hpin0 : ∀ (nK : ℕ) [NeZero nK], D4Pin k (F'.lf nK))
    (hpink : ∀ (nK : ℕ) [NeZero nK], ∀ A ∈ (F'.lf nK).hist, ∀ Z : A.H.Comp k, IsKept A.H k Z →
      Z.1 ∉ A.H.rem k →
      (F'.lf nK).κK k (A.H.localHistory M K k Z) = (F'.lf nK).kappaPreH A k Z)
    (hopBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F'.lf nK))
    (hbudget : ∀ (nK : ℕ) [NeZero nK], D6Budget (F'.lf nK))
    (hbdry : ∀ (nK : ℕ) [NeZero nK], D7Bdry2Post (fineFrame S (sides S.L K nK) K hM6)
      (sides_hnn S.L K nK) hkK (F'.lf nK)
      (fun A => (A.H.step k).Z) F'.weights cs.mu (P6.eps S.d S.L) (epsOne S P6 C7) cs.nu C7.B0
      P6.κ hv rH) :
    IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F' ρ' St vc :=
  isRep2_of_isRepPre2_of_fields hpre hsf
    (fun nK _ => complete_succ_of_enum hpre nK (henum nK)) hform hsfData
    (fun nK _ => pin_succ_of_pin nK (hpin0 nK) (hpink nK)) hopBound hbudget hbdry

end Assembly

/-! ### T5: no removal -/

section NoRemoval

/-- **No removal** (`F' = F`, `ρ' = ρ`, `A.H.rem k = ∅` for every history).  `coh field corr
coherent coeff` are copied, `sfData` follows from the pre field (`sfData_of_pre`, `0 ≤ β_k`) and
`bdry` from the pre field (`d7Bdry2Post_of_pre_of_rem_empty`; `0 ≤ B_st ≤ B₀`, `0 ≤ κ`).  The
residual hypotheses are the five fields that do not follow (see the module doc): `complete`,
`form`, `pin`, `opBound`, `budget`. -/
theorem isRep2_of_isRepPre2_of_no_removal
    (hpre : IsRepPre2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hrem : ∀ (nK : ℕ) [NeZero nK], ∀ A ∈ (F.lf nK).hist, A.H.rem k = ∅)
    (hβ : 0 ≤ F.sf.β k) (hBst : 0 ≤ C7.Bst) (hBB : C7.Bst ≤ C7.B0) (hκ : 0 ≤ P6.κ)
    (hcomplete : ∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (F.lf nK).hist)
    (hform : ∀ (nK : ℕ) [NeZero nK], D1Form2 (F.ctx hM6 hkK nK) vc (F.lf nK) hv (ρ nK))
    (hpin : ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1) (F.lf nK))
    (hopBound : ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1) hkK (F.lf nK))
    (hbudget : ∀ (nK : ℕ) [NeZero nK], D6Budget (F.lf nK)) :
    IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc :=
  isRep2_of_isRepPre2_of_fields hpre rfl hcomplete hform (sfData_of_pre hβ hpre.sfData) hpin
    hopBound hbudget
    (fun nK _ => d7Bdry2Post_of_pre_of_rem_empty (hpre.bdry nK) hκ hBst hBB (hrem nK))

end NoRemoval

end Balaban.LargeField.Def7v2
