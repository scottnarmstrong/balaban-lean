/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RStep
public import Balaban.Spine.KeptHalfKernels

/-!
# `RKeptGasInput` from its named pieces (the final assembly of the step `R`)

`rKeptGasInput_of_parts` proves `RKeptGasInput` (LFR Lemma III.10.5, Definition III.10.6, Theorem
III.8.9, Theorem III.10.8; P7 (1.3)–(1.7), (3.1)–(3.29); ruling R4) from named open pieces, with the
outputs of `R` explicit:

* `lf₁ = outLF Ks rec`: `keptRep` on every torus with the kept data `KeptScaleData.ofKernels` of the
  kernels `Ks` of the five outcomes at the scale `k` (the class's kept costs `γ_i`, `rec.gamVal`);
* `ℬ' = B rec`, `ℛ'' = Rpp rec`: the boundary terms and the remainder of the output, P7 (3.26)–(3.29)
  (the old terms of the kept histories with the decorated removed gas of `gasR4Decor_eq` re-expanded
  onto the domains; their construction is the parameter `B`, `Rpp` of the assembly);
* `ρ' = outDens Ks B Rpp rec`: `R ρ` in its post-`R` form (LFR Theorem III.10.8 (b)), the sum over the
  histories of the output of the terms `postTerm2` (ruling R12: the terms of histories with a removal
  record are zero, the removed components are in `ℬ'`, `ℛ''`).

The pieces (each a named `Prop` over every vacuum-tied record at large `β`, `ForRecords`):
* (K3) `RKeptKernelsCoh Ks`: the datum coherence (D8) of the kept kernels at the scale `k`;
* (G1) `RRemH4 Rpp`: the bounds of (D2) of `ℛ''` with the allowance `1/2`;
* (G2) `RRemD8 Rpp`: the torus coherence `D8SF` of `ℛ''`;
* (G3) `RPostConv Ks B Rpp`: the absolute convergence of the post-`R` terms (the form (D1) of `ρ'`
  holds by the definition of `ρ'`);
* (G4) `RBdryPost Ks B Rpp`: (D7) of `ℬ'`, the post-`R` record;
* (F1) `RCoherent Ks B Rpp`: the torus coherence of the output family;
* (E1) `RIntegral Ks B Rpp`: `∫ ρ' = ∫ ρ` (P7 (1.7)).

The kept half (`D4Pin`, `D5Bound`, `D6Budget`, completeness, the step data of the input, the kept
costs) is proved from `Ks` and (K3) (`keptOutput_of_kernels`, `keptLF_gamConst`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

section Parts

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- A property of the records of `ℛ^pre_k` (with all their parameters). -/
abbrev RecProp :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk → Prop

/-- **`Q` holds for every vacuum-tied record at every `β` above a threshold**: the quantifier prefix
of `RKeptGasInput` (`1 ≤ k ≤ k₀`, `‖h‖ = 1`, the horizon, the masses). -/
def ForRecords (Q : RecProp d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
  ∀ rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk,
  VacuumTied rec → Q κ c₉ β ν h kf k ρ νk rec

variable {d N T P6 C7 PB cs₀ M1 c rH ϱ}

/-- Two properties of the records at large `β` hold together (the larger threshold). -/
theorem ForRecords.and {Q₁ Q₂ : RecProp d N T P6 C7 PB cs₀ M1 c rH ϱ}
    (h₁ : ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ Q₁)
    (h₂ : ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ Q₂) :
    ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ
      (fun κ c₉ β ν h kf _ _ k ρ νk rec => Q₁ κ c₉ β ν h kf k ρ νk rec ∧
        Q₂ κ c₉ β ν h kf k ρ νk rec) := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₁, hb₁⟩ := h₁ κ hκ c₉ hc₉
  obtain ⟨b₂, hb₂⟩ := h₂ κ hκ c₉ hc₉
  refine ⟨max b₁ b₂, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hvac => ⟨?_, ?_⟩⟩
  · exact hb₁ β (le_of_max_le_left hβ) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hvac
  · exact hb₂ β (le_of_max_le_right hβ) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hvac

variable (d N T P6 C7 PB cs₀ M1 c rH ϱ)

/-- The kept kernels of the five outcomes at the scale `k`, for every record and torus (the
construction of the piece (K3): LFR Lemma III.5.3, Definition III.8.8). -/
abbrev KeptKernelsFam :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk) (nK : ℕ) [NeZero nK],
    KeptScaleKernels (rec.F.lf nK)

/-- The boundary terms `ℬ'` of the output, for every record and torus (P7 (3.26)–(3.27)). -/
abbrev BdryFam :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk) (nK : ℕ) [NeZero nK],
    BTerms 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
      (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N k

/-- The remainder `ℛ''` of the output, for every record (P7 (3.28)–(3.29)). -/
abbrev RemFam :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (_rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk),
    RemTerm d (T κ c₉).L (C7 κ c₉).m₁ k N

variable {d N T P6 C7 PB cs₀ M1 c rH ϱ}

section Out

variable (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
  (B : BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
  {κ c₉ β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf : ℕ} [NeZero (T κ c₉).L]
  [NeZero (T κ c₉).M] {k : ℕ} {ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]} {νk : ℝ}
  (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
    (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk)

/-- **The kept large-field part `lf₁` of the output of `R`**: `keptRep` with the kept data of the
kernels `Ks` (the kept costs `γ_i = log 5 + A'₃ λ̂_i^{p_R}` of the class, `rec.gamVal`). -/
noncomputable abbrev outLF :
    ∀ (nK : ℕ) [NeZero nK], Rep 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
      (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N
      (rec.geo nK) rec.cs rec.P k :=
  keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec
    (fun nK _ => KeptScaleData.ofKernels (rec.F.lf nK) (fun i _ l => rec.gamVal nK i l)
      (Ks κ c₉ β ν h kf k ρ νk rec nK))

/-- **The output family of `R`**: the small-field data `sf + ℛ''`, the kept part `lf₁`, the
boundary terms `ℬ'`. -/
noncomputable abbrev outFam :=
  repFamPost rec.F (outLF Ks rec) (B κ c₉ β ν h kf k ρ νk rec) (Rpp κ c₉ β ν h kf k ρ νk rec)

/-- **`ρ' = R ρ` in its post-`R` form** (LFR Theorem III.10.8 (b); ruling R12): the sum over the
histories of the output of the terms `postTerm2`. -/
noncomputable def outDens : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k] :=
  fun nK _ ψk g => ∑ A ∈ ((outFam Ks B Rpp rec).lf nK).hist,
    postTerm2 ((outFam Ks B Rpp rec).ctx rec.hM6 rec.hkK nK) rec.vc ((outFam Ks B Rpp rec).lf nK)
      A ψk h g

end Out

/-! ### The pieces -/

/-- **(K3) OPEN: the datum coherence of the kept kernels** (LFR Definition II.6.2 (D8), D-IV.9;
Lemma III.5.3, Definition III.8.8).  On corresponding localized histories of two tori the kept
kernels `Ks` at the scale `k` agree.  Owner A4 (after R28 and the labelled locality of `K^pre`);
the bound (1.26) of the physical kernels (a field of `KeptScaleKernels`) is W1155's window export. -/
def RKeptKernelsCoh (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun κ c₉ β ν h kf _ _ k ρ νk rec =>
    KeptDatumCohAt (K := kf + 1) (M := (T κ c₉).M) (R := rec.R) (k0 := kZero d (T κ c₉).L β ν)
      k (fun nK _ a ϰ => (Ks κ c₉ β ν h kf k ρ νk rec nK).datum a ϰ)

/-- **(G1) OPEN: the bounds of (D2) of `ℛ''`** with the allowance `1/2` at the index `m₀ + m₁`
(OPEN-R-RM-H4; P7 (3.26)–(3.29)).  Owner A4. -/
def RRemH4 (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun κ c₉ β ν h kf _ _ k ρ νk rec =>
    ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ κ c₉) (P6 κ c₉) rec.F.sf.β rec.F.sf.ν rec.F.sf.a N₁
      (Rpp κ c₉ β ν h kf k ρ νk rec N₁)
      (fun nn => if nn = (P6 κ c₉).m₀ + (C7 κ c₉).m₁ then 1 / 2 else 0)

/-- **(G2) OPEN: the torus coherence `D8SF` of `ℛ''`** (LFR D-IV.9; row (f)).  Owner A2 (the local
isomorphisms) with A4. -/
def RRemD8 (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) : Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun κ c₉ β ν h kf _ _ k ρ νk rec =>
    D8SF (P6 κ c₉).m₀ (sfWithRem rec.F.sf (Rpp κ c₉ β ν h kf k ρ νk rec))

/-- **(G3) OPEN: the post-`R` terms converge absolutely** (the form (D1) of `ρ'`; LFR Theorem
III.10.8 (b), the gas of removed clusters with the decorated couplings, `gasR4Decor_eq`).  Owner A4
(uses `rBPrime_aggregate`, the tie `r4Coupling = Rep.B`, `hcut`, the vacuum identity). -/
def RPostConv (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B : BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun κ c₉ β _ h kf _ _ k _ _ rec =>
    ∀ (nK : ℕ) [NeZero nK] (ψk : BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M (kf + 1) k → EuclideanSpace ℝ (Fin N))
      (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
        (kf + 1) N → ℂ), g ∈ l1Ball _ →
      ∀ A ∈ ((outFam Ks B Rpp rec).lf nK).hist,
        PostConv2 ((outFam Ks B Rpp rec).ctx rec.hM6 rec.hkK nK) rec.vc
          ((outFam Ks B Rpp rec).lf nK) A ψk h g

/-- **(G4) OPEN: (D7) of `ℬ'`, the post-`R` record** (OPEN-R-D7-PHYSICAL;
`d7Post_bound_of_avoid_of_gas` with the gas activity bound).  Owner A4. -/
def RBdryPost (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B : BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun κ c₉ β _ h kf _ _ k _ _ rec =>
    ∀ (nK : ℕ) [NeZero nK], D7Bdry2Post (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) (kf + 1) rec.hM6) (sides_hnn (T κ c₉).L (kf + 1) nK)
      rec.hkK ((outFam Ks B Rpp rec).lf nK) (fun A => (A.H.step k).Z)
      (outFam Ks B Rpp rec).weights rec.cs.mu ((P6 κ c₉).eps d (T κ c₉).L)
      (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉)) rec.cs.nu (C7 κ c₉).B0
      (P6 κ c₉).κ h (rH κ c₉)

/-- **(F1) OPEN: the torus coherence of the output family** (LFR D-IV.9, row (f): two-torus
agreement of `ℬ'` and `ℛ''` on corresponding local data).  Owner A2 (the local isomorphisms). -/
def RCoherent (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B : BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun _ _ _ _ _ _ _ _ _ _ _ rec =>
    LFCoherent (outFam Ks B Rpp rec)

/-- **(E1) OPEN: `R` preserves the integral** (P7 (1.7), row (e)): `∫ ρ' = ∫ ρ` on every torus and
every source of the unit `ℓ¹` ball, for `ρ'` the post-`R` form.  Owner A4 (the normalizations of
`R`, the kept outcomes, the gas identity). -/
def RIntegral (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (B : BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    Prop :=
  ForRecords d N T P6 C7 PB cs₀ M1 c rH ϱ fun κ c₉ β _ _ kf _ _ _ ρ _ rec =>
    ∀ (nK : ℕ) [NeZero nK] (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M (kf + 1) N → ℂ), g ∈ l1Ball _ →
      ∫ ψ, outDens Ks B Rpp rec nK ψ g = ∫ ψ, ρ nK ψ g

/-! ### The assembly -/

/-- **`RKeptGasInput` from its named pieces** (L0).  The outputs are `lf₁ = outLF Ks rec`,
`ℬ' = B rec`, `ℛ'' = Rpp rec`, `ρ' = outDens Ks B Rpp rec`.  The kept half is
`keptOutput_of_kernels` (from (K3)) and `keptLF_gamConst`; the gas half is (G1), (G2), (G3) with the
definition of `ρ'`, (G4), (F1), (E1). -/
theorem rKeptGasInput_of_parts {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (Ks : KeptKernelsFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (B : BdryFam d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (Rpp : RemFam d N T P6 C7 PB cs₀ M1 c rH ϱ) (hK3 : RKeptKernelsCoh Ks) (hG1 : RRemH4 Rpp)
    (hG2 : RRemD8 Rpp) (hG3 : RPostConv Ks B Rpp) (hG4 : RBdryPost Ks B Rpp)
    (hF1 : RCoherent Ks B Rpp) (hE1 : RIntegral Ks B Rpp) :
    RKeptGasInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₀, hb₀⟩ := keptOutput_of_kernels (N := N) (rH := rH) hP hκ hc₉
  have hall := (((((hK3.and hG1).and hG2).and hG3).and hG4).and hF1).and hE1
  obtain ⟨b₁, hb₁⟩ := hall κ hκ c₉ hc₉
  refine ⟨max b₀ b₁, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk rec hvac => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hk3, hg1⟩, hg2⟩, hg3⟩, hg4⟩, hf1⟩, he1⟩ :=
    hb₁ β (le_of_max_le_right hβ) ν hν hνL h hh kf hkf k hk1 hk ρ νk rec hvac
  obtain ⟨hlf, hkept⟩ := hb₀ β (le_of_max_le_left hβ) ν h kf k hk1 hk ρ νk rec
    (fun nK _ => Ks κ c₉ β ν h kf k ρ νk rec nK) hk3
  refine ⟨outLF Ks rec, B κ c₉ β ν h kf k ρ νk rec, Rpp κ c₉ β ν h kf k ρ νk rec,
    outDens Ks B Rpp rec, hlf, hkept, ⟨hg1, hg2, ?_, hg4, hf1, he1⟩, ?_⟩
  · exact fun nK _ ψk g hg => ⟨hg3 nK ψk g hg, rfl⟩
  · exact fun nK _ => keptLF_gamConst rec _ nK

end Parts

end Balaban.RootFSpine
