/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FrozenSFStep
public import Balaban.Spine.LFStep

/-!
# The large-field half of the frozen step from its parts (A4f-1, part 4)

`frozenLFStepInput_of_parts` proves `FrozenLFStepInput` (`Spine/FrozenSFStep.lean`) from the frozen
step map `Λ♭` (`FrozenLFStepMap`, the large-field data created by a frozen step: histories, kernels,
boundary terms, the vacuum normalization `s`) and eight parts, following `lfStepInput_of_parts`
(`Spine/LFStep.lean`) with `IsRepFlat2` in place of `IsRepPre2`: completeness of the histories
(`FrozenHistInput`), the step data (`FrozenStepDataInput`), the boundary terms in the post-`R` record
(`FrozenBdryInput`: no hull and no operation `R`, so (D7) is the record `D7Bdry2Post` with
`B_st ≤ B_0 - 1`), the form (D1) (`FrozenFormInput`, `D1Form2`), the operator bound
(`FrozenOpBoundInput`), the pins (`FrozenPinInput`), the torus coherence (`FrozenCoherenceInput'`)
and the coefficient data (`FrozenCorrInput`). The constants of the successor and the kept data are
those of `LFStep` (`succOpConsts`, `succBudgetConsts`, `KeptData.upTo`), the clauses `Coh` and
`FieldClauses` are `coh_succ`, `field_succ`, the budget is proved (`frozenBudget_of_pin`).
There are no removals in a frozen step, so the audit of the removal histories (`notes/phase1/REMOVAL-HIST.md`) does not
touch these parts.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation
  Balaban.Localization Balaban.Background Balaban.Multiscale

namespace Balaban.RootFSpine

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **The large-field step map of the frozen steps** (a parameter of the sub-spine, defined by the
provider): for every record of `ℛ♭_k` the large-field data of the successor at the scale `k + 1`
on the tori of its family (LF-5; no hull, no `R`). -/
abbrev FrozenLFStepMap :=
  ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
    [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
    (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (hkK : k ≤ kf + 1)
    (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
      (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
      (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ k N) (vc : CorrCoef d),
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    LFStepRaw 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
      (T κ c₉).M N (k + 1)

/-- **The successor families of a frozen step**: `Q` holds for the family with the small-field data
`sf'` and, on every torus, the histories, kernels and boundary terms of `D`, the kept data of `F`
restricted to the scales `≤ k` at the constants of the successor (`KeptData.upTo`, (S3)), the
exponents of `F`, and any step data at the constants of the successor that carry the kernels of
`D`. -/
def FrozenSuccFams {d N : ℕ} {T : Typing} {C7 : Consts7} {cs₀ : OpConsts} {β ν ϱ : ℝ}
    {kf k : ℕ} [NeZero T.M] [NeZero T.L] (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (sf' : SFData d T.L C7.m₁ (k + 1) N ϱ)
    (D : LFStepRaw 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N (k + 1))
    (Q : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo
      (succOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 cs k sf')
      (succBudgetConsts (S := 𝒮[d, T, β, cs₀.aKer]) P k sf') (k + 1) C7.m₁ ϱ → Prop) : Prop :=
  ∀ SD : ∀ (nK : ℕ) [NeZero nK], StepData (kZero d T.L β ν) (geo nK)
      (succOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 cs k sf') N
      (kappaStepLoc (K := kf + 1) 𝒮[d, T, β, cs₀.aKer]
        (succBudgetConsts (S := 𝒮[d, T, β, cs₀.aKer]) P k sf') T.M),
    D.Matches SD → Q (D.fam sf' (fun nK _ => (F.lf nK).κK) SD fun nK _ =>
      (F.lf nK).KD.upTo k (succOpConsts 𝒮[d, T, β, cs₀.aKer] (kZero d T.L β ν) C7.A0 cs k sf')
        (fun _ hi => vacExt_of_le _ hi) (fun _ hi => vacExt_of_le _ hi) rfl)

end Inputs

section Parts

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)
  (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))

/-- **The form of the parts of the frozen large-field half**: a property `Q` of every record of
`ℛ♭_k`, `max(k₀, 1) ≤ k < k̂_f`, with `ν_k L² ≤ 7/8`, for `β ≥ β₀(κ, c₉)`, every unit field and the
horizon `kf`, whose small-field image `Φ♭ F.sf` satisfies the hypotheses of `FrozenLFStepInput`. -/
def FrozenLFImageInput
    (Q : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (hkK : k ≤ kf + 1)
      (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
      (cs : OpConsts) (P : BudgetConsts)
      (F : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
      (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ k N)
      (vc : CorrCoef d),
      FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk → k + 1 ≤ kf + 1 → Prop) :
    Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → kZero d (T κ c₉).L β ν ≤ k → k < kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc
    (hF : FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk),
    νk * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
    SFFlat2 (P6 κ c₉) (kZero d (T κ c₉).L β ν) (Φ κ c₉ β ν k F.sf) →
    D8SF (P6 κ c₉).m₀ (Φ κ c₉ β ν k F.sf) → D9Flat (P6 κ c₉) (Φ κ c₉ β ν k F.sf) →
    (∀ j, 1 ≤ j → j ≤ k + 1 →
      (Φ κ c₉ β ν k F.sf).a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j) →
    (∀ j, j ≤ k → (Φ κ c₉ β ν k F.sf).β j = F.sf.β j ∧ (Φ κ c₉ β ν k F.sf).ν j = F.sf.ν j ∧
      (Φ κ c₉ β ν k F.sf).z j = F.sf.z j) →
    ∀ hkK' : k + 1 ≤ kf + 1, Q κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF hkK'

variable (Λ : FrozenLFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)

/-- **The histories of the frozen successor (LF-5; (R8)).** On every torus the histories of the map
are a complete set of the histories up to the scale `k + 1` with the `R`-records up to `k + 1` (the
record at `k + 1` is empty: a frozen step has no operation `R`), `IsComplete (k + 1) (k + 2)`. -/
def FrozenHistInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF _ =>
    ∀ (nK : ℕ) [NeZero nK], IsComplete (k + 1) (k + 1 + 1)
      ((Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF).hist nK)

/-- **The step data of the frozen successor (LF-5; P5 (2.47)·P6 (3.2) at the complete backgrounds).**
On every torus there are step data (S0)–(S2) at the constants of the successor whose kernels are
those of the map. -/
def FrozenStepDataInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF _ =>
    ∀ (nK : ℕ) [NeZero nK], ∃ SD : StepData (kZero d (T κ c₉).L β ν) (geo nK)
        (succOpConsts 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (kZero d (T κ c₉).L β ν) (C7 κ c₉).A0 cs k
          (Φ κ c₉ β ν k F.sf)) N
        (kappaStepLoc (K := kf + 1) 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (succBudgetConsts (S := 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]) P k (Φ κ c₉ β ν k F.sf))
          (T κ c₉).M),
      SD.ker = (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF).ker nK

/-- **The boundary terms of the frozen successor (LF-5; LFR Lemma IV.1.5, P6 §4 at the complete
backgrounds; `B_st ≤ B_0 - 1`).** On every torus the boundary terms `ℬ^{(k+1)}` of the map satisfy
(D7) of the post-`R` record `D7Bdry2Post` (there is no hull and no `R`): locality, reality,
analyticity, the bound `B_0 e^{-κ d^cov}` on the H7 domain, covariance, support, including the
terms across the holes of the successor. -/
def FrozenBdryInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF hkK' =>
    FrozenSuccFams R geo cs P F (Φ κ c₉ β ν k F.sf)
      (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D7Bdry2Post (fineFrame 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (sides (T κ c₉).L (kf + 1) nK) (kf + 1) hM6) (sides_hnn (T κ c₉).L (kf + 1) nK)
        hkK' (F'.lf nK) (fun A => (A.H.step (k + 1)).Z) F'.weights
        (succOpConsts 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (kZero d (T κ c₉).L β ν) (C7 κ c₉).A0 cs k
          (Φ κ c₉ β ν k F.sf)).mu ((P6 κ c₉).eps d (T κ c₉).L)
        (epsOne 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (P6 κ c₉) (C7 κ c₉))
        (succOpConsts 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (kZero d (T κ c₉).L β ν) (C7 κ c₉).A0 cs k
          (Φ κ c₉ β ν k F.sf)).nu (C7 κ c₉).B0 (P6 κ c₉).κ h (rH κ c₉)

/-- **The form of the frozen successor (LF-5; (D1) at the complete backgrounds; P5 (2.1)–(2.14),
(2.42)–(2.48), §3 (Propositions 3.1–3.4, (3.18)), P6 §2).** On every torus the step density
`ρ' = e^{-s|T^{(k+1)}_1|} z^{N|T^{(k+1)}|}(T^{(k)}ρ)(z·)` is the sum over the histories of the map of the
terms of the successor (`D1Form2`), for the coefficient data `vc'` defined by the limits `D1CorrLim`
of the image. -/
def FrozenFormInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF hkK' =>
    FrozenSuccFams R geo cs P F (Φ κ c₉ β ν k F.sf)
      (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF) fun F' =>
      ∀ (St' : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ (k + 1) N)
        (vc' : CorrCoef d), D1CorrLim (P6 κ c₉).m₀ (Φ κ c₉ β ν k F.sf) St' h vc' →
      ∀ (nK : ℕ) [NeZero nK], D1Form2 (F'.ctx hM6 hkK' nK) vc' (F'.lf nK) h
        (stepDensity d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k
          (F.sf.β k * (cs₀ κ c₉).aKer * ((T κ c₉).L : ℝ) ^ (d - 2))
          ((Φ κ c₉ β ν k F.sf).z (k + 1))
          (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF).s ρ nK)

/-- **The operator bound of the frozen successor ((D5))** at every scale `≤ k + 1`. -/
def FrozenOpBoundInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF hkK' =>
    FrozenSuccFams R geo cs P F (Φ κ c₉ β ν k F.sf)
      (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D5Bound (k + 1 + 1) hkK' (F'.lf nK)

/-- **The pinned exponents of the frozen successor ((D4))**: `D4Pin (k + 1 + 1)`. -/
def FrozenPinInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF _ =>
    FrozenSuccFams R geo cs P F (Φ κ c₉ β ν k F.sf)
      (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF) fun F' =>
      ∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1 + 1) (F'.lf nK)

/-- **The torus coherence of the frozen successor ((D8), LF-3 (h) at the complete backgrounds).** -/
def FrozenLFCoherenceInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h kf _ _ k ρ νk hM6 hkK R geo cs P F St vc hF _ =>
    FrozenSuccFams R geo cs P F (Φ κ c₉ β ν k F.sf)
      (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF) fun F' => LFCoherent F'

/-- **The coefficient data of the image (P1 (3.106)–(3.110), P5 (1.8))**: the source-form terms
`St'` and the limits `vc'` (`D1CorrLim`). -/
def FrozenCorrInput : Prop :=
  FrozenLFImageInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ
    fun κ c₉ β ν h _ _ _ k _ _ _ _ _ _ _ _ F _ _ _ _ =>
    ∃ (St' : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ (k + 1) N)
      (vc' : CorrCoef d), D1CorrLim (P6 κ c₉).m₀ (Φ κ c₉ β ν k F.sf) St' h vc'

end Parts

section Assembly

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}
  {Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)}

/-- **The large-field half of the frozen step from its parts** (LFR Theorem IV.2.2 (b)–(f)). For a
record of `ℛ♭_k` and its image `Φ♭ F.sf`: the step data on every torus are chosen by
`FrozenStepDataInput` (their kernels are those of the map `Λ♭`); the kept data are those of `F`
(`KeptData.upTo`, (S3)); the constants are `succOpConsts`, `succBudgetConsts`, whose ties to the outer
constants are those of the input and whose `Coh`, `FieldClauses` at `k + 1` are `coh_succ`,
`field_succ`; `IsRepFlat2` is assembled clause by clause from the hypotheses on the image and the
parts, with (H6♭) as the premise that `frozenSFStepInput_of_parts` discharges
(`frozenBudget_of_pin`). The threshold is the largest of the eight thresholds. -/
theorem frozenLFStepInput_of_parts (Λ : FrozenLFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hH : FrozenHistInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hS : FrozenStepDataInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hB : FrozenBdryInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hF : FrozenFormInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hO : FrozenOpBoundInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hP : FrozenPinInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hC : FrozenLFCoherenceInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ)
    (hc : FrozenCorrInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ) :
    FrozenLFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ := by
  intro κ hκ c₉ hc₉
  obtain ⟨b₁, h₁⟩ := hH κ hκ c₉ hc₉
  obtain ⟨b₂, h₂⟩ := hS κ hκ c₉ hc₉
  obtain ⟨b₄, h₄⟩ := hB κ hκ c₉ hc₉
  obtain ⟨b₆, h₆⟩ := hF κ hκ c₉ hc₉
  obtain ⟨b₇, h₇⟩ := hO κ hκ c₉ hc₉
  obtain ⟨b₈, h₈⟩ := hP κ hκ c₉ hc₉
  obtain ⟨b₁₀, h₁₀⟩ := hC κ hκ c₉ hc₉
  obtain ⟨b₁₁, h₁₁⟩ := hc κ hκ c₉ hc₉
  refine ⟨max (max (max b₁ b₂) (max b₄ b₆)) (max (max b₇ b₈) (max b₁₀ b₁₁)), ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep hνkL hD2
    hD8 hD9 hafree hcst hkK'
  simp only [max_le_iff] at hβ
  obtain ⟨⟨⟨hb₁, hb₂⟩, hb₄, hb₆⟩, ⟨hb₇, hb₈⟩, hb₁₀, hb₁₁⟩ := hβ
  choose SD hSDker using
    h₂ β hb₂ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep hνkL hD2 hD8
      hD9 hafree hcst hkK'
  have hM : (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hrep).Matches SD :=
    fun nK _ => hSDker nK
  obtain ⟨St', vc', hcorr⟩ :=
    h₁₁ β hb₁₁ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep hνkL hD2 hD8
      hD9 hafree hcst hkK'
  have hrep' := hrep
  have hrepc := hrep
  obtain ⟨-, o1, o2, o3, o4, o5, o6, o7, hrepF, -⟩ := hrepc
  refine ⟨succOpConsts 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (kZero d (T κ c₉).L β ν) (C7 κ c₉).A0 cs
      k (Φ κ c₉ β ν k F.sf),
    succBudgetConsts (S := 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]) P k (Φ κ c₉ β ν k F.sf),
    fun nK _ => (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hrep').rep nK (F.lf nK).κK
      (SD nK) ((F.lf nK).KD.upTo k
        (succOpConsts 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (kZero d (T κ c₉).L β ν) (C7 κ c₉).A0 cs
          k (Φ κ c₉ β ν k F.sf)) (fun _ hi => vacExt_of_le _ hi) (fun _ hi => vacExt_of_le _ hi)
        rfl),
    St', vc', (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hrep').s,
    o1, o2, o3, o4, o5, o6, o7,
    h₈ β hb₈ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep' hνkL hD2 hD8
      hD9 hafree hcst hkK' SD hM,
    coh_succ hrepF.coh (fun j hj => (hcst j hj).1) (fun j hj => (hcst j hj).2.1)
      (fun j hj => (hcst j hj).2.2) fun j hj1 hj => (hafree j hj1 hj).trans (by rw [o1]),
    fun hbud => ?_,
    h₁₀ β hb₁₀ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep' hνkL hD2
      hD8 hD9 hafree hcst hkK' SD hM⟩
  exact
    { range := hk0.trans (Nat.le_succ k)
      coh := coh_succ hrepF.coh (fun j hj => (hcst j hj).1) (fun j hj => (hcst j hj).2.1)
        (fun j hj => (hcst j hj).2.2) fun j hj1 hj => (hafree j hj1 hj).trans (by rw [o1])
      field := field_succ hrepF.field fun j hj => (hcst j hj).2.1
      complete := h₁ β hb₁ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep'
        hνkL hD2 hD8 hD9 hafree hcst hkK'
      form := h₆ β hb₆ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep'
        hνkL hD2 hD8 hD9 hafree hcst hkK' SD hM St' vc' hcorr
      corr := hcorr
      sfData := hD2
      pin := h₈ β hb₈ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep'
        hνkL hD2 hD8 hD9 hafree hcst hkK' SD hM
      opBound := h₇ β hb₇ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep'
        hνkL hD2 hD8 hD9 hafree hcst hkK' SD hM
      budget := hbud
      bdry := h₄ β hb₄ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep'
        hνkL hD2 hD8 hD9 hafree hcst hkK' SD hM
      coherent := hD8
      coeff := hD9 }

end Assembly

end Balaban.RootFSpine
