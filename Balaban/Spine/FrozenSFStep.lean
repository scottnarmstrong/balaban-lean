/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FrozenSFImage
public import Balaban.Spine.FrozenSFBudget
public import Balaban.Spine.StepDensity

/-!
# The frozen small-field step from a sub-spine (A4f-1)

`frozenSFStepInput_of_parts` proves `FrozenSFStepInput` (LF-5, LFR Theorem IV.2.2 (a)–(f)) from the
frozen small-field sub-inputs of `Spine/FrozenSFImage.lean` (A4-1a–f, i at the complete backgrounds)
and the large-field half `FrozenLFStepInput`, as `sfStepInput_of_parts` does for the pre-`R` steps.

The large-field half is stated without the budget: the successor's large-field data are asked to
satisfy the pins of the pre-`R` exponents (`D4Pin`), the coherence `Coh` of the constants and the
representation `IsRepFlat2` **given** (H6♭); (H6♭) itself is proved here (`frozenBudget_of_pin`,
LF-2 (ii) truncated at `k + 1`), so the sub-input never asks for it.
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

/-- **The large-field half of the frozen step (LF-5; LFR Theorem IV.2.2 (a)–(f); P5 §§2–3, P6 §§2–3 at
the complete backgrounds; no hull, no operation `R`).** For `max(k₀, 1) ≤ k < k̂_f`, a record
`FlatRep` of `ℛ♭_k` with `ν_k L² ≤ 7/8` whose small-field image `Φ♭ F.sf` satisfies the small-field
clauses of `ℛ♭_{k+1}` ((D2♭), (D8), (D9♭), the free flow of `a_j` up to `k + 1`) and keeps the running
constants at the scales `j ≤ k`: on the tori of the family there are operator and budget constants
`cs', P'` (with the outer constants of the prefix), large-field data `lf'` at `k + 1`, coefficient
data `St', vc'` and a vacuum normalization `s` such that the pins of `lf'` are those of the pre-`R`
exponents (`D4Pin (k + 2)`), the constants are coherent (`Coh`), the family `⟨Φ♭ F.sf, lf'⟩` is torus
coherent, and, if (H6♭) holds for `lf'` (it is proved from the pins, `frozenBudget_of_pin`), the
family represents the step density in `ℛ♭_{k+1}` (`IsRepFlat2`: the histories of `ρ` followed by every
step record, with no hull and no `R`; the step data of P5 (2.47)·P6 (3.2); boundary terms with
`B_st ≤ B₀ - 1`). -/
def FrozenLFStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → kZero d (T κ c₉).L β ν ≤ k → k < kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    νk * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
    SFFlat2 (P6 κ c₉) (kZero d (T κ c₉).L β ν) (Φ κ c₉ β ν k F.sf) →
    D8SF (P6 κ c₉).m₀ (Φ κ c₉ β ν k F.sf) → D9Flat (P6 κ c₉) (Φ κ c₉ β ν k F.sf) →
    (∀ j, 1 ≤ j → j ≤ k + 1 →
      (Φ κ c₉ β ν k F.sf).a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j) →
    (∀ j, j ≤ k → (Φ κ c₉ β ν k F.sf).β j = F.sf.β j ∧ (Φ κ c₉ β ν k F.sf).ν j = F.sf.ν j ∧
      (Φ κ c₉ β ν k F.sf).z j = F.sf.z j) →
    ∀ hkK' : k + 1 ≤ kf + 1,
    ∃ (cs' : OpConsts) (P' : BudgetConsts)
      (lf' : ∀ (nK : ℕ) [NeZero nK], Rep 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N
        (geo nK) cs' P' (k + 1))
      (St' : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ (k + 1) N)
      (vc' : CorrCoef d) (s : ℝ),
      cs'.aKer = (cs₀ κ c₉).aKer ∧ cs'.Cpsi = (cs₀ κ c₉).Cpsi ∧ cs'.Cb = (cs₀ κ c₉).Cb ∧
      cs'.aw = (cs₀ κ c₉).aw ∧ P'.c1 = (PB κ c₉).c1 ∧ P'.c2 = (PB κ c₉).c2 ∧
      P'.H0 = (PB κ c₉).H0 ∧
      (∀ (nK : ℕ) [NeZero nK], D4Pin (k + 1 + 1) (lf' nK)) ∧
      Coh 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (T κ c₉).M cs' P'
        (P6 κ c₉) (C7 κ c₉) β ν (k + 1) (Φ κ c₉ β ν k F.sf) ∧
      ((∀ (nK : ℕ) [NeZero nK], D6Flat kf (lf' nK)) →
        IsRepFlat2 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
          (T κ c₉).M N geo cs' P' (P6 κ c₉) (C7 κ c₉) β ν h (rH κ c₉) (k + 1) kf hM6 hkK'
          ⟨Φ κ c₉ β ν k F.sf, lf'⟩
          (stepDensity d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k
            (F.sf.β k * (cs₀ κ c₉).aKer * ((T κ c₉).L : ℝ) ^ (d - 2))
            ((Φ κ c₉ β ν k F.sf).z (k + 1)) s ρ) St' vc') ∧
      LFCoherent (⟨Φ κ c₉ β ν k F.sf, lf'⟩ : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R
        (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N geo cs' P' (k + 1) (C7 κ c₉).m₁
        (ϱ κ c₉))

end Inputs

/-!
### The assembly
-/

section Assembly

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}

/-- **The frozen small-field step from its sub-inputs** (LFR Theorem IV.2.2 (a)–(f)). For a record of
`ℛ♭_k`, `max(k₀, 1) ≤ k < k̂_f`, `ν_k L² ≤ 7/8`, the small-field data of the successor are the image
`sf' = Φ♭ F.sf`; the clauses (D2♭), (D8), (D9♭) at `k + 1` follow from the input class and the
sub-inputs A4-1a–f (`sfFlatSucc_clauses`, the instance of `sfSucc_core`); (I.2) up to `k + 1` is the
coefficient step (`runningHypTo_succ_of_coeffBounds_core` at `massOne P6`, `FlowRateInput`); the
large-field half gives the data `lf'` with the pins and the coherence, and (H6♭) is
`frozenBudget_of_pin` from the facts of the prefix (`prefixBudgetFacts`); `∫ ρ' = c ∫ ρ` is
`integralStep_stepDensity` with the integrability A4-1i. The threshold is the largest of the nine
thresholds and that of `prefixBudgetFacts`. -/
theorem frozenSFStepInput_of_parts {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hQ : FlowRateInput T P6)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
    (hI : FrozenInheritInput d N T P6 C7 cs₀ ϱ Φ) (hNw : FrozenNewLevelInput d N T P6 C7 cs₀ ϱ Φ)
    (hRn : FrozenRenormInput d N T P6 C7 cs₀ ϱ Φ) (hDn : FrozenDensityInput d N T P6 C7 cs₀ ϱ Φ)
    (hRt : FrozenRemainderInput d N T P6 C7 cs₀ ϱ Φ)
    (hCo : FrozenCoherenceInput d N T P6 C7 cs₀ ϱ Φ)
    (hLF : FrozenLFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ)
    (hInt : FrozenIntegrableInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    FrozenSFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  have hd : 3 ≤ d :=
    (hP 1 one_pos 1 one_pos).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.three_le_d
  intro κ hκ c₉ hc₉
  have hL := (hP κ hκ c₉ hc₉).1
  have hϱ := (hP κ hκ c₉ hc₉).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨b₁, h₁⟩ := hI κ hκ c₉ hc₉
  obtain ⟨b₂, h₂⟩ := hNw κ hκ c₉ hc₉
  obtain ⟨b₃, h₃⟩ := hRn κ hκ c₉ hc₉
  obtain ⟨b₄, h₄⟩ := hDn κ hκ c₉ hc₉
  obtain ⟨b₅, h₅⟩ := hRt κ hκ c₉ hc₉
  obtain ⟨b₆, h₆⟩ := hCo κ hκ c₉ hc₉
  obtain ⟨b₈, h₈⟩ := hLF κ hκ c₉ hc₉
  obtain ⟨b₉, h₉⟩ := hInt κ hκ c₉ hc₉
  obtain ⟨b₀, h₀⟩ := prefixBudgetFacts d δ T P6 C7 PB cs₀ M1 c ϱ hP κ hκ c₉ hc₉
  refine ⟨max (max (max b₁ b₂) (max b₃ b₄)) (max (max b₅ b₆) (max (max b₈ b₉) b₀)), ?_⟩
  intro β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hrep hνkL
  simp only [max_le_iff] at hβ
  obtain ⟨⟨⟨hb₁, hb₂⟩, hb₃, hb₄⟩, ⟨hb₅, hb₆⟩, ⟨hb₈, hb₉⟩, hb₀⟩ := hβ
  have hhor : ν * ((T κ c₉).L : ℝ) ^ (2 * k + 2) < 1 := hkf.2 k hk
  have hF := hrep
  have hsf0 := hF.sfFlatClassAt
  obtain ⟨hgeo, o1, o2, o3, o4, o5, o6, o7, hrepF, hβ0, hν0, hνk, hrun, hcoh, hX⟩ := hrep
  have hcls : SFFlatClassAt d N (T κ c₉).L (P6 κ c₉) (C7 κ c₉).m₁ (ϱ κ c₉) (cs₀ κ c₉).aKer β ν k
      F.sf ∧ F.sf.ν k * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 := ⟨hsf0, by rw [hνk]; exact hνkL⟩
  obtain ⟨hcst, hfree', hz, hTm⟩ := h₁ β hb₁ ν hν hνL k hk1 hk0 hhor F.sf hcls
  obtain ⟨hnew, hgsnew, hhatnew, hTInew⟩ := h₂ β hb₂ ν hν hνL k hk1 hk0 hhor F.sf hcls
  obtain ⟨hC', hR'⟩ := h₃ β hb₃ ν hν hνL k hk1 hk0 hhor F.sf hcls
  have hreal := h₄ β hb₄ ν hν hνL k hk1 hk0 hhor F.sf hcls
  have hRtm := h₅ β hb₅ ν hν hνL k hk1 hk0 hhor F.sf hcls
  have hD8n := h₆ β hb₆ ν hν hνL k hk1 hk0 hhor F.sf hcls
  obtain ⟨hcl, hD8, -, hfreeOld, -, -, hrunOld, hν910⟩ := hsf0
  obtain ⟨hD2', hD8', hD9'⟩ := sfFlatSucc_clauses hd (hL) (hϱ) hk1 hcl hD8 hν910 hfreeOld hrunOld
    hcst hfree' hTm hnew hgsnew hhatnew hTInew hC' hR' hreal hRtm hD8n
  have hkK' : k + 1 ≤ kf + 1 := by omega
  have hafree : ∀ j, 1 ≤ j → j ≤ k + 1 →
      (Φ κ c₉ β ν k F.sf).a j = compWeight (T κ c₉).L (cs₀ κ c₉).aKer j := by
    intro j hj1 hjk
    by_cases hj : j ≤ k
    · rw [(hcst j hj).2.2.2]; exact hfreeOld j hj1 hj
    · obtain rfl : j = k + 1 := by omega
      exact hfree'
  obtain ⟨cs', P', lf', St', vc', s, p1, p2, p3, p4, p5, p6, p7, hpin, hcoh', hrepB, hcohL⟩ :=
    h₈ β hb₈ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hF hνkL hD2' hD8'
      hD9' hafree (fun j hj => ⟨(hcst j hj).1, (hcst j hj).2.1, (hcst j hj).2.2.1⟩) hkK'
  -- the running constants up to `k + 1`
  have hβ0' : (Φ κ c₉ β ν k F.sf).β 0 = β := (hcst 0 (Nat.zero_le k)).1.trans hβ0
  have hν0' : (Φ κ c₉ β ν k F.sf).ν 0 = ν := (hcst 0 (Nat.zero_le k)).2.1.trans hν0
  have hrun' : RunningHypTo d (T κ c₉).L β ν (cs₀ κ c₉).aKer (1 / 20) (Φ κ c₉ β ν k F.sf).β
      (Φ κ c₉ β ν k F.sf).ν k :=
    runningHypTo_congr hrun (fun j hj => (hcst j hj).1) (fun j hj => (hcst j hj).2.1)
  have hrun1 := runningHypTo_succ_of_coeffBounds_core (P := massOne (P6 κ c₉))
    hcl.admissible.γ_pos hcl.admissible.c₈_pos (hQ κ hκ c₉ hc₉) hC' hβ0' hν0' hrun'
  -- (H6♭)
  have hbud : ∀ (nK : ℕ) [NeZero nK], D6Flat kf (lf' nK) := fun nK _ =>
    frozenBudget_of_pin (lf' nK) (h₀ β hb₀ ν hν kf hkf) p5 p6 p7
      (fun j hj => hcoh'.beta_P j hj) hrun1 (hpin nK) (by omega) hk
  have hβk : 0 < F.sf.β k := by
    obtain ⟨γ, hγ, -, hβk⟩ := hrun.beta_eq k le_rfl
    rw [hβk]
    have := hrun.hβ
    have hL0 : (0 : ℝ) < (T κ c₉).L := by exact_mod_cast (by have := hL; omega : 0 < (T κ c₉).L)
    positivity
  have hcK : 0 < F.sf.β k * (cs₀ κ c₉).aKer * ((T κ c₉).L : ℝ) ^ (d - 2) := by
    have ha := hrun.ha1
    have hL0 : (0 : ℝ) < (T κ c₉).L := by exact_mod_cast (by have := hL; omega : 0 < (T κ c₉).L)
    have : (0 : ℝ) < (cs₀ κ c₉).aKer := by linarith
    positivity
  have hint := h₉ β hb₉ ν hν hνL h hh kf hkf k hk1 hk ρ νk ⟨hk0, ⟨hM6, hkK, R, geo, cs, P, F, St,
    vc, hF⟩, hνkL⟩
  refine ⟨_, (Φ κ c₉ β ν k F.sf).ν (k + 1), ?_,
    integralStep_stepDensity s hcK hz ρ hint⟩
  refine ⟨hM6, hkK', R, geo, cs', P', ⟨Φ κ c₉ β ν k F.sf, lf'⟩, St', vc', hgeo, p1, p2, p3, p4, p5,
    p6, p7, hrepB hbud, hβ0', hν0', rfl, ?_, hcohL, ?_⟩
  · exact runningHypTo_congr hrun' (fun j _ => rfl) (fun j _ => rfl)
  · exact ⟨(hcst k le_rfl).2.1.trans hνk, fun j hj =>
      ⟨(hcst j hj).1, (hcst j hj).2.1, (hcst j hj).2.2.2⟩⟩

end Assembly

end Balaban.RootFSpine
