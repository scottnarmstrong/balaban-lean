/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KeptPinned
public import Balaban.Spine.Coherence

/-!
# `LFCoherent` of the output of the kept half of `R`

The family with the large-field parts `keptRep (F.lf nK) (D nK)` and no boundary terms is torus
coherent (`lfCoherent_post`) if the input family is, the kept data of the five outcomes are
(`KeptDatumCoh`, the datum clause of (D8)), and the kept costs are those of LFR Definition III.5.2
(`KeptScaleData.gam_val`).  The step kernels and the exponents `κ_j`, `j ≠ k`, are those of the
input; the exponent `κ_k` is the pinned exponent, coherent by `pinnedExp_corr`; the boundary terms
of the family are zero.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

section Coh

variable {S : Setting} [NeZero S.L] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {k m₁ : ℕ} {ϱ : ℝ}

/-- **The datum clause of (D8) at the scale `j` for a family of kept data**: the kept variable sets
`I''` and the kept kernels and boundary factors at corresponding localized histories, variables,
outputs, configurations and sources agree (LFR Definition II.6.2 (D8), D-IV.9). -/
def KeptDatumCohAt (j : ℕ)
    (D : ∀ (nK : ℕ) [NeZero nK] (a : LocalHistory S (sides S.L K nK) M K),
      LabRec S (sides S.L K nK) M K → Fin 5 → KeptDatum (S := S) N R a j) : Prop :=
  ∀ (nK₁ nK₂ : ℕ) [NeZero nK₁] [NeZero nK₂] (c : Fin S.d → ℤ)
    (H₁ : RegionHistory S (sides S.L K nK₁) R k0 K) (H₂ : RegionHistory S (sides S.L K nK₂) R k0 K),
    H₁.Admissible → H₂.Admissible → ∀ (Z₁ : H₁.Comp j) (Z₂ : H₂.Comp j),
      HistCorr c (H₁.localHistory M K j Z₁) (H₂.localHistory M K j Z₂) →
      SetCorr c (Vsites R (H₁.localHistory M K j Z₁) j) (Vsites R (H₂.localHistory M K j Z₂) j) →
      ∀ (lab₁ : ∀ i, H₁.Comp i → Fin 5) (lab₂ : ∀ i, H₂.Comp i → Fin 5),
        LabCorr c (H₁.locLab M lab₁ j Z₁) (H₂.locLab M lab₂ j Z₂) → ∀ ϰ : Fin 5,
        (∀ p₁ p₂, VarCorr c p₁ p₂ →
          (p₁ ∈ (D nK₁ (H₁.localHistory M K j Z₁) (H₁.locLab M lab₁ j Z₁) ϰ).Ikeep ↔
            p₂ ∈ (D nK₂ (H₂.localHistory M K j Z₂) (H₂.locLab M lab₂ j Z₂) ϰ).Ikeep)) ∧
        ∀ o₁ o₂ x₁ x₂ hv g₁ g₂, OutCorr c j o₁ o₂ → CfgCorr c x₁ x₂ → GCorr c g₁ g₂ →
          (D nK₂ (H₂.localHistory M K j Z₂) (H₂.locLab M lab₂ j Z₂) ϰ).ker.K o₂ x₂ hv =
              (D nK₁ (H₁.localHistory M K j Z₁) (H₁.locLab M lab₁ j Z₁) ϰ).ker.K o₁ x₁ hv ∧
            (D nK₂ (H₂.localHistory M K j Z₂) (H₂.locLab M lab₂ j Z₂) ϰ).ker.b o₂ x₂ hv g₂ =
              (D nK₁ (H₁.localHistory M K j Z₁) (H₁.locLab M lab₁ j Z₁) ϰ).ker.b o₁ x₁ hv g₁

/-- **The datum clause of (D8) for the kept data of a family of tori**, at every scale. -/
def KeptDatumCoh
    (κ : ∀ (nK : ℕ) [NeZero nK], ℕ → LocalHistory S (sides S.L K nK) M K → ℝ)
    (KD : ∀ (nK : ℕ) [NeZero nK], KeptData k0 (geo nK) cs N (κ nK) S.lam) : Prop :=
  ∀ j, KeptDatumCohAt (K := K) (M := M) (R := R) (k0 := k0) j
    (fun nK _ a ℓ ϰ => (KD nK).datum j a ℓ ϰ)

/-- **`LFCoherent` of the output of the kept half of `R`.**  The family with the large-field parts
`keptRep (F.lf nK) (D nK)` (the pinned exponents `κ_k = κ^pre_k` at the scale `k`, the kept data of
the five outcomes) and no boundary terms is torus coherent, given that the input family is
(`hin`: the step kernels and the exponents `κ_j`, `j ≠ k`, are those of the input), that the kept
data of the five outcomes are (`hdat`), and that the kept costs `γ_i` are those of LFR Definition
III.5.2 (`KeptScaleData.gam_val`).  The coherence of the pinned exponent is `pinnedExp_corr`. -/
theorem lfCoherent_post {F : RepFam S R k0 K M N geo cs P k m₁ ϱ} (hin : LFCoherent F)
    (D : ∀ (nK : ℕ) [NeZero nK], KeptScaleData (F.lf nK)) (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hpin : ∀ (nK : ℕ) [NeZero nK], D4Pin k (keptRep (F.lf nK) (D nK)))
    (hdat : KeptDatumCoh (K := K) (M := M) (R := R) (geo := geo) (cs := cs) (k0 := k0)
      (fun nK _ => keptExpOut (F.lf nK) (canonHist S (sides S.L K nK) R k0 K k (k + 1)) k)
      (fun nK _ => (D nK).KD)) :
    LFCoherent (repFamPost F (fun nK _ => keptRep (F.lf nK) (D nK)) bZero remZero) := by
  classical
  intro nK₁ nK₂ _ _ c
  obtain ⟨c1, c2, c3⟩ := hin nK₁ nK₂ c
  refine ⟨c1, ?_, ?_⟩
  · intro H₁ H₂ ad₁ ad₂ j Z₁ Z₂ hH hV
    refine ⟨?_, hdat j nK₁ nK₂ c H₁ H₂ ad₁ ad₂ Z₁ Z₂ hH hV⟩
    by_cases hjk : j = k
    · subst hjk
      obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hl₁ : KappaPreLocal (F.lf nK₁) (canonHist S (sides S.L K nK₁) R k0 K j (j + 1)) j :=
        kappaPreLocal_of_gam_indep _ _ hkK fun i hi l l' => (D nK₁).gam_indep_below hi l l'
      have hl₂ : KappaPreLocal (F.lf nK₂) (canonHist S (sides S.L K nK₂) R k0 K j (j + 1)) j :=
        kappaPreLocal_of_gam_indep _ _ hkK fun i hi l l' => (D nK₂).gam_indep_below hi l l'
      have := pinnedExp_corr (F.lf nK₁) (F.lf nK₂) (D nK₁) (D nK₂) hj' hkK (hpin nK₁) (hpin nK₂)
        hl₁ hl₂ (fun i => Real.log 5 + S.A3' * S.lam i ^ S.pR)
        (fun i _ l => (D nK₁).gam_val i l) (fun i _ l => (D nK₂).gam_val i l) Z₁ Z₂ hH hV
      show keptExpOut (F.lf nK₂) _ j j _ = keptExpOut (F.lf nK₁) _ j j _
      unfold keptExpOut
      simpa using this
    · have := (c2 H₁ H₂ ad₁ ad₂ j Z₁ Z₂ hH hV).1
      show keptExpOut (F.lf nK₂) _ _ j _ = keptExpOut (F.lf nK₁) _ _ j _
      unfold keptExpOut
      simpa [hjk] using this
  · intros
    rfl

end Coh

end Balaban.RootFSpine
