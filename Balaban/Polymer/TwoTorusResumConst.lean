/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusResumWired

/-!
# The rate condition `lam ≤ 2 c₀ M` for large blocks (W870, blocker 7)

In `resum_lastScale_rootF_weighted` the decay constant `c₀` of the closeness of the last-scale
terms is chosen after the block size `M`, so the rate condition `lam ≤ 2 c₀ M` of the resummation
cannot be met by taking `M` large.  The decay constant is the decay constant of
`final_region_entry_close_unif`, which depends on `d` and `L` only.  The cores
`..._const` (`final_coef_logdet_close_twoTorus_unif_weighted_const`,
`final_coef_cutoffInteraction_close_twoTorus_unif_weighted_const`,
`finalCoef_close_quarterBox_weighted_const`, `fibre_hcoef_of_quarterBox_weighted_const`,
`resum_lastScale_rootF_weighted_const`) choose `c₀` first; the landed statements are applications.
Here the rate condition is replaced by the lower bound `lam / (2 c₀) ≤ M` for the block size.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Matrix Filter Topology Balaban.Green Balaban.Localization MeasureTheory
  Balaban.Analysis

namespace Balaban.Polymer

variable {d : ℕ} {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The rate condition `lam ≤ 2 c₀ M` holds for `M ≥ lam / (2 c₀)`. -/
theorem rootF_lam_le_of_block_large {c₀ lam : ℝ} {M : ℕ} (hc : 0 < c₀)
    (h : lam / (2 * c₀) ≤ (M : ℝ)) : lam ≤ 2 * c₀ * (M : ℝ) := by
  have h2 : 0 < 2 * c₀ := by positivity
  rw [div_le_iff₀ h2] at h
  linarith

/-- **The limit resummation for the last-scale terms of Root-F's tori with the decay constant
chosen before the block size (W870, blocker 7).**  There is `c₀ > 0` depending on `d` and `L`
only such that for every block size `M` and every `κ` satisfying the landed size conditions, the
conclusion of `resum_lastScale_rootF_weighted` holds for every rate `lam` with
`lam ≤ 2 c₀ M`, that is for `M ≥ lam / (2 c₀)`: the rate condition is replaced by a lower bound
on `M`. -/
theorem resum_lastScale_rootF_weighted_of_block_large {L : ℕ} [NeZero L] (hd : 0 < d) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {M : ℕ} {k : ℕ},
    (0 < M) →
    ∀ {κ : ℝ},
    (1 ≤ κ) →
    (4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) →
    (8 * κ * 7 ^ d ≤ pdEps d L * M) →
    ∀ {rE η : ℝ},
    (pdEps d L / 4 ≤ rE) →
    (0 ≤ η) →
    (4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) →
    (1 ≤ k) →
    ∀ {v a sc : ℝ},
    (0 ≤ v) →
    (v ≤ 1) →
    (1 / 2 ≤ a) →
    (a ≤ 2) →
    (7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) →
    (0 ≤ sc) →
    ∀ (N : ι → ℕ) [∀ ℓ, NeZero (N ℓ)] (K : ι → ℕ),
    (∀ ℓ, K ℓ = macK (N ℓ) M) →
    (∀ ℓ, M ∣ N ℓ) →
    ∀ (cen : ∀ ℓ, MacIdx d (N ℓ) M → Fin d → ℤ),
    (∀ ℓ z μ, cen ℓ z μ = ((z μ : ℕ) : ZMod (macK (N ℓ) M)).valMinAbs) →
    ∀ (D : Set G) (Q : ι → Finset (Fin d → ℤ) → Prop),
    (∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4) →
    ∀ (sz : Finset (Fin d → ℤ) → ℕ),
    (∀ X, sz X = X.card) →
    ∀ (τ : ι → Finset (Fin d → ℤ) → ℕ),
    (∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs)) →
    ∀ {t₀ : ℕ},
    (5 ≤ t₀) →
    ∀ (E : ∀ ℓ, G → Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ),
    (∀ ℓ g, g ∈ D → WSmall rE η (E ℓ g)) →
    (∀ ℓ, WSmall rE η (0 : Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ)) →
    ∀ (ε : ι → G → Finset (Fin d → ℤ) → ℝ),
    (∀ ℓ g X, 0 ≤ ε ℓ g X) →
    (∀ ℓ ℓ' g, g ∈ D → ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M), ∀ x ∈ macRegion d (N ℓ) M C, ∀ y ∈ macRegion d (N ℓ) M C,
        ‖E ℓ g x y - E ℓ' g (f x) (f y)‖ ≤ ε ℓ g (C.image (cen ℓ))) →
    ∀ {ρ : ℝ},
    (Real.exp κ < ρ) →
    ∀ (ellE ell0 : ∀ ℓ, G → (MacIdx d (N ℓ) M → ℂ) → ℂ),
    (∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (ellE ℓ g) (Metric.ball 0 ρ)) →
    (∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (ell0 ℓ g) (Metric.ball 0 ρ)) →
    (∀ ℓ g, g ∈ D → ellE ℓ g 0 = 0) →
    (∀ ℓ g, g ∈ D → ell0 ℓ g 0 = 0) →
    (∀ ℓ g, g ∈ D → ∀ s' ∈ Metric.ball (0 : MacIdx d (N ℓ) M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d (N ℓ) M)
        (fun z => boxR (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z)
            (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) sc -
          E ℓ g * (Matrix.diagonal (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) *
            boxG (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z) sc)) s').det =
        Complex.exp (ellE ℓ g s')) →
    (∀ ℓ g, g ∈ D → ∀ s' ∈ Metric.ball (0 : MacIdx d (N ℓ) M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d (N ℓ) M)
        (fun z => boxR (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z)
            (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) sc -
          (0 : Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ) *
            (Matrix.diagonal (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) *
            boxG (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z) sc)) s').det =
        Complex.exp (ell0 ℓ g s')) →
    ∀ {ρJ RF Lb mb : ℝ},
    (0 ≤ ρJ) →
    (0 ≤ Lb) →
    (0 ≤ mb) →
    ∀ (γ : ∀ ℓ, Measure (L1Torus d (N ℓ) → ℝ)),
    (∀ ℓ, γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ} < ⊤) →
    (∀ ℓ, (γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}).toReal ≤ mb) →
    ((4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρJ < RF) →
    ∀ (F : ∀ ℓ, G → (L1Torus d (N ℓ) → ℂ) → ℂ) (B' : G → ℝ) (Lip : ι → G → ℝ),
    (∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (F ℓ g) (polydisc (0 : L1Torus d (N ℓ) → ℂ) (fun _ => RF))) →
    (∀ ℓ g, g ∈ D → ∀ w ∈ polydisc (0 : L1Torus d (N ℓ) → ℂ) (fun _ => RF),
      ‖F ℓ g w‖ ≤ B' g) →
    (∀ ℓ g, g ∈ D → Measurable (F ℓ g)) →
    (∀ ℓ g, g ∈ D → Lip ℓ g ≤ Lb) →
    (∀ ℓ ℓ' g, g ∈ D → ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M),
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK (N ℓ) M - m ≤ (z i : ℕ)) →
      ∀ {e : MacIdx d (N ℓ) M → MacIdx d (N ℓ') M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK (N ℓ) M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK (N ℓ') M = ((z i : ℕ) + (m + 4)) % macK (N ℓ) M) →
      ∀ (w : L1Torus d (N ℓ) → ℂ) (w' : L1Torus d (N ℓ') → ℂ),
        (∀ x, x ∉ macRegion d (N ℓ) M C → w x = 0) →
        (∀ x', x' ∉ macRegion d (N ℓ') M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρJ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρJ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d (N ℓ) M C, ‖w' (f x) - w x‖ ≤ η) →
        ‖F ℓ' g w' - F ℓ g w‖ ≤ Lip ℓ g * η) →
    (∀ ℓ ℓ', ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M),
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK (N ℓ) M - m ≤ (z i : ℕ)) →
        Measure.map (fun (ψ : L1Torus d (N ℓ) → ℝ) (q : ↥(macRegion d (N ℓ) M C)) => ψ q)
            ((γ ℓ).restrict {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}) =
          Measure.map (fun (ψ' : L1Torus d (N ℓ') → ℝ) (q : ↥(macRegion d (N ℓ) M C)) => ψ' (f q))
            ((γ ℓ').restrict {ψ' : L1Torus d (N ℓ') → ℝ | ∀ y, |ψ' y| ≤ ρJ})) →
    ∀ (T : ι → G → Finset (Fin d → ℤ) → ℂ),
    (∀ ℓ g X, T ℓ g X = ∑ C ∈ (Finset.univ : Finset (Finset (MacIdx d (N ℓ) M))).filter
      (fun C => C.image (cen ℓ) = X),
      (coef (ellE ℓ g) C - coef (ell0 ℓ g) C +
        coef (fun s : MacIdx d (N ℓ) M → ℂ =>
          ∫ ψ in {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ},
            F ℓ g (fun x => ∑ y, taggedCfin d L (N ℓ) k M v a s x y * ((ψ y : ℝ) : ℂ))
              ∂(γ ℓ)) C)) →
    (∀ ℓ, 2 ≤ K ℓ) →
    ∀ (P : ι → Finset (Finset (Fin d → ℤ))) (tor : ℕ → ι),
    (IsOpen D) →
    ∀ (W : Submodule ℂ (G → ℂ)),
    (∀ f, f ∈ W ↔ AnalyticOnNhd ℂ f D) →
    ∀ (R : Finset (Fin d → ℤ) → Prop) (Ag : Finset (Fin d → ℤ) → G → G → Prop),
    (∀ m n, m ≤ n → K (tor m) ≤ K (tor n)) →
    (Filter.Tendsto (fun n => K (tor n)) Filter.atTop Filter.atTop) →
    (∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs)) →
    (∀ ℓ X, X ∈ P ℓ → R X) →
    (∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g') →
    (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0) →
    (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X) →
    (∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W) →
    ∃ κ₁ Pc C₀ : ℝ, 0 < κ₁ ∧ Real.exp κ₁ - 1 = Real.sqrt (Real.exp κ - 1) ∧ 0 ≤ Pc ∧
      0 < C₀ ∧
    ∀ (B κo κ' lam ε₁ : ℝ), 0 ≤ B → 0 ≤ κo → κo + Real.log 2 ≤ κ' → κ' ≤ lam → 0 ≤ ε₁ →
      2 * κ' ≤ Real.log (Real.exp κ - 1) → lam / (2 * c₀) ≤ (M : ℝ) →
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ))) →
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
        ε ℓ g X ≤ ε₁ * Real.exp (-(2 * lam) * (τ ℓ X : ℝ))) →
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ V : G → Finset (Fin d → ℤ) → ℂ,
      (∀ g X, V g X = limUnder atTop (fun n => T (tor n) g X)) ∧
      ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then V g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - V g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (Pc * (C₀ * Real.exp (7 * c₀ * (M : ℝ)) + Real.sqrt ε₁)) * Real.exp κ' +
          2 * B * Real.exp (κ' * (t₀ : ℝ))) * Real.exp (-κo * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  obtain ⟨c₁, hc₁, h⟩ := resum_lastScale_rootF_weighted_const (L := L) (ι := ι) (G := G) hd
  refine ⟨c₁, hc₁, ?_⟩
  intro M k hM κ hκ hMB hMκ rE η hrE hη0 hη hk v a sc hv0 hv1 ha1 ha2 hmass hsc N _ K hK hMN cen hcen D Q hQ sz hsz τ hτ t₀ ht₀ E hW hW0 ε hε0 hEcl ρ hρ ellE ell0 han han0 hz hz0 hdet hdet0 ρJ RF Lb mb hρJ hLb hmb γ hγfin hγmass hBR F B' Lip hFan hFB hFm hLipb hFcl hγ T hT hK2 P tor hD W hWsp R Ag hKm hKt hP hR hAg hsupp hloc hanT
  obtain ⟨κ₁, Pc, C₀, hκ₁, hexp, hPc, hC, H⟩ := h hM hκ hMB hMκ hrE hη0 hη hk hv0 hv1 ha1 ha2 hmass hsc N K hK hMN cen hcen D Q hQ sz hsz τ hτ ht₀ E hW hW0 ε hε0 hEcl hρ ellE ell0 han han0 hz hz0 hdet hdet0 hρJ hLb hmb γ hγfin hγmass hBR F B' Lip hFan hFB hFm hLipb hFcl hγ T hT hK2 P tor hD W hWsp R Ag hKm hKt hP hR hAg hsupp hloc hanT
  refine ⟨κ₁, Pc, C₀, hκ₁, hexp, hPc, hC, ?_⟩
  intro B κo κ' lam ε₁ hB hκo hκ' hlam hε₁ hκh hMl
  exact H B κo κ' lam ε₁ hB hκo hκ' hlam hε₁ hκh (rootF_lam_le_of_block_large hc₁ hMl)

end Balaban.Polymer
