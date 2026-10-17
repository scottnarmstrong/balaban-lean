module

public import Balaban.Polymer.TwoTorusResumRootF
public import Balaban.Polymer.TwoTorusFibreWeighted

/-!
# The limit resummation for Root-F's tori with the size-uniform closeness (W867, blocker 7)

`resum_lastScale_rootF_weighted` wires `fibre_hcoef_of_quarterBox_weighted` into
`resum_lastScale_torus_limit` for the last-scale terms
`T ℓ g X = ∑_{C : C.image (cen ℓ) = X} (coef ellE C - coef ell0 C + coef J C)` (the hypothesis `hT`).
The closeness `hcoef` of `resum_lastScale_torus_limit` is proved (with `ε := √ε`, the denominator
rate `κ₁ = log (1 + √(e^κ - 1))`, `Mr = M`), the tori are Root-F's block tori (`hK`), and the
chain, the eventual box, the margin and the analyticity of the limit are discharged by the landed
theorems.

The physical hypotheses that remain: `hW`, `hW0` (`WSmall` of `E` and of `0`), `hdet`, `hdet0`,
`han`, `han0`, `hz`, `hz0` (analytic logarithms of the determinants), `hEcl`, `hFcl`, `hγ`,
`hFan`, `hFB`, `hFm`, `hLipb`, `hγmass` (the correspondence of the operators, of the cutoff
interaction and of the measures on two tori), `hT`, the support, locality and analyticity of `T`,
the crude bound `hbd` with the rate `κ'`, and the decay `hε` of the closeness of the operators
(rate `2 lam`).  The remaining rate conditions are `κ_out + log 2 ≤ κ' ≤ lam`, `2 κ' ≤
log (e^κ - 1)` and `lam ≤ 2 c₀ M`; `rootF_rates_of_kappa_large` shows that the first two hold for
`κ` large.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Matrix Filter Topology Balaban.Green Balaban.Localization MeasureTheory
  Balaban.Analysis

namespace Balaban.Polymer

section Wired

variable {d M : ℕ} {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **Core of `resum_lastScale_rootF_weighted`, with the decay constant `c₀` chosen before the
block size `M`, the scale `k` and the rate `κ`.**  `c₀` depends on `d, L` only; the rate condition
`lam ≤ 2 c₀ M` then holds for `M` large (`rootF_lam_le_of_block_large`). -/
theorem resum_lastScale_rootF_weighted_const {L : ℕ} [NeZero L] (hd : 0 < d) :
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
      2 * κ' ≤ Real.log (Real.exp κ - 1) → lam ≤ 2 * c₀ * (M : ℝ) →
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
  classical
  obtain ⟨c₁, hc₁, hcq⟩ := fibre_hcoef_of_quarterBox_weighted_const (L := L) hd
  refine ⟨c₁, hc₁, ?_⟩
  intro M k hM κ hκ hMB hMκ rE η hrE hη0 hη hk v a sc hv0 hv1 ha1 ha2 hmass hsc N _ K hK hMN cen hcen D Q hQ sz hsz τ hτ t₀ ht₀ E hW hW0 ε hε0 hEcl ρ hρ ellE ell0 han han0 hz hz0 hdet hdet0 ρJ RF Lb mb hρJ hLb hmb γ hγfin hγmass hBR F B' Lip hFan hFB hFm hLipb hFcl hγ T hT hK2 P tor hD W hWsp R Ag hKm hKt hP hR hAg hsupp hloc hanT
  obtain ⟨κ₁, Pc, C₀, hκ₁, hexp, hPc, hC, hcl⟩ :=
    hcq hM hκ hMB hMκ hrE hη0 hη hk hv0 hv1 ha1 ha2 hmass hsc
      N K hK hMN cen hcen D Q hQ sz hsz τ hτ ht₀ E hW hW0 ε hε0 hEcl hρ ellE ell0 han han0 hz hz0
      hdet hdet0 hρJ hLb hmb γ hγfin hγmass hBR F B' Lip hFan hFB hFm hLipb hFcl hγ T hT
  refine ⟨κ₁, Pc, C₀, hκ₁, hexp, hPc, hC, ?_⟩
  intro B κo κ' lam ε₁ hB hκo hκ' hlam hε₁ hκh hlamc hbd hεd
  have hKne : ∀ ℓ, NeZero (K ℓ) := fun ℓ => ⟨by have := hK2 ℓ; omega⟩
  have hsq : 0 ≤ Real.exp κ - 1 := by
    have := Real.add_one_le_exp κ; linarith
  have hκ'₁ : κ' ≤ Real.log (Real.exp κ₁ - 1) := by
    rw [hexp, Real.log_sqrt hsq]; linarith
  have hε' : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      Real.sqrt (ε ℓ g X) ≤ Real.sqrt ε₁ * Real.exp (-lam * (τ ℓ X : ℝ)) := by
    intro ℓ X hX hQX ht g hg
    have := sqrt_le_sqrt_mul_exp_half hε₁ (hεd ℓ X hX hQX ht g hg)
    rwa [show 2 * lam / 2 = lam by ring] at this
  have := hKne
  exact resum_lastScale_torus_limit K hd hK2 P Q sz τ tor D hD W hWsp R Ag T
    (fun ℓ g X => Real.sqrt (ε ℓ g X)) hKm hKt hP hQ hsz hτ hR hAg hB hκo hκ' hlam hPc hC.le
    (Real.sqrt_nonneg _) hκ₁ hκ'₁ (by simpa using hlamc) hsupp hloc hanT hbd
    (fun ℓ ℓ' X _ hQX _ hKK ht g hg => hcl ℓ ℓ' X hQX hKK ht g hg)
    (fun _ _ _ => Real.sqrt_nonneg _) hε'

/-- **The limit resummation for the last-scale terms of Root-F's tori, with every abstract
hypothesis discharged (W867, blocker 7).**  The constants `κ₁`, `Pc`, `C₀`, `c₀` are those of
`fibre_hcoef_of_quarterBox_weighted`.  For every output rate `κo ≥ 0`, crude rate `κ'`, decay
rate `lam` of the resummed closeness, constant `B` of the crude bound and constant `ε₁` of the
closeness of the operators, the conclusion is the conclusion of `resum_lastScale_torus_limit`
(with `Mr = M`, `ε₁` replaced by `√ε₁`). -/
theorem resum_lastScale_rootF_weighted {L k : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (hk : 1 ≤ k)
    {v a sc : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hsc : 0 ≤ sc)
    (N : ι → ℕ) [∀ ℓ, NeZero (N ℓ)] (K : ι → ℕ)
    (hK : ∀ ℓ, K ℓ = macK (N ℓ) M) (hMN : ∀ ℓ, M ∣ N ℓ)
    (cen : ∀ ℓ, MacIdx d (N ℓ) M → Fin d → ℤ)
    (hcen : ∀ ℓ z μ, cen ℓ z μ = ((z μ : ℕ) : ZMod (macK (N ℓ) M)).valMinAbs)
    (D : Set G) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (sz : Finset (Fin d → ℤ) → ℕ) (hsz : ∀ X, sz X = X.card)
    (τ : ι → Finset (Fin d → ℤ) → ℕ)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    {t₀ : ℕ} (ht₀ : 5 ≤ t₀)
    -- the operator `E`, its closeness `ε`, and the logarithms of the defects
    (E : ∀ ℓ, G → Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ)
    (hW : ∀ ℓ g, g ∈ D → WSmall rE η (E ℓ g))
    (hW0 : ∀ ℓ, WSmall rE η (0 : Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ))
    (ε : ι → G → Finset (Fin d → ℤ) → ℝ) (hε0 : ∀ ℓ g X, 0 ≤ ε ℓ g X)
    (hEcl : ∀ ℓ ℓ' g, g ∈ D → ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M), ∀ x ∈ macRegion d (N ℓ) M C, ∀ y ∈ macRegion d (N ℓ) M C,
        ‖E ℓ g x y - E ℓ' g (f x) (f y)‖ ≤ ε ℓ g (C.image (cen ℓ)))
    {ρ : ℝ} (hρ : Real.exp κ < ρ)
    (ellE ell0 : ∀ ℓ, G → (MacIdx d (N ℓ) M → ℂ) → ℂ)
    (han : ∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (ellE ℓ g) (Metric.ball 0 ρ))
    (han0 : ∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (ell0 ℓ g) (Metric.ball 0 ρ))
    (hz : ∀ ℓ g, g ∈ D → ellE ℓ g 0 = 0) (hz0 : ∀ ℓ g, g ∈ D → ell0 ℓ g 0 = 0)
    (hdet : ∀ ℓ g, g ∈ D → ∀ s' ∈ Metric.ball (0 : MacIdx d (N ℓ) M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d (N ℓ) M)
        (fun z => boxR (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z)
            (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) sc -
          E ℓ g * (Matrix.diagonal (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) *
            boxG (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z) sc)) s').det =
        Complex.exp (ellE ℓ g s'))
    (hdet0 : ∀ ℓ g, g ∈ D → ∀ s' ∈ Metric.ball (0 : MacIdx d (N ℓ) M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d (N ℓ) M)
        (fun z => boxR (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z)
            (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) sc -
          (0 : Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ) *
            (Matrix.diagonal (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) *
            boxG (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z) sc)) s').det =
        Complex.exp (ell0 ℓ g s'))
    -- the cutoff interaction
    {ρJ RF Lb mb : ℝ} (hρJ : 0 ≤ ρJ) (hLb : 0 ≤ Lb) (hmb : 0 ≤ mb)
    (γ : ∀ ℓ, Measure (L1Torus d (N ℓ) → ℝ))
    (hγfin : ∀ ℓ, γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ} < ⊤)
    (hγmass : ∀ ℓ, (γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}).toReal ≤ mb)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρJ < RF)
    (F : ∀ ℓ, G → (L1Torus d (N ℓ) → ℂ) → ℂ) (B' : G → ℝ) (Lip : ι → G → ℝ)
    (hFan : ∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (F ℓ g) (polydisc (0 : L1Torus d (N ℓ) → ℂ) (fun _ => RF)))
    (hFB : ∀ ℓ g, g ∈ D → ∀ w ∈ polydisc (0 : L1Torus d (N ℓ) → ℂ) (fun _ => RF),
      ‖F ℓ g w‖ ≤ B' g)
    (hFm : ∀ ℓ g, g ∈ D → Measurable (F ℓ g))
    (hLipb : ∀ ℓ g, g ∈ D → Lip ℓ g ≤ Lb)
    (hFcl : ∀ ℓ ℓ' g, g ∈ D → ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
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
        ‖F ℓ' g w' - F ℓ g w‖ ≤ Lip ℓ g * η)
    (hγ : ∀ ℓ ℓ', ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M),
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK (N ℓ) M - m ≤ (z i : ℕ)) →
        Measure.map (fun (ψ : L1Torus d (N ℓ) → ℝ) (q : ↥(macRegion d (N ℓ) M C)) => ψ q)
            ((γ ℓ).restrict {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}) =
          Measure.map (fun (ψ' : L1Torus d (N ℓ') → ℝ) (q : ↥(macRegion d (N ℓ) M C)) => ψ' (f q))
            ((γ ℓ').restrict {ψ' : L1Torus d (N ℓ') → ℝ | ∀ y, |ψ' y| ≤ ρJ}))
    (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hT : ∀ ℓ g X, T ℓ g X = ∑ C ∈ (Finset.univ : Finset (Finset (MacIdx d (N ℓ) M))).filter
      (fun C => C.image (cen ℓ) = X),
      (coef (ellE ℓ g) C - coef (ell0 ℓ g) C +
        coef (fun s : MacIdx d (N ℓ) M → ℂ =>
          ∫ ψ in {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ},
            F ℓ g (fun x => ∑ y, taggedCfin d L (N ℓ) k M v a s x y * ((ψ y : ℝ) : ℂ))
              ∂(γ ℓ)) C))
    -- the family of tori, the sets of polymers, and the analytic structure
    (hK2 : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ))) (tor : ℕ → ι)
    (hD : IsOpen D) (W : Submodule ℂ (G → ℂ)) (hWsp : ∀ f, f ∈ W ↔ AnalyticOnNhd ℂ f D)
    (R : Finset (Fin d → ℤ) → Prop) (Ag : Finset (Fin d → ℤ) → G → G → Prop)
    (hKm : ∀ m n, m ≤ n → K (tor m) ≤ K (tor n))
    (hKt : Filter.Tendsto (fun n => K (tor n)) Filter.atTop Filter.atTop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (hanT : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W) :
    ∃ κ₁ Pc C₀ c₀ : ℝ, 0 < κ₁ ∧ Real.exp κ₁ - 1 = Real.sqrt (Real.exp κ - 1) ∧ 0 ≤ Pc ∧
      0 < C₀ ∧ 0 < c₀ ∧
    ∀ (B κo κ' lam ε₁ : ℝ), 0 ≤ B → 0 ≤ κo → κo + Real.log 2 ≤ κ' → κ' ≤ lam → 0 ≤ ε₁ →
      2 * κ' ≤ Real.log (Real.exp κ - 1) → lam ≤ 2 * c₀ * (M : ℝ) →
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
  obtain ⟨κ₁, Pc, C₀, hκ₁, hexp, hPc, hC, hcl⟩ := h hM hκ hMB hMκ hrE hη0 hη hk hv0 hv1 ha1 ha2 hmass hsc N K hK hMN cen hcen D Q hQ sz hsz τ hτ ht₀ E hW hW0 ε hε0 hEcl hρ ellE ell0 han han0 hz hz0 hdet hdet0 hρJ hLb hmb γ hγfin hγmass hBR F B' Lip hFan hFB hFm hLipb hFcl hγ T hT hK2 P tor hD W hWsp R Ag hKm hKt hP hR hAg hsupp hloc hanT
  exact ⟨κ₁, Pc, C₀, c₁, hκ₁, hexp, hPc, hC, hc₁, hcl⟩

end Wired

section Rates

/-- **The rate conditions are satisfiable for `κ` large (W867).**  For `κo` put
`κ' = κo + log 2` and `κ₀ = log (e^{2κ'} + 1)`.  For every `κ ≥ max 1 κ₀` the condition
`2 κ' ≤ log (e^κ - 1)` of `resum_lastScale_rootF_weighted` holds (hence also
`κ' ≤ log (e^{κ₁} - 1)` for `e^{κ₁} - 1 = √(e^κ - 1)`), and `κo + log 2 ≤ κ' ≤ κ'` holds with
`lam = κ'`. -/
theorem rootF_rates_of_kappa_large {κo : ℝ} {κ : ℝ}
    (hκ : Real.log (Real.exp (2 * (κo + Real.log 2)) + 1) ≤ κ) :
    2 * (κo + Real.log 2) ≤ Real.log (Real.exp κ - 1) := by
  have h1 : Real.exp (Real.log (Real.exp (2 * (κo + Real.log 2)) + 1)) ≤ Real.exp κ :=
    Real.exp_le_exp.2 hκ
  rw [Real.exp_log (by positivity)] at h1
  rw [← Real.log_exp (2 * (κo + Real.log 2))]
  exact Real.log_le_log (Real.exp_pos _) (by linarith)

end Rates

end Balaban.Polymer
