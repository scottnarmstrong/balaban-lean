/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrRooted
public import Balaban.Inhabited.DecMarkCorrTotalFromTowerG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical sum identity for the corrected marks at every scale of the general tower

General versions of `markedRad_slice_lt_fromTower`, `sum_decMarkCorr_physical_fromTower`,
`sum_markedOutDec_decMarkCorr_physical_fromTower` and
`ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTower`, at the step
`S₀.withDatum D' hDh` of a scale of `T : StepTowerG d L N κmin` over any `ϱ = rhoSepG d L T.m₁`
(`hϱ`), with `S₀ = hatStepKG … ϱ …` (`hS₀`); the constants of the tower are `BG₂ = T.BG₂`,
`κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set Filter Topology MeasureTheory

/-- **The first marks of the disc `‖u‖ ≤ 17/16` lie in the slice of the bidisc of the pairs.**
At a scale of the tower, `(‖u‖ + 0) · markedRad(p₁) < T.t` for every `‖u‖ ≤ 17/16`
(`StepScaleData.marked_radius_lt`). -/
theorem markedRad_slice_lt_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁)
    {u : ℂ} (hu : ‖u‖ ≤ 17 / 16) :
    (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hr0 := D.r_pos
  have hmem := compWeightG_mem T hk
  have hCs : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by have := T.hd; omega) T.hL (by linarith [hmem.1]) T.κ
  have hmr : 0 ≤ markedRad d L N k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    unfold markedRad
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg hCs hp.le))
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ hmr) (D.marked_radius_lt hp)
  rw [norm_zero, add_zero]
  nlinarith [hr0, hu]

/-- **The physical sum identity for the corrected marks at every scale of the tower** (zero
class).  Let `(F₁ b, Sol b)` be a pair with the eight clauses for every block `b`, at the step
`S = S₀.withDatum D' hDh` with the constants of the tower
(`cc = β_k^{-1/2}`, mask `blockU z`, `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁`).  For
a hat field `‖x‖ ≤ p₁`, the clamp radius `p₁` and real `s ∈ [0,1]`,
`∑_b ∑_{Y ∈ 𝒟_b} −β · decMarkCorr_b … Y … s (restr x) = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_decMarkCorr_physical_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D' : BgData S₀.G' N)
    (hDh : ∀ y i, D'.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D')
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = S₀.withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ T.m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (CTorus d L N₁ T.m₁ (k + 1))}
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (x : S.E) (hx : ‖x‖ ≤ p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        -(S.β : ℂ) * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b)
          (S.blockU z) Y p₁ hSp (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hSp).restr x) =
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  subst hϱ
  obtain rfl : S₀ = T.step k hk N₁ ν β p₁ := hS₀
  subst hS
  have hxρ : ∀ u, ‖x u‖ ≤ p₁ := fun u => (norm_le_pi_norm x u).trans hx
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; exact hs.2
  have hrad := markedRad_slice_lt_fromTowerG T D hp (u := (s : ℂ)) (by linarith)
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, ∀ u : ℂ, f u = deriv (fun t : ℂ =>
      ((T.step k hk N₁ ν β p₁).withDatum D' hDh).VkC
        (((T.step k hk N₁ ν β p₁).withDatum D' hDh).psi0C +
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).markedTangentC z u t x) +
      (1 / 2) * deltaForm (((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG.precedes
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG' (le_refl (k + 1)))
        (compWeight L ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a₁)
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν
        (bgMultC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).G'
          (compWeight L ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a₁)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν (bgC0 d L N)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).D')
        (bgFieldC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).G'
          (compWeight L ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a₁)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν (bgC0 d L N)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).D')
        (liftC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG'
          (((T.step k hk N₁ ν β p₁).withDatum D' hDh).markedTangentC z u t x))) 0 :=
    ⟨_, fun _ => rfl⟩
  have hT := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_decMarkCorr_eq_taylor1_of_mark z F₁ Sol
    hP hp le_rfl hSp D.core.δ₁_pos hD x hxρ (U := 17 / 16) (by norm_num) f
    (fun u hu => mark_eq_deriv_blockEnergy_fromTowerG T D hβ hp rfl (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD rfl x hx z f hf hu)
    hrad (by linarith)
  rw [fderiv_mask_corrected_total_fromTowerG T D hβ hp rfl (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD rfl x hx z hs f hf, ← hT,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

/-- **The rooted physical identity for the corrected marks at every scale of the tower** (zero
class).  Under the hypotheses of `sum_decMarkCorr_physical_fromTower`, with the terms
`decMarkCorrTerm`, `T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`, of the pairs
`(F₁ b, Sol b)`:
`∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′ = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_markedOutDec_decMarkCorr_physical_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D' : BgData S₀.G' N)
    (hDh : ∀ y i, D'.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D')
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = S₀.withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ T.m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (CTorus d L N₁ T.m₁ (k + 1))}
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (x : S.E) (hx : ‖x‖ ≤ p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
          (S.blockU z) p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hSp).restr x)) Y' =
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  subst hϱ
  obtain rfl : S₀ = T.step k hk N₁ ν β p₁ := hS₀
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; exact hs.2
  have hrad : (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t := by
    subst hS
    exact markedRad_slice_lt_fromTowerG T D hp (u := (s : ℂ)) (by linarith)
  have hΘ : rawOf S.D' ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t := by
    subst hS
    exact ⟨D', hD, rfl⟩
  rw [S.sum_markedOutDec_eq_sum_decMarkCorr z F₁ Sol hP hp le_rfl hSp D.core.δ₁_pos hΘ hrad
    ((S.blockSplit m₀ hSp).restr x) (-(S.β : ℂ)) _
    (fun b Y => deriv_decMarkCorrTerm S F₁ Sol p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ) _ b Y)]
  exact sum_decMarkCorr_physical_fromTowerG T D hβ hp rfl (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS hSp z F₁ Sol hP x hx hs

/-- **The rooted physical identity for the corrected marks at every scale of the tower, almost
everywhere** (zero class).  Under the hypotheses of `sum_decMarkCorr_physical_fromTower` on the
pairs, for real `s ∈ [0,1]` and almost every hat field `x` of the fluctuation measure `ν_{p₁}`,
`DΦ₁(s ψ')[M_z ψ'] = ∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′`, with the terms `decMarkCorrTerm`,
`T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`. -/
theorem ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) (hβ : 0 < β) (hp : 0 < p₁) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D' : BgData S₀.G' N)
    (hDh : ∀ y i, D'.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D')
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = S₀.withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ T.m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (CTorus d L N₁ T.m₁ (k + 1))}
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              Sol (S.blockU z) p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ)
              ((S.blockSplit m₀ hSp).restr x)) Y' := by
  subst hϱ
  obtain rfl : S₀ = T.step k hk N₁ ν β p₁ := hS₀
  have hpS : S.p₁ = p₁ := by subst hS; rfl
  filter_upwards [S.ae_norm_nuFl hSp] with x hx
  have hxn : ‖x‖ ≤ p₁ :=
    (pi_norm_le_iff_of_nonneg hp.le).2 fun u => by rw [← hpS]; exact (hx u).le
  exact (sum_markedOutDec_decMarkCorr_physical_fromTowerG T D hβ hp rfl (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS hSp z F₁ Sol hP x
    hxn hs).symm

end Balaban.Inhabited
