/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrRooted
public import Balaban.Inhabited.DecMarkCorrTotalFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical sum identity for the corrected marks at every scale of the shared tower

At the step `(T.step k hk N₁ ν β p₁).withDatum D' hDh` of a scale of a shared tower with
`StepScaleData`, for a family of decoupling pairs given with its clauses (one pair for every
block, the constants `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁` of the tower, any
covers), a root `z`, a hat field `‖x‖ ≤ p₁` and real `s ∈ [0,1]`:

* `markedRad_slice_lt_fromTower`: every first mark `‖u‖ ≤ 17/16` lies in the slice
  `(‖u‖ + 0) · markedRad(p₁) < T.t` of the bidisc of the pairs;
* `sum_decMarkCorr_physical_fromTower`: the sum over the blocks and the labels of
  `−β · decMarkCorr` at the first mark `s` is `DΦ₁(s ψ')[M_z ψ']`;
* `sum_markedOutDec_decMarkCorr_physical_fromTower`: the sum over the bridge family of the rooted
  outputs of the terms `decMarkCorrTerm` is `DΦ₁(s ψ')[M_z ψ']`;
* `ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTower`: the same identity for almost every
  hat field of the fluctuation measure.

The total-mark identity and the corrected mark of the total are the landed
`mark_eq_deriv_blockEnergy_fromTower` and `fderiv_mask_corrected_total_fromTower`.  The base step
is the case `D' = (T.step k hk N₁ ν β p₁).D'` (in the chart by `StepScaleData.xi`).  The pairs are
arguments: the statements apply to the pairs of `corrected_markedOutDec_count_fromTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set Filter
  Topology MeasureTheory

/-- **The first marks of the disc `‖u‖ ≤ 17/16` lie in the slice of the bidisc of the pairs.**
At a scale of the tower, `(‖u‖ + 0) · markedRad(p₁) < T.t` for every `‖u‖ ≤ 17/16`
(`StepScaleData.marked_radius_lt`). -/
theorem markedRad_slice_lt_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁)
    {u : ℂ} (hu : ‖u‖ ≤ 17 / 16) :
    (‖u‖ + ‖(0 : ℂ)‖) * markedRad 3 3 2 k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hr0 := D.r_pos
  have hmem := compWeight_three_mem hk
  have hCs : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) T.κ
  have hmr : 0 ≤ markedRad 3 3 2 k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    unfold markedRad
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg hCs hp.le))
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ hmr) (D.marked_radius_lt hp)
  rw [norm_zero, add_zero]
  nlinarith [hr0, hu]

/-- **The physical sum identity for the corrected marks at every scale of the tower** (zero
class).  Let `(F₁ b, Sol b)` be a pair with the eight clauses for every block `b`, at the step
`S = (T.step k hk N₁ ν β p₁).withDatum D' hDh` with the constants of the tower
(`cc = β_k^{-1/2}`, mask `blockU z`, `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁`).  For
a hat field `‖x‖ ≤ p₁`, the clamp radius `p₁` and real `s ∈ [0,1]`,
`∑_b ∑_{Y ∈ 𝒟_b} −β · decMarkCorr_b … Y … s (restr x) = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_decMarkCorr_physical_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1))}
    {X₁V : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (CTorus 3 3 N₁ T.m₁ (k + 1))}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (x : S.E) (hx : ‖x‖ ≤ p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        -(S.β : ℂ) * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b)
          (S.blockU z) Y p₁ hSp (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hSp).restr x) =
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  subst hS
  have hxρ : ∀ u, ‖x u‖ ≤ p₁ := fun u => (norm_le_pi_norm x u).trans hx
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; exact hs.2
  have hrad := markedRad_slice_lt_fromTower T D hp (u := (s : ℂ)) (by linarith)
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, ∀ u : ℂ, f u = deriv (fun t : ℂ =>
      ((T.step k hk N₁ ν β p₁).withDatum D' hDh).VkC
        (((T.step k hk N₁ ν β p₁).withDatum D' hDh).psi0C +
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).markedTangentC z u t x) +
      (1 / 2) * deltaForm (((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG.precedes
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG' (le_refl (k + 1)))
        (compWeight 3 ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a₁)
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν
        (bgMultC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).G'
          (compWeight 3 ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a₁)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν (bgC0 3 3 2)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).D')
        (bgFieldC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).G'
          (compWeight 3 ((T.step k hk N₁ ν β p₁).withDatum D' hDh).a₁)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).ν (bgC0 3 3 2)
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).D')
        (liftC ((T.step k hk N₁ ν β p₁).withDatum D' hDh).hG'
          (((T.step k hk N₁ ν β p₁).withDatum D' hDh).markedTangentC z u t x))) 0 :=
    ⟨_, fun _ => rfl⟩
  have hT := ((T.step k hk N₁ ν β p₁).withDatum D' hDh).sum_decMarkCorr_eq_taylor1_of_mark z F₁ Sol
    hP hp le_rfl hSp D.core.δ₁_pos hD x hxρ (U := 17 / 16) (by norm_num) f
    (fun u hu => mark_eq_deriv_blockEnergy_fromTower T D hβ hp D' hDh hD rfl x hx z f hf hu)
    hrad (by linarith)
  rw [fderiv_mask_corrected_total_fromTower T D hβ hp D' hDh hD rfl x hx z hs f hf, ← hT,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

/-- **The rooted physical identity for the corrected marks at every scale of the tower** (zero
class).  Under the hypotheses of `sum_decMarkCorr_physical_fromTower`, with the terms
`decMarkCorrTerm`, `T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`, of the pairs
`(F₁ b, Sol b)`:
`∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′ = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_markedOutDec_decMarkCorr_physical_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1))}
    {X₁V : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (CTorus 3 3 N₁ T.m₁ (k + 1))}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (x : S.E) (hx : ‖x‖ ≤ p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
          (S.blockU z) p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hSp).restr x)) Y' =
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; exact hs.2
  have hrad : (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad 3 3 2 k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t := by
    subst hS
    exact markedRad_slice_lt_fromTower T D hp (u := (s : ℂ)) (by linarith)
  have hΘ : rawOf S.D' ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t := by
    subst hS
    exact ⟨D', hD, rfl⟩
  rw [S.sum_markedOutDec_eq_sum_decMarkCorr z F₁ Sol hP hp le_rfl hSp D.core.δ₁_pos hΘ hrad
    ((S.blockSplit m₀ hSp).restr x) (-(S.β : ℂ)) _
    (fun b Y => deriv_decMarkCorrTerm S F₁ Sol p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ) _ b Y)]
  exact sum_decMarkCorr_physical_fromTower T D hβ hp D' hDh hD hS hSp z F₁ Sol hP x hx hs

/-- **The rooted physical identity for the corrected marks at every scale of the tower, almost
everywhere** (zero class).  Under the hypotheses of `sum_decMarkCorr_physical_fromTower` on the
pairs, for real `s ∈ [0,1]` and almost every hat field `x` of the fluctuation measure `ν_{p₁}`,
`DΦ₁(s ψ')[M_z ψ'] = ∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′`, with the terms `decMarkCorrTerm`,
`T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`. -/
theorem ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTower {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleData T k hk N₁ ν β p₁) (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1))}
    {X₁V : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (CTorus 3 3 N₁ T.m₁ (k + 1))}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              Sol (S.blockU z) p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ)
              ((S.blockSplit m₀ hSp).restr x)) Y' := by
  have hpS : S.p₁ = p₁ := by subst hS; rfl
  filter_upwards [S.ae_norm_nuFl hSp] with x hx
  have hxn : ‖x‖ ≤ p₁ :=
    (pi_norm_le_iff_of_nonneg hp.le).2 fun u => by rw [← hpS]; exact (hx u).le
  exact (sum_markedOutDec_decMarkCorr_physical_fromTower T D hβ hp D' hDh hD hS hSp z F₁ Sol hP x
    hxn hs).symm

end Balaban.Inhabited
