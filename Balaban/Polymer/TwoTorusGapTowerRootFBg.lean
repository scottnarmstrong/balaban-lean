/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexAgree
public import Balaban.Fluctuation.StepComplexSource
public import Balaban.Polymer.TwoTorusGapTowerRootFSource
public import Balaban.Inhabited.StepActivityHatWitnessRay
public import Balaban.LargeField.R.SmallFactorAction

/-!
# The background field of the source term of the tower's step identity (blocker 7)

The source term of the zero-class step identity is `⟨g, φ_k⟩` with `φ_k = bgFieldC (stepG …) S.a S.ν
(bgC0 …) S.psiKdC` (`fcompAtC_zeroClass_psiKdC_eq`).  For real block data of the domain of the
landed step:

* `bgFieldC_psiKdC_eq_restrict`: `φ_k` is the restriction to `Ω₁` of the background field
  `φ_{k+1}(θ)` of the block datum `θ = S.D'` (Lemma 2.2 (b), (2.2));
* `svec_bgFieldC_psiKdC_unitBg`: if `θ` is the constant unit datum `unitBg … (unitVec hN)` (the
  critical datum: all blocks equal to the unit vector `e₀`, external field `e₀`), then `φ_k ≡ e₀`
  on the whole lattice, so the source term is exactly `⟨g, e₀⟩`;
* `fcompAtC_zeroClass_psiKdC_unitBg`: at that datum the source term is exactly `∑ g y i h₀ i`;
* `sqrt_mul_spacing_mul_vn_phiK_sub_le`: for general real data of size `δ'`, the deviation of `φ_k`
  from the external field obeys `√ν ℓ' |φ_k(y) - h(y)| ≤ K₁ δ'` (P2 (1.16)), the only landed bound.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.SmallField.Def6 Balaban.SmallField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **`φ_k` is the restriction of `φ_{k+1}(θ)`.** -/
theorem bgFieldC_psiKdC_eq_restrict (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D') :
    bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKdC =
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (bgField S.G' S.a S.ν S.D') := by
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  obtain ⟨-, hDG, -, -, -, -, hfield, -⟩ :=
    criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU'
  rw [S.psiKdC_eq H hδ'0 hδ' hD'R]
  have h1 : S.psiKd = composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgField S.G' S.a S.ν S.D') S.D' := rfl
  rw [h1, (theorem72_real H hDG).1]
  exact hfield

/-- **At the constant unit datum, `φ_k` is the external field.**  If the block datum is the constant
unit datum `unitBg S.G' hN (unitVec hN)`, then the background field `φ_k` of the critical point is
the constant field `e₀`, and `e₀` is the external field `h₀` of the step, at every site. -/
theorem svec_bgFieldC_psiKdC_unitBg (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
    (hN : 0 < N) (hD : S.D' = unitBg S.G' hN (unitVec hN))
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    svec (stepG d L N₁ m₁ k ϱ)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKdC) y i =
      (S.h₀ i : ℂ) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR S.G' (bgC1 d L N) S.ν (unitBg S.G' hN (unitVec hN)) := by
    rw [← hD]; exact ⟨δ', hδ'0, hδ'c1, hD'R⟩
  have ha : ∀ n, 0 ≤ S.a n := fun n =>
    Balaban.LargeField.compWeight_nonneg (by have := H.hL; omega) ha₁ n
  have hbg : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN := by
    rw [hD]; exact bgField_unitBg_nu S.hG' hN ha H hDU1
  have hy : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 := (S.hG y).1
  rw [S.bgFieldC_psiKdC_eq_restrict ha₁ H hδ'0 hδ' hD'R, svec_of_mem' _ hy, hbg]
  have hh := S.hh₀ y i
  rw [hD, unitBg_h_of_mem S.G' hN _ (S.hG'.Ω_one ▸ Finset.mem_univ _)] at hh
  have : S.h₀ i = unitVec hN i := by exact_mod_cast hh.symm
  rw [this]
  rfl

/-- **The deviation of `φ_k` from the external field, real data.**  For block data of size `δ'`
(`InDomainR S.G' S.ν δ' S.D'`), `√ν ℓ' |φ_k(y) - h₀| ≤ K₁ δ'` at every site `y` (P2 (1.16)); this is
the only landed bound of the deviation: it is a sup bound in the size `δ'` of the datum, with no
decay in a polymer. -/
theorem sqrt_mul_spacing_mul_vn_phiK_sub_le (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
    (y : CTorus d L N₁ m₁ (k + 1)) :
    Real.sqrt S.ν * S.G'.spacing (y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) *
        vn (fun i => svec (stepG d L N₁ m₁ k ϱ)
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKdC) y i - (S.h₀ i : ℂ)) ≤
      bgK1 d L N * δ' := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hy : y ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 := (S.hG y).1
  have hy' : y ∈ S.G'.Ω 1 := (S.hG' y).1
  obtain ⟨φ, α, hs, -, hu, -, -, -⟩ := bg_real H hδ'0 hδ'c1 hD'R
  obtain ⟨hf, -⟩ := bgFieldC_eq hs hu
  have hf' : bgField S.G' S.a S.ν S.D' = φ := by
    rw [← (theorem72_real H ⟨δ', hδ'0, hδ'c1, hD'R⟩).1]; exact hf
  obtain ⟨Ψ, h₁, hP, hΨ, hh⟩ := hD'R
  have hmb := mass_bound_spacing H hδ'0 hδ'c1 hP hΨ hh hs ⟨y, hy'⟩
  have e : ∀ i, svec (stepG d L N₁ m₁ k ϱ)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKdC) y i - (S.h₀ i : ℂ) =
      φ (⟨y, hy'⟩, i) - S.D'.h y i := by
    intro i
    rw [S.bgFieldC_psiKdC_eq_restrict ha₁ H hδ'0 hδ' ⟨Ψ, h₁, hP, hΨ, hh⟩, svec_of_mem' _ hy,
      S.hh₀ y i, ← hf']
    rfl
  simp only [e]
  exact hmb

/-- **At the constant unit datum the source term is exactly `⟨g, h₀⟩`.** -/
theorem fcompAtC_zeroClass_psiKdC_unitBg (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
    (hN : 0 < N) (hD : S.D' = unitBg S.G' hN (unitVec hN)) (g : Fld d L N₁ m₁ (k + 1) N) :
    FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC g =
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i * (S.h₀ i : ℂ) := by
  rw [fcompAtC_zeroClass_psiKdC_eq]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by
    rw [S.svec_bgFieldC_psiKdC_unitBg ha₁ H hδ'0 hδ' hD'R hN hD y i]

end StepSetting

end Balaban.Fluctuation
