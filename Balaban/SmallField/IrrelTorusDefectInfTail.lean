/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectInfSum

/-!
# The filed term of one infinite shape

For a polymer of `T∞` containing the origin, `T_X + Φ_X` of the infinite-volume lifted family is
bounded in the Cauchy form `C E₀ (1 + d_∞)^4 e^{-κ d_∞}` (`IsSFFamily.norm_filed_inf_le`), with
the linear block count `card_le_dInf` of the shape.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- The linear block count of an infinite shape. -/
theorem card_le_dInf (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    (X'.card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d * (1 + dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hcard := card_le_good (P := P) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk
    (torusSeq_dvd P.m₀ n) hn.1 hn.2
  have hseq : sizeJ (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X') =
      sizeSeq L m₁ k P.m₀ j X' n := rfl
  rw [hseq] at hcard
  have hs := sizeSeq_le_dInf hjk hn
  have hH : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  exact hcard.trans (mul_le_mul_of_nonneg_left (by linarith) hH)

/-- **The filed term of one infinite shape in the Cauchy form.** -/
theorem IsSFFamily.norm_filed_inf_le (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (h0 : (0 : Site d) ∈ X') (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom (nuIdeal L k (ν k) j) σ ε K₂ ψ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) X' ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X' ψ‖ ≤
      (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2)) *
        (P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') * (1 + dInf L m₁ k P.m₀ j X') ^ 4) := by
  have hP := hF.premisesTermAnisoInf hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hn.hκ hne
  have hr := (hF.anisoRadiusOK hn.hsmall i₀).1
  have hmem : X' ∈ (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)).polys := ⟨h0, hX⟩
  have han := (hP.analytic X' hmem).mono polyAniso_subset_tubeAniso
  have hM := fun c hc => hP.bdd_tube X' hmem c (polyAniso_subset_tubeAniso hc)
  have hdiam : ∀ x ∈ X', ((Balaban.SmallField.l1 x : ℕ) : ℝ) ≤ diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') := by
    intro x hx
    rw [Balaban.SmallField.l1_cast]
    exact hP.diam X' hmem x hx
  have hcard := card_le_dInf (P := P) hn.hjk hX
  obtain ⟨n, hgood⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have hd0 := dInf_nonneg hn.hjk hgood
  have hH : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  exact norm_ttw_add_phitw_le_of_data (i₁ := i₁) dat hσ hσ1 hε hεΛ hτ hr han hM hdiam
    (by linarith) hH hcard

end Balaban.SmallField.Def6
