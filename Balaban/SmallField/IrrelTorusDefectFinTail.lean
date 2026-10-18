/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectFiledId
public import Balaban.SmallField.IrrelTorusDefectCauchy

/-!
# The filed term of one finite shape

At the origin, for a shape of the lifted family, `T_X + Φ_X` of the pulled-back one-polymer family
is bounded in the Cauchy form `C E₀ (1 + d_j)^4 e^{-κ d_j}` with `d_j = sizeJ`
(`norm_filed_fin_le`). The linear block count `liftPolys_card_le` and the path bound of the
polymer give the constant.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}

/-- **The filed term of one finite shape in the Cauchy form**: at the origin, for a shape of the
lifted family, `T_X + Φ_X` of the pulled-back one-polymer family is bounded by
`C E₀ (1 + d_j)^4 e^{-κ d_j}`, `d_j = sizeJ`. -/
theorem norm_filed_fin_le (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X' : Finset (Site d)}
    (hX' : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ Λ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (dat : DataHypAniso Dom ν σ ε K₂ ψ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ‖Ttw (⟨{X'}, fun _ => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'),
        fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
          Tm.E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
            (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - 0))
            (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ ν X' ψ b +
      Phitw (⟨{X'}, fun _ => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'),
        fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
          Tm.E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
            (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - 0))
            (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ i₁ ν X' ψ‖ ≤
      (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2)) *
        (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) *
          (1 + sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) ^ 4) := by
  obtain ⟨h0, hnw, hpd⟩ := hX'
  have hy : Aligned (L ^ j) (0 : CTorus d L N₁ m₁ k) := fun μ => by simp
  have hyX : (0 : CTorus d L N₁ m₁ k) ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' :=
    zero_mem_Ypoly h0
  have hS : ∀ z ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X',
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - 0) ∈ X' := fun z hz => by
    rw [sub_zero]
    exact hz
  have hS' : ∀ s ∈ X', ∃ x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X',
      Aligned (L ^ j) x ∧ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - 0) = s := by
    intro s hs
    refine ⟨ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s, ?_, aligned_ibase hjk s, ?_⟩
    · show unlift j (ibase j s) ∈ X'
      rw [unlift_ibase hjk (hnw s hs)]
      exact hs
    · simpa only [sub_zero] using unlift_ibase hjk (hnw s hs)
  have hP := premisesTermAniso_centred hcl hBg hν hμν hνb hj1 hjk hy hpd hyX hS hS' hne hrad
  have hmem : X' ∈ ({X'} : Set (Finset (Site d))) := Set.mem_singleton X'
  have han := (hP.analytic X' hmem).mono polyAniso_subset_tubeAniso
  have hM := fun c hc => hP.bdd_tube X' hmem c (polyAniso_subset_tubeAniso hc)
  have hdiam : ∀ x ∈ X', ((l1 x : ℕ) : ℝ) ≤ diamA d L P.m₀ m₁ *
      (1 + sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) := by
    intro x hx
    rw [l1_cast]
    exact hP.diam X' hmem x hx
  have hcard := liftPolys_card_le hjk hN ⟨h0, hnw, hpd⟩
  have hs0 : 0 ≤ sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') :=
    treeLenCovOne_nonneg _ _ _
  have hH : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hr := hrad.1
  have h := norm_ttw_add_phitw_le_of_data (i₁ := i₁) dat hσ hσ1 hε hεΛ hτ hr han hM hdiam
    (by linarith) hH hcard
  exact h

end Balaban.SmallField.Def6v2
