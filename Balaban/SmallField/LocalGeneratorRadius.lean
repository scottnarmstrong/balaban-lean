/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorRestriction
public import Balaban.SmallField.XiProps
import Mathlib.Tactic.Linarith

/-!
# Linear radius loss for restriction to a local generating set

In the massless case the level of the norm test is immaterial. The data estimate (Ξ1)
and the data-to-chart estimate (D2) give a local radius proportional to the ambient
chart radius. The coefficient is explicit and exceeds one.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]
  {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {hsep : bgR0 d L ≤ minSep L (L ^ m₁)} {ϱhi : ℝ}
  {A : ℕ → ℝ} {εamb εloc : ℝ}

/-- At zero background mass the radius test is independent of the level. -/
theorem xiC_zero_level (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱhi)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Fld d L N₁ m₁ k N}
    (h : XiC G A 0 j 1 εamb Ψ₀ h₀ Ψ'' h'') :
    XiC G A 0 k 1 εamb Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hσ, hε, Dr, Dc, ⟨hR, hUD, hBR⟩, hC, hU, hBC⟩ := h
  refine ⟨hσ, hε, Dr, Dc, ⟨hR, hUD, ?_⟩, hC, hU, hBC⟩
  exact { hBR with hnorm := by simpa [zero_mul] using hBR.hnorm }

/-- Massless ambient chart data recomputed on `localB` have a radius linear in the
ambient chart radius. The data radius is `xiC1 d * εamb` (P3 (Ξ1)); the loss
`(2 K₁+2) xiC1 d` is the data-to-chart estimate (D2). -/
theorem localB_xiDom_massless_linear (hj1 : 1 ≤ j)
    (Hamb : BgHyp d L k ϱhi A 0)
    (Hloc : BgHyp d L k (bgR0 d L) A 0)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * εamb) ≤ 1)
    (hcap0 : xiC1 d * εamb ≤ bgC0 d L N)
    (hcap1 : xiC1 d * εamb ≤ bgC1 d L N)
    (hbudget : (2 * bgK1 d L N + 2) * (xiC1 d * εamb) ≤ εloc)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hAmb : XiDom
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱhi) j hj)
      A 0 j εamb Ψ h) :
    XiDom (localB j hj X hsep) A 0 j εloc Ψ h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hXi⟩ := hAmb
  have hεpos : 0 < εamb := hXi.2.1
  have hXiTop := xiC_zero_level (G := levelGS j hj) hXi
  have hData := xiC_one_subset Hamb hsmall hXiTop
  obtain ⟨_, _, Dr, Dc, hXR, hC, hU, hBC⟩ := hXi
  have hc1 : 0 < xiC1 d := lt_of_lt_of_le zero_lt_one (one_le_xiC1 d)
  have hδpos : 0 < xiC1 d * εamb := mul_pos hc1 hεpos
  have hmass : (0 : ℝ) * ((L : ℝ) ^ k) ^ 2 *
      (xiC1 d * εamb) ^ 2 ≤ (xiC1 d * εamb) ^ 2 := by
    simpa only [zero_mul] using sq_nonneg (xiC1 d * εamb)
  have hLoc : XiCData (localB j hj X hsep) A 0 j 1 εloc
      (localBRestrict (X := X) (hsep := hsep) hj1 Dc) := by
    apply localB_xiCData_restrict hj1 Hloc (le_refl 0) hδpos le_rfl hcap0 hcap1 hmass
    · nlinarith [hbudget]
    · exact ⟨Ψ₀, h₀, Ψ'', h'', hData, hC⟩
  refine localB_xiDom_of_xiCData_one le_rfl hLoc (fun x hx i => ?_)
    (fun x hx i => ?_)
  · rw [localBRestrict_Ψ hj1 Dc hx]
    rw [hΨ x i, hC.1 x ((mem_dataSites _).2
      (Or.inl (localB_dataSites_subset_levelGS_omega_one hj1 hj hx))) i]
  · rw [localBRestrict_h hj1 Dc hx]
    rw [hh x i, hC.2 x (by simp [levelGS, hj1]) i]

/-- The massless chart comparison in the existing low-index field-domain interface. -/
theorem localB_fieldDom_massless_linear (hj1 : 1 ≤ j)
    (Hamb : BgHyp d L k ϱhi A 0)
    (Hloc : BgHyp d L k (bgR0 d L) A 0)
    {εambSeq εlocSeq : ℕ → ℝ}
    (hsmall : (4 * d + 6) * ((2 * d + 1) * εambSeq j) ≤ 1)
    (hcap0 : xiC1 d * εambSeq j ≤ bgC0 d L N)
    (hcap1 : xiC1 d * εambSeq j ≤ bgC1 d L N)
    (hbudget : (2 * bgK1 d L N + 2) * (xiC1 d * εambSeq j) ≤ εlocSeq j)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hAmb : (xiFieldDom A 0 εambSeq : FieldDom d L N₁ m₁ k N ϱhi).dom j
      (levelGS j hj) Ψ h) :
    (xiFieldDom A 0 εlocSeq : FieldDom d L N₁ m₁ k N (bgR0 d L)).dom j
      (localB j hj X hsep) Ψ h :=
  localB_xiDom_massless_linear hj1 Hamb Hloc hsmall hcap0 hcap1 hbudget hAmb

/-- The displayed linear-loss bound cannot fit into the same positive class radius. -/
theorem massless_linear_budget_not_same (hε : 0 < εamb) :
    ¬ (2 * bgK1 d L N + 2) * (xiC1 d * εamb) ≤ εamb := by
  have hK : 0 < bgK1 d L N := bgK1_pos d L N
  have hc : 1 ≤ xiC1 d := one_le_xiC1 d
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hε.le]

end Balaban.SmallField.GsSpec
