/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomCanonicalData
public import Balaban.Fluctuation.StepTaylorComplex

/-!
# The exact shifted old-spin datum in the level-site tube

The raw chart test is written on the affine line supplied by `dataUC_psiAtCc_eq_lineAt`.
The conclusion uses the chosen datum of `psiAtCc`, its canonical composed field, and an
arbitrary class domain. Thus the class mass may be the inherited term's birth mass.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.Fluctuation Balaban.SmallField.GsSpec Balaban.SmallField.Def6

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {e ε s θh : ℝ}

/-- The strict raw chart test on the affine fluctuation line supplies `XiCData` for the
shifted old-spin datum itself. -/
theorem StepSetting.xiCData_psiAtCc_of_line_chart
    (z : ℂ) (x : S.E)
    (hraw : rawOf ((S.dataUC S.psi0C).lineAt (S.rayDatumC x) z) ∈
      XiCRaw (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 e) :
    XiCData (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 e
      (S.dataUC (S.psiAtCc z x)) := by
  have hraw' : rawOf (S.dataUC (S.psiAtCc z x)) ∈
      XiCRaw (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 e := by
    rw [S.dataUC_psiAtCc_eq_lineAt]
    exact hraw
  obtain ⟨D, hD, hEq⟩ := hraw'
  have hDatum : S.dataUC (S.psiAtCc z x) = D := BgData.eq_of_raw hEq
  rw [hDatum]
  exact hD

/-- P1 (3.107) and the anisotropic tube for the actual shifted old-spin datum. The only
class-domain input is membership of the pulled-back field and its constant centre; it may be
instantiated at any class mass. -/
theorem StepSetting.psiAtCc_dataHypAniso_of_line_chart
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (H' : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) j (Nat.lt_succ_of_le hjk).le)
      (stepG d L N₁ m₁ k ϱ))
    (ha₁ : 0 < S.a₁) (hs : 0 < s) (hs1 : s ≤ 1)
    (hjs : (L : ℝ) ^ j = s * (L : ℝ) ^ (k + 1))
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) j (Nat.lt_succ_of_le hjk).le)
      (stepG d L N₁ m₁ k ϱ) s)
    (hcol : ∀ w ∈ collar (levelGS (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j (Nat.lt_succ_of_le hjk).le),
      w ∈ (stepG d L N₁ m₁ k ϱ).Ω 1 ∧
        1 ≤ s * (stepG d L N₁ m₁ k ϱ).spacing w)
    (hsmall : (4 * d + 6) * (xiC1 d * e) ≤ 1)
    (hc1 : xiC1 d * e ≤ bgC1 d L N)
    (z : ℂ) (x : S.E)
    (hraw : rawOf ((S.dataUC S.psi0C).lineAt (S.rayDatumC x) z) ∈
      XiCRaw (stepG d L N₁ m₁ k ϱ) S.a S.ν (k + 1) 1 e)
    (hθh0 : 0 < θh) (hθh1 : θh < 1)
    (hν : 0 < S.ν * ((L : ℝ) ^ j) ^ 2)
    (hτ1 : scaledC0 d * s ≤ 1)
    (hντ : S.ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * s) ^ 2)
    (hζ1 : xiC1 d * e ≤ 1 / 200) (hee : e ≤ ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (y : CTorus d L N₁ m₁ (k + 1)) (ψ : Site d → Spin N) (b : Spin N),
        (∀ v, ψ v = composeField
          (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) j (Nat.lt_succ_of_le hjk).le)
          (stepG d L N₁ m₁ k ϱ) S.a
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
            (S.dataUC (S.psiAtCc z x)))
          (S.dataUC (S.psiAtCc z x)).Ψ
          (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v)) →
        b = (((S.ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) •
          (S.dataUC (S.psiAtCc z x)).h y) →
        ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
          (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom →
          DataHypAniso Dom (S.ν * ((L : ℝ) ^ j) ^ 2)
            (16 * scaledC0 d * xiC1 d * s) ε
            (xiSigma d L N B θh * s ^ (2 - θh) * e) ψ b := by
  exact xiCData_dataHypAniso_of_levelGS_canonical hd hL hj1
    (Nat.lt_succ_of_le hjk) H' hprec ha₁ hs hs1 hjs hgap hcol hsmall hc1
    (StepSetting.xiCData_psiAtCc_of_line_chart S z x hraw)
    hθh0 hθh1 hν hτ1 hντ hζ1 hee

end Balaban.SmallField
