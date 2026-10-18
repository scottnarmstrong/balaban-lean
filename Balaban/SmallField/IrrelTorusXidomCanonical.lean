/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSecondDiffData
public import Balaban.SmallField.IrrelTorusXidomChart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The canonical composition of a chosen complex chart datum

The `XiCData` carrier fixes the complex background field. This module keeps that field visible
through the scaled-composition argument, so the pulled-back second-difference estimate applies
to the same function as the anisotropic data constructor.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.GsSpec Balaban.SmallField.Def6

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
  {a₁ ν s e : ℝ} {D : BgData G' N}

/-- A chosen chart datum supplies the scaled source witness with its *canonical* complex
background field. The real background datum remains existential, as required by `XiC`. -/
theorem xiCData_scaledComposition_canonical
    (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le) G')
    (ha₁ : 0 < a₁) (hs : 0 < s) (hs1 : s ≤ 1)
    (hjs : (L : ℝ) ^ j = s * (L : ℝ) ^ k)
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le) G' s)
    (hcol : ∀ z ∈ collar (levelGS (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le), z ∈ G'.Ω 1 ∧ 1 ≤ s * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * e) ≤ 1)
    (hD : XiCData G' (compWeight L a₁) ν k 1 e D) :
    ∃ Ψ0 h0 Ψ'' h'' φr,
      RealizesC D Ψ0 h0 Ψ'' h'' ∧
      HypS (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k) (ϱ := ϱ) j hjk.le) G' a₁ ν
        (xiC1 d * e) (xiC1 d * e) (xiC1 d * e) s j
        Ψ0 h0 Ψ'' h'' φr
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) := by
  obtain ⟨Ψ0, h0, Ψ'', h'', hX, hReal⟩ := hD
  obtain ⟨-, he, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  have hDc : Dc = D := BgData.eq_of_realizesC hC hReal
  subst Dc
  have hc1 := one_le_xiC1 d
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC1a : 2 * (2 * (d : ℝ) + 1) ≤ xiC1 d := by
    unfold xiC1
    nlinarith
  have hsmall' : (4 * d + 6) * ((2 * d + 1) * e) ≤ 1 := by
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith : (2 * (d : ℝ) + 1) ≤ xiC1 d) he.le)
      (by positivity)
  have hX : XiC G' (compWeight L a₁) ν k 1 e Ψ0 h0 Ψ'' h'' :=
    ⟨one_pos, he, Dr, D, hXr, hC, hDcU, hb⟩
  have hP := xiC_one_subset H' hsmall' hX
  have hXr' := hXr
  obtain ⟨hR, _, hbr⟩ := hXr
  set η := xiC1 d * e with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    nlinarith [mul_nonneg hd hηpos.le]
  have hEta : xiEta d 1 e ≤ η := by
    unfold xiEta
    rw [hη]
    nlinarith [mul_le_mul_of_nonneg_right
      (by linarith : (2 * (d : ℝ) + 1) ≤ xiC1 d) he.le]
  have hEta2 : 2 * xiEta d 1 e ≤ η := by
    unfold xiEta
    rw [hη]
    nlinarith [mul_le_mul_of_nonneg_right hC1a he.le]
  obtain ⟨hφre, _⟩ := xi_unit H' hXr'
  have hfr := fieldBounds_mono (xi_fieldBounds H' one_pos he le_rfl hXr') hEta
  have hfc := fieldBounds_mono (xiC_fieldBounds H' one_pos he le_rfl hXr' hC hDcU hb) hEta2
  let φr := bgField G' (compWeight L a₁) ν Dr
  let φc := bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D
  have hnj : ∀ x ∈
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k) (ϱ := ϱ) j hjk.le).Ω 1,
      (levelGS (ϱ := ϱ) j hjk.le).layerIndex x ≤ j := by
    intro x hx
    rw [levelGS_layerIndex hj1 hjk.le]
  refine ⟨Ψ0, h0, Ψ'', h'', φr, hReal, ?_⟩
  exact {
    prec := hprec, hL := hL, ha₁ := ha₁, hθ0 := hs, hθ1 := hs1,
    hjθ := hjs, hnj := hnj, gap := hgap, hcol := hcol,
    hδ := hηpos, hδη := le_rfl, hηε := le_rfl, hε1 := hη1,
    hsmall := hsmall, hν := H'.mass, hνk := H'.massLe, hPC := hP,
    hφr := hφre,
    hbr := fieldBounds_congr hfr
      (fun x hx => by funext i; simp [psiR, hR.1 x hx i]),
    hmass := fun z => by
      have hh := (hbr.mass z).le
      rw [one_mul] at hh
      exact hh.trans (by nlinarith),
    hbc := fieldBounds_congr hfc (fun x hx => by funext i; simp [psiC]),
    hdiff := fun z => (hb.val z).le.trans (by nlinarith) }

end Balaban.SmallField
