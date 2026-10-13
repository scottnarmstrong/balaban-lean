/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedTwoMarkLocal
public import Balaban.Inhabited.FanChainWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Instance of the decoupled marked block expansion with mark-locality at the zero-class witness step

`vblock_expansion_hat_marked_scaled_two` (`MarkedTwoMarkLocal`) applies at the zero-class witness
step of `FanChainWitness`, with the hypotheses discharged exactly as in `markedVBlockDec_instance`:
for every block `z` and every mask `Zm`, `MarkedBlockExpansionDecTwo` holds, and the radius set of
marks contains the closed bidisc `|um| ≤ 2`, `|tm| ≤ t₁` with `t₁ > 0`.  The hypotheses of clauses 7
and 8 are satisfiable at the witness: for `Zm = ∅` every set `Y` has no site with unit point in `Zm`
(`noUnitPt_empty`), so clause 7 is a statement about every domain.  The witness step has
`X₁ = univ`, so every domain of `polyDom` contains all sites; for a non-empty mask no domain of the
expansion misses the mask, and clauses 7 and 8 are then non-trivial only for sets `Y` outside
`polyDom` (for the empty mask they say that the term does not depend on `tm`, which is
`deriv_evTerm_marked_empty`).  This proves nothing about general classes or the physical model.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Matrix Balaban.Inhabited.LevelStep

set_option hygiene false in
/-- Local tactic: the tower data of `tower_core_fixed` and `tower_C_items` shared by the instances
(names `m₁ c BG κ t c₂ BG₂ κdec κ0 δc δ hC hMX hdm hα hsmX hκpos β₀t hβ₀t hitems`). -/
local macro "fan_setup" : tactic => `(tactic| (
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  have hκpos : 0 < κ := by
    have : 0 < κdec := by linarith
    have h5 : (0 : ℝ) < 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec := by positivity
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c))

set_option quotPrecheck false in
/-- The top level generating set of the witness step. -/
local notation "Gw[" m "," b "," e "]" => (wStep m b e).G'
set_option quotPrecheck false in
/-- The factor `cc = β_k^{-1/2}` of the witness step. -/
local notation "ccw[" m "," b "," e "]" => ((((wStep m b e).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))

open Classical in
/-- **Instance of `vblock_expansion_hat_marked_scaled_two` at the witness step**: for every block `z`
and mask `Zm` the conclusion `MarkedBlockExpansionDecTwo` holds on the whole torus, and the radius set
of marks contains the bidisc `|um| ≤ 2`, `|tm| ≤ t₁` for some `t₁ > 0`. -/
theorem markedVBlockDecTwo_instance :
    ∃ (m₁ : ℕ) (BG BG₂ κ κdec t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₁ : ℝ, 0 < t₁ ∧
        (2 + t₁) * markedRad 3 3 2 1 1 κ (pLog 1 2 β) ccw[m₁, β, δ] < t ∧
        ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))
          (Zm : Finset (unitPts Gw[m₁, β, δ])),
          MarkedBlockExpansionDecTwo 2 (Hm m₁ (rhoSep m₁)) (wStep m₁ β δ).hG' ccw[m₁, β, δ] 1 nuW BG BG₂
            κ t t κdec (pLog 1 2 β) Zm (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) 1 1
            ({0} : Set (CTorus 3 3 9 m₁ (1 + 1))) z := by
  classical
  fan_setup
  refine ⟨m₁, BG, BG₂, κ, κdec, t, δ, β₀t, hβ₀t, ht0, hκpos, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  set p₁ := pLog 1 2 β with hp₁def
  set cψ := towerCpsi κ t β with hcψdef
  set W : ℝ := Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((hatStep m₁ β p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) with hW
  have ha : 0 < compWeight 3 (1 : ℝ) 1 :=
    lt_of_lt_of_le (by norm_num) (hC.HBp.weights 1 le_rfl (by norm_num)).1
  have hCs := covSupConstC_nonneg (N := 2) (d := 3) (L := 3) (by norm_num) (by norm_num) ha κ
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWc : W * cψ < t := by rw [hW]; nlinarith [hδ₁]
  have hrad := fanChain_radius_real hcψ0 hp (r := towerR κ t β p₁) rfl hr0.le hW0 hWc
    (t₁ := 8 * p₁ / cψ) rfl
  have ht₁0 : 0 < 8 * p₁ / cψ := by positivity
  refine ⟨8 * p₁ / cψ, ht₁0, ?_, fun z Zm => ?_⟩
  · have e : markedRad 3 3 2 1 1 κ p₁ ccw[m₁, β, δ] = W * p₁ := by
      rw [hW]; simp only [markedRad]; ring
    rw [e]; exact hrad
  · exact vblock_expansion_hat_marked_scaled_two hC le_rfl isLevel_Hm (wStep m₁ β δ).hG' _ hp.le Zm
      hMX hdm hα hsmX (j := 1) (m₀ := 1) (X := Xr) (𝒦X := {0}) (X₁f := Finset.univ)
      covSetup (by rw [Finset.coe_univ]; exact X1_eq_univ.symm) hatConn
      (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hopt treeLen_zero hκ0 hκdec
      (by exact_mod_cast hκ) h1 hlog z
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (blockMargin_univ fun x _ _ => mem_some_intBox h4 x)

end Balaban.Inhabited
