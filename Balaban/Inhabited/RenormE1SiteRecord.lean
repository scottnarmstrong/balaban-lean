/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CoeffFamilyLocExp
public import Balaban.Inhabited.RenormHalfDetOnly
public import Balaban.Inhabited.E1CoeffFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked energy at the renormalized datum as a localized expansion on site domains

For the step `S` of a tower with renormalization data `R` and an abstract coefficient family `c`
with analyticity, exact locality on `sitesOf C`, the bound, the support and the value identity at
every chart datum with constant field, the physical marked energy of the step at the renormalized
datum is a localized expansion on the fibre `D.h = h₀` over the site sets, at class radius `t / 2`.

Nothing is assumed about the tower's own family; the locality is a hypothesis on `c`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

open Classical in
/-- **Conditional marked site record.**  Given a coefficient family with exact locality on
`sitesOf T` (hypothesis `hloc`) and the stated analyticity, bound, support and value hypotheses, the
marked energy at the renormalized datum has a localized expansion on site domains, on the fibre of
constant field `h₀`.  The tower's family (`e1CoeffFamily_value_fromTower`) supplies every hypothesis
except `hloc`, which it has only in the thick form. -/
theorem renE1_siteRecord_of_family {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    {κ B : ℝ} (hB : 0 ≤ B)
    (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))))
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁)
      (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C) :
    ∃ term, IsLocExp (N := 2) (R.toStepTower.step k hk N₁ ν β p₁).G'
      (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (R.toStepTower.step k hk N₁ ν β p₁).G' 1) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
          (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E1locC
            (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0)
      term := by
  have h3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨P, hP⟩ := exists_rawProj (N := 2) (R.toStepTower.step k hk N₁ ν β p₁).G'
  have h := isLocExp_of_coeffFamily_renTheta_tower R k hk N₁ hν0 hν β p₁ (m₀ := 1) h3 hB c han
    hloc hbd hsupp 0 (by simp [l1Ball]) P hP
  have h' := h.mono_dom (Dom' := fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
    (fun D hD => hD.1)
  refine ⟨_, { h' with sum_eq := ?_ }⟩
  intro D hD ξ hξ
  have hx := R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD.1 ξ hξ
  rw [dite_eq_left_of_eq_true (eq_true hD.2)]
  rw [hval (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD.2 hx]
  exact h'.sum_eq D hD ξ hξ

/-- **Bridge: the determinant summand at the renormalized datum.**  For a determinant record `E`
at chart radius `2 t`, a fibre datum `D` of the chart of radius `t / 2` and `‖ξ‖ < r₀`, the sum of
the terms of `E z` at the renormalized datum is `-½ ∑ tr 𝕃` of the step with that datum. -/
theorem renE0θ_det_eq_logAC {κmin : ℝ} (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t) (towerDetRate R.κ) (towerDetConst R.κ))
    (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))))
    (D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
    (hD : XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D)
    (hDh : ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < R.r₀) :
    renE0θ_det (R.t / 2) E z D ξ =
      -(1 / 2 : ℂ) * ∑ y ∈ ((R.toStepTower.step k hk N₁ ν β p₁).withDatum (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hDh).blockU z,
        ∑ i : Fin 2, ((R.toStepTower.step k hk N₁ ν β p₁).withDatum (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hDh).logAC (y, i) (y, i) := by
  have hx := R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ
  have hx2 := xiCData_mono_radius zero_le_one (by linarith [R.t_pos] : R.t ≤ 2 * R.t) hx
  exact ((E z).atDatum (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hDh hx2).sum_eq.symm

open Classical in
/-- **Conditional physical `E₀` site record** (conditional on exact locality `hloc` of the mark
family, as in `renE1_siteRecord_of_family`).  The determinant record (`renormDetOnlyZeroM_onFibre_half`) and the marked record
(`renE1_siteRecord_of_family`) at the common rate `min (3/2 κ_dec) κ`, summed over the union of the
two index families; the value function is `E₀^{(k+1)}(z)` of the step with the renormalized
datum. -/
theorem renE0_siteRecord_of_family {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    {κ B : ℝ} (hB : 0 ≤ B)
    (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))))
    (c : physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.toStepTower.step k hk N₁ ν β p₁)
      (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁ (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C) :
    ∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
      (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ))
      R.r₀
      (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪
        Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) κ)
      (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
          Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + B)
      (fun D ξ => if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
        then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
          (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
            (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0)
      term := by
  obtain ⟨E, F, Fcut, -, -, -, -, hE', -, -, -⟩ :=
    renormDetOnlyZeroM_onFibre_half R hR k hk N₁ h3N hN hν0 hν β p₁ Set.univ
  obtain ⟨term₁, h₁⟩ := hE' z
  obtain ⟨term₂, h₂⟩ := renE1_siteRecord_of_family R k hk N₁ h3N hν0 hν β p₁ hB z c han hloc hbd
    hsupp hval
  have hκ0 : 0 ≤ R.κdec := by have := R.κdec_lower; have := R.κ0_nonneg; linarith
  have hH0 : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) * Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) := by
    have hconst := towerDetConst_nonneg R.toStepTower
    have : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) := by
      unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
    positivity
  have h₁' := h₁.mono_rate (κ' := min (3 / 2 * R.κdec) κ) (min_le_left _ _) hH0
    (fun Y _ => renDY_nonneg Y)
  have h₂' := h₂.mono_rate (κ' := min (3 / 2 * R.κdec) κ) (min_le_right _ _) hB
    (fun Y _ => renDY_nonneg Y)
  have h := h₁'.add_union h₂' hH0 hB
  refine ⟨_, { h with sum_eq := ?_ }⟩
  intro D hD ξ hξ
  have hb := renE0θ_det_eq_logAC R k hk N₁ hν0 hν β p₁ E z D hD.1 hD.2 ξ hξ
  refine Eq.trans ?_ (h.sum_eq D hD ξ hξ)
  rw [dite_eq_left_of_eq_true (eq_true hD.2), hb, dite_eq_left_of_eq_true (eq_true hD.2)]
  rfl

end Balaban.Inhabited
