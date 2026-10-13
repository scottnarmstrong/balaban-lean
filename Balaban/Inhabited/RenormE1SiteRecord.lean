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
/-- **Conditional marked site record for any step setting whose renormalized datum at class radius
`t / 2` lies in the chart of radius `t` (`hchart`).**  Given a coefficient family with exact locality on
`sitesOf T` (hypothesis `hloc`) and the stated analyticity, bound, support and value hypotheses, the
marked energy at the renormalized datum has a localized expansion on site domains, on the fibre of
constant field `h₀`.  The tower's family (`e1CoeffFamily_value_fromTower`) supplies every hypothesis
except `hloc`, which it has only in the thick form. -/
theorem renE1_siteRecord_of_chart {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {t r : ℝ}
    (hchart : ∀ D : BgData S.G' N, XiCOneReal S.G' S.a S.ν (t / 2) D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S (t / 2) D ξ))
    {κ B : ℝ} (hB : 0 ≤ B)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (c : physParam N (S) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (S)
      (S).a₁ (S).ν t))
    (hloc : ∀ T, ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ θ' ∈ physV (S)
        (S).a₁ (S).ν t,
      physRestrict (sitesOf T) (physIncl N (S) θ) =
        physRestrict (sitesOf T) (physIncl N (S) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (S).G' N)
        (hDh : ∀ y i, D'.h y i = ((S).h₀ i : ℂ)),
      XiCData (S).G' (S).a
        (S).ν (k + 1) 1 t D' →
      ((S).withDatum D' hDh).E1locC
          (zeroClass d L N₁ m₁ k N ϱ) z =
        ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) C) :
    ∃ term, IsLocExp (N := N) (S).G'
      (fun D => XiCOneReal (S).G'
          (S).a (S).ν (t / 2) D ∧
        ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ))
      r
      (Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (S).G' m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ)
        then ((S).withDatum
          (renThetaDatum (S) (t / 2) D ξ) hD).E1locC
            (zeroClass d L N₁ m₁ k N ϱ) z else 0)
      term := by
  obtain ⟨P, hP⟩ := exists_rawProj (N := N) S.G'
  have h := isLocExp_of_coeffFamily_renTheta S hN (t / 2) _ hB c han hloc hbd hsupp 0
    (by simp [l1Ball]) (fun D hD ξ hξ => hchart D hD ξ hξ) P hP
  have h' := h.mono_dom (Dom' := fun D => XiCOneReal S.G' S.a S.ν (t / 2) D ∧
        ∀ x i, D.h x i = (((S).h₀ i : ℝ) : ℂ))
    (fun D hD => hD.1)
  refine ⟨_, { h' with sum_eq := ?_ }⟩
  intro D hD ξ hξ
  have hx := hchart D hD.1 ξ hξ
  rw [dite_eq_left_of_eq_true (eq_true hD.2)]
  rw [hval (renThetaDatum S (t / 2) D ξ) hD.2 hx]
  exact h'.sum_eq D hD ξ hξ


open Classical in
/-- **Conditional marked site record, general tower.**  Given a coefficient family with exact locality on
`sitesOf T` (hypothesis `hloc`) and the stated analyticity, bound, support and value hypotheses, the
marked energy at the renormalized datum has a localized expansion on site domains, on the fibre of
constant field `h₀`.  The tower's family (`e1CoeffFamily_value_fromTower`) supplies every hypothesis
except `hloc`, which it has only in the thick form. -/
theorem StepTowerThetaG.renE1_siteRecord_of_family {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    {κ B : ℝ} (hB : 0 ≤ B)
    (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))))
    (c : physParam N (R.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.step k hk N₁ ν β p₁)
      (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom m₀ (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom m₀ (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.step k hk N₁ ν β p₁).G' N)
        (hDh : ∀ y i, D'.h y i = ((R.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
        (R.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) z =
        ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) C) :
    ∃ term, IsLocExp (N := N) (R.step k hk N₁ ν β p₁).G'
      (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
      R.r₀
      (Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (R.step k hk N₁ ν β p₁).G' m₀) κ B
      (fun D ξ => if hD : ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)
        then ((R.step k hk N₁ ν β p₁).withDatum
          (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E1locC
            (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) z else 0)
      term := by
  exact renE1_siteRecord_of_chart (R.step k hk N₁ ν β p₁) hN
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) hB z c han hloc
    hbd hsupp hval

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
  exact renE1_siteRecord_of_chart (R.toStepTower.step k hk N₁ ν β p₁) h3
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) hB z c han hloc
    hbd hsupp hval

/-- **Bridge: the determinant summand at the renormalized datum, for any step setting.**  For a
determinant record `E` at chart radius `2 t`, a fibre datum `D` of the chart of radius `t / 2` and
`‖ξ‖ < r`, with the renormalized datum in the chart of radius `t` (`hchart`), the sum of the terms
of `E z` at the renormalized datum is `-½ ∑ tr 𝕃` of the step with that datum. -/
theorem renE0θ_det_eq_logAC_of_chart {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) {t r κdet cdet : ℝ} (ht : 0 < t)
    (hchart : ∀ D : BgData S.G' N, XiCOneReal S.G' S.a S.ν (t / 2) D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S (t / 2) D ξ))
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC S 1 z (2 * t) κdet cdet)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (D : BgData S.G' N)
    (hD : XiCOneReal S.G' S.a S.ν (t / 2) D)
    (hDh : ∀ x i, D.h x i = ((S.h₀ i : ℝ) : ℂ))
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r) :
    renE0θ_det (t / 2) E z D ξ =
      -(1 / 2 : ℂ) * ∑ y ∈ (S.withDatum (renThetaDatum S (t / 2) D ξ) hDh).blockU z,
        ∑ i : Fin N, (S.withDatum (renThetaDatum S (t / 2) D ξ) hDh).logAC (y, i) (y, i) := by
  have hx := hchart D hD ξ hξ
  have hx2 := xiCData_mono_radius zero_le_one (by linarith : t ≤ 2 * t) hx
  exact ((E z).atDatum (renThetaDatum S (t / 2) D ξ) hDh hx2).sum_eq.symm

/-- **Bridge: the determinant summand at the renormalized datum, general tower.** -/
theorem StepTowerThetaG.renE0θ_det_eq_logAC {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) {κdet cdet : ℝ}
    (E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.step k hk N₁ ν β p₁) 1 z (2 * R.t) κdet cdet)
    (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))))
    (D : BgData (R.step k hk N₁ ν β p₁).G' N)
    (hD : XiCOneReal (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
      (R.step k hk N₁ ν β p₁).ν (R.t / 2) D)
    (hDh : ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < R.r₀) :
    renE0θ_det (R.t / 2) E z D ξ =
      -(1 / 2 : ℂ) * ∑ y ∈ ((R.step k hk N₁ ν β p₁).withDatum
          (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hDh).blockU z,
        ∑ i : Fin N, ((R.step k hk N₁ ν β p₁).withDatum
          (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hDh).logAC (y, i) (y, i) :=
  renE0θ_det_eq_logAC_of_chart (R.step k hk N₁ ν β p₁) R.t_pos
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) E z D hD hDh ξ hξ

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
  exact renE0θ_det_eq_logAC_of_chart (R.toStepTower.step k hk N₁ ν β p₁) R.t_pos
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) E z D hD hDh ξ hξ

open Classical in
/-- **Conditional physical `E₀` site record from its two parts, for any step setting.**  `h₁` is the
localized expansion of the determinant summand `renE0θ_det (t / 2) E z` on the fibre, and the
chart hypothesis `hchart` is as in `renE1_siteRecord_of_chart`; the marked record
(`renE1_siteRecord_of_chart`) and `h₁` are summed over the union of the two index families. -/
theorem renE0_siteRecord_of_parts {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (hN : L ^ 1 ∣ N₁) {t r κdet cdet κ1 H : ℝ} (ht : 0 < t)
    (hchart : ∀ D : BgData S.G' N, XiCOneReal S.G' S.a S.ν (t / 2) D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S (t / 2) D ξ))
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S 1 z (2 * t) κdet cdet)
    (hH0 : 0 ≤ H)
    {κ B : ℝ} (hB : 0 ≤ B)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (c : physParam N (S) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (S)
      (S).a₁ (S).ν t))
    (hloc : ∀ T, ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ θ' ∈ physV (S)
        (S).a₁ (S).ν t,
      physRestrict (sitesOf T) (physIncl N (S) θ) =
        physRestrict (sitesOf T) (physIncl N (S) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (S)
        (S).a₁ (S).ν t,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (S).G' N)
        (hDh : ∀ y i, D'.h y i = ((S).h₀ i : ℂ)),
      XiCData (S).G' (S).a
        (S).ν (k + 1) 1 t D' →
      ((S).withDatum D' hDh).E1locC
          (zeroClass d L N₁ m₁ k N ϱ) z =
        ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) C)
    (h₁ : ∃ term, IsLocExp (N := N) S.G'
      (fun D => XiCOneReal S.G' S.a S.ν (t / 2) D ∧
        ∀ x i, D.h x i = ((((S).h₀ i : ℝ)) : ℂ)) r
      (renYs (renCube S.G' (X1 S.G' 1 k (fam 1 (blockSite k z)))) S.G' 1
        (X1 S.G' 1 k (fam 1 (blockSite k z))))
      (renDY S.G' 1) κ1 H (renE0θ_det (t / 2) E z) term) :
    ∃ term, IsLocExp (N := N) S.G'
      (fun D => XiCOneReal (S).G'
          (S).a (S).ν (t / 2) D ∧
        ∀ x i, D.h x i = ((((S).h₀ i : ℝ)) : ℂ))
      r
      (renYs (renCube S.G'
          (X1 S.G' 1 k (fam 1 (blockSite k z)))) S.G' 1
          (X1 S.G' 1 k (fam 1 (blockSite k z))) ∪
        Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T))
      (renDY S.G' 1) (min κ1 κ)
      (H + B)
      (fun D ξ => if hD : ∀ x i, D.h x i = ((((S).h₀ i : ℝ)) : ℂ)
        then ((S).withDatum
          (renThetaDatum (S) (t / 2) D ξ) hD).E0locC
            (zeroClass d L N₁ m₁ k N ϱ) z else 0)
      term := by
  obtain ⟨term₁, h₁⟩ := h₁
  obtain ⟨term₂, h₂⟩ := renE1_siteRecord_of_chart S hN hchart hB z c han hloc hbd hsupp hval
  have h₁' := h₁.mono_rate (κ' := min κ1 κ) (min_le_left _ _) hH0
    (fun Y _ => renDY_nonneg Y)
  have h₂' := h₂.mono_rate (κ' := min κ1 κ) (min_le_right _ _) hB
    (fun Y _ => renDY_nonneg Y)
  have h := h₁'.add_union h₂' hH0 hB
  refine ⟨_, { h with sum_eq := ?_ }⟩
  intro D hD ξ hξ
  have hb := renE0θ_det_eq_logAC_of_chart S ht hchart E z D hD.1 hD.2 ξ hξ
  refine Eq.trans ?_ (h.sum_eq D hD ξ hξ)
  rw [dite_eq_left_of_eq_true (eq_true hD.2), hb, dite_eq_left_of_eq_true (eq_true hD.2)]
  rfl

open Classical in
open Classical in
/-- **Conditional physical `E₀` site record, general tower** (conditional on exact locality `hloc` of the mark
family, as in `renE1_siteRecord_of_family`).  The determinant record (`StepTowerThetaG.expE0_det_scale_of_tower_at`) and the marked record
(`renE1_siteRecord_of_family`) at the common rate `min (3/2 κ_dec) κ`, summed over the union of the
two index families; the value function is `E₀^{(k+1)}(z)` of the step with the renormalized
datum. -/
theorem StepTowerThetaG.renE0_siteRecord_of_family {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * R.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    {κ B : ℝ} (hB : 0 ≤ B)
    (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))))
    (c : physParam N (R.step k hk N₁ ν β p₁) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → ℂ)
    (han : ∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV (R.step k hk N₁ ν β p₁)
      (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t))
    (hloc : ∀ T, ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ θ' ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf T) (physIncl N (R.step k hk N₁ ν β p₁) θ') →
        c θ T = c θ' T)
    (hbd : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, IsPolyDom 1 (k + 1) (sitesOf T) → ‖c θ T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsupp : ∀ θ ∈ physV (R.step k hk N₁ ν β p₁)
        (R.step k hk N₁ ν β p₁).a₁ (R.step k hk N₁ ν β p₁).ν R.t,
      ∀ T, c θ T ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ (D' : BgData (R.step k hk N₁ ν β p₁).G' N)
        (hDh : ∀ y i, D'.h y i = ((R.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.step k hk N₁ ν β p₁).G' (R.step k hk N₁ ν β p₁).a
        (R.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      ((R.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
          (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) z =
        ∑ C, c (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus d L N₁ R.m₁ (k + 1) → Fin N → ℂ)) C) :
    ∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
      (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν (R.t / 2) D ∧
        ∀ x i, D.h x i = ((((R.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ))
      R.r₀
      (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))) ∪
        Finset.univ.image fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ R.m₁ (k + 1) => x ∈ sitesOf T))
      (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1) (min (3 / 2 * R.κdec) κ)
      (hullConst d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
            ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
          Real.exp (c1 d L * Real.log 2) * Real.exp (hullRate d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))) + B)
      (fun D ξ => if hD : ∀ x i, D.h x i = ((((R.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
        then ((R.step k hk N₁ ν β p₁).withDatum
          (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
            (zeroClass d L N₁ R.m₁ k N (rhoSepG d L R.m₁)) z else 0)
      term := by
  have he : 0 < R.t / 2 := by have := R.t_pos; positivity
  have het : R.t / 2 ≤ R.t := by have := R.t_pos; linarith
  obtain ⟨E, -, hE⟩ := R.expE0_det_scale_of_tower_at hhull he het k hk N₁ hLN hN5 hν0 hν β p₁
  have hH0 : 0 ≤ hullConst d L
        ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
      Real.exp (c1 d L * Real.log 2) * Real.exp (hullRate d L
        ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))) := by
    have hconst := R.detConst_nonneg
    have : 0 ≤ hullConst d L
        ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) := by
      unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
    positivity
  have hN1 : L ^ 1 ∣ N₁ := by simpa using hLN
  exact renE0_siteRecord_of_parts (R.step k hk N₁ ν β p₁) hN1 R.t_pos
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) E hH0 hB z c han
    hloc hbd hsupp hval
    ((hE z).imp fun _ h => h.mono_dom (fun D hD => hD.1))

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
  have hκ0 : 0 ≤ R.κdec := by have := R.κdec_lower; have := R.κ0_nonneg; linarith
  have hH0 : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) * Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) := by
    have hconst := towerDetConst_nonneg R.toStepTower
    have : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) := by
      unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
    positivity
  have h3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  exact renE0_siteRecord_of_parts (R.toStepTower.step k hk N₁ ν β p₁) h3 R.t_pos
    (fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD ξ hξ) E hH0 hB z c han
    hloc hbd hsupp hval (hE' z)

end Balaban.Inhabited
