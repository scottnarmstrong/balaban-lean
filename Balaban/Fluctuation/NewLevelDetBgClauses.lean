/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelCoeffBg
public import Balaban.Fluctuation.LocalSetDetConn
public import Balaban.Fluctuation.DetRotation

/-!
# The clauses of the determinant part of the coefficient on a generating set without `HatConn`
(`NewLevelDetBgClauses`)

P3 pp. 78-79 for the determinant: the determinant part `newLevelDetBg Gb … Zb θ T` of the
coefficient of the new level, recomputed on a generating set `Gb` (a local set `𝔹_{k+1}(Y)` of a
label polymer, for which `HatConn` fails), has on the chart `Ξ^c_{k+1}(Gb; 1, ε)` the clauses the
class asks of a term: analyticity in the parameter (`newLevelDetBg_analyticOnNhd`, on the open set
`physVBg`), the bound and the support for polymers avoiding the layer `1` of `Gb`
(`norm_newLevelDetBg_le_of_avoid`, `newLevelDetBg_ne_zero_imp_of_avoid`, from the forms of
`LocalSetDetConn` without `HatConn`), locality in the datum (`newLevelDetBg_eq_of_agree`) and
invariance under the spin rotations of the datum (`newLevelDetBg_rot`).  Every hypothesis is a
condition of `FlCore` of `Gb` at the radius of the chart and the margins of the covariance chart;
the radius may be the radius of the class chart (analyticity, bound) or the larger radius of the
datum read from the step (locality), the conditions at the two radii being smallness conditions
against absolute constants.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6 Finset Matrix

section Clauses

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱb ϱm : ℝ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)

include hC hk hδc hcap hsm hmar hα

/-- **Analyticity of the determinant part in the parameter** (P3 (4.46) for the determinant): the
determinant part of the coefficient on `Gb` is analytic on the admissible parameters
`physVBg N Gb a₁ ν ε` of the chart of `Gb` (a finite sum of the analytic functions of
`exists_analytic_detActivityBg_raw` composed with the inclusion, on the open set `physVBg`). -/
theorem newLevelDetBg_analyticOnNhd (HB : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν)
    (Zb : Finset (unitPts Gb))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    AnalyticOnNhd ℂ (fun θ => newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb θ T)
      (physVBg N Gb a₁ ν eps) := by
  classical
  choose A hA hAv using fun y : unitPts Gb =>
    exists_analytic_detActivityBg_raw (m₀ := 1) hC hk hδc hcap hsm hmar hα y T
  have hval : ∀ θ' ∈ physVBg N Gb a₁ ν eps,
      ∑ y ∈ Zb, A y (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
        newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb θ' T := by
    intro θ' hθ'
    obtain ⟨D, hD, hθD'⟩ := hθ'.1
    have hθD : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D := hθD'
    rw [newLevelDetBg_of_eq Gb _ _ _ _ Zb hθD]
    exact Finset.sum_congr rfl fun y _ => by rw [hθD, hAv y D hD]
  intro θ hθ
  obtain ⟨D, hD, hθD'⟩ := hθ.1
  have hθD : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D := hθD'
  have hfst : AnalyticAt ℂ (fun θ' : physParamBg N Gb =>
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) θ :=
    ((rawSub N Gb).subtypeL.comp
      (ContinuousLinearMap.fst ℂ (rawSub N Gb) (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))).analyticAt θ
  have han : AnalyticAt ℂ (fun θ' : physParamBg N Gb =>
      ∑ y ∈ Zb, A y (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) θ :=
    Finset.analyticAt_fun_sum _ fun y _ => (hA y D hD).comp_of_eq hfst hθD
  refine han.congr ?_
  filter_upwards [(isOpen_physVBg Gb a₁ ν eps HB).mem_nhds hθ] with θ' hθ'
  exact hval θ' hθ'

variable {D : BgData Gb N} (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)

include hD

open Classical in
/-- **The bound of the determinant part for a polymer avoiding the layer `1` of `Gb`, without
`HatConn`** (P3 (4.47) for the determinant): with `Δ = detDeg d L + 1`, `z = Δ² · 2 / e^κ < 1` and
`λ = κ - log 2 - 2 log Δ`, `‖newLevelDetBg … Zb θ T‖ ≤ |Zb| · ½ N covBLog / (1 - z) ·
exp(-(λ / (2 d L)) dExt T)` at the parameter of a datum of the chart. -/
theorem norm_newLevelDetBg_le_of_avoid (hN : L ^ 1 ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) (Zb : Finset (unitPts Gb))
    (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTav : ∀ x ∈ sitesOf T, x ∉ Gb.layer 1) :
    ‖newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb
        (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T‖ ≤
      Zb.card * ((1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
      Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt T)) := by
  rw [newLevelDetBg_rawOf]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun y _ =>
    norm_detActivityBg_le_of_avoid hC hk hδc hcap hsm hmar hα hD hN y hz T hTav

open Classical in
/-- **The support of the determinant part for a polymer avoiding the layer `1` of `Gb`, without
`HatConn`**: a non-zero determinant part at the parameter of a datum of the chart lives on a
polymer containing the root cube of a unit point of the mask. -/
theorem newLevelDetBg_ne_zero_imp_of_avoid (hN : L ^ 1 ∣ N₁) (Zb : Finset (unitPts Gb))
    (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)}
    (hTav : ∀ x ∈ sitesOf T, x ∉ Gb.layer 1)
    (h : newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb
      (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T ≠ 0) :
    ∃ y ∈ Zb, rootCube (m₀ := 1) (rootIdxOf y) ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T) := by
  rw [newLevelDetBg_rawOf] at h
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨y, hy, detActivityBg_ne_zero_imp_of_avoid hC hk hδc hcap hsm hmar hα hD hN hTav hne⟩

/-- **Invariance of the determinant part under the spin rotations of the datum**: for `Rᵀ R = 1`
and a datum `D` of the chart, the determinant part at the rotated datum is that at `D` (any
sources). -/
theorem newLevelDetBg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (Zb : Finset (unitPts Gb)) (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb
        (⟨rawOf (D.rot R), rawOf_mem_rawSub _⟩, g') T =
      newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb
        (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T := by
  rw [newLevelDetBg_rawOf, newLevelDetBg_rawOf]
  exact Finset.sum_congr rfl fun y _ =>
    detActivityBg_rot hC hk hδc hcap hsm hmar hα hR hD y T

/-- **Locality of the determinant part in the datum, without `HatConn`**: at the parameters of two
data of the chart whose raw data agree on the dependency sets `resDep x` of the sites `x ∈ Ω₁` of
the polymer `T`, the determinant parts are equal (any sources). -/
theorem newLevelDetBg_eq_of_agree {D₂ : BgData Gb N}
    (hD₂ : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D₂) (hN : L ^ 1 ∣ N₁)
    (Zb : Finset (unitPts Gb)) (g g₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hdata : ∀ x : Gb.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ sitesOf T →
      ∀ z ∈ resDep Gb (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ z = D₂.Ψ z ∧ (z ∈ Gb.Ω 1 → D.h z = D₂.h z)) :
    newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb
        (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T =
      newLevelDetBg Gb (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zb
        (⟨rawOf D₂, rawOf_mem_rawSub D₂⟩, g₂) T := by
  rw [newLevelDetBg_rawOf, newLevelDetBg_rawOf]
  exact Finset.sum_congr rfl fun y _ =>
    detActivityBg_eq_of_agree_core hC hk hδc hcap hsm hmar hα hD hD₂ hN y T hdata

end Clauses

end Balaban.Fluctuation
