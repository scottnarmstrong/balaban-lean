/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseDetLocality
public import Balaban.LargeField.Base.BaseXLogShiftInt
public import Balaban.Fluctuation.DetCauchyGraph
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rooted trace of the first step and its cut expansion

The first step has no decoupled unit lattice: the root block of the general step is a single
site.  For a unit point `y` (a site of `Ω₁`, the `L^0`-block) the **rooted trace of the first
step** is
`rootTraceBase s = -(1/2) ∑_i baseCovXLogShift(s)_{(y,i),(y,i)}`,
the diagonal of the shifted logarithm of `BaseXLogShift` (`BASEX.md`, Q5, Q11).  At `s ≡ 1` it is
`-(1/2) ∑_i logMat(A_e)_{(y,i),(y,i)}`.

* `rootTraceBase_cut_insert_eq`: switching on a parameter cube not joined to the root by a chain
  does not change it (from `baseLogShift_rows_of_comp` and `baseLogShift_rows_of_unattached`);
* `rootSupported_rootTraceBase`: the support hypothesis of the cores of `DetCauchyGraph`;
* `rootTraceBase_cut_expansion`: the cut expansion with the Cauchy bound `½ N B (1+ν)`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Multiscale Balaban.Localization Balaban.Analysis Balaban.Fluctuation

section Trace

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}

/-- A site of `Ω₁` in the unit block `y` (at the first step the unit block is a single site). -/
noncomputable def baseUnitSite (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (y : unitPts G) :
    G.Ω 1 :=
  ⟨Classical.choose ((mem_unitPts G).1 y.2),
    G.layer_subset (by omega) le_rfl (Classical.choose_spec ((mem_unitPts G).1 y.2)).1⟩

theorem unitBlock_baseUnitSite (y : unitPts G) :
    unitBlock (baseUnitSite G y : Balaban.Localization.CTorus d L N₁ m₁ 1) =
      (y : UnitTorus d L N₁ m₁ 0) :=
  (Classical.choose_spec ((mem_unitPts G).1 y.2)).2

/-- **The rooted trace of the first step**, `-(1/2) ∑_i baseCovXLogShift(s)_{(y,i),(y,i)}`, at the
site of the unit block `y`, for the decoupling parameters `s` and fixed fields `φ`, `α`. -/
noncomputable def rootTraceBase (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (y : unitPts G) (s : DecParams G) : ℂ :=
  -(1 / 2 : ℂ) * ∑ i : Fin N,
    baseCovXLogShift G a aT ν α (extS G s) φ (baseUnitSite G y, i) (baseUnitSite G y, i)

variable {a : ℕ → ℝ} {aT ν Cx κ δ : ℝ} {α : G.Ω 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}

theorem norm_extS_cutPt_le (hκ : 0 ≤ κ) (I : Finset (cubeIdx G)) (P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1) :
    ‖extS G (cutPt I) P‖ ≤ Real.exp κ := by
  classical
  have h1 := Real.one_le_exp hκ
  unfold extS cutPt
  have h0 := (Real.exp_pos κ).le
  split_ifs <;> simp [h1, h0]

section Insert

variable (hdg : DGSetting G a ν) (SX : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
  (hκ : 0 ≤ κ) (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
  (hφ : IsConstraintField G δ φ)
include hdg SX hCx hκ hM hδ hsm hα hφ

/-- **Switching on a parameter cube not joined to the root does not change the rooted trace of
the first step.** -/
theorem rootTraceBase_cut_insert_eq (hconn : HatConn G) {J I : Finset (cubeIdx G)}
    {p : cubeIdx G} (hpJ : p ∈ J) (hIJ : I ⊆ J) (y : unitPts G)
    (hnc : ∀ q, RootChain G J y q → p ∉ QsetP G q) :
    rootTraceBase G a aT ν φ α y (cutPt (insert p I)) =
      rootTraceBase G a aT ν φ α y (cutPt I) := by
  classical
  have hs := fun I' : Finset (cubeIdx G) => norm_extS_cutPt_le (G := G) hκ I'
  suffices hrow : ∀ i : Fin N,
      baseCovXLogShift G a aT ν α (extS G (cutPt (insert p I))) φ
        (baseUnitSite G y, i) (baseUnitSite G y, i) =
      baseCovXLogShift G a aT ν α (extS G (cutPt I)) φ
        (baseUnitSite G y, i) (baseUnitSite G y, i) by
    unfold rootTraceBase
    rw [Finset.sum_congr rfl fun i _ => hrow i]
  intro i
  by_cases hatt : ∃ q0 ∈ Zs G (extS G (cutPt I)), HatAttached G y q0
  · obtain ⟨Y', hY, hY', hl, hag⟩ := exists_root_comp hdg hpJ hIJ y hnc hatt
    have hx : (baseUnitSite G y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y' :=
      hl _ (unitBlock_baseUnitSite y)
    exact (baseLogShift_rows_of_comp hdg hconn SX hCx hκ hM hδ hsm hα (hs _) (hs _) hY' hY
      (fun q hq hsub => (hag q hq hsub).symm) hφ (baseUnitSite G y) hx i
      (baseUnitSite G y, i)).2
  · have hatt' : ¬ ∃ q0 ∈ Zs G (extS G (cutPt (insert p I))), HatAttached G y q0 := by
      rintro ⟨q0, hq0, ha⟩
      have hq0' := mem_Zs_cutPt_iff.1 hq0
      have hact : ActIn G J q0 := by
        refine ⟨hq0'.1, hq0'.2.trans ?_⟩
        intro r hr
        rcases Finset.mem_insert.1 hr with h | h
        · exact h ▸ hpJ
        · exact hIJ h
      have hnp := hnc q0 (RootChain.of_attached hact ha)
      refine hatt ⟨q0, mem_Zs_cutPt_iff.2 ⟨hq0'.1, fun P hP => ?_⟩, ha⟩
      rcases Finset.mem_insert.1 (hq0'.2 hP) with h | h
      · exact absurd (h ▸ hP) hnp
      · exact h
    refine (baseLogShift_rows_of_unattached hdg SX hCx hκ hM hδ hsm hα (hs _) (hs _) hφ
      (baseUnitSite G y) ?_ ?_ i (baseUnitSite G y, i)).2
    · intro q hq hxq
      exact hatt' ⟨q, hq, baseUnitSite G y, unitBlock_baseUnitSite y, hxq⟩
    · intro q hq hxq
      exact hatt ⟨q, hq, baseUnitSite G y, unitBlock_baseUnitSite y, hxq⟩

/-- **The support hypothesis for the first step's rooted trace**: a non-zero mixed difference
forces every parameter cube of `J` to be chained to the root block. -/
theorem rootSupported_rootTraceBase (hconn : HatConn G) (y : unitPts G) :
    RootSupported {y} (rootTraceBase G a aT ν φ α y) := by
  intro J hne
  refine ⟨y, Finset.mem_singleton_self _, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨p, hpJ, hp⟩ := h
  exact hne (mixDiff_eq_zero_of_insert_eq hpJ _ fun _ hI =>
    rootTraceBase_cut_insert_eq hdg SX hCx hκ hM hδ hsm hα hφ hconn hpJ
      (hI.trans (Finset.erase_subset _ _)) y hp)

end Insert

section Expansion

/-- **The cut expansion of the first step's rooted trace** (the analogue of
`rootTrace_cut_expansion`): for fixed admissible fields (strict constraint field, strict potential
bound) and `R = e^κ > 1`, the value at `s = 1` is the sum over `J` of the mixed differences
`Δ_J`, each bounded by `(1/2) N B (1+ν) (2 / e^κ)^{|J|}`; `B` depends on `d, L, N, κ` only. -/
theorem rootTraceBase_cut_expansion (d L N : ℕ) [NeZero L] (κ : ℝ) (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hCx : 0 ≤ Cx)
      (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintFieldStrict G δ φ) {α : G.Ω 1 → ℂ}
      (_hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing
        (w : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2)) (y : unitPts G),
      rootTraceBase G a aT ν φ α y (fun _ => 1) =
          ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset,
            mixDiff J (rootTraceBase G a aT ν φ α y) ∧
        ∀ J : Finset (cubeIdx G),
          ‖mixDiff J (rootTraceBase G a aT ν φ α y)‖ ≤
            ((1 / 2 : ℝ) * N * (B * (1 + ν))) * (2 / Real.exp κ) ^ J.card := by
  classical
  obtain ⟨B, hB0, H⟩ := baseCovXLogShift_main d L N κ
  refine ⟨B, hB0, ?_⟩
  intro N₁ m₁ _ ϱ G a aT ν Cx S hCx hM δ hδ hsm ha0 ha1 ha1' haT φ hφ α hα y
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hν : 0 ≤ ν := S.mass
  have hmem : ∀ s ∈ cutPolydisc (cubeIdx G) (Real.exp κ), ((s, (φ, α)) : DecData G N) ∈
      DecDom G N κ δ := fun s hs => ⟨hs, hφ, hα⟩
  refine ⟨sum_mixDiff _, fun J => ?_⟩
  refine norm_mixDiff_le hR J ?_ ?_
  · intro s hs
    have hterm : ∀ i : Fin N, AnalyticAt ℂ (fun s : DecParams G =>
        baseCovXLogShift G a aT ν α (extS G s) φ (baseUnitSite G y, i) (baseUnitSite G y, i)) s := by
      intro i
      obtain ⟨-, -, hA, -⟩ := H S hCx hκ.le hM hδ hsm ha0 ha1 ha1' haT
        (baseUnitSite G y, i) (baseUnitSite G y, i)
      have h := hA ((s, (φ, α)) : DecData G N) (hmem s hs)
      have hc : AnalyticAt ℂ (fun s : DecParams G => ((s, (φ, α)) : DecData G N)) s :=
        AnalyticAt.prod analyticAt_id analyticAt_const
      exact AnalyticAt.comp (g := fun e : DecData G N =>
        baseCovXLogShift G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1
          (baseUnitSite G y, i) (baseUnitSite G y, i))
        (f := fun s : DecParams G => ((s, (φ, α)) : DecData G N)) h hc
    have : AnalyticAt ℂ (rootTraceBase G a aT ν φ α y) s := by
      unfold rootTraceBase
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => hterm i)
    exact this.differentiableAt.differentiableWithinAt
  · intro s hs
    have hent : ∀ i : Fin N, ‖baseCovXLogShift G a aT ν α (extS G s) φ
        (baseUnitSite G y, i) (baseUnitSite G y, i)‖ ≤ B * (1 + ν) := by
      intro i
      obtain ⟨-, -, -, hb⟩ := H S hCx hκ.le hM hδ hsm ha0 ha1 ha1' haT
        (baseUnitSite G y, i) (baseUnitSite G y, i)
      exact hb ((s, (φ, α)) : DecData G N) (hmem s hs)
    unfold rootTraceBase
    rw [norm_mul]
    have hhalf : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [hhalf]
    calc (1 / 2 : ℝ) * ‖∑ i : Fin N, baseCovXLogShift G a aT ν α (extS G s) φ
          (baseUnitSite G y, i) (baseUnitSite G y, i)‖
        ≤ (1 / 2 : ℝ) * ∑ i : Fin N, (B * (1 + ν)) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hent i))
            (by norm_num)
      _ = _ := by simp; ring

end Expansion

end Trace

end Balaban.LargeField.Base
