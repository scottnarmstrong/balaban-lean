/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedCubicJoint
public import Balaban.Fluctuation.StepComplexOutAnalytic
public import Balaban.Inhabited.FanChainWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Instances of the joint analyticity of the marked terms at the zero-class witness step

`markedEv_joint_physV` (`MarkedEvJoint`) and `markedCubic_joint_param` (`MarkedCubicJoint`) apply,
with all their hypotheses discharged, at the zero-class witness step of `FanChainWitness`
(`wStep = hatStep m₁ β (pLog 1 2 β) δ`: `d = L = 3`, `N = 2`, `k = 1`, `N₁ = 9`, `ν = 1/81`, the
whole torus `X₁ = univ`), exactly as in `markedVBlockDecTwo_instance` and
`marked_count_scaled_at_witness`.

* `wStep_xiCData`, `wStep_physV_nonempty`: the step datum lies in the chart, so the parameter set
  `physV` is non-empty.
* `markedEvJoint_instance`: for every block `z` and every mask `Zm`, the proposition
  `MarkedEvJointPhysV` holds (one pair `(F₁, Sol)`: the eight landed clauses, joint analyticity of
  `evDec` in (datum, hat field, marks) on the chart and on `physV`, analytic derivative marks); the
  radius set of marks contains the bidisc `|um| ≤ 2`, `|tm| ≤ t₁` with `t₁ > 0`, so clause 4 applies
  with `a = 2`, `b = t₁`.
* `markedCubicJoint_instance`: for every marked block `z`, every old block `zb` and every
  fluctuation variable `‖ψ̂‖ ≤ p₁`: the terms `E_{zb,Y}` of the landed block expansion, a function `Q`
  of the raw data, analytic on the chart, equal to `shiftUC ψ̂` at the step datum, and the three
  family clauses of `markedCubic_joint_param` with `R₁ = R_σ = 2`, the radial radius
  `r = towerR > 0` of the tower and `t₁ = 8 p₁ / c_ψ > 0`.  The radial margin
  `(R₁ + r)(R_σ + t₁) · markedRad < t` is the inequality of `marked_radius_and_derivative_at_witness`;
  the bound of the unit field on the whole chart is `exists_analytic_shiftUC_chart`.

The witness step has `X₁ = univ`, so every domain of the expansion is the whole torus.  Zero class
only: this proves nothing about general classes or the physical model; the root assembly, the
clamped global marks, the common labels and the `E1MarksC` inhabitant are NOT constructed.  Nothing
depends on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Matrix Balaban.Inhabited.LevelStep Metric

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

/-- **The datum of the witness step lies in the chart** `Ξ^c(𝔹₂; 1, t)`, for every `t > 0`. -/
theorem wStep_xiCData (m₁ : ℕ) (β δ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t (wStep m₁ β δ).D' := by
  refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
    exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
  · intro x hx i
    have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
    show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
    rw [this]; simp
  · intro x hx i
    have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
    show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
    rw [this]; simp

/-- **The parameter set `physV` of the witness step is non-empty**: it contains the step datum with
the zero source. -/
theorem wStep_physV_nonempty (m₁ : ℕ) (β δ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    (physV (wStep m₁ β δ) 1 nuW t).Nonempty := by
  refine ⟨(⟨rawOf (wStep m₁ β δ).D', rawOf_mem_rawSub _⟩, 0),
    ⟨⟨_, wStep_xiCData m₁ β δ ht0, rfl⟩, ?_⟩⟩
  show (0 : CTorus 3 3 9 m₁ (1 + 1) → Fin 2 → ℂ) ∈ l1Ball 3 3 9 m₁ (1 + 1) 2
  simp [l1Ball]

open Classical in
/-- **Instance of `markedEv_joint_physV` at the witness step**: for every block `z` and mask `Zm`
the proposition `MarkedEvJointPhysV` holds on the whole torus; the parameter set `physV` is
non-empty, and the radius set of marks contains the bidisc `|um| ≤ 2`, `|tm| ≤ t₁` for some
`t₁ > 0`. -/
theorem markedEvJoint_instance :
    ∃ (m₁ : ℕ) (BG BG₂ κ κdec t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < κ ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₁ : ℝ, 0 < t₁ ∧
        (2 + t₁) * markedRad 3 3 2 1 1 κ (pLog 1 2 β) ccw[m₁, β, δ] < t ∧
        (physV (wStep m₁ β δ) 1 nuW t).Nonempty ∧
        ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))
          (Zm : Finset (unitPts Gw[m₁, β, δ])),
          MarkedEvJointPhysV (wStep m₁ β δ) (Hm m₁ (rhoSep m₁)) ccw[m₁, β, δ] 1 nuW BG BG₂
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
  refine ⟨8 * p₁ / cψ, ht₁0, ?_, wStep_physV_nonempty m₁ β δ ht0, fun z Zm => ?_⟩
  · have e : markedRad 3 3 2 1 1 κ p₁ ccw[m₁, β, δ] = W * p₁ := by
      rw [hW]; simp only [markedRad]; ring
    rw [e]; exact hrad
  · exact markedEv_joint_physV (wStep m₁ β δ) hC isLevel_Hm _ hp.le Zm
      hMX hdm hα hsmX (j := 1) (m₀ := 1) (X := Xr) (𝒦X := {0}) (X₁f := Finset.univ)
      covSetup (by rw [Finset.coe_univ]; exact X1_eq_univ.symm) hatConn
      (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hopt treeLen_zero hκ0 hκdec
      (by exact_mod_cast hκ) h1 hlog z
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (blockMargin_univ fun x _ _ => mem_some_intBox h4 x)

open Classical in
/-- **Instance of `markedCubic_joint_param` at the witness step.**  There are fixed data and a
threshold `β₀` such that for every `β ≥ β₀`, with `p₁ = pLog 1 2 β`, `r = towerR κ t β p₁ > 0` and
some `t₁ > 0`: the radial margin `(2 + r)(2 + t₁) · markedRad < t` holds, `physV` is non-empty, and
for every marked block `z` and old block `zb` there are terms `E_{zb,Y}` summing to the block
energy of `zb`, analytic on `Ξ^c × FlBall`, such that for every fluctuation variable `‖ψ̂‖ ≤ p₁`
there is a function `Q` of the raw data, analytic on the chart and equal to `shiftUC ψ̂` at the step
datum, for which, for every label `Y`, the marked term along
`v_t(e, u) = u · Q(e.1) + t · M_z Q(e.1)` is analytic on `(physV × {|u| < 2}) × {|t| < t₁}`, its
`t`-derivative at `0` is analytic on `physV × {|u| < 2}`, and is at most
`3 E* e^{-2 κ_dec d(Y)} / (r³ t₀)` for `0 < t₀ < t₁`. -/
theorem markedCubicJoint_instance :
    ∃ (m₁ : ℕ) (BG BG₂ κ κdec t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₁ : ℝ, 0 < t₁ ∧ 0 < towerR κ t β (pLog 1 2 β) ∧
        (2 + towerR κ t β (pLog 1 2 β)) * (2 + t₁) *
          markedRad 3 3 2 1 1 κ (pLog 1 2 β) ccw[m₁, β, δ] < t ∧
        (physV (wStep m₁ β δ) 1 nuW t).Nonempty ∧
        ∀ (z zb : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))),
        ∃ Ev : Set (CTorus 3 3 9 m₁ (1 + 1)) →
            RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 × (CTorus 3 3 9 m₁ (1 + 1) → Fin 2 → ℂ) → ℂ,
          (∀ D : BgData (wStep m₁ β δ).G' 2,
            XiCData (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t D →
            ∀ ψ' ∈ FlBall (Hm m₁ (rhoSep m₁)) t,
            energyBlock (wStep m₁ β δ).G' (Hm m₁ (rhoSep m₁)) (compWeight 3 1) nuW 1
              (bgMultC (wStep m₁ β δ).G' (compWeight 3 1) nuW (bgC0 3 3 2) D)
              (flFieldOne (wStep m₁ β δ).G' (Hm m₁ (rhoSep m₁)) BG₂ κ 1 nuW D ψ') ψ' zb =
            ∑ Y ∈ polyDom (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) 1 1
              ({0} : Set (CTorus 3 3 9 m₁ (1 + 1))), Ev Y (rawOf D, ψ')) ∧
          (∀ Y, AnalyticOnNhd ℂ (Ev Y)
            (XiCRaw (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t ×ˢ
              FlBall (Hm m₁ (rhoSep m₁)) t)) ∧
          ∀ x : (wStep m₁ β δ).E, ‖x‖ ≤ pLog 1 2 β →
          ∃ Q : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 → (wStep m₁ β δ).EC,
            AnalyticOnNhd ℂ Q (XiCRaw (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t) ∧
            Q (rawOf (wStep m₁ β δ).D') = (wStep m₁ β δ).shiftUC x ∧
            ∀ Y,
              AnalyticOnNhd ℂ (fun p : (physParam 2 (wStep m₁ β δ) × ℂ) × ℂ =>
                  markedBlockTerm (Ev Y) taylorWeight
                    (liftC (wStep m₁ β δ).hG'
                      (p.1.2 • Q (p.1.1.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2)))
                    (liftC (wStep m₁ β δ).hG' ((wStep m₁ β δ).maskUC z
                      (Q (p.1.1.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2))))
                    (p.1.1.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2) p.2)
                ((physV (wStep m₁ β δ) 1 nuW t ×ˢ ball (0 : ℂ) 2) ×ˢ ball (0 : ℂ) t₁) ∧
              AnalyticOnNhd ℂ (fun p : physParam 2 (wStep m₁ β δ) × ℂ =>
                  deriv (markedBlockTerm (Ev Y) taylorWeight
                    (liftC (wStep m₁ β δ).hG'
                      (p.2 • Q (p.1.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2)))
                    (liftC (wStep m₁ β δ).hG' ((wStep m₁ β δ).maskUC z
                      (Q (p.1.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2))))
                    (p.1.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2)) 0)
                (physV (wStep m₁ β δ) 1 nuW t ×ˢ ball (0 : ℂ) 2) ∧
              ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < t₁ → ∀ e ∈ physV (wStep m₁ β δ) 1 nuW t,
                ∀ u : ℂ, ‖u‖ < 2 →
                ‖deriv (markedBlockTerm (Ev Y) taylorWeight
                    (liftC (wStep m₁ β δ).hG'
                      (u • Q (e.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2)))
                    (liftC (wStep m₁ β δ).hG' ((wStep m₁ β δ).maskUC z
                      (Q (e.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2))))
                    (e.1 : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2)) 0‖ ≤
                  3 * (energyBdScaled 3 3 2 (compWeight 3 1) 1
                    (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t) t (rho4 3 3 2 BG κ) *
                    Real.exp (-2 * κdec * treeLenCov (wStep m₁ β δ).G' 1 Y)) /
                    (towerR κ t β (pLog 1 2 β) ^ 3 * t₀) := by
  classical
  fan_setup
  refine ⟨m₁, BG, BG₂, κ, κdec, t, δ, β₀t, hβ₀t, ht0, ?_⟩
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
  set t₁ : ℝ := 8 * p₁ / cψ with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have hmain : (2 + towerR κ t β p₁) * (2 + t₁) * p₁ ≤ cψ := by
    have e : (2 + towerR κ t β p₁) * (2 + t₁) * p₁ = cψ - 16 * p₁ ^ 2 / cψ := by
      unfold towerR
      rw [ht₁]
      field_simp
      ring
    rw [e]
    have : 0 ≤ 16 * p₁ ^ 2 / cψ := by positivity
    linarith
  have eR : markedRad 3 3 2 1 1 κ p₁ ccw[m₁, β, δ] = W * p₁ := by
    rw [hW]; simp only [markedRad]; ring
  have hradial : (2 + towerR κ t β p₁) * (2 + t₁) * markedRad 3 3 2 1 1 κ p₁ ccw[m₁, β, δ] < t := by
    rw [eR]
    calc (2 + towerR κ t β p₁) * (2 + t₁) * (W * p₁)
        = ((2 + towerR κ t β p₁) * (2 + t₁) * p₁) * W := by ring
      _ ≤ cψ * W := mul_le_mul_of_nonneg_right hmain hW0
      _ = W * cψ := by ring
      _ < t := hWc
  refine ⟨t₁, ht₁0, hr0, hradial, wStep_physV_nonempty m₁ β δ ht0, fun z zb => ?_⟩
  obtain ⟨Ev, hsum, -, -, han, hfam⟩ := (wStep m₁ β δ).markedCubic_joint_param z
    (Hm := Hm m₁ (rhoSep m₁)) (j := 1) (m₀ := 1) (X := Xr) (𝒦X := {0}) (X₁f := Finset.univ)
    hC covSetup (by rw [Finset.coe_univ]; exact X1_eq_univ.symm) hatConn
    (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hopt treeLen_zero hκ0 hκdec
    (by exact_mod_cast hκ) h1 hlog isLevel_Hm zb
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
  refine ⟨Ev, hsum, han, fun x hx => ?_⟩
  obtain ⟨Q, hQan, hQfib, hQb⟩ := (wStep m₁ β δ).exists_analytic_shiftUC_chart
    (Hm := Hm m₁ (rhoSep m₁)) hC hMX hdm hα hsmX x hp.le
    (fun q => (wStep m₁ β δ).yhat_le_of_norm_le hx q)
  refine ⟨Q, hQan, ?_, fun Y => ?_⟩
  · exact hQfib (wStep m₁ β δ).D' (wStep m₁ β δ).hh₀ (wStep_xiCData m₁ β δ ht0)
  · exact hfam Y hQan hQb hradial (by norm_num) hr0 ht₁0

end Balaban.Inhabited
