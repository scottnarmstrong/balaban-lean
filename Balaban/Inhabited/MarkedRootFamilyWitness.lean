/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedRootAssembly
public import Balaban.Inhabited.MarkedJointWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The marked root family at the zero-class witness step

The field-generic count (`MarkedFieldCount`), the analytic family of rooted sums
(`MarkedRootFamily`) and the root assembly (`MarkedRootAssembly`) apply, with all their hypotheses
discharged, at the zero-class witness step of `FanChainWitness`
(`wStep = hatStep m₁ β (pLog 1 2 β) δ`: `d = L = 3`, `N = 2`, `k = 1`, `N₁ = 9`, `ν = 1/81`, the
whole torus `X₁ = univ`), with the fixed data of `tower_core_fixed` and the radii of
`tower_C_items`, exactly as in `marked_count_scaled_at_witness` and `markedCubicJoint_instance`.

* `marked_count_field_at_witness`: for every `β ≥ β₀` there is one family of block terms such that
  for every marked block `z`, every complex field `y` of the unit lattice with the coordinate bound
  and the uniform radial margin, and every datum of the chart, the clauses of the rooted count
  (`MarkedCountClauses`) hold.
* `markedRootAssembly_instance`: for every `β ≥ β₀`, with `R₁ = R_σ = 2`, the radial radius
  `r = towerR > 0`, `t₁ = 8 p₁/c_ψ` and `t₀ = t₁/2`: one family `Ev` and one matrix function `M` of
  the raw data, analytic on the chart, such that for every marked block `z` and every hat field
  `‖ψ̂‖ ≤ p₁`, with the tangent `Q(Θ) = β_k^{-1/2} M(Θ) ψ̂`:
  `Q` at the step datum is `shiftUC ψ̂`; `MARK-REAL` holds at the step datum (`MarkRealAt`, by
  `markRealAt_of_chart`: every hypothesis of `MARK-REAL` is supplied by a landed theorem, at the
  witness datum and at every datum of the chart with `h = h₀`); the clauses of `MarkedRootFamily`
  hold (the rooted sums are analytic on `physV × {|u| < 2}`, bounded and anchored at every point);
  and the clauses of `MarkedRootAssembly` hold (the marks `-β · markedOut`, with the finite sum
  equal to the integrand of `E1MarksC` on the constant-`h₀` slice).  The parameter set `physV` is
  non-empty.

The witness step has `X₁ = univ`, so every domain of the expansion is the whole torus.  Zero class
only: this proves nothing about general classes or the physical model; the clamped global marks,
the common labels and the `E1MarksC` inhabitant are NOT constructed.  Nothing depends on a choice
of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Matrix Balaban.Inhabited.LevelStep Metric

open Classical in
/-- **Instance of the field-generic count at the witness step.**  There are fixed data and a
threshold `β₀` such that for every `β ≥ β₀` there is one family of block terms for which, for every
marked block `z`, every complex field `y` of the unit lattice with `|y(b)| ≤ Y₀` at the unit
points, every radial margin `(R₁ + r)(R_σ + t₁) Y₀ < t`, `R₁ > 1`, `r > 0`, `0 < t₀ < t₁`, every
`|u| < R_σ` and every datum `Θ` of the chart, the clauses of the rooted count hold.  The field
`y = 0` with `Y₀ = 0` and the step datum are admissible, so the statement is not empty. -/
theorem marked_count_field_at_witness :
    ∃ (m₁ : ℕ) (BG BG₂ κ κdec t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ aEnt 3 3 + 1 ≤ 2 * κdec - 1 ∧
      ∀ β : ℝ, β₀ ≤ β →
      ∃ Ev : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))) → Set (CTorus 3 3 9 m₁ (1 + 1)) →
          RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 × (CTorus 3 3 9 m₁ (1 + 1) → Fin 2 → ℂ) → ℂ,
        ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) {Y₀ R₁ r Rσ t₁ t₀ : ℝ}
          {y : (wStep m₁ β δ).EC},
          (∀ b : (wStep m₁ β δ).U, vn (fun i => y (b, i)) ≤ Y₀) →
          (R₁ + r) * (Rσ + t₁) * Y₀ < t → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
          ∀ {u : ℂ}, ‖u‖ < Rσ → ∀ {Θ : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2},
            Θ ∈ XiCRaw (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t →
          MarkedCountClauses 1
            (fun _ => polyDom (wStep m₁ β δ).G' (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1)))
              1 1 ({0} : Set (CTorus 3 3 9 m₁ (1 + 1)))) z Ev
            (liftC (wStep m₁ β δ).hG' (u • y))
            (liftC (wStep m₁ β δ).hG' ((wStep m₁ β δ).maskUC z y)) Θ
            (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) 1
                (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t) t (rho4 3 3 2 BG κ)‖ / (r ^ 3 * t₀) *
              (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3) *
              ((nFibre 3 3 : ℝ) * Real.exp ((2 * κdec - 1) * cBr 3 3))) (2 * κdec - 1) := by
  classical
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  refine ⟨m₁, BG, BG₂, κ, κdec, t, 1, 2, le_rfl, ht0, by linarith, ?_⟩
  intro β _
  obtain ⟨Ev, -, -, -, -, hfield⟩ := (wStep m₁ β 1).marked_count_field
    (Hm := Hm m₁ (rhoSep m₁)) (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
    (X₁V := fun _ => Finset.univ) (m₀ := 1) hC (fun _ => covSetup)
    (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm)
    hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) (fun _ => hopt)
    (fun _ => treeLen_zero) hκ0 hκdec (by exact_mod_cast hκ) h1 hlog isLevel_Hm
    (fun _ _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun _ => blockMargin_univ fun x _ _ => mem_some_intBox h4 x) (by norm_num)
  refine ⟨Ev, fun z Y₀ R₁ r Rσ t₁ t₀ y hY hrad hR₁ hr ht₀ ht₀₁ u hu Θ hΘ => ?_⟩
  exact hfield z hY hrad hR₁ hr ht₀ ht₀₁ hu hΘ

open Classical in
/-- **Instance of the root assembly at the witness step, with `MARK-REAL` discharged.**  There are
fixed data and a threshold `β₀` such that for every `β ≥ β₀`, with `p₁ = pLog 1 2 β`,
`r = towerR κ t β p₁ > 0` and some `0 < t₀ < t₁`: the radial margin
`(2 + r)(2 + t₁) · markedRad < t` holds, `physV` is non-empty, and there are one family `Ev` of
block terms and one matrix function `M` of the raw data, with entries analytic on the chart, such
that for every marked block `z` and every hat field `‖ψ̂‖ ≤ p₁`, with the tangent
`Q(Θ) = β_k^{-1/2} M(Θ) ψ̂`:

* `Q` at the step datum is `shiftUC ψ̂`;
* `MARK-REAL` holds at the step datum (`MarkRealAt` with ball radius `t` and disc radius `2`);
* the clauses of `MarkedRootFamily` hold on `physV × {|u| < 2}`;
* the clauses of `MarkedRootAssembly` hold for the marks `-β · markedOut z Y'`. -/
theorem markedRootAssembly_instance :
    ∃ (m₁ : ℕ) (BG BG₂ κ κdec t δ β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ aEnt 3 3 + 1 ≤ 2 * κdec - 1 ∧
      ∀ β : ℝ, β₀ ≤ β → ∃ t₀ t₁ : ℝ, 0 < t₀ ∧ t₀ < t₁ ∧ 0 < towerR κ t β (pLog 1 2 β) ∧
        (2 + towerR κ t β (pLog 1 2 β)) * (2 + t₁) * markedRad 3 3 2 1 1 κ (pLog 1 2 β)
          ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < t ∧
        (physV (wStep m₁ β δ) 1 nuW t).Nonempty ∧
        ∃ (Ev : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))) → Set (CTorus 3 3 9 m₁ (1 + 1)) →
            RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 × (CTorus 3 3 9 m₁ (1 + 1) → Fin 2 → ℂ) → ℂ)
          (M : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 →
            Matrix ((wStep m₁ β δ).U × Fin 2) ((wStep m₁ β δ).U × Fin 2) ℂ),
          (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
            (XiCRaw (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t)) ∧
          ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (x : (wStep m₁ β δ).E),
            ‖x‖ ≤ pLog 1 2 β →
            ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) •
                (M (rawOf (wStep m₁ β δ).D') *ᵥ yhat x) = (wStep m₁ β δ).shiftUC x ∧
            (wStep m₁ β δ).MarkRealAt t 2 x ∧
            (wStep m₁ β δ).MarkedRootFamily z 1
              (fun _ => polyDom (wStep m₁ β δ).G'
                (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) 1 1
                ({0} : Set (CTorus 3 3 9 m₁ (1 + 1)))) Ev 1 nuW t 2
              (fun Θ => ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
              (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) 1
                  (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t) t (rho4 3 3 2 BG κ)‖ /
                  (towerR κ t β (pLog 1 2 β) ^ 3 * t₀) *
                (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3) *
                ((nFibre 3 3 : ℝ) * Real.exp ((2 * κdec - 1) * cBr 3 3))) (2 * κdec - 1) ∧
            (wStep m₁ β δ).MarkedRootAssembly z 1
              (fun _ => polyDom (wStep m₁ β δ).G'
                (Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))) 1 1
                ({0} : Set (CTorus 3 3 9 m₁ (1 + 1)))) Ev t 2
              (fun Θ => ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
              (|β| * (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) 1
                  (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t) t (rho4 3 3 2 BG κ)‖ /
                  (towerR κ t β (pLog 1 2 β) ^ 3 * t₀) *
                (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3) *
                ((nFibre 3 3 : ℝ) * Real.exp ((2 * κdec - 1) * cBr 3 3)))) (2 * κdec - 1) := by
  classical
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
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c
  refine ⟨m₁, BG, BG₂, κ, κdec, t, δ, β₀t, hβ₀t, ht0, by linarith, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, -, -⟩ := hitems β hβ
  have hβ0 : 0 < β := by linarith
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
  have eR : markedRad 3 3 2 1 1 κ p₁
      ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = W * p₁ := by
    rw [hW]; simp only [markedRad]; ring
  have hradial : (2 + towerR κ t β p₁) * (2 + t₁) * markedRad 3 3 2 1 1 κ p₁
      ((((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < t := by
    rw [eR]
    calc (2 + towerR κ t β p₁) * (2 + t₁) * (W * p₁)
        = ((2 + towerR κ t β p₁) * (2 + t₁) * p₁) * W := by ring
      _ ≤ cψ * W := mul_le_mul_of_nonneg_right hmain hW0
      _ = W * cψ := by ring
      _ < t := hWc
  have hlt : p₁ < cψ := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + towerR κ t β p₁ by linarith) hp.le
    linarith
  have hδ₁' : Real.sqrt ((2 : ℕ) : ℝ) * ((wStep m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * cψ)) < t := by
    rw [← (wStep m₁ β δ).norm_betaU_rpow hβ0.le]
    exact hδ₁
  refine ⟨t₁ / 2, t₁, by positivity, by linarith, hr0, hradial,
    wStep_physV_nonempty m₁ β δ ht0, ?_⟩
  obtain ⟨Ev, M, -, -, -, -, hMan, hfib, hall⟩ := (wStep m₁ β δ).markedRootAssembly_zero
    (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
    (X₁V := fun _ => Finset.univ) (m₀ := 1) (R := 2) (pp := cψ) (R₁ := 2) (Rσ := 2)
    (r := towerR κ t β p₁) (t₁ := t₁) (t₀ := t₁ / 2) hC (fun _ => covSetup)
    (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm)
    hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) (fun _ => hopt)
    (fun _ => treeLen_zero) hκ0 hκdec (by exact_mod_cast hκ) h1 hlog
    (fun _ _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun _ => blockMargin_univ fun x _ _ => mem_some_intBox h4 x) (by norm_num)
    hMX hdm hα hsmX one_pos hc7 le_rfl g1 g2 g3 g4 g5 hβ0 hδ₁' hlt hp.le hradial (by norm_num) hr0
    (by positivity) (by linarith) (by norm_num)
  refine ⟨Ev, M, hMan, fun z x hx => ?_⟩
  obtain ⟨-, hMR, hfam, hasm⟩ := hall z x hx
  exact ⟨hfib (wStep m₁ β δ).D' (wStep m₁ β δ).hh₀ (wStep_xiCData m₁ β δ ht0) x,
    hMR (wStep m₁ β δ).D' (wStep m₁ β δ).hh₀ (wStep_xiCData m₁ β δ ht0), hfam, hasm⟩

end Balaban.Inhabited
