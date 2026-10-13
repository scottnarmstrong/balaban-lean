/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexAnalytic
public import Balaban.Fluctuation.StepComplexOut
public import Balaban.Fluctuation.HatEngineLift
public import Balaban.Fluctuation.ParamActivitySubspace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked tangent of the fluctuation step

The first-order energy term of the step at a root `z` is the expectation of the function
`f_z(u, ψ̂) = DΦ₁(u ψ')[1_{B(z)} ψ']` (`E1Marks`, `E1MarksC`), `ψ' = shiftU ψ̂`.  To expand it with
domains anchored at the root one replaces the fluctuation tangent `y = ψ'` by the one-parameter
family
`v_t = u · y + t · M_z y`,
where `M_z` is the restriction of a field of the unit lattice to the block `B_{k+1}(z)` (`maskU`,
`maskUC`, applied after the covariance square root), and differentiates in `t` at `0`
(formula (2) of the note `MARKCUBIC`).

This file proves the facts about the marked tangent itself.

* `markedTangent`, `markedTangentC`: the family, real and complex (`t` complex in the complex
  version, so that Cauchy estimates in `t` apply).
* `MASK-LC`: the mask is a coordinate projection (`norm_maskUC_apply_le`, `vn_maskUC_le`), it is
  complex linear (`maskUCL`), and the fine-lattice lift of every field of the unit lattice, masked
  or not, is constant on the blocks of every layer (`isLayerConstant_liftC_markedTangentC`).
* `MARK-RADIUS`: explicit radii.  `vn_markedTangentC_le`, `liftC_markedTangentC_mem_flBallLC`
  (the marked tangent lies in `FlBallLC Hm δ₁` when `(|u| + |t|)·Y < δ₁`, `Y` a bound for the
  Euclidean norm of the unit field `y` at the unit points), `markedDisc_mem_flBall` (the discs of
  the third-derivative Cauchy estimate: `(R₁ + r)(R_σ + t₁)·Y < δ₁`), and the version in terms of
  a coordinate bound `V` of `y` (`liftC_markedTangentC_mem_flBallLC_of_coord`: the condition
  `√N · (R_σ + t₁) · V < δ₁`, the hypothesis `hδ₁` of the hat-field theorems with the factor
  `R_σ + t₁` in place of `1`).
* Analyticity: `markedTangentC_analytic` (jointly analytic in `(u, t)`), and in the datum on the
  chart (`exists_analytic_markedTangentC`, pointwise `AnalyticOnNhd` on `XiCRaw × ℂ × ℂ`; the chart
  is not open in `RawData`, so the statement is the landed one: the function is defined on all raw
  data) and `exists_analytic_markedTangentC_physV` (on the relatively open set `physV` of the
  parameter space `physParam`).

No mark family is constructed here and nothing depends on a choice of generating set for the class
terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-! ### Definitions -/

/-- **The marked tangent** (real): `v_t = u · ψ' + t · 1_{B(z)} ψ'` with `ψ' = shiftU ψ̂` a field of
the unit lattice; the mask is applied after the covariance square root.  At `t = 0` it is the ray
point `u • shiftU ψ̂` of `E1Marks`. -/
noncomputable def markedTangent (u t : ℝ) (x : S.E) : S.E :=
  u • S.shiftU x + t • S.maskU z (S.shiftU x)

/-- **The marked tangent** (complex): `v_t = u · ψ' + t · 1_{B(z)} ψ'` with the complex shift
`ψ' = shiftUC ψ̂` and the mask `maskUC`; `u, t` are complex parameters. -/
noncomputable def markedTangentC (u t : ℂ) (x : S.E) : S.EC :=
  u • S.shiftUC x + t • S.maskUC z (S.shiftUC x)

theorem markedTangent_zero_t (u : ℝ) (x : S.E) : S.markedTangent z u 0 x = u • S.shiftU x := by
  simp [markedTangent]

theorem markedTangentC_zero_t (u : ℂ) (x : S.E) :
    S.markedTangentC z u 0 x = u • S.shiftUC x := by
  simp [markedTangentC]

theorem markedTangentC_zero_u (t : ℂ) (x : S.E) :
    S.markedTangentC z 0 t x = t • S.maskUC z (S.shiftUC x) := by
  simp [markedTangentC]

/-! ### The mask is a coordinate projection (`MASK-LC`) -/

theorem maskUC_add (v w : S.EC) : S.maskUC z (v + w) = S.maskUC z v + S.maskUC z w := by
  classical
  funext q
  by_cases h : q.1 ∈ S.blockU z <;> simp [maskUC, h]

theorem maskUC_smul (c : ℂ) (v : S.EC) : S.maskUC z (c • v) = c • S.maskUC z v := by
  classical
  funext q
  by_cases h : q.1 ∈ S.blockU z <;> simp [maskUC, h]

/-- The mask of the complex unit-lattice fields as a continuous complex linear map. -/
noncomputable def maskUCL : S.EC →L[ℂ] S.EC :=
  LinearMap.toContinuousLinearMap
    { toFun := S.maskUC z
      map_add' := S.maskUC_add z
      map_smul' := S.maskUC_smul z }

theorem maskUCL_apply (v : S.EC) : S.maskUCL z v = S.maskUC z v := rfl

theorem maskU_add (v w : S.E) : S.maskU z (v + w) = S.maskU z v + S.maskU z w := by
  classical
  funext b
  by_cases h : b ∈ S.blockU z <;> simp [maskU, h]

theorem maskU_smul (c : ℝ) (v : S.E) : S.maskU z (c • v) = c • S.maskU z v := by
  classical
  funext b
  by_cases h : b ∈ S.blockU z <;> simp [maskU, h]

/-- The mask keeps or kills each coordinate: `|(M_z y)(q)| ≤ |y(q)|`. -/
theorem norm_maskUC_apply_le (v : S.EC) (q : S.U × Fin N) : ‖S.maskUC z v q‖ ≤ ‖v q‖ := by
  classical
  unfold maskUC
  by_cases h : q.1 ∈ S.blockU z <;> simp [h]

/-- The Euclidean norm at a unit point does not increase under the mask. -/
theorem vn_maskUC_le (v : S.EC) (b : S.U) :
    vn (fun i => S.maskUC z v (b, i)) ≤ vn (fun i => v (b, i)) := by
  classical
  unfold maskUC
  by_cases h : b ∈ S.blockU z
  · simp [h]
  · simp only [h, ite_false]
    have : (fun i : Fin N => (0 : ℂ)) = 0 := rfl
    simp only [this, vn_zero]
    exact vn_nonneg _

/-- **`MASK-LC`**: the fine-lattice lift of every complex field of the unit lattice is constant on
the blocks of every layer of a level-`k` generating set; in particular the lift of the marked
tangent, and of the masked field `M_z y`. -/
theorem isLayerConstant_liftC_markedTangentC {ϱm : ℝ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k) (u t : ℂ) (x : S.E) :
    IsLayerConstant Hm (liftC S.hG' (S.markedTangentC z u t x)) ∧
      IsLayerConstant Hm (liftC S.hG' (S.maskUC z (S.shiftUC x))) :=
  ⟨isLayerConstant_liftC hG S.hG' _, isLayerConstant_liftC hG S.hG' _⟩

/-- The lift is linear: the lift of the marked tangent is `u · lift y + t · lift (M_z y)`. -/
theorem liftC_markedTangentC (u t : ℂ) (x : S.E) :
    liftC S.hG' (S.markedTangentC z u t x) =
      u • liftC S.hG' (S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x)) := by
  unfold markedTangentC
  rw [map_add, map_smul, map_smul]

/-! ### Radii (`MARK-RADIUS`) -/

/-- The Euclidean norm of the marked tangent at a unit point is at most `(|u| + |t|)` times that of
`y`, because the mask does not increase it. -/
theorem vn_markedTangentC_le (u t : ℂ) (x : S.E) (b : S.U) :
    vn (fun i => S.markedTangentC z u t x (b, i)) ≤
      (‖u‖ + ‖t‖) * vn (fun i => S.shiftUC x (b, i)) := by
  have h1 : (fun i => S.markedTangentC z u t x (b, i)) =
      u • (fun i => S.shiftUC x (b, i)) + t • (fun i => S.maskUC z (S.shiftUC x) (b, i)) := by
    funext i; simp [markedTangentC]
  rw [h1]
  refine (vn_add _ _).trans ?_
  rw [vn_smul', vn_smul']
  have := vn_maskUC_le S z (S.shiftUC x) b
  have h0 := vn_nonneg (fun i => S.shiftUC x (b, i))
  nlinarith [norm_nonneg u, norm_nonneg t, mul_le_mul_of_nonneg_left this (norm_nonneg t)]

variable {z}

/-- **`MARK-RADIUS` (ball).**  If `Y` bounds the Euclidean norm of `y = shiftUC ψ̂` at every unit
point, the marked tangent lies in the admissible ball `FlBallLC Hm δ₁` as soon as
`(|u| + |t|) · Y < δ₁`. -/
theorem liftC_markedTangentC_mem_flBallLC {ϱm : ℝ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k) {δ₁ Y : ℝ} {x : S.E}
    (hY : ∀ b : S.U, vn (fun i => S.shiftUC x (b, i)) ≤ Y) {u t : ℂ}
    (h : (‖u‖ + ‖t‖) * Y < δ₁) :
    liftC S.hG' (S.markedTangentC z u t x) ∈ FlBallLC Hm δ₁ := by
  refine liftC_mem_flBallLC hG S.hG' fun b => ?_
  refine lt_of_le_of_lt ((S.vn_markedTangentC_le z u t x b).trans ?_) h
  exact mul_le_mul_of_nonneg_left (hY b) (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- **`MARK-RADIUS` (discs of the third-derivative Cauchy estimate).**  Let `Y ≥ 0` bound the
Euclidean norm of `y` at the unit points and
`(R₁ + r) (R_σ + t₁) Y < δ₁` (formula (2) of the note).  Then for `|u| < R_σ`, `|t| < t₁`, every
radial parameter `|s| < R₁` and every `|τ| ≤ r`, the field `(s + τ) · v_t` lies in `FlBallLC Hm δ₁`
(hence the closed circles `|τ| = r` around each point of the radial disc stay in the admissible
ball). -/
theorem markedDisc_mem_flBallLC {ϱm : ℝ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {δ₁ Y R₁ r Rσ t₁ : ℝ} (hY0 : 0 ≤ Y) {x : S.E}
    (hY : ∀ b : S.U, vn (fun i => S.shiftUC x (b, i)) ≤ Y)
    (h : (R₁ + r) * (Rσ + t₁) * Y < δ₁) {u t s τ : ℂ} (hu : ‖u‖ < Rσ) (ht : ‖t‖ < t₁)
    (hs : ‖s‖ < R₁) (hτ : ‖τ‖ ≤ r) :
    (s + τ) • liftC S.hG' (S.markedTangentC z u t x) ∈ FlBallLC Hm δ₁ := by
  have hsτ : ‖(s + τ) * u‖ + ‖(s + τ) * t‖ ≤ (R₁ + r) * (Rσ + t₁) := by
    rw [norm_mul, norm_mul, ← mul_add]
    have h1 : ‖s + τ‖ ≤ R₁ + r := (norm_add_le _ _).trans (add_le_add hs.le hτ)
    exact mul_le_mul h1 (add_le_add hu.le ht.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (by linarith [norm_nonneg s, norm_nonneg τ, hs, hτ])
  have hm : (s + τ) • S.markedTangentC z u t x = S.markedTangentC z ((s + τ) * u) ((s + τ) * t) x := by
    unfold markedTangentC
    rw [smul_add, smul_smul, smul_smul]
  have := S.liftC_markedTangentC_mem_flBallLC hG (z := z) (δ₁ := δ₁) (Y := Y) hY
    (u := (s + τ) * u) (t := (s + τ) * t)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsτ hY0) h)
  rwa [← hm, map_smul] at this

/-- **`MARK-RADIUS` in terms of a coordinate bound.**  If every coordinate of `y = shiftUC ψ̂`
satisfies `|y(q)| ≤ V` (for the hat field of the landed engines
`V = |c_c| · covSupConstC · c_ψ`, `decCovSqrt_supNorm`), then the marked tangent with `|u| < R_σ`,
`|t| < t₁` lies in `FlBallLC Hm δ₁` as soon as
`√N · ((R_σ + t₁) · V) < δ₁`: the hypothesis `hδ₁` of `hatLift_mem_flBallLC` with the factor
`R_σ + t₁` in place of `1`. -/
theorem liftC_markedTangentC_mem_flBallLC_of_coord {ϱm : ℝ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k) {δ₁ V Rσ t₁ : ℝ}
    {x : S.E} (hV : 0 ≤ V) (hcoord : ∀ q : S.U × Fin N, ‖S.shiftUC x q‖ ≤ V)
    (h : Real.sqrt N * ((Rσ + t₁) * V) < δ₁) {u t : ℂ} (hu : ‖u‖ < Rσ) (ht : ‖t‖ < t₁) :
    liftC S.hG' (S.markedTangentC z u t x) ∈ FlBallLC Hm δ₁ := by
  refine S.liftC_markedTangentC_mem_flBallLC hG (Y := Real.sqrt N * V) (fun b => ?_) ?_
  · exact vn_le_sqrt_mul hV (fun i => hcoord (b, i))
  · have h1 : ‖u‖ + ‖t‖ ≤ Rσ + t₁ := (add_le_add hu.le ht.le)
    calc (‖u‖ + ‖t‖) * (Real.sqrt N * V) ≤ (Rσ + t₁) * (Real.sqrt N * V) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.sqrt_nonneg _) hV)
      _ = Real.sqrt N * ((Rσ + t₁) * V) := by ring
      _ < δ₁ := h

/-! ### Analyticity -/

variable (z)

/-- The marked tangent is jointly analytic in `(u, t)` for fixed `ψ̂`, and in fact linear. -/
theorem markedTangentC_analytic (x : S.E) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => S.markedTangentC z p.1 p.2 x) Set.univ := by
  intro p _
  unfold markedTangentC
  exact (analyticAt_fst.smul analyticAt_const).add (analyticAt_snd.smul analyticAt_const)

end StepSetting

/-! ### Analyticity in the datum on the chart -/

namespace StepSetting

open Balaban.SmallField Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- The mask of the step with the datum replaced is the mask of the step. -/
theorem withDatum_maskUC (D : BgData S.G' N) (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ))
    (v : S.EC) : (S.withDatum D hD).maskUC z v = S.maskUC z v := rfl

/-- **The marked tangent is analytic in `(Θ, u, t)` on the chart** (`MARK-PARAM` input, tangent
part): one function of the raw data and the two complex parameters, analytic at every point of
`Ξ^c(𝔹_{k+1}; 1, ε) × ℂ × ℂ` (as a function on all of `RawData × ℂ × ℂ`, like the landed
analyticity statements), returns the marked tangent of the step with the datum `D`, for every
datum `D` of the chart with `h = h₀`. -/
theorem exists_analytic_markedTangentC
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (x : S.E) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ → S.EC,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ (Set.univ : Set (ℂ × ℂ))) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ u t : ℂ,
          F (rawOf D, u, t) = (S.withDatum D hD).markedTangentC z u t x := by
  obtain ⟨Q, hQan, hQ⟩ := S.exists_analytic_shiftUC hC hMX hdm hα hsm x
  refine ⟨fun p => p.2.1 • Q p.1 + p.2.2 • S.maskUCL z (Q p.1), fun p hp => ?_,
    fun D hD hX u t => ?_⟩
  · have hQp : AnalyticAt ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ => Q p.1) p :=
      (hQan p.1 hp.1).comp (analyticAt_fst (p := p))
    have hmQ : AnalyticAt ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ =>
        S.maskUCL z (Q p.1)) p :=
      AnalyticAt.comp (g := S.maskUCL z) (f := fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ =>
        Q p.1) ((S.maskUCL z).analyticAt (Q p.1)) hQp
    exact ((analyticAt_fst.comp analyticAt_snd).smul hQp).add
      ((analyticAt_snd.comp analyticAt_snd).smul hmQ)
  · show u • Q (rawOf D) + t • S.maskUCL z (Q (rawOf D)) = _
    rw [hQ D hD hX]
    rfl

/-- The same, for the lift of the marked tangent to the fine lattice (the tangent of the block
functionals): analytic in `(Θ, u, t)` on the chart. -/
theorem exists_analytic_liftC_markedTangentC
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (x : S.E) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ (Set.univ : Set (ℂ × ℂ))) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ u t : ℂ,
          F (rawOf D, u, t) = liftC S.hG' ((S.withDatum D hD).markedTangentC z u t x) := by
  obtain ⟨F, hF, hFe⟩ := S.exists_analytic_markedTangentC z hC hMX hdm hα hsm x
  exact ⟨fun p => liftC S.hG' (F p), analyticOnNhd_liftC S.hG' hF,
    fun D hD hX u t => congrArg (liftC S.hG') (hFe D hD hX u t)⟩

/-- **The marked tangent is analytic on the relatively open parameter set `physV`.**  The
parameter space `physParam = rawSub × sources` carries the raw data of data; on the open set
`physV` (`isOpen_physV`) the function `(e, u, t) ↦ F (e.1, u, t)` is analytic. -/
theorem exists_analytic_markedTangentC_physV (a₁' ν' eps' : ℝ)
    {F : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ → S.EC}
    (hF : AnalyticOnNhd ℂ F (XiCRaw S.G' (compWeight L a₁') ν' (k + 1) 1 eps' ×ˢ
      (Set.univ : Set (ℂ × ℂ)))) :
    AnalyticOnNhd ℂ (fun p : physParam N S × ℂ × ℂ => F ((p.1.1 : RawData d L (N₁ * L ^ m₁)
      (k + 1) N), p.2.1, p.2.2)) (physV S a₁' ν' eps' ×ˢ (Set.univ : Set (ℂ × ℂ))) := by
  let g : physParam N S × ℂ × ℂ →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ × ℂ :=
    ((rawSub N S.G').subtypeL.comp ((ContinuousLinearMap.fst ℂ _ _).comp
      (ContinuousLinearMap.fst ℂ (physParam N S) (ℂ × ℂ)))).prod
      (ContinuousLinearMap.snd ℂ (physParam N S) (ℂ × ℂ))
  refine hF.comp (g.analyticOnNhd _) fun p hp => ?_
  exact ⟨hp.1.1, trivial⟩

end StepSetting

end Balaban.Fluctuation
