/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegFamily
public import Balaban.Fluctuation.StepLocalInhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Regularity of the background field along the ray (FLUCTUATION.md §2.5, P4 (2.53))

The components of `ℳ_k(y; ψ^{(k)} + t ψ', g)` contain the field `svec (bgField …)` of the datum of
`ψ^{(k)} + s ψ'`.  On the real domain the real background field is the restriction of the analytic
function of the raw data (Theorem 7.2, `theorem72_analytic`, `theorem72_real`), so
`s ↦ bgField (dataU (ψ^{(k)} + s ψ'))` is `C^∞` near every point with `|s| ‖ψ̂‖ < p⁺`
(`contDiffAt_bgFieldRay`); with `p₁ < p⁺` the truncation of any component to the support of `ν_{p₁}`
is a `C¹` family on a neighbourhood of `[0,1]`, bounded with its derivative
(`isC1Family_bgComp`).

`RayData` collects the premises of Proposition 2.6 / Lemma 2.5 (the source hypotheses of
`contDiffAt_Vjoint`), together with the margin radius `p⁺`.  It is inhabited by a non-degenerate step
datum in `StepRegWitness`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The premises of the step** (Lemma 2.2-2.5, Proposition 2.6) with the margin radius `p⁺`:
the weights and mass of the backgrounds, the domain of `θ` and its smallness, the nonvanishing
test `χ_u`, the hypotheses on `C^{(k)1/2}` (the decoupled Green function), and "`β` large"
(`p₁ < p⁺`, P4 (2.40), the radius of Lemma 2.3 (d)). -/
structure RayData (pp : ℝ) where
  ha₁ : 0 < S.a₁
  H : BgHyp d L (k + 1) ϱ S.a S.ν
  δ' : ℝ
  hδ'0 : 0 < δ'
  hδ' : δ' ≤ thm73C3 d L N / 2
  hD'R : InDomainR S.G' S.ν δ' S.D'
  hδ0 : 0 < S.δ
  hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1)
  hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4
  hχu : chiU S.G' S.a S.ν S.δ S.D' = 1
  hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2
  hβ : 0 < S.β
  hpp : 0 < pp
  B₅ : ℝ
  K₂ : ℝ
  hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅
  hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂
  hp40 : pp / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹
  hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * pp ≤ fluctRadius d L N

variable {S} {pp : ℝ}

theorem RayData.betaU_pos (R : S.RayData pp) : 0 < S.betaU :=
  S.betaU_pos' (Nat.pos_of_ne_zero (NeZero.ne L)) R.hβ

/-- The data of the ray lie in the real domain for `|s| ‖ψ̂‖ < p⁺`. -/
theorem RayData.dom (R : S.RayData pp) {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt q.1 q.2)) :=
  S.dataU_inDomainR_plus R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 R.hfam R.hsm R.hχu R.hnorm R.hβ
    R.hpp R.hB5 R.hK2 R.hp40 R.hrad hq

/-- **The interaction is smooth along the ray** (landed `contDiffAt_Vjoint`). -/
theorem RayData.contDiffAt_Vray (R : S.RayData pp) {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.Vk (S.psiAt q.1 q.2)) q :=
  S.contDiffAt_Vjoint R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 R.hfam R.hsm R.hχu R.hnorm R.hβ
    R.hpp R.hB5 R.hK2 R.hp40 R.hrad hq

/-- **The background field is smooth along the ray**: the map
`(s, ψ̂) ↦ bgField (dataU (ψ^{(k)} + s ψ'))` is `C^∞` near every point with `|s| ‖ψ̂‖ < p⁺`
(`bgField` is the restriction to real data of the analytic function of Theorem 7.2). -/
theorem RayData.contDiffAt_bgFieldRay (R : S.RayData pp) {q : ℝ × S.E}
    (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU (S.psiAt q.1 q.2))) q := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν) R.H
  have hpsi := S.contDiff_psiAt
  have hdomC := S.inUnionDomainC_of_R' R.H (R.dom hq)
  have hFat : AnalyticAt ℂ F (S.rawU (S.psiAt q.1 q.2)) :=
    hF _ ⟨S.dataU (S.psiAt q.1 q.2), hdomC, (S.dataU_raw _).symm⟩
  have hFc : ContDiffAt ℝ ⊤ F (S.rawU (S.psiAt q.1 q.2)) :=
    (hFat.contDiffAt (n := ⊤)).restrict_scalars ℝ
  have hraw : ContDiff ℝ ⊤ (fun q : ℝ × S.E => S.rawU (S.psiAt q.1 q.2)) :=
    S.contDiff_rawU.comp hpsi
  have hG1 : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => F (S.rawU (S.psiAt q.1 q.2))) q :=
    hFc.comp q hraw.contDiffAt
  have hmodel : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => (F (S.rawU (S.psiAt q.1 q.2))).1) q :=
    contDiff_fst.contDiffAt.comp q hG1
  refine hmodel.congr_of_eventuallyEq ?_
  have hopen : IsOpen {q : ℝ × S.E | |q.1| * ‖q.2‖ < pp} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  have hdom' := R.dom hq'
  have hdomC' := S.inUnionDomainC_of_R' R.H hdom'
  have hFq := hFe (S.dataU (S.psiAt q'.1 q'.2)) hdomC'
  rw [S.dataU_raw] at hFq
  rw [hFq]
  exact (theorem72_real R.H hdom').1.symm

/-- Smoothness of `s ↦ svec φ(s) y i` from that of `φ(s)`. -/
theorem contDiffAt_svec {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X} {n : WithTop ℕ∞}
    {φ : X → G.Ω 1 × Fin N → ℂ} (hφ : ContDiffAt ℝ n φ x) (y : CTorus d L N₁ m₁ (k + 1))
    (i : Fin N) : ContDiffAt ℝ n (fun z => svec G (φ z) y i) x := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · simp only [svec_of_mem G _ ⟨y, hy⟩ i]
    exact (contDiffAt_pi.1 hφ) (⟨y, hy⟩, i)
  · simp only [svec_of_not_mem G _ hy i]
    exact contDiffAt_const

/-- The component `(y, i)` of `svec φ_k` along the ray: `svec (bgField (dataU (ψ^{(k)} + sψ')))`. -/
noncomputable def bgComp (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) (q : ℝ × S.E) : ℂ :=
  svec (stepG d L N₁ m₁ k ϱ) (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν
    (S.dataU (S.psiAt q.1 q.2))) y i

theorem RayData.contDiffAt_bgComp (R : S.RayData pp) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) : ContDiffAt ℝ ⊤ (S.bgComp y i) q :=
  contDiffAt_svec (R.contDiffAt_bgFieldRay hq) y i

/-- **Regularity of the background along the ray** (target of the fluctuation step): the component
`svec (bgField (dataU (ψ^{(k)} + sψ')))(y)_i`, truncated to the support of `ν_{p₁}`, is a `C¹` family
on an open neighbourhood of `[0,1]`, bounded with its derivative, for `‖ψ̂‖ ≤ p₁ < p⁺`. -/
theorem RayData.isC1Family_bgComp (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ∃ U : Set ℝ, IsC1Family U (S.truncF (S.bgComp y i)) (S.dtruncF (S.bgComp y i)) :=
  S.isC1Family_trunc hp₁ hlt fun q hq =>
    (R.contDiffAt_bgComp y i hq).of_le (by exact_mod_cast le_top)

/-! ### The shifted variable `y = s ψ'` -/

theorem RayData.Kinv_K' (R : S.RayData pp) (x : S.E) : S.Kinv (S.K x) = x := by
  have hd := R.hD'R
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  exact S.Kinv_K R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm x

theorem RayData.K_Kinv (R : S.RayData pp) (y : S.E) : S.K (S.Kinv y) = y := by
  have hinj : Function.Injective S.K := fun a b hab => by
    have := congrArg S.Kinv hab
    rwa [R.Kinv_K', R.Kinv_K'] at this
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj) y
  rw [← hz, R.Kinv_K']

/-- The inverse of the shift `ψ̂ ↦ ψ'`. -/
noncomputable def unshiftU (y : S.E) : S.E := (S.betaU ^ (-(1 / 2 : ℝ)))⁻¹ • S.Kinv y

theorem RayData.shiftU_unshiftU (R : S.RayData pp) (y : S.E) : S.shiftU (S.unshiftU y) = y := by
  have hc : S.betaU ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos R.betaU_pos _).ne'
  unfold shiftU unshiftU
  rw [map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact R.K_Kinv y

theorem RayData.unshiftU_shiftU (R : S.RayData pp) (x : S.E) : S.unshiftU (S.shiftU x) = x := by
  have hc : S.betaU ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos R.betaU_pos _).ne'
  unfold shiftU unshiftU
  rw [map_smul, R.Kinv_K', smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem contDiff_unshiftU : ContDiff ℝ ⊤ S.unshiftU := by
  unfold unshiftU
  exact ((LinearMap.toContinuousLinearMap S.Kinv).contDiff).const_smul _

theorem RayData.psi0_add_eq (R : S.RayData pp) (y : S.E) :
    S.psi0 + y = S.psiAt 1 (S.unshiftU y) := by
  unfold psiAt
  rw [one_smul, R.shiftU_unshiftU]

/-- **From the ray to the block directions**: if `G ∘ ψ_{(s,ψ̂)}` is `C^n` at `(1, ψ̂)` with
`‖ψ̂‖ < p⁺`, then `y ↦ G(ψ^{(k)} + y)` is `C^n` at `y = ψ'(ψ̂)`. -/
theorem RayData.contDiffAt_shift {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : S.RayData pp) {n : WithTop ℕ∞} {G : S.E → V} {y : S.E}
    (h : ContDiffAt ℝ n (fun q : ℝ × S.E => G (S.psiAt q.1 q.2)) (1, S.unshiftU y)) :
    ContDiffAt ℝ n (fun y => G (S.psi0 + y)) y := by
  have hJ : ContDiffAt ℝ ⊤ (fun y : S.E => ((1 : ℝ), S.unshiftU y)) y :=
    (contDiff_const.prodMk contDiff_unshiftU).contDiffAt
  have := h.comp y (hJ.of_le (by exact_mod_cast le_top))
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
  show G (S.psi0 + y') = G (S.psiAt 1 (S.unshiftU y'))
  rw [R.psi0_add_eq]

/-- The segment points `s ψ'(ψ̂)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁ < p⁺` have `‖ψ̂'‖ < p⁺` after unshift. -/
theorem RayData.unshift_ray (R : S.RayData pp) (hlt : S.p₁ < pp) {x : S.E} (hx : ‖x‖ ≤ S.p₁)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |(1 : ℝ)| * ‖S.unshiftU (s • S.shiftU x)‖ < pp := by
  have : S.unshiftU (s • S.shiftU x) = s • x := by
    unfold unshiftU shiftU
    have hc : S.betaU ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos R.betaU_pos _).ne'
    rw [map_smul, map_smul, R.Kinv_K', smul_smul, smul_smul]
    have : (S.betaU ^ (-(1 / 2 : ℝ)))⁻¹ * s * S.betaU ^ (-(1 / 2 : ℝ)) = s := by
      field_simp
    rw [this]
  rw [this, norm_smul, abs_one, one_mul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  calc s * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs.2 hx (norm_nonneg _) zero_le_one
    _ < pp := by linarith

/-- **The interaction `V^{(k)}` is smooth in the block directions along the segments.** -/
theorem RayData.contDiffAt_Vk_shift (R : S.RayData pp) (hlt : S.p₁ < pp) {x : S.E}
    (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (fun y => S.Vk (S.psi0 + y)) (s • S.shiftU x) :=
  R.contDiffAt_shift (R.contDiffAt_Vray (by simpa using R.unshift_ray hlt hx hs))

end StepSetting

end Balaban.Fluctuation
