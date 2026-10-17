/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoreResponseSum
public import Balaban.LargeField.R.PsiZeroAnalyticAction
import Balaban.Multiscale.ConstraintLocality
import Balaban.LargeField.R.PsiZeroAnalyticLocal
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The core-to-action response: the second derivative (Q13-SHARED (2.4), `A₃`)

Let `H_{x i; z' j', z j} = ∂² φ⁰(ψ_k)(x, i) / ∂ψ_k(z')_{j'} ∂ψ_k(z)_j` be the mixed second derivative of the
massless background (the real derivative at `s = 0` of the real derivative at `t = 0` of
`φ⁰(ψ_k + s e_{z' j'} + t e_{z j})(x, i)`).  The background is the restriction to real block fields of the
analytic function `bgFun` of the complex data (Theorem 7.2), and Lemma 4.1 applies to complex data, so:

* `dataC_add_inDomainC`: a complex perturbation `V` of a real field of `Ψ̃(𝔹; τ)` with `|V| ≤ s ≤ 1` lies in
  `Ψ̃^c(𝔹; τ + 4s, τ + 4s)`;
* `norm_deriv_bgFun_le`: at the complex base points `ψ_k + W`, `|W| ≤ s`, the complex derivative along `e_{z j}` is
  bounded by `K_w C_F e^{-γ_w d(x, W_z)}` (Lemma 4.1 for complex data);
* `deriv_deriv_real_eq`, `fderiv_fderiv_symm_of_analyticAt`, `norm_fderiv_fderiv_le_of_sphere` (general facts on
  analytic functions): `H` is the second Fréchet derivative of the analytic extension at `(e_{z' j'}, e_{z j})`, it is
  symmetric in the two directions, and it obeys Cauchy's estimate on a circle;
* `coreResponse_hess_le`: Cauchy's estimate on the circle `|w| = r` gives
  `|H_{x i; z' j', z j}| ≤ (K_w C_F / r) min(e^{-γ_w d(x, W_z)}, e^{-γ_w d(x, W_{z'})})
  ≤ (K_w C_F / r) e^{-(γ_w/2) d(x, W_z)} e^{-(γ_w/2) d(x, W_{z'})}`,
  for `τ + 4r < c₁` and `K₁ (τ + 4r) ≤ min(δ_*, δ_w)`;
* `deriv_deriv_bgField_eq`, `coreResponse_hess_symm`: `H` is `D²φ^C(ψ_k)(E_{z' j'}, E_{z j})` and is symmetric;
* `coreResponse_sum_hess_blocks_le` (opposite index): `∑_{z, z' ∈ Z_f} |H_{x i; z' j', z j}| ≤ A₃`;
* `coreResponse_sum_hess_le` (the third bound of (2.4)): for a set `Z_f` of top-layer blocks,
  `∑_{x ∈ Ω₁} ℓ(x)^{-d} ∑_{z' ∈ Z_f} |H_{x i; z' j', z j}| ≤ A₃` and the same with `L^{-kd}` in place of `ℓ(x)^{-d}`,
  `A₃ = (K_w C_F / r) (e^{(γ_w/2)(2d+1)} C(d, L, γ_w/2))²`, under the separation premise of the counting lemma at the
  rate `γ_w/2` (`2 d log L ≤ (γ_w/4)(ϱ - 1)`; `Dec2.OpSetting` gives it at the rate `γ_w` only).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Filter Topology
  Metric
open scoped ContDiff

section Domain

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- **A complex perturbation of a tube field lies in the complex domain**: for `ψ ∈ Ψ̃(𝔹; τ)` (`τ ≤ 1`) and a complex
block field `V` with `|V(z)| ≤ s ≤ 1`, the data of `ψ + V` lie in `Ψ̃^c(𝔹; τ + 4s, τ + 4s)` (mass `0`). -/
theorem dataC_add_inDomainC {τ s : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ τ ψ) (V : BlockFieldC d L N₀ k N)
    (hV : ∀ z, vn (V z) ≤ s) :
    InDomainC G 0 (τ + 4 * s) (τ + 4 * s) (dataC G ((fun z i => (ψ z i : ℂ)) + V)) := by
  classical
  have hP := (tubeOn_univ_iff G hτ ψ).1 ht
  have hδ : 0 < τ + 4 * s := by linarith
  have hlift : ∀ x, vn (blockLift k V x) ≤ s := fun x => hV _
  refine ⟨liftR ψ, 0, blockLift k V, fun _ _ => 0, ?_, ?_, ?_⟩
  · refine
      { toInPsiTilde :=
          { layerConst := hP.layerConst
            r1 := fun x x' h => (hP.r1 x x' h).trans_le (by linarith)
            r2 := fun x hx => (hP.r2 x hx).trans_le (by linarith)
            r3 := fun x _ => by rw [zero_mul, zero_mul]; positivity
            r4 := by rw [zero_mul, zero_mul]; positivity }
        eps_pos := hδ
        layerConst' := liftSingle_layerConst G V
        hLayerConst' := fun _ _ _ _ _ _ _ => rfl
        c1 := ?_, c2a := ?_, c2b := ?_, c3a := ?_, c3b := ?_ }
    · intro x x' _
      have := vn_sub_le (blockLift k V x) (blockLift k V x')
      linarith [hlift x, hlift x']
    · intro x _
      linarith [hlift x]
    · intro x hx
      set p : Fin N → ℝ := fun i => liftR ψ x i with hp
      set q : Fin N → ℂ := blockLift k V x with hq
      have hp2 : ∑ i, p i ^ 2 < 2 := by
        have := hP.r2 x hx
        have h2 : ∑ i, liftR ψ x i ^ 2 - 1 < τ := (abs_lt.1 this).2
        simp only [hp]
        linarith
      have hq2 : ∑ i, ‖q i‖ ^ 2 ≤ s ^ 2 := by
        rw [← vn_sq]
        exact pow_le_pow_left₀ (vn_nonneg _) (hlift x) 2
      have hCS : (∑ i, |p i| * ‖q i‖) ^ 2 ≤ (∑ i, |p i| ^ 2) * ∑ i, ‖q i‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      have hp2' : ∑ i, |p i| ^ 2 = ∑ i, p i ^ 2 := Finset.sum_congr rfl fun i _ => sq_abs _
      have hX0 : 0 ≤ ∑ i, |p i| * ‖q i‖ :=
        Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have hX : ∑ i, |p i| * ‖q i‖ ≤ 3 / 2 * s := by
        rw [hp2'] at hCS
        have h1 : (∑ i, |p i| * ‖q i‖) ^ 2 ≤ 2 * s ^ 2 := by
          calc _ ≤ (∑ i, p i ^ 2) * ∑ i, ‖q i‖ ^ 2 := hCS
            _ ≤ 2 * s ^ 2 := mul_le_mul hp2.le hq2 (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)
        nlinarith
      have e : ∑ i, ((liftR ψ x i : ℂ) + blockLift k V x i) * ((liftR ψ x i : ℂ) + blockLift k V x i) -
          ∑ i, (liftR ψ x i : ℂ) * (liftR ψ x i : ℂ) = ∑ i, (2 * (p i : ℂ) * q i + q i * q i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hp, hq]
        ring
      rw [e]
      calc ‖∑ i, (2 * (p i : ℂ) * q i + q i * q i)‖ ≤ ∑ i, ‖2 * (p i : ℂ) * q i + q i * q i‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, (2 * (|p i| * ‖q i‖) + ‖q i‖ ^ 2) := by
            refine Finset.sum_le_sum fun i _ => (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have : ‖(2 : ℂ)‖ = 2 := by simp
            rw [this, sq]
            nlinarith [norm_nonneg (q i), abs_nonneg (p i)]
        _ = 2 * ∑ i, |p i| * ‖q i‖ + ∑ i, ‖q i‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ < τ + 4 * s := by nlinarith
    · intro x _
      rw [zero_mul, zero_mul]; positivity
    · intro x _
      rw [zero_mul, zero_mul]; positivity
  · intro x hx i
    simp [dataC, liftSingle_Ψ G _ _ hx, liftR, blockLift]
  · intro x hx i
    simp [dataC, liftSingle_h G _ _ hx]

/-- The data of a tube field perturbed as in `dataC_add_inDomainC` lie in the union domain `𝒟` when
`τ + 4s ≤ c₁`. -/
theorem dataC_add_inUnionDomainC (hd0 : 0 < d) {τ s : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hc : τ + 4 * s ≤ bgC1 d L N) {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ τ ψ)
    (V : BlockFieldC d L N₀ k N) (hV : ∀ z, vn (V z) ≤ s) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 (dataC G ((fun z i => (ψ z i : ℂ)) + V)) :=
  ⟨τ + 4 * s, τ + 4 * s, by linarith, le_rfl, hc.trans (bgC1_le_bgC0 d L N hd0), hc,
    by rw [zero_mul, zero_mul]; positivity, dataC_add_inDomainC hτ hτ1 hs hs1 ht V hV⟩

/-- `|e_{z j}| = 1` at `z` and `0` elsewhere; in particular `|t e_{z j}(z')| ≤ |t|`. -/
theorem vn_smul_single_le (t : ℂ) (z z' : Torus d (N₀ * L ^ (k - k))) (j : Fin N) :
    vn ((t • (Pi.single z (Pi.single j (1 : ℂ)) : BlockFieldC d L N₀ k N)) z') ≤ ‖t‖ := by
  have h : vn ((t • (Pi.single z (Pi.single j (1 : ℂ)) : BlockFieldC d L N₀ k N)) z') ^ 2 ≤ ‖t‖ ^ 2 := by
    rw [vn_sq]
    by_cases hz : z' = z
    · subst hz
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · simp [hz]
  exact le_of_sq_le_sq (by simpa using h) (norm_nonneg t) |>.trans_eq rfl

end Domain

section Complex

variable {d L N : ℕ} [NeZero L] {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ}

/-- **Lemma 4.1 at complex base points: the complex one-site derivative.**  For `ψ ∈ Ψ̃(𝔹; τ)`, a complex block field
`W` with `|W| ≤ s ≤ 1/2`, `τ + 4s < c₁` and `K₁ (τ + 4s) ≤ min(δ_*, δ_w)`, the complex derivative at `t = 0` of
`t ↦ φ^C(ψ + W + t e_{z j})(x, i)` (`φ^C = (bgFun ·).1`, the analytic background of Theorem 7.2) is bounded by
`K_w C_F e^{-γ_w d(x, W_z)}`. -/
theorem norm_deriv_bgFun_le {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw) (hKw : 0 ≤ Kw) (hδw : 0 < δw)
    (hd0 : 0 < d) (H : BgHyp d L k ϱ a 0) (hOp : Dec2.OpSetting G a 0) {τ s : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : τ + 4 * s < bgC1 d L N)
    (hK : bgK1 d L N * (τ + 4 * s) ≤ min (deltaStar d L N) δw)
    {ψ : BlockField d L (N₁ * L ^ m₁) k N} (ht : TubeOn G Set.univ τ ψ)
    (W : BlockFieldC d L (N₁ * L ^ m₁) k N) (hWs : ∀ z, vn (W z) ≤ s)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j : Fin N) (x : G.Ω 1) (i : Fin N) :
    ‖deriv (fun t : ℂ => (bgFun G H (rawMapC G ((fun z' i' => (ψ z' i' : ℂ)) + W +
        t • (Pi.single z (Pi.single j (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N)))).1 (x, i)) 0‖ ≤
      Kw * cF d L * decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
  classical
  set P : BlockFieldC d L (N₁ * L ^ m₁) k N := fun z' i' => (ψ z' i' : ℂ) with hP
  set E : BlockFieldC d L (N₁ * L ^ m₁) k N := Pi.single z (Pi.single j (1 : ℂ)) with hE
  set C := Kw * cF d L * decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)
    with hC
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg hKw (cF_pos d L).le) (decay_nonneg _ _)
  have hds := deltaStar_pos d L N hd0
  set η := min (min (1 / 2) ((bgC1 d L N - (τ + 4 * s)) / 4)) (min (deltaStar d L N) δw) with hη
  have hη0 : 0 < η := lt_min (lt_min (by norm_num) (by linarith)) (lt_min hds hδw)
  have hη1 : η ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ (bgC1 d L N - (τ + 4 * s)) / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ deltaStar d L N := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η ≤ δw := (min_le_right _ _).trans (min_le_right _ _)
  have hc10 := bgC1_le_bgC0 d L N hd0
  refine norm_deriv_le_of_lip' hC0 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hη0] with t htη
  have ht' : ‖t‖ ≤ η := by simpa using htη
  have hVt : ∀ z', vn ((W + t • E) z') ≤ s + ‖t‖ := fun z' =>
    (vn_add _ _).trans (add_le_add (hWs z') (vn_smul_single_le t z z' j))
  have hst : s + ‖t‖ ≤ 1 := by linarith
  have hc' : τ + 4 * (s + ‖t‖) ≤ bgC1 d L N := by linarith
  have hD := dataC_add_inDomainC hτ hτ1 hs (by linarith) ht W hWs
  have hDu := dataC_add_inDomainC hτ hτ1 (by positivity) hst ht (W + t • E) hVt
  have hUD := dataC_add_inUnionDomainC hd0 hτ hτ1 hs (by linarith) hc.le ht W hWs
  have hUDu := dataC_add_inUnionDomainC hd0 hτ hτ1 (by positivity) hst hc' ht (W + t • E) hVt
  have e0 : (bgFun G H (rawMapC G (P + W + (0 : ℂ) • E))).1 =
      bgFieldC G a 0 (bgC0 d L N) (dataC G (P + W)) := by
    rw [zero_smul, add_zero]
    exact congrArg Prod.fst (bgFun_eq G H _ hUD)
  have et : (bgFun G H (rawMapC G (P + W + t • E))).1 =
      bgFieldC G a 0 (bgC0 d L N) (dataC G (P + (W + t • E))) := by
    rw [add_assoc]
    exact congrArg Prod.fst (bgFun_eq G H _ hUDu)
  set δΨ : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ := fun y i' =>
    (dataC G (P + (W + t • E))).Ψ y i' - (dataC G (P + W)).Ψ y i' with hδΨ
  have hval : ∀ y ∈ dataSites G, δΨ y = (t • E) (jBlock d L (N₁ * L ^ m₁) k k y) := by
    intro y hy
    funext i'
    simp only [hδΨ, dataC, liftSingle_Ψ G _ _ hy, Pi.add_apply]
    ring
  have hsupp : ∀ y ∉ fib d L (N₁ * L ^ m₁) k k z, δΨ y = 0 := by
    intro y hy
    by_cases hyd : y ∈ dataSites G
    · rw [hval y hyd]
      have hne : jBlock d L (N₁ * L ^ m₁) k k y ≠ z := fun h => hy (mem_fib.2 h)
      funext i'
      simp [hE, hne]
    · funext i'
      simp [hδΨ, (dataC G (P + (W + t • E))).Ψ_zero y hyd, (dataC G (P + W)).Ψ_zero y hyd]
  have hΨ : ∀ y i', (dataC G (P + (W + t • E))).Ψ y i' = (dataC G (P + W)).Ψ y i' + δΨ y i' :=
    fun y i' => by simp [hδΨ]
  have hh : ∀ y i', (dataC G (P + (W + t • E))).h y i' = (dataC G (P + W)).h y i' := by
    intro y i'
    by_cases hy : y ∈ G.Ω 1
    · simp [dataC, liftSingle_h G _ _ hy]
    · rw [(dataC G (P + (W + t • E))).h_zero y hy, (dataC G (P + W)).h_zero y hy]
  have hdΨ : ∀ y ∈ dataSites G, vn (δΨ y) ≤ ‖t‖ := fun y hy => by
    rw [hval y hy]
    exact vn_smul_single_le t z _ j
  have hν : ∀ ε δ : ℝ, (0 : ℝ) * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2 := fun ε δ => by
    rw [zero_mul, zero_mul]; positivity
  have hF := lemma41_domain_S hW hd0 H hOp (by linarith) le_rfl ((by linarith : τ + 4 * s ≤ bgC1 d L N).trans hc10)
    (by linarith) (hν _ _) hD (by positivity) le_rfl (hc'.trans hc10) hc' (hν _ _) hDu
    (hK.trans (min_le_left _ _)) (hK.trans (min_le_right _ _)) (fib d L (N₁ * L ^ m₁) k k z) hsupp hΨ hh
    (norm_nonneg t) (ht'.trans hη3) (ht'.trans hη4) hdΨ
  have hv := hF.val x i
  simp only [Pi.sub_apply] at hv
  show ‖(bgFun G H (rawMapC G (P + W + t • E))).1 (x, i) - (bgFun G H (rawMapC G (P + W + (0 : ℂ) • E))).1 (x, i)‖ ≤
    C * ‖t - 0‖
  rw [et, e0, sub_zero]
  calc _ ≤ Kw * (cF d L * ‖t‖) * decay (gammaW d)
        (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := hv
    _ = C * ‖t‖ := by rw [hC]; ring

end Complex

section AnalyticCauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : E → ℂ}

/-- The derivative along a complex line of a function analytic at the base point. -/
theorem hasDerivAt_line_of_analyticAt {Q : E} (h : AnalyticAt ℂ Φ Q) (E₂ : E) :
    HasDerivAt (fun t : ℂ => Φ (Q + t • E₂)) (fderiv ℂ Φ Q E₂) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => Q + t • E₂) E₂ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const E₂).const_add Q
  have h2 : HasFDerivAt Φ (fderiv ℂ Φ Q) (Q + (0 : ℂ) • E₂) := by
    rw [zero_smul, add_zero]
    exact h.differentiableAt.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℂ) h1

/-- The derivative along a complex line of the Fréchet derivative of a function analytic at the base point. -/
theorem hasDerivAt_fderiv_line {P : E} (h : AnalyticAt ℂ Φ P) (E₁ E₂ : E) :
    HasDerivAt (fun w : ℂ => fderiv ℂ Φ (P + w • E₁) E₂) (fderiv ℂ (fderiv ℂ Φ) P E₁ E₂) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => P + w • E₁) E₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const E₁).const_add P
  have hd0 : DifferentiableAt ℂ (fderiv ℂ Φ) P := h.fderiv.differentiableAt
  have hd : HasFDerivAt (fderiv ℂ Φ) (fderiv ℂ (fderiv ℂ Φ) P) (P + (0 : ℂ) • E₁) := by
    rw [zero_smul, add_zero]
    exact hd0.hasFDerivAt
  have h5 := hd.comp_hasDerivAt (0 : ℂ) h1
  have h4 := h5.clm_apply (hasDerivAt_const (0 : ℂ) E₂)
  exact h4.congr_deriv (by rw [Function.comp_apply, map_zero, add_zero])

/-- **Cauchy's estimate for a mixed second derivative**: if `Φ` is analytic at the points `P + w E₁`, `|w| ≤ r`, and
the derivative of `Φ` along `E₂` at these points is bounded by `B` on the circle `|w| = r`, then
`|D²Φ(P)(E₁, E₂)| ≤ B / r`. -/
theorem norm_fderiv_fderiv_le_of_sphere {P E₁ E₂ : E} {r B : ℝ} (hr : 0 < r)
    (h1 : ∀ w ∈ closedBall (0 : ℂ) r, AnalyticAt ℂ Φ (P + w • E₁))
    (h2 : ∀ w ∈ sphere (0 : ℂ) r, ‖deriv (fun t : ℂ => Φ (P + w • E₁ + t • E₂)) 0‖ ≤ B) :
    ‖fderiv ℂ (fderiv ℂ Φ) P E₁ E₂‖ ≤ B / r := by
  set g : ℂ → ℂ := fun w => fderiv ℂ Φ (P + w • E₁) E₂ with hg
  have hdiff : DifferentiableOn ℂ g (closedBall 0 r) := by
    intro w hw
    have ha := (h1 w hw).fderiv
    have hin : DifferentiableAt ℂ (fun w' : ℂ => P + w' • E₁) w := by fun_prop
    exact ((ha.differentiableAt.comp w hin).clm_apply (differentiableAt_const E₂)).differentiableWithinAt
  have hcl : DiffContOnCl ℂ g (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball 0 hr.ne']
  have hsph : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ B := by
    intro w hw
    have e := (hasDerivAt_line_of_analyticAt (h1 w (sphere_subset_closedBall hw)) E₂).deriv
    simp only [hg]
    rw [← e]
    exact h2 w hw
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hsph
  have hP : AnalyticAt ℂ Φ P := by simpa using h1 0 (mem_closedBall_self hr.le)
  rw [← (hasDerivAt_fderiv_line hP E₁ E₂).deriv]
  exact hc

/-- **The real mixed second derivative of the restriction to real lines**: if `f s t = Φ(P + s E₁ + t E₂)` for real
`s, t` near `0` and `Φ` is analytic at `P`, then `∂_s ∂_t f(0, 0) = D²Φ(P)(E₁, E₂)`. -/
theorem deriv_deriv_real_eq {P E₁ E₂ : E} (h : AnalyticAt ℂ Φ P) {f : ℝ → ℝ → ℂ}
    (hf : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), f s t = Φ (P + (s : ℂ) • E₁ + (t : ℂ) • E₂)) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => f s t) 0) 0 = fderiv ℂ (fderiv ℂ Φ) P E₁ E₂ := by
  have hev : ∀ᶠ Q in 𝓝 P, AnalyticAt ℂ Φ Q := h.eventually_analyticAt
  have hcont : Tendsto (fun s : ℝ => P + (s : ℂ) • E₁) (𝓝 0) (𝓝 P) := by
    have hc : Continuous (fun s : ℝ => P + (s : ℂ) • E₁) := by fun_prop
    simpa using hc.tendsto 0
  have hJ : (fun s : ℝ => deriv (fun t : ℝ => f s t) 0) =ᶠ[𝓝 0]
      fun s : ℝ => fderiv ℂ Φ (P + (s : ℂ) • E₁) E₂ := by
    filter_upwards [hf, hcont.eventually hev] with s hs ha
    have h0 : HasDerivAt (fun t : ℂ => Φ (P + (s : ℂ) • E₁ + t • E₂))
        (fderiv ℂ Φ (P + (s : ℂ) • E₁) E₂) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hasDerivAt_line_of_analyticAt ha E₂
    exact (h0.comp_ofReal.congr_of_eventuallyEq hs).deriv
  rw [hJ.deriv_eq]
  have h0 : HasDerivAt (fun w : ℂ => fderiv ℂ Φ (P + w • E₁) E₂) (fderiv ℂ (fderiv ℂ Φ) P E₁ E₂)
      ((0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero]
    exact hasDerivAt_fderiv_line h E₁ E₂
  exact h0.comp_ofReal.deriv

/-- The second derivative of an analytic function is symmetric. -/
theorem fderiv_fderiv_symm_of_analyticAt {P : E} (h : AnalyticAt ℂ Φ P) (E₁ E₂ : E) :
    fderiv ℂ (fderiv ℂ Φ) P E₁ E₂ = fderiv ℂ (fderiv ℂ Φ) P E₂ E₁ :=
  (h.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega E₁ E₂

end AnalyticCauchy

section Hess

variable {d L N : ℕ} [NeZero L]

theorem single_single_apply {α β R : Type*} [DecidableEq α] [DecidableEq β] [Zero R] (a : α) (b : β) (c : R)
    (x : α) (y : β) : (Pi.single a (Pi.single b c) : α → β → R) x y = if x = a ∧ y = b then c else 0 := by
  by_cases hx : x = a
  · subst hx
    by_cases hy : y = b
    · subst hy; simp
    · simp [hy]
  · simp [hx]

/-- The complexification of the real field `ψ + s e_{z' j'} + t e_{z j}` is `ψ + s E_{z' j'} + t E_{z j}`. -/
theorem ofReal_add_smul_single {N₀ k : ℕ} (ψ : BlockField d L N₀ k N) (s t : ℝ)
    (z z' : Torus d (N₀ * L ^ (k - k))) (j j' : Fin N) :
    (fun z'' i'' => ((ψ + s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L N₀ k N) +
        t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L N₀ k N)) z'' i'' : ℂ)) =
      (fun z'' i'' => (ψ z'' i'' : ℂ)) + (s : ℂ) • (Pi.single z' (Pi.single j' (1 : ℂ)) : BlockFieldC d L N₀ k N) +
        (t : ℂ) • (Pi.single z (Pi.single j (1 : ℂ)) : BlockFieldC d L N₀ k N) := by
  funext z'' i''
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_single_apply]
  split_ifs <;> simp

/-- **The second derivative of the massless background** (the `H` of Q13-SHARED (2.4)).  There are `K_w, δ_w > 0`
depending only on `(d, L, N)` such that for `ψ_k ∈ Ψ̃(𝔹; τ)` (`τ ≤ 1`) and a Cauchy radius `0 < r ≤ 1/2` with
`τ + 4r < c₁` and `K₁ (τ + 4r) ≤ min(δ_*, δ_w)`, the mixed derivative
`H_{x i; z' j', z j} = ∂_s ∂_t φ⁰(ψ_k + s e_{z' j'} + t e_{z j})(x, i)` at `s = t = 0` satisfies
`|H| ≤ (K_w C_F / r) min(e^{-γ_w d(x, W_z)}, e^{-γ_w d(x, W_{z'})})`. -/
theorem coreResponse_hess_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 →
        ∀ {τ r : ℝ}, 0 < τ → τ ≤ 1 → 0 < r → r ≤ 1 / 2 → τ + 4 * r < bgC1 d L N →
        bgK1 d L N * (τ + 4 * r) ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (z z' : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j j' : Fin N) (x : G.Ω 1) (i : Fin N),
        ‖deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
            s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
            t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0‖ ≤
          Kw * cF d L / r * min
            (decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x))
            (decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z')) x)) := by
  obtain ⟨Kw, δw, hK, hδw, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp τ r hτ hτ1 hr hr2 hc hKs ψ ht z z' j j' x i
  have hd0 : 0 < d := by omega
  have hc10 := bgC1_le_bgC0 d L N hd0
  have hτc : τ ≤ bgC1 d L N := by linarith
  set P : BlockFieldC d L (N₁ * L ^ m₁) k N := fun z'' i'' => (ψ z'' i'' : ℂ) with hP
  set E : BlockFieldC d L (N₁ * L ^ m₁) k N := Pi.single z (Pi.single j (1 : ℂ)) with hE
  set E' : BlockFieldC d L (N₁ * L ^ m₁) k N := Pi.single z' (Pi.single j' (1 : ℂ)) with hE'
  set Φ : BlockFieldC d L (N₁ * L ^ m₁) k N → ℂ := fun Q => (bgFun G H (rawMapC G Q)).1 (x, i) with hΦ
  have hAn : ∀ (z₀ : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j₀ : Fin N) (w : ℂ), ‖w‖ ≤ r →
      AnalyticAt ℂ Φ (P + w • (Pi.single z₀ (Pi.single j₀ (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N)) := by
    intro z₀ j₀ w hw
    have hU := dataC_add_inUnionDomainC hd0 hτ hτ1 (norm_nonneg w) (by linarith) (by linarith) ht _
      (fun z'' => vn_smul_single_le w z₀ z'' j₀)
    have hB := bgFun_analytic G H (rawMapC G (P + w •
      (Pi.single z₀ (Pi.single j₀ (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N))) ⟨_, hU, rfl⟩
    exact analyticAt_apply (analyticAt_fst.comp (hB.comp (analyticAt_rawMapC G _))) (x, i)
  have hPan : AnalyticAt ℂ Φ P := by simpa using hAn z j 0 (by simp [hr.le])
  have hreal : ∀ ψ'' : BlockField d L (N₁ * L ^ m₁) k N, TubeOn G Set.univ τ ψ'' →
      bgField G a 0 (dataR G ψ'') (x, i) = Φ (fun z'' i'' => (ψ'' z'' i'' : ℂ)) := by
    intro ψ'' ht''
    have hC := inUnionDomainC_of_tube G hτ (hτc.trans hc10) hτc ht''
    have hR := inUnionDomainR_of_tube G hτ hτc ht''
    have e1 : rawMapC G (fun z'' i'' => (ψ'' z'' i'' : ℂ)) = ((dataR G ψ'').Ψ, (dataR G ψ'').h) := rfl
    simp only [hΦ, e1, bgFun_eq G H _ hC, (theorem72_real H hR).1]
  have hf : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      bgField G a 0 (dataR G (ψ +
          s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
          t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i) =
        Φ (P + (s : ℂ) • E' + (t : ℂ) • E) := by
    have hcont : Continuous fun p : ℝ × ℝ => ψ +
        p.1 • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
        p.2 • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) := by fun_prop
    have ht0 := hcont.tendsto' ((0 : ℝ), (0 : ℝ)) ψ (by simp)
    have hev := ht0.eventually (eventually_tubeOn G ht)
    rw [nhds_prod_eq] at hev
    filter_upwards [hev.curry] with s hs
    filter_upwards [hs] with t htube
    rw [hreal _ htube, ofReal_add_smul_single ψ s t z z' j j']
  rw [deriv_deriv_real_eq hPan hf]
  have hsph : ∀ (z₁ : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j₁ : Fin N) (z₂ : Torus d (N₁ * L ^ m₁ * L ^ (k - k)))
      (j₂ : Fin N),
      ‖fderiv ℂ (fderiv ℂ Φ) P (Pi.single z₁ (Pi.single j₁ (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N)
          (Pi.single z₂ (Pi.single j₂ (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N)‖ ≤
        Kw * cF d L * decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z₂)) x) / r := by
    intro z₁ j₁ z₂ j₂
    refine norm_fderiv_fderiv_le_of_sphere hr (fun w hw => hAn z₁ j₁ w (by simpa using hw)) ?_
    intro w hw
    have hwr : ‖w‖ = r := by simpa using hw
    exact norm_deriv_bgFun_le hW hK.le hδw hd0 H hOp hτ hτ1 (norm_nonneg w) (by linarith) (by linarith)
      (by rw [hwr]; exact hKs) ht _ (fun z'' => vn_smul_single_le w z₁ z'' j₁) z₂ j₂ x i
  have h1 := hsph z' j' z j
  have h2 := hsph z j z' j'
  rw [fderiv_fderiv_symm_of_analyticAt hPan] at h2
  have hcr : 0 ≤ Kw * cF d L / r := div_nonneg (mul_nonneg hK.le (cF_pos d L).le) hr.le
  rcases min_cases (decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x))
    (decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z')) x)) with hm | hm
  · rw [hm.1]
    calc _ ≤ _ := h1
      _ = _ := by ring
  · rw [hm.1]
    calc _ ≤ _ := h2
      _ = _ := by ring

/-- `min(e^{-γ D}, e^{-γ D'}) ≤ e^{-(γ/2) D} e^{-(γ/2) D'}`. -/
theorem min_decay_le_mul_decay_half {γ : ℝ} (D D' : ENNReal) :
    min (decay γ D) (decay γ D') ≤ decay (γ / 2) D * decay (γ / 2) D' := by
  have e : ∀ D'' : ENNReal, decay γ D'' = decay (γ / 2) D'' * decay (γ / 2) D'' := fun D'' => by
    rw [← Localization.decay_split]; ring_nf
  rw [e D, e D']
  have hu := decay_nonneg (γ / 2) D
  have hv := decay_nonneg (γ / 2) D'
  rcases le_total (decay (γ / 2) D) (decay (γ / 2) D') with h | h
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h hu)
  · exact (min_le_right _ _).trans (by
      calc decay (γ / 2) D' * decay (γ / 2) D' ≤ decay (γ / 2) D' * decay (γ / 2) D :=
            mul_le_mul_of_nonneg_left h hv
        _ = _ := mul_comm _ _)

/-- **(2.4), third bound**: for a top-layer block `z` and a set `Z_f` of top-layer blocks,
`∑_{x ∈ Ω₁} ℓ(x)^{-d} ∑_{z' ∈ Z_f} |H_{x i; z' j', z j}| ≤ A₃` and `L^{-kd} ∑_x ∑_{z' ∈ Z_f} |H_{x i; z' j', z j}| ≤ A₃`,
`A₃ = (K_w C_F / r) (e^{(γ_w/2)(2d+1)} C(d, L, γ_w/2))²`, uniformly in the torus, `k`, `z`, `Z_f`, the indices and
`ψ_k ∈ Ψ̃(𝔹; τ)`.  The counting is at the rate `γ_w/2`, whose separation premise
`2 d log L ≤ (γ_w/4)(ϱ - 1)` is a hypothesis (`Dec2.OpSetting` gives the rate `γ_w`). -/
theorem coreResponse_sum_hess_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 → 1 ≤ k →
        2 * d * Real.log L ≤ gammaW d / 4 * (ϱ - 1) →
        ∀ {τ r : ℝ}, 0 < τ → τ ≤ 1 → 0 < r → r ≤ 1 / 2 → τ + 4 * r < bgC1 d L N →
        bgK1 d L N * (τ + 4 * r) ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))), OverTop G ({z} : Set _) →
        ∀ (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))), (∀ z' ∈ Zf, OverTop G ({z'} : Set _)) →
        ∀ (j j' i : Fin N),
        ∑ x : G.Ω 1, siteWeight G x * ∑ z' ∈ Zf,
            ‖deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
              s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
              t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0‖ ≤
          Kw * cF d L / r * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2)) ^ 2 ∧
        (((L : ℝ) ^ k) ^ d)⁻¹ * ∑ x : G.Ω 1, ∑ z' ∈ Zf,
            ‖deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
              s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
              t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0‖ ≤
          Kw * cF d L / r * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2)) ^ 2 := by
  obtain ⟨Kw, δw, hK, hδw, hH⟩ := coreResponse_hess_le (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp hk hsep2 τ r hτ hτ1 hr hr2 hc hKs ψ ht z hz Zf hZ j j' i
  obtain ⟨hϱ, -⟩ := opSetting_counting hOp
  have hγ : 0 < gammaW d / 2 := by
    unfold gammaW; have := agmonRate_pos (d := d) (by omega); positivity
  have hcond : 2 * d * Real.log L ≤ gammaW d / 2 / 2 * (ϱ - 1) := by
    have e : gammaW d / 2 / 2 = gammaW d / 4 := by ring
    rw [e]; exact hsep2
  set S := Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2) with hS
  set c := Kw * cF d L / r with hcdef
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg hK.le (cF_pos d L).le) hr.le
  set D : Torus d (N₁ * L ^ m₁ * L ^ (k - k)) → G.Ω 1 → ENNReal := fun z₀ x =>
    siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z₀)) x with hD
  set Hn : G.Ω 1 → Torus d (N₁ * L ^ m₁ * L ^ (k - k)) → ℝ := fun x z' =>
    ‖deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
      s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
      t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0‖ with hHn
  have hx : ∀ x : G.Ω 1, ∑ z' ∈ Zf, Hn x z' ≤ c * (decay (gammaW d / 2) (D z x) * S) := by
    intro x
    calc ∑ z' ∈ Zf, Hn x z'
        ≤ ∑ z' ∈ Zf, c * (decay (gammaW d / 2) (D z x) * decay (gammaW d / 2) (D z' x)) := by
          refine Finset.sum_le_sum fun z' _ => ?_
          exact (hH H hOp hτ hτ1 hr hr2 hc hKs ht z z' j j' x i).trans
            (mul_le_mul_of_nonneg_left (min_decay_le_mul_decay_half _ _) hc0)
      _ = c * (decay (gammaW d / 2) (D z x) * ∑ z' ∈ Zf, decay (gammaW d / 2) (D z' x)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ c * (decay (gammaW d / 2) (D z x) * S) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (decay_nonneg _ _)) hc0
          exact sum_decay_shadow_fib_le hk hϱ hγ hcond Zf hZ x
  have h1 : ∑ x : G.Ω 1, siteWeight G x * ∑ z' ∈ Zf, Hn x z' ≤ c * S ^ 2 := by
    calc ∑ x : G.Ω 1, siteWeight G x * ∑ z' ∈ Zf, Hn x z'
        ≤ ∑ x : G.Ω 1, c * S * (siteWeight G x * decay (gammaW d / 2) (D z x)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          calc siteWeight G x * ∑ z' ∈ Zf, Hn x z'
              ≤ siteWeight G x * (c * (decay (gammaW d / 2) (D z x) * S)) :=
                mul_le_mul_of_nonneg_left (hx x) (siteWeight_nonneg G _)
            _ = _ := by ring
      _ = c * S * ∑ x : G.Ω 1, siteWeight G x * decay (gammaW d / 2) (D z x) := by
          rw [Finset.mul_sum]
      _ ≤ c * S * S := by
          have hS0 : 0 ≤ S := mul_nonneg (Real.exp_pos _).le
            (tsum_nonneg fun m => by positivity)
          exact mul_le_mul_of_nonneg_left (sum_siteWeight_decay_shadow_fib_le hk hϱ hγ hcond hz)
            (mul_nonneg hc0 hS0)
      _ = c * S ^ 2 := by ring
  refine ⟨h1, le_trans ?_ h1⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (inv_pow_le_siteWeight x)
    (Finset.sum_nonneg fun z' _ => norm_nonneg _)

/-- **The real second derivative is the second Fréchet derivative of the analytic background**: for
`ψ_k ∈ Ψ̃(𝔹; τ)` (`τ ≤ 1`, `τ ≤ c₁`), `∂_s ∂_t φ⁰(ψ_k + s e_{z' j'} + t e_{z j})(x, i)` at `0` is
`D²φ^C(ψ_k)(E_{z' j'}, E_{z j})(x, i)`, `φ^C = (bgFun ·).1` the analytic background of Theorem 7.2. -/
theorem deriv_deriv_bgField_eq {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ} (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτc : τ ≤ bgC1 d L N) {ψ : BlockField d L (N₁ * L ^ m₁) k N} (ht : TubeOn G Set.univ τ ψ)
    (z z' : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j j' : Fin N) (x : G.Ω 1) (i : Fin N) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
        s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
        t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0 =
      fderiv ℂ (fderiv ℂ (fun Q : BlockFieldC d L (N₁ * L ^ m₁) k N => (bgFun G H (rawMapC G Q)).1 (x, i)))
        (fun z'' i'' => (ψ z'' i'' : ℂ))
        (Pi.single z' (Pi.single j' (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N)
        (Pi.single z (Pi.single j (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hc10 := bgC1_le_bgC0 d L N hd0
  set P : BlockFieldC d L (N₁ * L ^ m₁) k N := fun z'' i'' => (ψ z'' i'' : ℂ) with hP
  set Φ : BlockFieldC d L (N₁ * L ^ m₁) k N → ℂ := fun Q => (bgFun G H (rawMapC G Q)).1 (x, i) with hΦ
  have hPan : AnalyticAt ℂ Φ P := by
    have hU := dataC_add_inUnionDomainC hd0 hτ hτ1 le_rfl zero_le_one (by linarith) ht
      (0 : BlockFieldC d L (N₁ * L ^ m₁) k N) (fun z'' => by simp [vn])
    have hB := bgFun_analytic G H (rawMapC G (P + 0)) ⟨_, hU, rfl⟩
    have := analyticAt_apply (analyticAt_fst.comp (hB.comp (analyticAt_rawMapC G _))) (x, i)
    simpa using this
  have hreal : ∀ ψ'' : BlockField d L (N₁ * L ^ m₁) k N, TubeOn G Set.univ τ ψ'' →
      bgField G a 0 (dataR G ψ'') (x, i) = Φ (fun z'' i'' => (ψ'' z'' i'' : ℂ)) := by
    intro ψ'' ht''
    have hC := inUnionDomainC_of_tube G hτ (hτc.trans hc10) hτc ht''
    have hR := inUnionDomainR_of_tube G hτ hτc ht''
    have e1 : rawMapC G (fun z'' i'' => (ψ'' z'' i'' : ℂ)) = ((dataR G ψ'').Ψ, (dataR G ψ'').h) := rfl
    simp only [hΦ, e1, bgFun_eq G H _ hC, (theorem72_real H hR).1]
  have hf : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      bgField G a 0 (dataR G (ψ +
          s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
          t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i) =
        Φ (P + (s : ℂ) • (Pi.single z' (Pi.single j' (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N) +
          (t : ℂ) • (Pi.single z (Pi.single j (1 : ℂ)) : BlockFieldC d L (N₁ * L ^ m₁) k N)) := by
    have hcont : Continuous fun p : ℝ × ℝ => ψ +
        p.1 • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
        p.2 • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) := by fun_prop
    have ht0 := hcont.tendsto' ((0 : ℝ), (0 : ℝ)) ψ (by simp)
    have hev := ht0.eventually (eventually_tubeOn G ht)
    rw [nhds_prod_eq] at hev
    filter_upwards [hev.curry] with s hs
    filter_upwards [hs] with t htube
    rw [hreal _ htube, ofReal_add_smul_single ψ s t z z' j j']
  exact deriv_deriv_real_eq hPan hf

/-- **Symmetry of the second derivative**: `H_{x i; z' j', z j} = H_{x i; z j, z' j'}` (the two orders of the real
mixed derivative of the massless background agree). -/
theorem coreResponse_hess_symm {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ} (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτc : τ ≤ bgC1 d L N) {ψ : BlockField d L (N₁ * L ^ m₁) k N} (ht : TubeOn G Set.univ τ ψ)
    (z z' : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j j' : Fin N) (x : G.Ω 1) (i : Fin N) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
        s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
        t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
        s • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
        t • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0 := by
  have hd0 : 0 < d := by have := H.hd; omega
  rw [deriv_deriv_bgField_eq H hτ hτ1 hτc ht z z' j j' x i, deriv_deriv_bgField_eq H hτ hτ1 hτc ht z' z j' j x i]
  have hU := dataC_add_inUnionDomainC hd0 hτ hτ1 le_rfl zero_le_one (by linarith) ht
    (0 : BlockFieldC d L (N₁ * L ^ m₁) k N) (fun z'' => by simp [vn])
  have hB := bgFun_analytic G H (rawMapC G ((fun z'' i'' => (ψ z'' i'' : ℂ)) + 0)) ⟨_, hU, rfl⟩
  have hPan : AnalyticAt ℂ (fun Q : BlockFieldC d L (N₁ * L ^ m₁) k N => (bgFun G H (rawMapC G Q)).1 (x, i))
      (fun z'' i'' => (ψ z'' i'' : ℂ)) := by
    have := analyticAt_apply (analyticAt_fst.comp (hB.comp (analyticAt_rawMapC G _))) (x, i)
    simpa using this
  exact fderiv_fderiv_symm_of_analyticAt hPan _ _

/-- **(2.4), the opposite-index bound for the second derivative**: for `x ∈ Ω₁` and a set `Z_f` of top-layer blocks,
`∑_{z ∈ Z_f} ∑_{z' ∈ Z_f} |H_{x i; z' j', z j}| ≤ (K_w C_F / r) (e^{(γ_w/2)(2d+1)} C(d, L, γ_w/2))²`. -/
theorem coreResponse_sum_hess_blocks_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 → 1 ≤ k →
        2 * d * Real.log L ≤ gammaW d / 4 * (ϱ - 1) →
        ∀ {τ r : ℝ}, 0 < τ → τ ≤ 1 → 0 < r → r ≤ 1 / 2 → τ + 4 * r < bgC1 d L N →
        bgK1 d L N * (τ + 4 * r) ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))), (∀ z' ∈ Zf, OverTop G ({z'} : Set _)) →
        ∀ (j j' : Fin N) (x : G.Ω 1) (i : Fin N),
        ∑ z ∈ Zf, ∑ z' ∈ Zf,
            ‖deriv (fun s : ℝ => deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ +
              s • (Pi.single z' (Pi.single j' (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N) +
              t • (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0) 0‖ ≤
          Kw * cF d L / r * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2)) ^ 2 := by
  obtain ⟨Kw, δw, hK, hδw, hH⟩ := coreResponse_hess_le (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp hk hsep2 τ r hτ hτ1 hr hr2 hc hKs ψ ht Zf hZ j j' x i
  obtain ⟨hϱ, -⟩ := opSetting_counting hOp
  have hγ : 0 < gammaW d / 2 := by
    unfold gammaW; have := agmonRate_pos (d := d) (by omega); positivity
  have hcond : 2 * d * Real.log L ≤ gammaW d / 2 / 2 * (ϱ - 1) := by
    have e : gammaW d / 2 / 2 = gammaW d / 4 := by ring
    rw [e]; exact hsep2
  set S := Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2) with hS
  set c := Kw * cF d L / r with hcdef
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg hK.le (cF_pos d L).le) hr.le
  have hsum := sum_decay_shadow_fib_le (G := G) hk hϱ hγ hcond Zf hZ x
  have hS0 : 0 ≤ S := mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun m => by positivity)
  calc _ ≤ ∑ z ∈ Zf, ∑ z' ∈ Zf, c *
        (decay (gammaW d / 2) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) *
          decay (gammaW d / 2) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z')) x)) := by
        refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun z' _ => ?_
        exact (hH H hOp hτ hτ1 hr hr2 hc hKs ht z z' j j' x i).trans
          (mul_le_mul_of_nonneg_left (min_decay_le_mul_decay_half _ _) hc0)
    _ = c * ((∑ z ∈ Zf, decay (gammaW d / 2) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x)) *
          ∑ z' ∈ Zf, decay (gammaW d / 2) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z')) x)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
    _ ≤ c * (S * S) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hsum
          (Finset.sum_nonneg fun z' _ => decay_nonneg _ _) hS0) hc0
    _ = c * S ^ 2 := by ring

end Hess

end Balaban.LargeField
