/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DetDecCovSymm
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Fluctuation.LocalClassDensityHAnalytic
public import Balaban.Fluctuation.LocalClassLatCore
public import Balaban.Fluctuation.StepComplexCov

/-!
# Covariance of the decoupled covariance operator under lattice symmetries (`StepTowerNewLevelSymCov`)

The decoupled objects `C^{1/2}(1)` and `𝕃(1)` of the step are the principal inverse square root
and the principal logarithm of the operator `𝒜 = covOp` (`decCovSqrt_one_eq_sqrtMat`,
`decLog_one_eq_logMat`), and `𝒜` involves neither the cover nor the paving.  Hence they are
covariant under every lattice symmetry preserving the unit blocks, in particular under the full
level group, which does not preserve the cover:

* `xH0_rm`, `constrainedOp_rm`, `covOp_rm`: `𝒜(σ α, σ φ) = rm (u × 1) 𝒜(α, φ)`;
* `sqrtMat_rm`, `logMat_rm`: the principal square root and logarithm commute with relabelling;
* `hatCovSqrt_sym`, `decLog_sym`: the covariance at the data of the chart `Ξ^c_{k+1}(𝔹'; 1, ε)`.
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence
  Balaban.Localization.DetDecCov Matrix Filter Topology

section Mat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ) (hU : UnitBlockPres σ)

include S hU in
/-- The Dirichlet operator `H₀` at `x = ∞` is covariant. -/
theorem xH0_rm {a : ℕ → ℝ} {aT ν : ℝ} (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (α : G.Ω 1 → ℂ) : xH0 G a ν (S.mul α) = rm S.Ω1Equiv (xH0 G a ν α) := by
  have h1 := tendsto_xDirichlet (aT := aT) (ν := ν) hak hb (S.mul α)
  have h2 : Tendsto (fun x => rm S.Ω1Equiv (xDirichletOperator G a aT x ν α)) atTop
      (𝓝 (rm S.Ω1Equiv (xH0 G a ν α))) := by
    have hc : Continuous (fun M : Matrix (G.Ω 1) (G.Ω 1) ℂ => rm S.Ω1Equiv M) := by
      unfold rm
      exact continuous_id.matrix_submatrix _ _
    exact (hc.tendsto _).comp (tendsto_xDirichlet (aT := aT) (ν := ν) hak hb α)
  simp only [← xDirichletOperator_rm S hU] at h2
  exact tendsto_nhds_unique h1 h2

include S in
theorem constrainedOp_rm (A : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    Multiscale.constrainedOp (rm S.Ω1Equiv A) (restrictField G (symSite σ φ)) =
      rm (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N)))
        (Multiscale.constrainedOp A (restrictField G φ)) := by
  have hf := fieldMul_restrict_symSite (N := N) S φ
  have hcf : Multiscale.constraintForm (rm S.Ω1Equiv A) (restrictField G (symSite σ φ)) =
      rm S.Ω1Equiv (Multiscale.constraintForm A (restrictField G φ)) := by
    unfold Multiscale.constraintForm
    rw [hf, DetDecCov.liftOp_rm]
    simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  unfold Multiscale.constrainedOp
  rw [hcf, hf, DetDecCov.liftOp_rm, ← rm_inv]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

include S hU in
/-- **Covariance of `𝒜 = covOp`** on the unit points under a lattice symmetry preserving the unit
blocks: `𝒜(σ α, σ φ) = rm (u × 1) 𝒜(α, φ)`, `u = unitAct`. -/
theorem covOp_rm {a : ℕ → ℝ} {aT ν : ℝ} (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (α : G.Ω 1 → ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    covOp G a aT ν (S.mul α) (symSite σ φ) (unitQ G) (unitP G) =
      rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (covOp G a aT ν α φ (unitQ G) (unitP G)) := by
  have hQ := liftRect_unitQ_invariant (N := N) S hU
  have hx0 := xH0_rm S hU (a := a) (aT := aT) (ν := ν) hak hb α
  have hXr : (liftOp N (xH0 G a ν (S.mul α))⁻¹ -
      Multiscale.constrainedOp (xH0 G a ν (S.mul α))⁻¹ (restrictField G (symSite σ φ))) =
      rm (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N)))
        (liftOp N (xH0 G a ν α)⁻¹ - Multiscale.constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ)) := by
    rw [hx0, ← rm_inv, constrainedOp_rm S, DetDecCov.liftOp_rm, rm_sub]
  have key : liftRect N (unitQ G) * (liftOp N (xH0 G a ν (S.mul α))⁻¹ -
      Multiscale.constrainedOp (xH0 G a ν (S.mul α))⁻¹ (restrictField G (symSite σ φ))) *
        (liftRect N (unitQ G))ᵀ =
      rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (liftRect N (unitQ G) * (liftOp N (xH0 G a ν α)⁻¹ -
          Multiscale.constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ)) *
          (liftRect N (unitQ G))ᵀ) := by
    rw [hXr]
    conv_lhs => rw [← hQ]
    simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  unfold covOp
  rw [key, rm_sub, rm_add, rm_smul, rm_smul, rm_smul, rm_one, liftOp_unitP_invariant S hU]

end Mat

section Fun

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem resolvent_rm (e : ι ≃ κ) (A : Matrix ι ι ℂ) (x : ℝ) :
    ((x : ℂ) • (1 : Matrix κ κ ℂ) + rm e A)⁻¹ =
      rm e (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) := by
  rw [rm_inv, rm_add, rm_smul, rm_one]

/-- The principal inverse square root commutes with relabelling of the index set. -/
theorem sqrtMat_rm (e : ι ≃ κ) (A : Matrix ι ι ℂ) : sqrtMat (rm e A) = rm e (sqrtMat A) := by
  unfold sqrtMat
  rw [rm_smul]
  congr 1
  have h : (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((x : ℂ) • (1 : Matrix κ κ ℂ) + rm e A)⁻¹) =
      fun x : ℝ => rm e (((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) := by
    funext x
    rw [resolvent_rm, rm_smul]
  rw [h]
  rfl

/-- The principal logarithm commutes with relabelling of the index set. -/
theorem logMat_rm (e : ι ≃ κ) (A : Matrix ι ι ℂ) : logMat (rm e A) = rm e (logMat A) := by
  unfold logMat
  have hn : ∀ M : Matrix ι ι ℂ, rm e (-M) = -rm e M := fun M => by ext x y; simp [rm]
  rw [hn]
  congr 1
  have h : (fun x : ℝ => ((x : ℂ) • (1 : Matrix κ κ ℂ) + rm e A)⁻¹ -
      (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) =
      fun x : ℝ => rm e (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
        (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) := by
    funext x
    rw [resolvent_rm, rm_sub, rm_smul, rm_one]
  rw [h]
  rfl

end Fun

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- At a datum of the chart the decoupled square root at `s ≡ 1` is the principal inverse square
root of `𝒜 = covOp`. -/
theorem hatCovSqrt_eq_sqrtMat {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    hatCovSqrt S.G' S.a₁ S.ν D =
      sqrtMat (covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G')) := by
  obtain ⟨hfam, hφ, hδ, hsm0⟩ := S.covData_of_chart_core D hC hMX hdm hα hsm hD
  unfold hatCovSqrt
  have hb : barField S.G' D.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) :=
    funext fun x => funext fun i => barField_eq_svec S.hG' _ _ x i
  rw [hb]
  exact decCovSqrt_one_eq_sqrtMat hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G'))

include hC hMX hdm hα hsm in
/-- At a datum of the chart the decoupled logarithm at `s ≡ 1` is the principal logarithm of
`𝒜 = covOp`. -/
theorem decLog_eq_logMat {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G') =
      logMat (covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G')) := by
  obtain ⟨hfam, hφ, hδ, hsm0⟩ := S.covData_of_chart_core D hC hMX hdm hα hsm hD
  exact decLog_one_eq_logMat hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G'))

variable (Sy : LatSymm S.G' S.G' σ) (hU : UnitBlockPres σ)

include hC hMX hdm hα hsm Sy hU in
/-- **`𝒜` at the transported datum is the relabelling of `𝒜`** (chart data). -/
theorem covOp_sym_chart {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D))
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D))) (unitQ S.G') (unitP S.G') =
      rm ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N)))
        (covOp S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
          (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G')) := by
  obtain ⟨hfam, -, -, -⟩ := S.covData_of_chart_core D hC hMX hdm hα hsm hD
  have h0 := hfam 0 le_rfl
  have hak : 0 < S.a k := by have := h0.st.hak1; linarith
  have hb : 0 ≤ S.a₁ / (L : ℝ) ^ 2 := by
    have := h0.st.haT1
    have : (0 : ℝ) < (L : ℝ) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    positivity
  have hs : svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D)) =
      symSite σ (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) := by
    rw [(Sy.bgFieldC_sym S.a S.ν (bgC0 d L N) D).1]
    funext y
    obtain ⟨z, rfl⟩ := σ.surjective y
    funext i
    rw [Sy.svec_sym]
    simp [symSite]
  rw [hs, (Sy.bgFieldC_sym S.a S.ν (bgC0 d L N) D).2]
  exact covOp_rm Sy hU hak hb _ _

include hC hMX hdm hα hsm Sy hU in
/-- **The decoupled square root is transported by a lattice symmetry** (chart data). -/
theorem hatCovSqrt_sym {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    hatCovSqrt S.G' S.a₁ S.ν (Sy.sym D) =
      rm ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N)))
        (hatCovSqrt S.G' S.a₁ S.ν D) := by
  rw [hatCovSqrt_eq_sqrtMat hC hMX hdm hα hsm hD,
    hatCovSqrt_eq_sqrtMat hC hMX hdm hα hsm (xiCData_sym_pair Sy hD),
    covOp_sym_chart hC hMX hdm hα hsm Sy hU hD, sqrtMat_rm]

include hC hMX hdm hα hsm Sy hU in
/-- **The decoupled logarithm is transported by a lattice symmetry** (chart data). -/
theorem decLog_sym {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D)) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) (Sy.sym D))) (unitQ S.G') (unitP S.G') =
      rm ((unitAct S.G' Sy hU).prodCongr (Equiv.refl (Fin N)))
        (decLog S.G' S.a S.a₁ S.ν (bgMultC S.G' S.a S.ν (bgC0 d L N) D) (fun _ => 1)
          (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) (unitQ S.G') (unitP S.G')) := by
  rw [decLog_eq_logMat hC hMX hdm hα hsm hD,
    decLog_eq_logMat hC hMX hdm hα hsm (xiCData_sym_pair Sy hD),
    covOp_sym_chart hC hMX hdm hα hsm Sy hU hD, logMat_rm]

end Chart
end Balaban.Inhabited.StepSym
