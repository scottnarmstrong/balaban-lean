/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Fluctuation.StepComplexProp26Agree
public import Balaban.Localization.DecoupledCovReal
public import Balaban.Fluctuation.DetRotation
public import Balaban.LargeField.Background.CubeUnitBg
public import Balaban.Fluctuation.StepNorm
public import Balaban.SmallField.XiMassResponse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The vacuum value of the determinant terms (OPEN-VACUUM of `notes/phase1/DETFIT.md` §1)

The determinant part of the new terms of a step is a family `t_z(D, T)` of localized terms, one
record `DetExpansionLocC S m₀ z ε κ'' c_det` for each root `z` of `T^{(k+1)}_1`.  At a real datum
`D₀` of the chart (the vacuum datum is one), their total is `½ log det C^{(k)}` at `D₀`, a real
number, so the vacuum part absorbed into `E_{k+1}` (P4 (4.21)) is real, and so is the value of
every root separately:

* `specFun_real_diag_im`: a diagonal entry of `f(A)` for a Hermitian `A` and real `f` is real;
* `sum_detExpansionLocC_term_eq`: `∑_{z,T} t_z(D', T) = ½ log det C^{(k)}` (the analytic branch
  `halfLogDetCC`) at the datum `D'` of the step, for every datum of the chart;
* `sum_detExpansionLocC_term_eq_real`: for real data (the premises of Lemma 2.4 (c),
  `halfLogDetCC_eq`) the total is the real number `halfLogDetC = ½ log det C^{(k)}`;
* `vacuum_det_density`: `∑_{z,T} t_z(D', T) = c_vac |T^{(k+1)}_1|` with the real number
  `c_vac = ½ log det C^{(k)} / |T^{(k+1)}_1|`, `|T^{(k+1)}_1| = nBlocks` the number of roots (the
  volume unit of `vacuumEnergy_succ_of_absorb`);
* `sum_detExpansionLocC_term_root_im`: for real data each root contributes a real number,
  `Im ∑_T t_z(D', T) = 0` (the diagonal of the real logarithm of `𝒜`).
* `norm_logA_le`, `norm_sum_detExpansionLocC_term_root_le`, `abs_halfLogDetC_le`: the bounds
  `‖𝕃_{pq}‖ ≤ covBLog`, `‖∑_T t_z(D', T)‖ ≤ ½ N |B(z)| covBLog` and
  `|½ log det C^{(k)}| ≤ ½ N L^d covBLog · |T^{(k+1)}_1|` (Theorem I-4c at `s = 1`, `κ = 0`):
  the determinant part of the vacuum value `e₀` of a step is at most `½ N L^d covBLog` per block.
* `sum_detExpansionLocC_term_rot`: the value of a root does not change under a real rotation of
  the datum, for every record (under the premises of the landed construction
  `exists_detExpansionLocC_rot_real`, whose terms are invariant one by one);
  `constUnitBg_rot`: the rotation of the vacuum datum of `e` is the vacuum datum of `Q e`;
  `xiCData_constUnitBg`: the vacuum datum lies in the chart `Ξ^c_n(𝔹; σ, ε)` for all `σ, ε > 0`;
  so the value of a root at the vacuum datum does not depend on the choice of the unit vector
  (`sum_detExpansionLocC_term_vacuum_rot`).

Not proved here: that the value of a root at the vacuum datum is independent of the root (only the
covariance under cell-aligned translations is landed, `rootTrace_unitAct`), and its independence of
the torus.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Finset Matrix

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

/-- **The diagonal of a real function of a Hermitian matrix is real**:
`(U diag(f(λ)) U*)_{pp} = ∑_j f(λ_j) |U_{pj}|²`. -/
theorem specFun_real_diag_im (hH : A.IsHermitian) (f : ℝ → ℝ) (p : ι) :
    (specFun hH (fun t => (f t : ℂ)) p p).im = 0 := by
  unfold specFun
  rw [Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply]
  set u : ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) p j
  have h : u * (f (hH.eigenvalues j) : ℂ) * star u =
      ((f (hH.eigenvalues j) * Complex.normSq u : ℝ) : ℂ) := by
    rw [mul_comm u, mul_assoc, Complex.star_def, Complex.mul_conj]
    push_cast
    ring
  rw [h, Complex.ofReal_im]

end Spectral

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} {eps κ'' cdet : ℝ}

/-- **The total of the determinant terms at the datum of the step**: for a family of records, one
for each root, `∑_z ∑_T t_z(D', T) = ½ log det C^{(k)}` (the analytic branch `halfLogDetCC`
`= -½ ∑_y tr 𝕃(y, y)`), for every datum `D'` of the chart. -/
theorem sum_detExpansionLocC_term_eq
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T = S.halfLogDetCC := by
  rw [← sum_rootTrace_one_eq_halfLogDetCC S]
  exact Finset.sum_congr rfl fun z _ => ((E z).sum_eq S.D' hD).symm

section Real

variable (H : BgHyp d L (k + 1) ϱ S.a S.ν) {δ' : ℝ} (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: the vacuum value of the determinant terms is the real `½ log det C^{(k)}`**:
`∑_z ∑_T t_z(D', T) = halfLogDetC` for a real datum `D'` of the chart (Lemma 2.4 (c)). -/
theorem sum_detExpansionLocC_term_eq_real
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T = (S.halfLogDetC : ℂ) := by
  rw [S.sum_detExpansionLocC_term_eq E hD,
    S.halfLogDetCC_eq H hδ'0 hδ' hD'R hδ0 hχ hfam hsm]

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **The vacuum density of the determinant terms (OPEN-VACUUM, total and reality)**: for a real
datum `D'` of the chart, `∑_z ∑_T t_z(D', T) = c_vac |T^{(k+1)}_1|` with the real number
`c_vac = ½ log det C^{(k)} / |T^{(k+1)}_1|`; `|T^{(k+1)}_1| = nBlocks` is the number of roots
(`nBlocks_eq`), the volume unit of `vacuumEnergy_succ_of_absorb`, so the determinant part of
`e₀ / nBlocks` there is `c_vac`. -/
theorem vacuum_det_density
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ z, ∑ T, (E z).term S.D' T = ((S.halfLogDetC / S.nBlocks : ℝ) : ℂ) * (S.nBlocks : ℂ) := by
  rw [S.sum_detExpansionLocC_term_eq_real H hδ'0 hδ' hD'R hδ0 hχ hfam hsm E hD,
    ← Complex.ofReal_mul]
  have hc : S.nBlocks ≠ 0 := by
    rw [S.nBlocks_eq]
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hc]

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **Real data: each root contributes a real number**: `Im ∑_T t_z(D', T) = 0`.  The sum over
`T` is the trace `-½ ∑_{y ∈ B(z)} tr 𝕃(y, y)` over the block of the root, and the diagonal of the
real logarithm `log 𝒜` of the positive definite `𝒜` is real. -/
theorem sum_detExpansionLocC_term_root_im
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    (∑ T, E.term S.D' T).im = 0 := by
  rw [← E.sum_eq S.D' hD, rootTrace_one_eq_logAC S z, S.logAC_eq H hδ'0 hδ' hD'R]
  unfold logA
  rw [decLog_one_eq_real hfam (S.constraintField_bg H hδ'0 hδ' hD'R hδ0 hχ) hδ0.le hsm
    (isUnitLatticeB_unit (G := S.G')) (fun w => S.bgMult_real_S H hδ'0 hδ' hD'R w)
    (fun b y => unitQ_real S.G' b y) (fun y i => S.svec_bg_real H hδ'0 hδ' hD'R y i)]
  rw [Complex.mul_im, Complex.im_sum]
  simp only [Complex.im_sum, specFun_real_diag_im, Finset.sum_const_zero, mul_zero, zero_add]
  norm_num

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- The standing hypotheses of Theorem I-4c at the real datum of the step, at `s = 1`, `κ = 0`. -/
theorem covStanding_step :
    CovStanding S.G' S.a S.a₁ S.ν (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1) S.δ
      (svec S.G' (bgField S.G' S.a S.ν S.D')) (unitQ S.G') (unitP S.G') :=
  ⟨hfam, S.constraintField_bg H hδ'0 hδ' hD'R hδ0 hχ, hδ0.le, hsm,
    (isUnitLatticeB_unit (G := S.G')).toIsUnitLattice⟩

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **The entries of `𝕃 = log 𝒜` are bounded**: `‖𝕃_{pq}‖ ≤ covBLog d L a_k (a₁/L²) 0`
(Theorem I-4c, at the real datum of the step). -/
theorem norm_logA_le (p q : S.U × Fin N) :
    ‖S.logA p q‖ ≤ covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 := by
  have Hs := S.covStanding_step H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have hc : 0 ≤ covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 := by
    unfold covBLog
    have := covB4_nonneg d L (S.a k) 0
    have := Hs.hak
    positivity
  exact norm_entry_le_of_sqNorm hc (fun f => decLog_bound Hs f) p q

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **The value of a root is bounded by the volume of its block**: for a real datum of the chart,
`‖∑_T t_z(D', T)‖ ≤ ½ N |B(z)| covBLog d L a_k (a₁/L²) 0`. -/
theorem norm_sum_detExpansionLocC_term_root_le
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ‖∑ T, E.term S.D' T‖ ≤
      (1 / 2 : ℝ) * N * (S.blockU z).card * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 := by
  rw [← E.sum_eq S.D' hD, rootTrace_one_eq_logAC S z, S.logAC_eq H hδ'0 hδ' hD'R, norm_mul]
  have hhalf : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hhalf]
  have hsum : ‖∑ y ∈ S.blockU z, ∑ i : Fin N, S.logA (y, i) (y, i)‖ ≤
      (S.blockU z).card * (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ S.blockU z, ‖∑ i : Fin N, S.logA (y, i) (y, i)‖
        ≤ ∑ _y ∈ S.blockU z, (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0) := by
          refine Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans ?_
          calc ∑ i : Fin N, ‖S.logA (y, i) (y, i)‖
              ≤ ∑ _i : Fin N, covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 :=
                Finset.sum_le_sum fun i _ =>
                  S.norm_logA_le H hδ'0 hδ' hD'R hδ0 hχ hfam hsm (y, i) (y, i)
            _ = N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 := by simp
      _ = (S.blockU z).card * (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0) := by simp
  calc (1 / 2 : ℝ) * ‖∑ y ∈ S.blockU z, ∑ i : Fin N, S.logA (y, i) (y, i)‖
      ≤ (1 / 2 : ℝ) * ((S.blockU z).card * (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

include H hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **The vacuum value of the determinant terms per block is bounded**: for a real datum of the
step, `|½ log det C^{(k)}| ≤ ½ N L^d covBLog d L a_k (a₁/L²) 0 · |T^{(k+1)}_1|`
(`|T^{(k)}_1| = L^d |T^{(k+1)}_1|`); the constant does not depend on the torus. -/
theorem abs_halfLogDetC_le :
    |S.halfLogDetC| ≤
      (1 / 2 : ℝ) * N * (L : ℝ) ^ d * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 * S.nBlocks := by
  have h1 := S.halfLogDetCC_eq H hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have hL : (L : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  have hnB : (L : ℝ) ^ d * S.nBlocks = S.nU := by
    unfold nBlocks; field_simp
  have hn : |S.halfLogDetC| = ‖S.halfLogDetCC‖ := by
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  unfold halfLogDetCC
  rw [S.logAC_eq H hδ'0 hδ' hD'R, norm_mul]
  have hhalf : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hhalf]
  have hsum : ‖∑ y : S.U, ∑ i : Fin N, S.logA (y, i) (y, i)‖ ≤
      S.nU * (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y : S.U, ‖∑ i : Fin N, S.logA (y, i) (y, i)‖
        ≤ ∑ _y : S.U, (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0) := by
          refine Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans ?_
          calc ∑ i : Fin N, ‖S.logA (y, i) (y, i)‖
              ≤ ∑ _i : Fin N, covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 :=
                Finset.sum_le_sum fun i _ =>
                  S.norm_logA_le H hδ'0 hδ' hD'R hδ0 hχ hfam hsm (y, i) (y, i)
            _ = N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0 := by simp
      _ = S.nU * (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0) := by simp [nU]
  rw [← hnB] at hsum
  calc (1 / 2 : ℝ) * ‖∑ y : S.U, ∑ i : Fin N, S.logA (y, i) (y, i)‖
      ≤ (1 / 2 : ℝ) * ((L : ℝ) ^ d * S.nBlocks *
          (N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) 0)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end Real

section Rot

variable {ϱm : ℝ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **A real rotation of the datum does not change the value of a root**: for every record `E` at
the root `z` and every datum `D` of the chart, `∑_T t_z(Q D, T) = ∑_T t_z(D, T)` for `Qᵀ Q = 1`
real.  Both sides are the rooted trace of the block of `z` (`DetExpansionLocC.sum_eq`), and the
record of the landed construction has invariant terms (`exists_detExpansionLocC_rot_real`, whose
premises are taken here). -/
theorem sum_detExpansionLocC_term_rot
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (D : BgData S.G' N)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ∑ T, E.term (D.rot (cmat Q)) T = ∑ T, E.term D T := by
  obtain ⟨E', -, hE'⟩ :=
    exists_detExpansionLocC_rot_real S hC hδc hMX hdm hα hsm hconn hN hz z hQ
  have hDr := xiCData_rot hQ hD
  rw [← E.sum_eq _ hDr, ← E.sum_eq D hD, E'.sum_eq _ hDr, E'.sum_eq D hD]
  exact Finset.sum_congr rfl fun T _ => hE' D hD T

end Rot

end StepSetting

section VacuumDatum

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The rotated vacuum datum**: `Q · (Ψ ≡ e, h̃ ≡ e) = (Ψ ≡ Q e, h̃ ≡ Q e)`. -/
theorem constUnitBg_rot (G : GeneratingSet d L N₀ K ϱ) (Q : Matrix (Fin N) (Fin N) ℝ)
    (e : Fin N → ℝ) :
    (LargeField.constUnitBg G e).rot (cmat Q) = LargeField.constUnitBg G (Q *ᵥ e) := by
  refine BgData.ext' (funext fun x => ?_) (funext fun x => ?_)
  · funext i
    simp only [BgData.rot, LargeField.constUnitBg, BgData.clip]
    split_ifs
    · exact (cmat_mulVec Q e i).symm
    · simp
  · funext i
    simp only [BgData.rot, LargeField.constUnitBg, BgData.clip]
    split_ifs
    · exact (cmat_mulVec Q e i).symm
    · simp

variable {m₁ : ℕ} {N₁ : ℕ} [NeZero N₁]

/-- **The vacuum datum lies in the chart**: under `BgHyp`, the constant datum of a unit vector `e`
is a datum of `Ξ^c_n(𝔹; σ, ε)` for every level `n` and all `σ, ε > 0`: it is real, its
background is the constant field `e` with multiplier `0` (`bgField_constUnitBg`,
`bgMult_constUnitBg`), so every difference in the inequalities of `Ξ_n` and of `Ξ^c_n` vanishes. -/
theorem xiCData_constUnitBg {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (n : ℕ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) :
    Localization.XiCData G a ν n σ ε (LargeField.constUnitBg G e) := by
  classical
  have hz0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := by unfold vn; exact norm_eq_zero.2 rfl
  have hU := LargeField.constUnitBg_inUnionDomainR (G := G) H he
  have hd0 : 0 < d := by have := H.hd; omega
  have hUC : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (LargeField.constUnitBg G e) :=
    SmallField.inUnionDomainC_of_R hd0 H.massLe hU
  obtain ⟨hfC, hmC⟩ := theorem72_real H hU
  have hφ := LargeField.bgField_constUnitBg (G := G) H he
  have hα := LargeField.bgMult_constUnitBg (G := G) H he
  have hsp : ∀ x, 0 < G.spacing x := fun x => by
    unfold GeneratingSet.spacing
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hbar : ∀ y ∈ dataSites G, ∀ i, barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) y i = (e i : ℂ) := by
    intro y hy i
    rw [hφ]
    exact LargeField.barField_constUnitPhi e hy i
  have hΩ : ∀ x ∈ G.Ω 1, x ∈ dataSites G := fun x hx => (mem_dataSites G).2 (Or.inl hx)
  have hReal : SmallField.Realizes (LargeField.constUnitBg G e) (fun _ i => e i) e :=
    ⟨fun x hx i => LargeField.constUnitBg_Ψ hx i, fun x hx i => LargeField.constUnitBg_h hx i⟩
  have hRC : SmallField.RealizesC (LargeField.constUnitBg G e) (fun _ i => e i) e 0 0 :=
    ⟨fun x hx i => by simp [LargeField.constUnitBg_Ψ hx i],
      fun x hx i => by simp [LargeField.constUnitBg_h hx i]⟩
  have hXB : SmallField.XiBounds G ν n σ ε (LargeField.constUnitBg G e) e (bgField G a ν (LargeField.constUnitBg G e)) (bgMult G a ν (LargeField.constUnitBg G e)) := by
    refine ⟨fun x hx μ => ⟨?_, ?_⟩, fun x hx => ?_, fun x => ?_, fun x hx => ?_,
      fun z hz z' hz' _ => ?_, fun z => ?_, ?_⟩
    · have h1 : (fun i => barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) (x + Pi.single μ 1) i -
          barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) x i) = fun _ => 0 := by
        funext i
        rw [hbar _ (LargeField.mem_dataSites_add hx μ), hbar x (hΩ x hx), sub_self]
      rw [h1, hz0]
      exact div_pos (mul_pos hσ hε) (hsp x)
    · have h1 : (fun i => barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) (x - Pi.single μ 1) i -
          barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) x i) = fun _ => 0 := by
        funext i
        rw [hbar _ (LargeField.mem_dataSites_sub hx μ), hbar x (hΩ x hx), sub_self]
      rw [h1, hz0]
      exact div_pos (mul_pos hσ hε) (hsp x)
    · have h1 : (fun i => ∑ μ : Fin d,
          (barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) (x + Pi.single μ 1) i +
            barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) (x - Pi.single μ 1) i -
            2 * barField G (LargeField.constUnitBg G e).Ψ (bgField G a ν (LargeField.constUnitBg G e)) x i)) = fun _ => 0 := by
        funext i
        refine Finset.sum_eq_zero fun μ _ => ?_
        rw [hbar _ (LargeField.mem_dataSites_add hx μ), hbar _ (LargeField.mem_dataSites_sub hx μ),
          hbar x (hΩ x hx)]
        ring
      rw [h1, hz0]
      exact div_pos (mul_pos (pow_pos hσ 2) hε) (pow_pos (hsp x) 2)
    · rw [hα]
      simp only [Pi.zero_apply, norm_zero, mul_zero]
      positivity
    · have h1 : (fun i => (LargeField.constUnitBg G e).Ψ x i - blockAvg G (bgField G a ν (LargeField.constUnitBg G e)) x i) = fun _ => 0 := by
        funext i
        rw [hφ, LargeField.constUnitBg_Ψ (hΩ x hx), LargeField.blockAvg_constUnitPhi e hx,
          sub_self]
      rw [h1, hz0]
      positivity
    · have h1 : (fun i => (LargeField.constUnitBg G e).Ψ z i - (LargeField.constUnitBg G e).Ψ z' i) = fun _ => 0 := by
        funext i
        rw [LargeField.constUnitBg_Ψ ((mem_dataSites G).2 (Or.inr hz)),
          LargeField.constUnitBg_Ψ ((mem_dataSites G).2 (Or.inr hz')), sub_self]
      rw [h1, hz0]
      positivity
    · have h1 : (fun i => bgField G a ν (LargeField.constUnitBg G e) (z, i) - (e i : ℂ)) = fun _ => 0 := by
        funext i
        rw [hφ]
        simp [LargeField.constUnitPhi]
      rw [h1, hz0, mul_zero]
      positivity
    · rw [he, sub_self, abs_zero, mul_zero]
      positivity
  have hXCB : SmallField.XiCBounds G ν σ ε (LargeField.constUnitBg G e) (LargeField.constUnitBg G e) 0 0 (bgField G a ν (LargeField.constUnitBg G e))
      (bgFieldC G a ν (bgC0 d L N) (LargeField.constUnitBg G e)) (bgMult G a ν (LargeField.constUnitBg G e)) (bgMultC G a ν (bgC0 d L N) (LargeField.constUnitBg G e)) := by
    rw [hfC, hmC]
    refine ⟨fun x _ μ => ⟨?_, ?_⟩, fun x _ => ?_, fun x => ?_, fun x => ?_, fun x _ => ?_,
      fun z _ z' _ _ => ?_, fun x _ => ?_, fun x => ?_⟩
    · simp only [sub_self, hz0]
      exact div_pos (mul_pos hσ hε) (hsp x)
    · simp only [sub_self, hz0]
      exact div_pos (mul_pos hσ hε) (hsp x)
    · simp only [sub_self, add_zero, mul_zero, Finset.sum_const_zero, hz0]
      exact div_pos (mul_pos (pow_pos hσ 2) hε) (pow_pos (hsp x) 2)
    · simp only [sub_self, norm_zero, mul_zero]
      positivity
    · simp only [sub_self, hz0]
      exact hε
    · simp only [Pi.zero_apply, sub_self, zero_sub]
      have h1 : (fun i => -blockAvg G (0 : G.Ω 1 × Fin N → ℂ) x i) = fun _ => 0 := by
        funext i
        simp [blockAvg, svec, zeroExt]
      rw [h1, hz0]
      positivity
    · simp only [Pi.zero_apply, sub_self, hz0]
      positivity
    · simp only [Pi.zero_apply]
      have : vn (0 : Fin N → ℂ) = 0 := vn_zero
      rw [show (fun _ : Fin N => (0 : ℂ)) = (0 : Fin N → ℂ) from rfl] at hz0
      simp only [this, mul_zero]
      positivity
    · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero]
      positivity
  exact ⟨fun _ i => e i, e, 0, 0,
    ⟨hσ, hε, (LargeField.constUnitBg G e), (LargeField.constUnitBg G e), ⟨hReal, hU, hXB⟩, hRC, hUC, hXCB⟩, hRC⟩

end VacuumDatum

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} {eps κ'' cdet : ℝ}
  {ϱm : ℝ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **The value of a root at the vacuum datum does not depend on the unit vector**: for a unit
vector `e` and every real `Q` with `Qᵀ Q = 1`, `∑_T t_z(D₀(Q e), T) = ∑_T t_z(D₀(e), T)`, `D₀(e)`
the vacuum datum of `e` (a datum of the chart, `xiCData_constUnitBg`). -/
theorem sum_detExpansionLocC_term_vacuum_rot
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    ∑ T, E.term (LargeField.constUnitBg S.G' (Q *ᵥ e)) T =
      ∑ T, E.term (LargeField.constUnitBg S.G' e) T := by
  rw [← constUnitBg_rot S.G' Q e]
  exact S.sum_detExpansionLocC_term_rot hC hδc hMX hdm hα hsm hconn hN hz E hQ _
    (xiCData_constUnitBg hC.HBp he (k + 1) one_pos hC.eps_pos)

end StepSetting

end Balaban.Fluctuation
