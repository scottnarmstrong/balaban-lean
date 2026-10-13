/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficient
public import Balaban.SmallField.Def6AvgSumConds
public import Balaban.SmallField.XiSymm
public import Balaban.SmallField.Def6InfCov
public import Balaban.SmallField.RenormAnisoBridgeInf
public import Balaban.SmallField.RenormClassFamily

/-!
# The radial coefficient for the averaged family and the axis of `D1Corr` (missing links M2, M3)

`RadialCoefficient.lean` identifies the marginal kernel `a_j` and the coefficient `v₁^{(j)}` for the
UNAVERAGED lifted family `liftTF` on one torus.  This file settles the two links it left open:
(M2) the family consumed by the renormalization theorem is the Reynolds average `avgFamilyA`, not
`liftTF`; (M3) `D1Corr` uses the axis `e₁ = hC hv`, the identities are at `e_{i₀}`.

## What is proved

* `v1Loc_axis_eq`, `v1T_axis_eq` (T3): `v1Loc`/`v1T` at `w = Q e_{i₀}` equal the value at `e_{i₀}`
  for a real orthogonal `Q` (`Qᵀ Q = 1`).  Uses `IsSF.rotE` and `xiDom_rot` (real `O(N)`-covariance
  of `XiDom`, from the landed `xiC_rot`).
* `aCoef_liftTF_eq_v1T_axis_of_D1Corr` (T4, one torus): `a_j(x) = v1T … (hC hv) 0 (blockPt j x)` for
  `liftTF`, premises `hsurj` (M4) and `hC hv = Q e_{i₀}`.
* `aCoefX_avgFamilyA`, `aCoef_avgFamilyA_eq_sum` (T2 (b), literal identity):
  `aCoef (avgFamilyA …) x = |Q|⁻¹ ∑_q aInfC (τ_q) (x + τ_q)`, `τ_q = offs (rep q)`, where
  `aInfC y z = ∑_{X' ∋ y} ∂_{ψ_{i₀}(z)} ℰ_∞(y, X')` is the kernel of `T∞` at the centre `y`
  (summability of the coefficients is an explicit hypothesis).
* `aCoef_liftInfA_eq_aInfC`: the kernel of the unaveraged `liftInfA` is `aInfC … 0 x`.
* `D1_Eloc_translate`, `v1T_translate`: `∂_x ℰ(y) = ∂_{x-y} ℰ(0)` and `v1T … y x = v1T … 0 (x-y)`
  on a torus, from `eucEloc`.
* `aInfC_translate_of_M1`: `aInfC y z = aInfC 0 (z - y)` from the torus identity and the limit
  premise `hM1`.
* `aCoef_avgFamilyA_eq_liftInfA_of_M1` (T2 (a)): `aCoef (avgFamilyA …) x = aCoef (liftInfA …) x`.
* `aCoef_avgFamilyA_eq_v1_of_M1` (T4): `aCoef (avgFamilyA …) i₀ ν_j x = vc.v1 j x` for the family
  of the renormalization theorem and the axis of `D1Corr`.

## T1: what is averaged, and which covariance is landed

*The average.*  `avgB` (Def6AvgFamily.lean:214) is `avgFB` (:113) evaluated at the state of the
centred polymer, and `avgFB` is the Reynolds average over the cosets `G_j / H_j` (`GG` :83, `HH`
:86, `KK` :90) of the cut-off term `FB` of `T∞` (Def6AvgInv.lean:260).  `G_j = symZ (L^j)` is the
symmetry group of the level-`j` lattice (translations by `L^j`, reflections, coordinate exchanges)
and `H_j = symZ (L^j M)` the one of the paving.  `exists_summand_rep` (:218) shows that every coset
is represented by a TRANSLATION by a paving offset `τ ∈ {0,…,M-1}^d` (`M = L^{m₀+m₁}`): the
reflections and exchanges of `G_j` are, modulo `H_j`, translations.  Hence `avgB_eq_sum` (:239):
`avgB X c = |Q|⁻¹ ∑_q GEs (τ_q) X c`, `GEs τ X c = ℰ_∞(τ, X + τ; c(· - τ))` (:206): the average runs over
the paving offsets only, and the centre moves with the translate.  The point group enters not as
a further averaging but as the covariance of the individual terms under `H_j` (`FB_act`,
Def6AvgInv.lean:446, from `eucE`), which makes the average invariant under all of `G_j` (`avgFB_act`
:121, used for `avgFamilyA_sym_inv`).  The polymers of `avgFamilyA` are the `X ∋ 0` with an active
translate (`avgPolys` :326).

*The covariance of the class.*  (i) `eucE` (Def6v2.lean:97, Def6.lean:227) is TERMWISE:
`E(blockBase (r y), r''X, r·Ψ, r·h) = E(y, X, Ψ, h)`, but only for `r ∈ pavingSymGroup`
(Def6Terms.lean:144: translations by the cell side `M L^j`, reflections of the cell, exchanges), and
under the domain conditions for both data.  It is NOT available for the translation by a single
paving offset `τ` (not a multiple of the cell).  (ii) `eucEloc` (Def6v2.lean:101) is SUMWISE: the
density `Eloc(y) = ∑_{X ∋ y} E(y, X)` (Def6.lean:106) is invariant under `fullJSymGroup`
(Def6Terms.lean:136: translations by `L^j`, so every block translation), on the data of
`XiDom (levelGS …)`.  (iii) `rotE` (Def6v2.lean:89): termwise `E(RΨ, Rh) = E(Ψ, h)` for `IsRot R`
(real orthogonal, or `det = 1`), requiring `XiDom` for `(Ψ, h)` AND `(RΨ, Rh)`.

*Termwise versus sum.*  A family that is invariant "term by term" would give, for each translation
in the averaging set, `E(τ, X + τ; c(· - τ)) = E(0, X; c)`; then the average of the terms is the term
and `a_avg(x) = a(x)` polymer by polymer.  This is NOT what is landed for the offsets: `eucE`
covers only `r ∈ pavingSymGroup`, which acts trivially on the coset space.  What is landed for all
block translations is `eucEloc`, the invariance of the SUM over the polymers through the centre.
It re-indexes the sum over polymers (`X ↦ X + τ`, the bijection `shiftEquiv`) and gives
`∑_{X' ∋ τ} ∂_{z+τ} ℰ(τ, X') = ∑_{X ∋ 0} ∂_z ℰ(0, X)`, which is all that `aCoef = ∑_X aCoefX` sees.
The individual `aCoefX` of the translated polymer need not equal that of the original (the term of
`X + τ` centred at `τ` is not the term of `X` centred at `0`).

## T2: the result

(b) is what happens: the average is a normalized sum of translated, re-centred kernels
(`aCoef_avgFamilyA_eq_sum`, no hypothesis beyond summability).  The missing invariance is the
proposition `aInfC τ (x + τ) = aInfC 0 x` (centre-translation covariance of the infinite-volume
kernel).  It FOLLOWS from the landed fields by `eucEloc` on each torus (`D1_Eloc_translate`) and the
thermodynamic limit, i.e. from the premise `hM1`: for each centre `y` and site `z`, the
whole-torus coefficient `v1T … (blockPt y) (blockPt z)` converges along `torusSeq` to `aInfC y z`
(`aInfC_translate_of_M1`).  `hM1` is the link M1 (dominated convergence of the tails, using the
Cauchy bound of the class and `tendsto_Eloc`; it is not proved here and is a premise).  So
(a) holds under `hM1` and summability, and no repair of `D1Corr` or of the class is needed.

## T3: the axis

`rotE` is applied along the first-order slice `(e_{i₀} + s δ_u e_{i₀}, e_{i₀})`, `|s| ≤ ρ`.  The
unrotated data are in `XiDom` by the landed `LiftCtx.xiDom_const` (`xiDom_line`); the rotated data
`(QΨ, Qh)` are in `XiDom` by `xiDom_rot` (the landed `xiC_rot`).  So the reference configuration
`(e_{i₀}, e_{i₀})` and the slices satisfy the domain hypothesis by landed lemmas and no `XiDom`
hypothesis is carried.  The real orthogonal `Q` with `Q e_{i₀} = hC hv` is a hypothesis
(`hw`; it exists, e.g. a reflection `exists_rot_single`, but is not constructed here).  The chain
rule for `fderiv` along the slice is `fderiv_eq_of_line_eventually` (equality of the lines only near
`s = 0`).

## T5: report on tension

(a) Termwise, the averaged and unaveraged kernels can differ (the term of `X + τ` centred at `τ` is
not the term of `X` at `0` for an offset that is not a paving cell), but for the kernels `a = ∑_X a_X`
I could not build a family satisfying the landed fields for which they differ: `eucEloc` forces the
sums to agree on every torus, and the only gap in the passage to `T∞` is the limit link M1 (an
analytic domination statement, not a covariance statement).
(b) `corrSum`/`EresJ2` (Def7v2Form.lean:110, Def7v2Corr.lean:197) use `vc.v1`, the limit of the
unaveraged whole-torus sum `v1T` at the centre `0` (`D1Corr.v1_lim`), while the renormalization
A-term uses `aCoef (avgFamilyA …)`; as landed they are the same kernel only through `hM1`
(`aCoef_avgFamilyA_eq_v1_of_M1`), so the grouped cancellation `grouped_eq_far_crossing` applies to
the landed objects once `hM1` and summability are discharged, and not before.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Filter Matrix

section Axis

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **The data domain `XiDom` is invariant under real orthogonal matrices** (from the landed
`xiC_rot`): a real `Q` with `Qᵀ Q = 1` carries `(Ψ, h)` to `(Q Ψ, Q h)`, both pointwise. -/
theorem xiDom_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a' : ℕ → ℝ} {ν' : ℝ} {ε : ℝ}
    {Ψ h : Fld d L N₁ m₁ k N} (H : XiDom G a' ν' j ε Ψ h) :
    XiDom G a' ν' j ε (rotField (cmat Q) Ψ) (rotField (cmat Q) h) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', h1, h2, h3⟩ := H
  refine ⟨fun x => Q *ᵥ Ψ₀ x, Q *ᵥ h₀, fun x => cmat Q *ᵥ Ψ'' x, fun x => cmat Q *ᵥ h'' x,
    fun x i => ?_, fun x i => ?_, xiC_rot G a' ν' hQ h3⟩
  · have e : Ψ x = (fun l => (Ψ₀ x l : ℂ)) + Ψ'' x := funext fun l => h1 x l
    show (cmat Q *ᵥ Ψ x) i = _
    rw [e, Matrix.mulVec_add, Pi.add_apply, cmat_mulVec]
  · have e : h x = (fun l => (h₀ l : ℂ)) + h'' x := funext fun l => h2 x l
    show (cmat Q *ᵥ h x) i = _
    rw [e, Matrix.mulVec_add, Pi.add_apply, cmat_mulVec]

theorem isRot_cmat {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) : IsRot (cmat Q) :=
  ⟨(isRealOrth_ofReal hQ).1, Or.inl fun i j => by simp [cmat]⟩

omit [NeZero L] [NeZero N₁] in
theorem rotField_constFld (R : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    rotField (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) R (constFld v) = constFld (R *ᵥ v) :=
  rfl

omit [NeZero L] [NeZero N₁] in
theorem rotField_blockDirV (R : Matrix (Fin N) (Fin N) ℂ) (u : Localization.CTorus d L N₁ m₁ k)
    (v : Fin N → ℂ) :
    rotField (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) R (blockDirV L j u v) =
      blockDirV L j u (R *ᵥ v) := by
  funext z
  unfold rotField blockDirV
  split_ifs <;> simp

omit [NeZero L] [NeZero N₁] in
theorem rotField_add_smul (R : Matrix (Fin N) (Fin N) ℂ) (Ψ Φ : Fld d L N₁ m₁ k N) (s : ℂ) :
    rotField R (Ψ + s • Φ) = rotField R Ψ + s • rotField R Φ := by
  funext z
  simp [rotField, Matrix.mulVec_add, Matrix.mulVec_smul]

/-- **Derivatives along a line, for functions that agree along the lines only near `0`.** -/
theorem fderiv_eq_of_line_eventually {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → ℂ} {g : F → ℂ} {p : E} {q : F} {v : E}
    {w : F} (hf : DifferentiableAt ℂ f p) (hg : DifferentiableAt ℂ g q)
    (h : ∀ᶠ s : ℂ in nhds 0, f (p + s • v) = g (q + s • w)) :
    fderiv ℂ f p v = fderiv ℂ g q w := by
  have h1 := hasDerivAt_line hf v
  have h2 := hasDerivAt_line hg w
  have h3 : HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ g q w) 0 :=
    h2.congr_of_eventuallyEq (by filter_upwards [h] with s hs using hs)
  exact h1.unique h3

omit [NeZero L] [NeZero N₁] in
theorem norm_blockDirV_single_le (u : Localization.CTorus d L N₁ m₁ k) (i₀ : Fin N)
    (z : Localization.CTorus d L N₁ m₁ k) (i : Fin N) :
    ‖(blockDirV L j u (Pi.single i₀ 1 : Fin N → ℂ)) z i‖ ≤ 1 := by
  rw [blockDirV_single]
  exact norm_blockDir_le L j u i₀ z i

/-- The line `e_{i₀} + s δ_u e_{i₀}` lies in the data domain of the term, for `|s| ≤ ρ`. -/
theorem xiDom_line (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ : Fin N}
    {X : Set (Localization.CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X)
    (u : Localization.CTorus d L N₁ m₁ k) {s : ℂ} (hs : ‖s‖ ≤ ρ) :
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (Def6.bgMass L k (β k) (ν k)) j (P.eps d L j)
      (eFld d L N₁ m₁ k N i₀ + s • blockDirV L j u (Pi.single i₀ 1))
      (eFld d L N₁ m₁ k N i₀) := by
  refine ctx.xiDom_const (Tm.gs j X) (ctx.sf.gs_spec j ctx.j1 ctx.jk X hX).2 i₀ _
    (fun z i => ?_) (fun z z' hz => ?_)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld, constFld, add_sub_cancel_left]
    rw [norm_mul]
    calc ‖s‖ * ‖(blockDirV L j u (Pi.single i₀ 1 : Fin N → ℂ)) z i‖ ≤ ρ * 1 :=
          mul_le_mul hs (norm_blockDirV_single_le u i₀ z i) (norm_nonneg _) ctx.rho_pos.le
      _ = ρ := mul_one _
  · simp only [Pi.add_apply, Pi.smul_apply, eFld, constFld]
    unfold blockDirV
    rw [cbase_pow_eq_of_jBlock ctx.jk hz]

/-- **T3, one polymer: the radial coefficient does not depend on the axis.**  Let `Et` be a source
form of the class term `Tm.E j y X` (the shape of `D1Corr.src_pos`), `ν_j > 0`, and `Q` a real
orthogonal matrix with `Q e_{i₀} = w`.  Then `v1Loc Et j ν_j w u = v1Loc Et j ν_j e_{i₀} u`.  The
rotation covariance `IsSF.rotE` needs `(Ψ, h)` and `(QΨ, Qh)` in `XiDom`; the first is the landed
`xiDom_line` (the reference configuration `(e_{i₀}, e_{i₀})` and its first-order slices),
the second follows from it by the landed `xiC_rot` (`xiDom_rot`). -/
theorem v1Loc_axis_eq (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {y : Localization.CTorus d L N₁ m₁ k} {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) (hpos : 0 < nuIdeal L k (ν k) j)
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j y X Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    {w : Fin N → ℂ} (hw : w = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (u : Localization.CTorus d L N₁ m₁ k) :
    v1Loc Et j (nuIdeal L k (ν k) j) w u =
      v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) u := by
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hEs : ∀ v : Fin N → ℂ, (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ) • v))) =
      fun ψ => Tm.E j y X ψ (constFld v) := by
    intro v; funext ψ
    rw [hEt, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  unfold v1Loc
  rw [hEs, hEs]
  have hre : rotField (cmat Q) (eFld d L N₁ m₁ k N i₀) = constFld w := by
    rw [eFld, rotField_constFld, hw]
  have hdomw : XiDom (Tm.gs j X) (aIdeal L k (a k)) (Def6.bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld w) (constFld w) := by
    have h0 := xiDom_line ctx hX (i₀ := i₀) u (s := 0) (by simpa using ctx.rho_pos.le)
    rw [zero_smul, add_zero] at h0
    have h1 := xiDom_rot hQ h0
    rwa [hre] at h1
  have hg : DifferentiableAt ℂ (fun ψ : Fld d L N₁ m₁ k N => Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀))
      (eFld d L N₁ m₁ k N i₀) := (ctx.analyticAt_E i₀ y hX hy).differentiableAt
  have hf : DifferentiableAt ℂ (fun ψ : Fld d L N₁ m₁ k N => Tm.E j y X ψ (constFld w))
      (constFld w) := by
    have h1 := ctx.sf.analyticE j ctx.j1 ctx.jk y X hX hy (constFld w, constFld w) hdomw
    have h2 : AnalyticAt ℂ (fun ψ : Fld d L N₁ m₁ k N => (ψ, (constFld w : Fld d L N₁ m₁ k N)))
        (constFld w : Fld d L N₁ m₁ k N) :=
      AnalyticAt.prod analyticAt_id analyticAt_const
    exact (AnalyticAt.comp (f := fun ψ : Fld d L N₁ m₁ k N => (ψ, (constFld w : Fld d L N₁ m₁ k N))) h1 h2).differentiableAt
  have hdir : blockDirV L j u w = rotField (cmat Q) (blockDirV L j u (Pi.single i₀ 1)) := by
    rw [rotField_blockDirV, hw]
  rw [hdir]
  refine fderiv_eq_of_line_eventually hf hg ?_
  have hev : ∀ᶠ s : ℂ in nhds 0, ‖s‖ ≤ ρ := by
    have : Metric.closedBall (0 : ℂ) ρ ∈ nhds (0 : ℂ) :=
      Metric.closedBall_mem_nhds _ ctx.rho_pos
    filter_upwards [this] with s hs using by simpa using hs
  filter_upwards [hev] with s hs
  have hd1 := xiDom_line ctx hX (i₀ := i₀) u hs
  have hd2 := xiDom_rot hQ hd1
  have key := ctx.sf.rotE j ctx.j1 ctx.jk y X hX hy (cmat Q) (isRot_cmat hQ) _ _ hd1 hd2
  rw [rotField_add_smul, hre] at key
  exact key


open Balaban.SmallField.Def6v2 in
/-- **T3, one torus, whole sum**: the whole-torus coefficient `v1T` does not depend on the axis,
`v1T … (w) y x = v1T … (e_{i₀}) y x` for `w = Q e_{i₀}`, `Q` real orthogonal. -/
theorem v1T_axis_eq (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (St : SourceTerms d L N₁ m₁ k N)
    (hpos : 0 < nuIdeal L k (ν k) j)
    (hsrc : ∀ (y : Localization.CTorus d L N₁ m₁ k) (Y : Set (Localization.CTorus d L N₁ m₁ k))
      (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ), St.E j y Y Ψ (constFld b) =
        Tm.E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    {w : Fin N → ℂ} (hw : w = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (y x : Localization.CTorus d L N₁ m₁ k) :
    v1T P.m₀ St j (nuIdeal L k (ν k) j) w y x =
      v1T P.m₀ St j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) y x := by
  classical
  unfold v1T
  refine finsum_mem_congr rfl fun X hX => ?_
  exact v1Loc_axis_eq ctx hQ hX.1 hX.2 hpos _ (fun Ψ b => hsrc y X Ψ b) hw x

open Balaban.SmallField.Def6v2 in
/-- The whole-torus coefficient at the coordinate axis is the derivative of the density: if `St`
is a source form of the terms (the shape of `D1Corr.src_pos`), then
`v1T … e_{i₀} y x = ∂_{δ_x e_{i₀}} ℰ^{(j)}(y; ·, e_{i₀})` at the constant field `e_{i₀}`. -/
theorem v1T_eq_fderiv_Eloc (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    (St : SourceTerms d L N₁ m₁ k N) (hpos : 0 < nuIdeal L k (ν k) j)
    (hsrc : ∀ (y : Localization.CTorus d L N₁ m₁ k) (Y : Set (Localization.CTorus d L N₁ m₁ k))
      (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ), St.E j y Y Ψ (constFld b) =
        Tm.E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (y x : Localization.CTorus d L N₁ m₁ k) :
    v1T P.m₀ St j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) y x =
      fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDirV L j x (Pi.single i₀ 1)) := by
  classical
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hfin : (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y).Finite :=
    Set.toFinite _
  have hEloc : (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀)) =
      fun ψ => ∑ X ∈ hfin.toFinset, Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    unfold Eloc
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [hEloc, fderiv_fun_sum (fun X hX => (ctx.analyticAt_E i₀ y
    (Set.Finite.mem_toFinset hfin |>.1 hX).1 (Set.Finite.mem_toFinset hfin |>.1 hX).2).differentiableAt)]
  unfold v1T
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [_root_.sum_apply]
  refine Finset.sum_congr rfl fun X _ => ?_
  unfold v1Loc
  have : (fun ψ : Fld d L N₁ m₁ k N =>
      St.E j y X ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
      fun ψ => Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    rw [hsrc, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  rw [this]

/-- **First-derivative translation covariance of the density on a torus** (the first-order
analogue of `LiftCtx.D2_Eloc_translate`; P1 (H.3-E), `eucEloc`): for `y` aligned,
`∂_x ℰ(y) = ∂_{x-y} ℰ(0)` at the constant field.  It is the covariance of the SUM over polymers
through the centre (`Eloc`), not of the individual terms. -/
theorem D1_Eloc_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {y : Localization.CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (x : Localization.CTorus d L N₁ m₁ k) :
    fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) =
      fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j (x - y) i₀) := by
  have hjk := ctx.jk
  have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hy
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  refine fderiv_eq_of_line_eventually (ctx.analyticAt_Eloc i₀ y).differentiableAt
    (ctx.analyticAt_Eloc i₀ 0).differentiableAt ?_
  have hev : ∀ᶠ s : ℂ in nhds 0, ‖s‖ ≤ ρ / 2 := by
    have : Metric.closedBall (0 : ℂ) (ρ / 2) ∈ nhds (0 : ℂ) :=
      Metric.closedBall_mem_nhds _ (by linarith [ctx.rho_pos])
    filter_upwards [this] with s hs using by simpa using hs
  filter_upwards [hev] with s hs
  have hst : ‖s‖ + ‖(0 : ℂ)‖ ≤ ρ := by rw [norm_zero]; linarith [ctx.rho_pos]
  have X1 := ctx.xiDom_const (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk) hlev i₀
    (eFld d L N₁ m₁ k N i₀ + s • blockDir L j x i₀ + (0 : ℂ) • blockDir L j 0 i₀)
    (fun z i => (slice_dev x 0 i₀ i₀ s 0 z i).trans hst)
    (fun z z' h => slice_jBlock hjk x 0 i₀ i₀ s 0 h)
  have X2 := ctx.xiDom_const (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk) hlev i₀
    (eFld d L N₁ m₁ k N i₀ + s • blockDir L j (x - y) i₀ + (0 : ℂ) • blockDir L j (-y) i₀)
    (fun z i => (slice_dev (x - y) (-y) i₀ i₀ s 0 z i).trans hst)
    (fun z z' h => slice_jBlock hjk (x - y) (-y) i₀ i₀ s 0 h)
  set r : Equiv.Perm (Localization.CTorus d L N₁ m₁ k) := Equiv.addRight (-y) with hrdef
  have e1 := actField_addRight_neg_blockDir (N := N) hjk hy x i₀
  have hact : actField (N := N) r (eFld d L N₁ m₁ k N i₀ + s • blockDir L j x i₀ +
      (0 : ℂ) • blockDir L j 0 i₀) = eFld d L N₁ m₁ k N i₀ + s • blockDir L j (x - y) i₀ +
        (0 : ℂ) • blockDir L j (-y) i₀ := by
    funext z i'
    have h1 := congrFun (congrFun e1 z) i'
    simp only [actField, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld, constFld, zero_mul,
      add_zero] at h1 ⊢
    rw [h1]
  have hc0 : actField (N := N) r (eFld d L N₁ m₁ k N i₀) = eFld d L N₁ m₁ k N i₀ := rfl
  have key := ctx.sf.eucEloc j ctx.j1 hjk y r hr
    (eFld d L N₁ m₁ k N i₀ + s • blockDir L j x i₀ + (0 : ℂ) • blockDir L j 0 i₀)
    (eFld d L N₁ m₁ k N i₀) X1 (by rw [hact, hc0]; exact X2)
  rw [hact, hc0] at key
  have hry : r y = 0 := by
    funext μ; simp [hrdef]
  rw [hry, blockBase_zero] at key
  simp only [zero_smul, add_zero] at key
  exact key.symm

end Axis

section AvgKernel

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (P β ν a Tm j) in
/-- **The coefficient `∂_{ψ_{i₀}(z)} ℰ_∞(y, X')` of one polymer of `T∞` at the reference point**,
for the cut-off term `GE` of `T∞` centred at `y` (`0` for `z ∉ X'`, and for every polymer that is not
active at `y`, since `GE` vanishes then).  It is the term-by-term quantity of which `aCoefX` is the
instance `y = 0`. -/
noncomputable def GEder (i₀ : Fin N) (νj : ℝ) (y : SmallField.Site d) (X' : Finset (SmallField.Site d)) (z : SmallField.Site d) : ℂ :=
  if hz : z ∈ X' then tensA i₀ νj X' (GE P β ν a Tm j i₀ νj y X') ⟨z, hz⟩ else 0

variable (P β ν a Tm j) in
/-- **The kernel of `T∞` at the centre `y`**: `a_y(z) = ∑_{X' ∋ y} ∂_{ψ_{i₀}(z)} ℰ_∞(y, X')`, the
sum over all polymers of `T∞` through `y` (the polymers not through `y` contribute `0`).  At `y = 0`
it is the kernel of the unaveraged family `liftInfA`
(`aCoef_liftInfA_eq_aInfC`). -/
noncomputable def aInfC (i₀ : Fin N) (νj : ℝ) (y z : SmallField.Site d) : ℂ :=
  ∑' X' : Finset (SmallField.Site d), GEder P β ν a Tm j i₀ νj y X' z

theorem GEder_of_not_mem {i₀ : Fin N} {νj : ℝ} {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)}
    (hz : z ∉ X') : GEder P β ν a Tm j i₀ νj y X' z = 0 := by
  unfold GEder; simp only [hz, dite_false]

theorem GEder_eq_zero_of_inactive {i₀ : Fin N} {νj : ℝ} {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)}
    (h : ¬ (InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X')) :
    GEder P β ν a Tm j i₀ νj y X' z = 0 := by
  unfold GEder
  split_ifs with hz
  · have : GE P β ν a Tm j i₀ νj y X' = fun _ => 0 := funext fun c => GE_eq_zero h _ c
    simp [tensA, this]
  · rfl

theorem shiftCfg_refPt_add_smul {i₀ : Fin N} (t : SmallField.Site d) (X : Finset (SmallField.Site d)) (νj : ℝ) (x : SmallField.Site d)
    (hx : x ∈ X) (s : ℂ) :
    shiftCfg t X (refPt i₀ νj X + s • (Pi.single (Sum.inl (⟨x, hx⟩, i₀)) 1 : Cfg d N X)) =
      refPt i₀ νj (shiftFin t X) +
        s • (Pi.single (Sum.inl (⟨x + t, add_mem_shiftFin x hx⟩, i₀)) 1 :
          Cfg d N (shiftFin t X)) := by
  ext (⟨z, i⟩ | i)
  · simp only [shiftCfg, reCfg_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, refPt_inl,
      Pi.single_apply, Sum.inl.injEq, Prod.mk.injEq, Subtype.ext_iff, sub_eq_iff_eq_add]
  · simp [shiftCfg, reCfg_inr, refPt_inr]

section Diff

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
include hF hn

/-- `GE` is differentiable at the reference point. -/
theorem GE_differentiableAt_refPt (hr : 0 < anisoRadius d L N P j) (y : SmallField.Site d)
    (X' : Finset (SmallField.Site d)) :
    DifferentiableAt ℂ (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X')
      (refPt i₀ (nuIdeal L k (ν k) j) X') := by
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X'
  · exact (GE_analyticAtA hF hn h.1 h.2 (refPt_mem_polyAniso hr)).differentiableAt
  · have : GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' = fun _ => 0 :=
      funext fun c => GE_eq_zero h _ c
    rw [this]; exact differentiableAt_const _

/-- **The coefficient of the translated term**: for `x ∈ X` and a paving offset `t`, the coefficient
of `GEs t X = ℰ_∞(offs t, X + offs t; c(· - offs t))` at the site `x` is the coefficient of the
polymer `X + offs t` of `T∞` at the centre `offs t`, at the site `x + offs t`. -/
theorem tensA_GEs_eq_GEder (hne : i₁ ≠ i₀) (hr : 0 < anisoRadius d L N P j) {Mb : ℕ}
    (t : Fin d → Fin Mb) {X : Finset (SmallField.Site d)} {x : SmallField.Site d} (hx : x ∈ X) :
    tensA i₀ (nuIdeal L k (ν k) j) X (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X) ⟨x, hx⟩ =
      GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) (shiftFin (offs t) X) (x + offs t) := by
  have hmem : x + offs t ∈ shiftFin (offs t) X := add_mem_shiftFin x hx
  unfold GEder tensA
  simp only [hmem, dite_true]
  refine fderiv_eq_of_line (v := Pi.single (Sum.inl (⟨x, hx⟩, i₀)) 1)
    (w := Pi.single (Sum.inl (⟨x + offs t, hmem⟩, i₀)) 1)
    ((GEs_tubeHypA hF hn hne t X).analytic _ (refPt_mem_polyAniso hr)).differentiableAt
    (GE_differentiableAt_refPt hF hn hr _ _) fun s => ?_
  show GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) (shiftFin (offs t) X)
      (shiftCfg (offs t) X _) = _
  rw [shiftCfg_refPt_add_smul]

end Diff


theorem summable_comp_shift {g : Finset (SmallField.Site d) → ℂ} (t : SmallField.Site d)
    (hg : Summable g) : Summable (fun X => g (shiftFin t X)) :=
  (Equiv.summable_iff (shiftEquiv t)).2 hg

theorem tsum_comp_shift (t : SmallField.Site d) (g : Finset (SmallField.Site d) → ℂ) :
    ∑' X, g (shiftFin t X) = ∑' X, g X :=
  Equiv.tsum_eq (shiftEquiv t) g

section AvgFormula

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

/-- **The coefficient of one polymer of the averaged family, exactly.**  With the coset
representatives `rep q` of `avgB_eq_sum`, for every polymer `X` and site `x`,
`aCoefX (avgFamilyA …) X x = |Q|⁻¹ ∑_q ∂_{ψ(x + τ_q)} ℰ_∞(τ_q, X + τ_q)` (`τ_q = offs (rep q)`): the
average of the coefficients of the translated polymers, centred at the translate and evaluated at
the translated site. -/
theorem aCoefX_avgFamilyA :
    ∃ rep : (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) → (Fin d → Fin (L ^ (P.m₀ + m₁))),
      ∀ (X : Finset (SmallField.Site d)) (x : SmallField.Site d),
        aCoefX (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) X x =
          (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
            ∑ q, GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs (rep q))
              (shiftFin (offs (rep q)) X) (x + offs (rep q)) := by
  have hr : 0 < anisoRadius d L N P j := (hF.anisoRadiusOK hn.hsmall i₀).1
  obtain ⟨rep, hrep⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  refine ⟨rep, fun X x => ?_⟩
  by_cases hx : x ∈ X
  · have hmain : tensA i₀ (nuIdeal L k (ν k) j) X
        ((avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).term X)
        ⟨x, hx⟩ =
        (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
          ∑ q, tensA i₀ (nuIdeal L k (ν k) j) X
            (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (rep q) X) ⟨x, hx⟩ := by
      unfold tensA
      have hev : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)).term X =ᶠ[nhds (refPt i₀ (nuIdeal L k (ν k) j) X)]
          avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X := by
        filter_upwards [isOpen_polyAniso.mem_nhds (refPt_mem_polyAniso hr)] with c hc
        exact trickFnA_of_poly (avgB_tubeHypA hF hn hne X) hc
      rw [hev.fderiv_eq]
      have hfun : avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X = fun c =>
          (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
            ∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (rep q) X c := by
        funext c; exact hrep i₀ _ X c
      have hdiff : ∀ q ∈ (Finset.univ : Finset (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j)),
          DifferentiableAt ℂ (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (rep q) X)
            (refPt i₀ (nuIdeal L k (ν k) j) X) := fun q _ =>
        ((GEs_tubeHypA hF hn hne (rep q) X).analytic _ (refPt_mem_polyAniso hr)).differentiableAt
      rw [hfun, fderiv_const_mul (DifferentiableAt.fun_sum hdiff), fderiv_fun_sum hdiff]
      simp only [_root_.smul_apply, smul_eq_mul, _root_.sum_apply]
    unfold aCoefX
    simp only [hx, dite_true]
    rw [hmain]
    congr 1
    exact Finset.sum_congr rfl fun q _ => tensA_GEs_eq_GEder hF hn hne hr (rep q) hx
  · unfold aCoefX
    simp only [hx, dite_false]
    symm
    rw [Finset.sum_eq_zero, mul_zero]
    intro q _
    refine GEder_of_not_mem fun h => hx ?_
    have := mem_shiftFin.1 h
    simpa using this

omit hF hn hne in
theorem GEder_support {Mb : ℕ} (t : Fin d → Fin Mb) (x : SmallField.Site d)
    (X : Finset (SmallField.Site d))
    (h : GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) (shiftFin (offs t) X)
      (x + offs t) ≠ 0) :
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧ (0 : SmallField.Site d) ∈ X := by
  by_contra hc
  refine h (GEder_eq_zero_of_inactive fun h' => hc ⟨h'.1, ?_⟩)
  have := mem_shiftFin.1 h'.2
  simpa using this


omit hF hn hne in
theorem support_GEder_shift_subset (t : Fin d → Fin (L ^ (P.m₀ + m₁))) (x : SmallField.Site d) :
    Function.support (fun X : Finset (SmallField.Site d) =>
      GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) (shiftFin (offs t) X) (x + offs t)) ⊆
    avgPolys (d := d) L m₁ k P j := by
  intro X hX
  obtain ⟨h1, h0⟩ := GEder_support t x X hX
  exact ⟨h0, t, h1⟩

/-- Near the reference point the term of the unaveraged infinite-volume family is the cut-off term
`GE` of `T∞` centred at `0`. -/
theorem termLInfA_eventuallyEq_GE {X' : Finset (SmallField.Site d)}
    (h0 : (0 : SmallField.Site d) ∈ X') (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' =ᶠ[
      nhds (refPt i₀ (nuIdeal L k (ν k) j) X')] GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 X' := by
  have hr : 0 < anisoRadius d L N P j := (hF.anisoRadiusOK hn.hsmall i₀).1
  obtain ⟨n, hgood⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hρ := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  filter_upwards [isOpen_polyAniso.mem_nhds (refPt_mem_polyAniso hr),
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)] with c hc1 hc2
  rw [termLInfA_eq hF.torusIndep hn.hj1 hn.hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hgood.1 hgood.2 c,
    termLA_eq (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hn.hd hn.hL hn.hϱ)
      hF.coeff.nu_pos hn.hj1 hn.hjk (hF.anisoRadiusOK hn.hsmall i₀) hgood.2 h0 hne isOrth_one
      entryBd_one (by rwa [rotCfgL_one]), rotCfgL_one,
    GE_eq_EauxC hF hn hX h0 hc2 hgood]
  simp [EauxC, Eaux, blockPt_zero]

/-- **The kernel of the unaveraged infinite-volume family is `a_0`**: `aCoef (liftInfA …) x` is the
sum over the polymers of `T∞` through `0` of `∂_{ψ(x)} ℰ_∞(0, X')`. -/
theorem aCoef_liftInfA_eq_aInfC (x : SmallField.Site d) :
    aCoef (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) x =
      aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 x := by
  classical
  unfold aCoef aInfC
  have hterm : ∀ X' : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)).polys, aCoefX (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀
        (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) X'.1 x =
      GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 X'.1 x := by
    intro X'
    obtain ⟨h0, hX⟩ := X'.2
    unfold aCoefX GEder
    by_cases hx : x ∈ X'.1
    · simp only [hx, dite_true]
      unfold tensA
      have hev := termLInfA_eventuallyEq_GE hF hn hne (X' := X'.1) h0 hX
      simp only [liftInfA]
      rw [hev.fderiv_eq (𝕜 := ℂ)]
    · simp [hx]
  rw [tsum_congr hterm]
  refine tsum_subtype_eq_of_support_subset (f := fun X' : Finset (SmallField.Site d) =>
    GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 X' x) (s := {X' | (0 : SmallField.Site d) ∈ X' ∧
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'}) fun X' hX' => ?_
  by_contra hc
  exact hX' (GEder_eq_zero_of_inactive fun h' => hc ⟨h'.2, h'.1⟩)

/-- **T2 (b): the kernel of the averaged family is the normalized sum of the translated kernels
of `T∞`.**  For `x : ℤ^d`, with the coset representatives `rep q` of `avgB_eq_sum`,
`a_avg(x) = |Q|⁻¹ ∑_q a_{τ_q}(x + τ_q)`, `a_y(z) = ∑_{X' ∋ y} ∂_{ψ(z)} ℰ_∞(y, X')` (`aInfC`), `τ_q`
the paving offsets.  The summability hypotheses say that, for each offset, the sum over the polymers
of the coefficients is absolutely convergent (the Cauchy bound with the counting of `sum_wt_dInf_le_at`
gives it in the class). -/
theorem aCoef_avgFamilyA_eq_sum (x : SmallField.Site d)
    (hsum : ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
      Summable (fun X' : Finset (SmallField.Site d) =>
        GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) X' (x + offs t))) :
    ∃ rep : (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) → (Fin d → Fin (L ^ (P.m₀ + m₁))),
      aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
          (nuIdeal L k (ν k) j) x =
        (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
          ∑ q, aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs (rep q)) (x + offs (rep q)) := by
  classical
  obtain ⟨rep, hrep⟩ := aCoefX_avgFamilyA hF hn hne (i₀ := i₀)
  refine ⟨rep, ?_⟩
  unfold aCoef
  have e1 : ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)).polys, aCoefX (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) X.1 x =
      ∑' X : avgPolys (d := d) L m₁ k P j, (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs (rep q))
          (shiftFin (offs (rep q)) X.1) (x + offs (rep q)) := tsum_congr fun X => hrep X.1 x
  have hs : ∀ q ∈ (Finset.univ : Finset (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j)),
      Summable (fun X : ↥(avgPolys (d := d) L m₁ k P j) =>
        GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs (rep q))
          (shiftFin (offs (rep q)) X.1) (x + offs (rep q))) := fun q _ =>
    (summable_comp_shift (offs (rep q)) (hsum (rep q))).subtype _
  rw [e1, tsum_mul_left, Summable.tsum_finsetSum hs]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [tsum_subtype_eq_of_support_subset (support_GEder_shift_subset (rep q) x)]
  exact tsum_comp_shift (offs (rep q)) (fun X' =>
    GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs (rep q)) X' (x + offs (rep q)))

end AvgFormula

end AvgKernel

open Balaban.SmallField.Def6v2 in
/-- **First-derivative translation covariance of the whole-torus coefficient**:
`v1T … y x = v1T … 0 (x - y)` for `y` aligned (from `eucEloc`, the covariance of the sum over
polymers through the centre). -/
theorem v1T_translate {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts}
    {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
    {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} {j : ℕ} {ρ : ℝ} (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    (St : SourceTerms d L N₁ m₁ k N) (hpos : 0 < nuIdeal L k (ν k) j)
    (hsrc : ∀ (y : Localization.CTorus d L N₁ m₁ k) (Y : Set (Localization.CTorus d L N₁ m₁ k))
      (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ), St.E j y Y Ψ (constFld b) =
        Tm.E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    {y : Localization.CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (x : Localization.CTorus d L N₁ m₁ k) :
    v1T P.m₀ St j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) y x =
      v1T P.m₀ St j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) 0 (x - y) := by
  rw [v1T_eq_fderiv_Eloc ctx i₀ St hpos hsrc y x, v1T_eq_fderiv_Eloc ctx i₀ St hpos hsrc 0 (x - y),
    blockDirV_single, blockDirV_single]
  exact D1_Eloc_translate ctx i₀ hy x

theorem blockPt_sub {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] (j : ℕ) (y z : SmallField.Site d) :
    blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) =
      blockPt j z - blockPt j y := by
  funext μ
  simp [blockPt, sub_mul, Int.cast_sub]

theorem blockPt_aligned {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {j : ℕ} (hjk : j ≤ k)
    (y : SmallField.Site d) :
    Aligned (L ^ j) (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) := by
  have hbp : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y = ibase j y := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  rw [hbp]; exact ibase_aligned hjk y

section Final

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Balaban.SmallField.Def6v2 in
/-- **The kernel of `T∞` is translation covariant, `a_y(z) = a_0(z - y)`, from the torus covariance
of the density.**  The premise `hM1` is the missing link M1 (thermodynamic limit): the
whole-torus coefficient `v1T` at the centre `y` converges along `torusSeq` to the kernel `a_y(z)` of
`T∞`.  The torus identity `v1T_translate` (`eucEloc`, the covariance of the SUM over the polymers
through the centre, for the translations of the level-`j` lattice) passes to the limit. -/
theorem aInfC_translate_of_M1 (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    (i₀ : Fin N) (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (hM1 : ∀ y z : SmallField.Site d, Tendsto (fun n : ℕ =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (ν k) j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) atTop
      (nhds (aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y z)))
    (y z : SmallField.Site d) :
    aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y z =
      aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 (z - y) := by
  have hpos := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  refine tendsto_nhds_unique (hM1 y z) ((hM1 0 (z - y)).congr fun n => ?_)
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  show v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (ν k) j) (Pi.single i₀ 1)
      (blockPt j 0) (blockPt j (z - y)) = _
  rw [blockPt_zero, blockPt_sub (L := L) (m₁ := m₁) (k := k), v1T_translate ctx i₀ _ hpos
    (hsrc (torusSeq L P.m₀ n)) (blockPt_aligned hn.hjk y)]

end Final

open Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 in
/-- **T4, one torus, the axis of `D1Corr`**: `a_j(x) = v₁^{(j)}(0, x)` for the lifted family `liftTF`
with the coefficient `v1T` taken at the direction `e₁ = hC hv` of `D1Corr` (not at a coordinate
vector), when `hC hv = Q e_{i₀}` for a real orthogonal `Q`.  Remaining premises: `hsurj` (M4, no
polymer of the torus winds). -/
theorem aCoef_liftTF_eq_v1T_axis_of_D1Corr {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    {P : Consts} {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d}
    {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} {j : ℕ} {ρ : ℝ} {i₀ i₁ : Fin N}
    (hD : D1Corr P.m₀ sf St hv vc)
    (ctx : LiftCtx P sf.β sf.ν sf.a (sf.Tm N₁) ρd Ek j ρ) (hne : i₁ ≠ i₀)
    (hpos : 0 < nuIdeal L k (sf.ν k) j)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hw : hC hv = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (hsurj : ∀ Y ∈ polysAt P.m₀ j (0 : Localization.CTorus d L N₁ m₁ k),
      ∃ X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
        Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Y)
    (x : SmallField.Site d) (hx : CentredAt L N₁ m₁ k j x) :
    aCoef (liftTF P j i₀ (nuIdeal L k (sf.ν k) j) ρ (sf.Tm N₁)) i₀ (nuIdeal L k (sf.ν k) j) x =
      v1T P.m₀ (St N₁) j (nuIdeal L k (sf.ν k) j) (hC hv) 0 (blockPt j x) := by
  rw [aCoef_liftTF_eq_v1T_of_D1Corr hD ctx hne hpos hsurj x hx,
    v1T_axis_eq ctx hQ (St N₁) hpos (fun y Y Ψ b => hD.src_pos N₁ j ctx.j1 ctx.jk hpos y Y Ψ b)
      hw]

section Final2

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Balaban.SmallField.Def6v2 in
/-- **T2 (a), with the invariance proved from the class: the averaged and the unaveraged kernels
agree.**  `aCoef (avgFamilyA …) x = aCoef (liftInfA …) x`, given the summability of the
coefficients over the polymers (explicit) and the limit link M1 (`hM1`, see
`aInfC_translate_of_M1`).  The proof is the exact formula `aCoef_avgFamilyA_eq_sum`, the translation
covariance `aInfC_translate_of_M1` of the SUM over polymers through a centre (landed `eucEloc`), and
`aCoef_liftInfA_eq_aInfC`; no covariance of the individual terms is used (it is not landed for
the offsets that are not multiples of the paving cell). -/
theorem aCoef_avgFamilyA_eq_liftInfA_of_M1 (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (hM1 : ∀ y z : SmallField.Site d, Tendsto (fun n : ℕ =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (ν k) j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) atTop
      (nhds (aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y z)))
    (x : SmallField.Site d)
    (hsum : ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
      Summable (fun X' : Finset (SmallField.Site d) =>
        GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) X' (x + offs t))) :
    aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
        (nuIdeal L k (ν k) j) x =
      aCoef (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) x := by
  obtain ⟨rep, hrep⟩ := aCoef_avgFamilyA_eq_sum hF hn hne x hsum
  rw [hrep, aCoef_liftInfA_eq_aInfC hF hn hne]
  have hq : ∀ q, aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs (rep q)) (x + offs (rep q)) =
      aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 x := fun q => by
    rw [aInfC_translate_of_M1 hF hn i₀ St hsrc hM1]; simp
  simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

open Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 in
/-- **T4: `a_j(x) = v₁^{(j)}(0, x)` for the family used by the renormalization theorem and the axis
used by `D1Corr`.**  For the averaged family `avgFamilyA` (the one `renormalization_aniso_of_v2`
consumes), at the radius `anisoRadius`, the marginal kernel is the limit coefficient `vc.v1 j x`
of `D1Corr`, with the axis `hC hv = Q e_{i₀}`.  Premises beyond the class and `D1Corr`: `hM1` (the
thermodynamic limit of the torus coefficient at every centre is the kernel of `T∞`, the missing
link M1) and the summability `hsum` of the coefficients over the polymers. -/
theorem aCoef_avgFamilyA_eq_v1_of_M1 {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d} (hD : D1Corr P.m₀ sf St hv vc)
    (hF : IsSFFamily P sf.β sf.ν sf.a sf.Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hw : hC hv = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (hM1 : ∀ y z : SmallField.Site d, Tendsto (fun n : ℕ =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (sf.ν k) j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) atTop
      (nhds (aInfC P sf.β sf.ν sf.a sf.Tm j i₀ (nuIdeal L k (sf.ν k) j) y z)))
    (x : SmallField.Site d)
    (hsum : ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
      Summable (fun X' : Finset (SmallField.Site d) =>
        GEder P sf.β sf.ν sf.a sf.Tm j i₀ (nuIdeal L k (sf.ν k) j) (offs t) X' (x + offs t))) :
    aCoef (avgFamilyA P sf.β sf.ν sf.a sf.Tm j i₀ (nuIdeal L k (sf.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (sf.ν k) j) x = vc.v1 j x := by
  have hpos := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (sf.Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun N₁ _ y Y Ψ b => hD.src_pos N₁ j hn.hj1 hn.hjk hpos y Y Ψ b
  rw [aCoef_avgFamilyA_eq_liftInfA_of_M1 hF hn hne St hsrc hM1 x hsum,
    aCoef_liftInfA_eq_aInfC hF hn hne]
  refine tendsto_nhds_unique (by simpa [blockPt_zero] using hM1 0 x) ?_
  refine (hD.v1_lim j hn.hj1 hn.hjk x).congr fun n => ?_
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  exact v1T_axis_eq ctx hQ (St (torusSeq L P.m₀ n)) hpos (hsrc (torusSeq L P.m₀ n)) hw 0
    (blockPt j x)

end Final2





end Balaban.LargeField.Def7v2
