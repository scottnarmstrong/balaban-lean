/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgMomTorus
public import Balaban.LargeField.Def7v2

/-!
# The radial coefficient: `a_j` and `v₁^{(j)}` (Q13-GROUPED §1, `regionalRadialCoefficient`)

The marginal kernel `a_j` of the renormalization step and the coefficient `v₁^{(j)}` of the
correction (1.8) of P5 are the radial spin derivative of the same energy term (P1 p. 146 (3.104),
(3.106)).  This file proves that identity termwise and for the sum over polymers of one torus,
for the lifted family `liftTF`, and records which links to the limit family of `D1Corr` are not
landed.

## What is proved

* `fderiv_eq_of_line`: the chain rule for `fderiv` along a line, through a reindexing.
* `tensA_EauxC_eq_v1Loc` (T2): for a polymer `X'` of the lift and a block corner `u` with
  `unlift u ∈ X'`, `tensA i₀ ν_j X' (EauxC …) ⟨unlift u, _⟩ = v1Loc Et j ν_j e_{i₀} u`, where `Et`
  is a source form of the term (the shape of `D1Corr.src_pos`).  Hypotheses: the context `LiftCtx`
  (analyticity at the reference point and at the constant field), non-winding, polymer, `y ∈ X'`.
* `fderiv_termL_eq`, `aCoefX_liftTF_eq_v1Loc` (T3, one polymer): the same for the term `termL` of
  `liftTF` at the origin, for every centred site `x` (for `x ∉ X'` both sides vanish: `aCoefX = 0`
  by definition, and `v1Loc = 0` by locality `IsSF.localE`).
* `aCoef_liftTF_eq_v1T_of_nonwinding` (T3, sum): `aCoef (liftTF …) i₀ ν_j x = v1T m₀ St j ν_j e_{i₀}
  0 (blockPt j x)`, i.e. `a(x) = v₁(0, x)` on one torus, if every polymer of `𝒟_j` through `0` is
  the torus polymer of a non-winding lattice polymer (`hsurj`).  The polymer sets are matched by the
  bijection `Ypoly j` (`Set.BijOn`), and the two sums are finite sums (`shN_finite`).
* `aCoef_liftTF_eq_v1T_of_D1Corr`: the same with the source relation supplied by `D1Corr.src_pos`.
The centre `0` is the only centre needed: `v1_lim` is stated at the centre `0` (`blockPt j 0 = 0`),
and the terms with centre `y` are handled by `EauxC` (T2 holds for every centre `y ∈ X'`).

## T1: the dictionary, with declaration names

Scale and carrier.  The torus is `CTorus d L N₁ m₁ k` (Localization/Cover.lean:30), fields
`Fld = CTorus → ℂ^N` (Def6Terms.lean:44).  The class terms are `Tm.E j y X Ψ h`
(`Terms`, Def6.lean:89), `y` the base point of a `j`-block, `X` a set of fine sites, `(Ψ, h)` the
spin field and the source `h`.  The unit lattice at scale `j` is `Fin d → ℤ` (`Site d`,
RenormDefs.lean:41); a fine site is sent to its centred block position by `unlift j`
(Def6Terms.lean:171, via `ZMod.valMinAbs` of `jBlock`), a block position `y` is sent to the fine
corner by `blockPt j y` (Def6Terms.lean:198) `= ibase j y` (Def6BridgeGeom.lean:82).
`Ypoly j X'` (Def6Terms.lean:176) is the torus polymer of a lattice polymer `X'`; it is injective on
non-winding `X'` (`NonWind`), with inverse `unlift` (`unlift_ibase`, Def6BridgeGeom.lean:85).

Polymers and terms of the lift.  `liftPolys P j` (Def6BridgeLift.lean:642): finite sets
`X' ∋ 0` that do not wind and have `Ypoly j X' ∈ 𝒟_j`.  The configuration of a polymer is
`Cfg d N X' = (X' × Fin N ⊕ Fin N) → ℂ` (RenormDefs.lean:48) and is turned into torus data by
`fieldOf j i₀ X' c` (Def6BridgeLift.lean:46: `c` on the blocks of `X'`, the constant `e_{i₀}`
elsewhere) and `hOf ν_j X' c` (:52, `h = c(inr)/ν_j`).  The centred term is
`Eaux Tm j i₀ ν_j X' c = Tm.E j 0 (Ypoly j X') (fieldOf c) (hOf c)` (:121; centre `y`:
`EauxC`, Def6AvgLiftC.lean:40), and the term of the family is `termL` (:528, the same function
composed with a complex orthogonal rotation on the tube, equal to `Eaux` on the ball:
`fderiv_termL_eq`).  `liftTF P j i₀ ν_j ρ Tm` (:649) is the `TermFamily` with these polymers and
terms.  The infinite-volume analogue is `liftInfA` (RenormAnisoBridgeInf.lean:61) with `termLInfA`
and `EauxInf` (Def6BridgeInfDict.lean:204).  The family to which the renormalization theorem is
applied, however, is `avgFamilyA` (RenormClassFamily.lean:140; used in
`Def6v2RenormCompare.renormalization_aniso_of_v2`, RenormClassTheorem.lean:152): its term is the
Reynolds average `avgB` (Def6AvgFamily.lean:214) over paving offsets and the point group
of the terms of `T∞`.

Source convention.  `TermFamily.term` is a function of `(ψ, b)`, `b = ν_j h`
(RenormDefs.lean:18): `refPt i₀ ν X` (:63) is `(e_{i₀}, ν e_{i₀})`, i.e. `h = e_{i₀}`
(`Def6BridgeLift.refPt_inr`; `hOf` divides by `ν_j`).  `v1Loc` (Def7v2Corr.lean:156) differentiates
a source form `Et ψ b` at `(constFld e₁, constFld (ν e₁))`, also in the variable `b`.
`D1Corr.src_pos` (Def7v2.lean:81) says `St.E … (constFld b) = Tm.E … (constFld (ν⁻¹ • b))`; so
`v1Loc (St.E …) j ν e₁` is the `ψ`-derivative of the class term `Tm.E` at `h = e₁`, the same point
as `refPt` (no mismatch; `tensA_EauxC_eq_v1Loc` proves it).  `sourceOf` (Def6v2Source.lean:192)
is the landed instance of the relation.

Landed links: `liftTF`/`Eaux` carry the torus term to `Cfg` (definitions, with analyticity
`LiftCtx.analyticAt_EauxC`, locality `IsSF.localE`); `unlift`/`blockPt`/`Ypoly` match blocks and
sites; `D1Corr.src_pos` relates `St` and `Tm`; `termL_eq`/`fderiv_termL_eq` relate the tube term to
`Eaux`.  Not landed (before this file): any statement relating `tensA` to `v1Loc`, or `aCoef` of any
family to `v1T`.

## T4: missing links (not assumed)

The identity `aCoef T i₀ ν z = vc.v1 j z` for a `D1Corr` datum needs, besides the above:

* (M1, limit) `Summable`-type domination of the tails and the following proposition.  For
  `P`, `Tm`, `St`, `hv`, `vc` as in `D1Corr P.m₀ sf St hv vc`, for `1 ≤ j ≤ k`, `z : Fin d → ℤ`,
  `i₀`, with `TorusIndep`: `Tendsto (fun n => v1T P.m₀ (St (torusSeq L P.m₀ n)) j ν_j e_{i₀} 0
  (blockPt j z)) atTop (𝓝 (aCoef (liftInfA P Tm j i₀ ν_j r) i₀ ν_j z))`.
  The terms agree for large `n` polymer by polymer (`termLInfA_eq`, `aCoefX_liftTF_eq_v1Loc`), but
  the torus sums also contain winding polymers, and the passage to the limit needs a bound
  `Σ_{X ∋ 0} sup_n |∂ψ(x) ℰ_n| < ∞` uniform in `n` (the tube bound `E₀ e^{-κ d_j}` of the
  class would give it by Cauchy estimates, but it is not stated for `v1Loc`).  Owner: a new bridge module
  next to `Def6BridgeInfSum.lean` (which already contains `tensA` sums for the infinite family).
* (M2, averaging) `aCoef (avgFamilyA P β ν a Tm j i₀ ν_j r) i₀ ν_j z = aCoef (liftInfA P Tm j i₀
  ν_j r) i₀ ν_j z`, i.e. the kernel of the renormalization theorem (the Reynolds average over the
  coset space `GG d L j ⧸ KK d L P.m₀ m₁ j`, `Def6AvgFamily.lean`) is the kernel of the unaveraged
  family.  This is not a consequence of the landed covariance (`eucE` holds for `pavingSymGroup`
  only); it needs that the whole-lattice kernel is invariant under the point group of `ℤ^d`
  (a property of `v1_lim`, which `D1Corr` does not state).  Owner: `Def6v2RenormCompare` or a file
  on `avgB`.
* (M3, axis) `D1Corr` takes the direction `e₁ = hC hv` of the physical field `h`; the identities
  above are at the coordinate axis `e_{i₀}`.  `v1Loc` at `hC hv` equals `v1Loc` at `e_{i₀}` by
  the real rotation invariance `IsSF.rotE`, which needs membership of the rotated data in `XiDom`.
* (M4, winding) `hsurj` of `aCoef_liftTF_eq_v1T_of_nonwinding`: every polymer of `𝒟_j` through `0`
  on the torus `N₁` is non-winding.

## T5: findings

(a) `a = v₁`, not `v₁ + ν_j v₂`.  `aCoefX` (RenormDefs.lean:199) is `tensA` (:112), the derivative
of the term at `refPt i₀ ν X = (e_{i₀}, ν e_{i₀})` in the single coordinate direction
`Pi.single (Sum.inl (x, i₀)) 1`: only `ψ_{i₀}(x)` moves, `b` stays at `ν e_{i₀}`.  `v1Loc`
(Def7v2Corr.lean:156) is the derivative in `ψ` in the direction `blockDirV x e₁` with the source
fixed at `constFld (ν e₁)`.  `tensA_EauxC_eq_v1Loc` proves they are equal.  The second coefficient
`v2Loc` (:164) is the `b`-derivative of the *transverse* derivative `D_{ψ(x)}[e₂]` at `b = ν e₁`
in the direction `e₂ ⟂ e₁`; it is a different quantity and does not enter `aCoefX` at all.  The
total derivative along the diagonal `(ψ, b) = (t e₁, ν t e₁)` is not what `aCoef` computes (that is
(H.5)(3), `RenormDefs.lean:168`, which sums `tensA`).  The sentence in SMALLFIELD.md §2.5(iii)
(line 231, "so `a = v₁ + ν_j v₂` at that point") conflates the two terms of the pair term
(1.8), which agree on parallel configurations, with the coefficients; for the landed objects
`a = v₁` is the correct statement (Q13-GROUPED line 15).

(b) Source convention.  No mismatch: with `src_pos`, `v1Loc (St.E …) j ν e₁` is the derivative of
the class term `Tm.E` at `(ψ, h) = (e₁, e₁)`, which is `(ψ, b) = (e₁, ν e₁)`, the point of `refPt`
(the class term is in the variable `h`, the `TermFamily` and `St` in `b = ν h`).  What does not
match is only the *averaging* and the *axis* (M2, M3 above).  `src_pos` is conditional on
`ν_j > 0` and holds for `constFld b` only, which is all that `v1Loc` uses.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Filter

section Line

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A differentiable function has, along a line, the derivative `fderiv f p v`. -/
theorem hasDerivAt_line {f : E → ℂ} {p : E} (hf : DifferentiableAt ℂ f p) (v : E) :
    HasDerivAt (fun s : ℂ => f (p + s • v)) (fderiv ℂ f p v) 0 := by
  have h1 : HasDerivAt (fun s : ℂ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have h2 : HasFDerivAt f (fderiv ℂ f p) (p + (0 : ℂ) • v) := by
    simpa using hf.hasFDerivAt
  exact h2.comp_hasDerivAt 0 h1

/-- Two differentiable functions that agree along two lines have the same derivatives along them
(the chain rule through the reindexing `s ↦ p + s v ↦ q + s w`). -/
theorem fderiv_eq_of_line {f : E → ℂ} {g : F → ℂ} {p : E} {q : F} {v : E} {w : F}
    (hf : DifferentiableAt ℂ f p) (hg : DifferentiableAt ℂ g q)
    (h : ∀ s : ℂ, f (p + s • v) = g (q + s • w)) : fderiv ℂ f p v = fderiv ℂ g q w := by
  have h1 := hasDerivAt_line hf v
  have h2 := hasDerivAt_line hg w
  have : (fun s : ℂ => f (p + s • v)) = fun s : ℂ => g (q + s • w) := funext h
  rw [this] at h1
  exact h1.unique h2

end Line

section Termwise

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **T2: the tensor `tensA` of the centre-`y` class term is the local coefficient `v1Loc`.**
For a polymer `X'` of the lift (`X'` does not wind, `Ypoly j X'` is a polymer of `𝒟_j`, `y ∈ X'`),
a block corner `u` whose centred position lies in `X'`, and a source form `Et` of the term in the
variable `b = ν_j h` (the shape of `D1Corr.src_pos`), the derivative of `EauxC` at the reference
point `(e_{i₀}, ν_j e_{i₀})` in the coordinate `ψ_{i₀}(unlift u)` is `v1Loc` at the block `u`. -/
theorem tensA_EauxC_eq_v1Loc (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ : Fin N}
    {y : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (huX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X')
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j (blockPt j y) (Ypoly j X') Ψ
        (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b))) :
    tensA i₀ (nuIdeal L k (ν k) j) X' (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X')
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩ =
      v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) u := by
  have hjk := ctx.jk
  have hνj : 0 < nuIdeal L k (ν k) j := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := ctx.nu_pos
    unfold nuIdeal; positivity
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have h2 : AnalyticAt ℂ (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X')
      (refPt i₀ (nuIdeal L k (ν k) j) X') :=
    ctx.analyticAt_EauxC i₀ hpd y hnw hy (Metric.mem_ball_self ctx.rho_pos)
  have h1 := ctx.analyticAt_E i₀ (blockPt j y) hpd (blockPt_mem_Ypoly hjk hnw hy)
  have hEt' : (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
      fun ψ => Tm.E j (blockPt j y) (Ypoly j X') ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    rw [hEt, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  unfold tensA v1Loc
  rw [hEt']
  refine fderiv_eq_of_line h2.differentiableAt h1.differentiableAt (fun s => ?_)
  have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) := fun z => by
    rw [cbase_eq_iff_jBlock hjk hu z, unlift_eq_iff]
  set c : Cfg d N X' := refPt i₀ (nuIdeal L k (ν k) j) X' +
    s • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩, i₀)) 1 :
      Cfg d N X') with hc
  have hf : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c =
      eFld d L N₁ m₁ k N i₀ + s • blockDirV L j u (Pi.single i₀ 1) := by
    funext z i
    by_cases hz : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ X'
    · simp only [fieldOf, hz, dite_true, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, refPt_inl, blockDirV, eFld, constFld, hcu z,
        Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq]
      by_cases h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
          unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u <;>
        by_cases hi : i = i₀ <;> simp [h, hi]
    · have hu0 : blockDirV L j u (Pi.single i₀ 1 : Fin N → ℂ) z i = 0 := by
        have hne : ¬ cbase (L ^ j) z = u := fun h => hz ((hcu z).1 h ▸ huX)
        simp [blockDirV, hne]
      simp only [fieldOf, hz, dite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld,
        constFld, hu0]
      ring
  have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c =
      eFld d L N₁ m₁ k N i₀ := by
    funext z i
    simp only [hOf, hc, Pi.add_apply, Pi.smul_apply, eFld, constFld]
    rw [refPt_inr]
    simp only [Pi.single_apply, smul_eq_mul]
    simp only [reduceCtorEq, ite_false, mul_zero, add_zero]
    field_simp
  show Tm.E j (blockPt j y) (Ypoly j X') (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c) = _
  rw [hf, hh]

end Termwise

section Sum

open Balaban.SmallField.Def6v2 in
/-- The centred integer positions: `x` is the representative of minimal absolute value of its
block class on the torus (the condition under which the lattice site `x` and the block corner
`blockPt j x` correspond; `NonWind` of `{x}`). -/
def CentredAt (L N₁ m₁ k j : ℕ) {d : ℕ} (x : SmallField.Site d) : Prop :=
  NonWind L N₁ m₁ k j ({x} : Finset (SmallField.Site d))

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- On the ball of the tube radius the lifted term `termL` is the class term `Eaux`, so they have
the same derivative at the reference point (the rotation is the identity). -/
theorem fderiv_termL_eq (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) {X' : Finset (SmallField.Site d)}
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    (h0 : (0 : SmallField.Site d) ∈ X') :
    fderiv ℂ (termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X') (refPt i₀ (nuIdeal L k (ν k) j) X') =
      fderiv ℂ (Eaux Tm j i₀ (nuIdeal L k (ν k) j) X') (refPt i₀ (nuIdeal L k (ν k) j) X') := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self ctx.rho_pos)] with c hc
  have hR : IsOrth (1 : Matrix (Fin N) (Fin N) ℂ) := by simp [IsOrth]
  have hRb : EntryBd N (1 : Matrix (Fin N) (Fin N) ℂ) := by
    intro i k'
    by_cases h : i = k' <;> simp [Matrix.one_apply, h, rotBound]
  have := ctx.termL_eq hpd h0 hne hR hRb (by rwa [rotCfgL_one])
  rw [this, rotCfgL_one]

/-- **T3, one polymer**: for a polymer `X'` of the lift and a centred site `x`, the coefficient
`aCoefX` of the lifted family is the local coefficient `v1Loc` of the source form at the block
corner of `x` (including the case `x ∉ X'`, both sides being `0`, by locality `localE`). -/
theorem aCoefX_liftTF_eq_v1Loc (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) {X' : Finset (SmallField.Site d)}
    (hX' : X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (x : SmallField.Site d) (hx : CentredAt L N₁ m₁ k j x)
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j 0 (Ypoly j X') Ψ
        (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b))) :
    aCoefX (liftTF P j i₀ (nuIdeal L k (ν k) j) ρ Tm) i₀ (nuIdeal L k (ν k) j) X' x =
      v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) (blockPt j x) := by
  obtain ⟨h0, hnw, hpd⟩ := hX'
  have hjk := ctx.jk
  have hbp : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x = ibase j x := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  have hxc : ∀ μ, ZMod.valMinAbs (((x μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) = x μ :=
    fun μ => hx x (Finset.mem_singleton_self x) μ
  have hux : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j x) = x := by
    rw [hbp]; exact unlift_ibase hjk hxc
  have hal : Aligned (L ^ j) (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) := by
    rw [hbp]; exact ibase_aligned hjk x
  have hEt0 : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j (blockPt j 0) (Ypoly j X') Ψ
        (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)) := by
    intro Ψ b; rw [hEt, blockPt_zero]
  unfold aCoefX
  by_cases hxX : x ∈ X'
  · simp only [hxX, dite_true]
    have hxu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j x) ∈ X' := by
      rw [hux]; exact hxX
    have key := tensA_EauxC_eq_v1Loc ctx (i₀ := i₀) (y := 0) hnw hpd h0 hal hxu Et hEt0
    unfold tensA at key ⊢
    simp only [liftTF]
    rw [fderiv_termL_eq ctx hne hpd h0]
    have e : EauxC Tm j i₀ (nuIdeal L k (ν k) j) 0 X' =
        Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' := by
      funext c; simp [EauxC, Eaux, blockPt_zero]
    rw [e] at key
    convert key using 2
    · simp only [hux]
  · simp only [hxX, dite_false]
    have hjh := ctx.analyticAt_E i₀ (blockPt j 0) hpd
      (blockPt_mem_Ypoly hjk hnw h0)
    have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
        (cbase (L ^ j) z = blockPt j x ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z = x) :=
      fun z => by rw [cbase_eq_iff_jBlock hjk hal z, ← unlift_eq_iff, hux]
    have hνj : 0 < nuIdeal L k (ν k) j := by
      have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      have := ctx.nu_pos
      unfold nuIdeal; positivity
    have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    have hEt' : (fun ψ : Fld d L N₁ m₁ k N =>
        Et ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
        fun ψ => Tm.E j (blockPt j 0) (Ypoly j X') ψ (eFld d L N₁ m₁ k N i₀) := by
      funext ψ
      rw [hEt0, smul_smul, inv_mul_cancel₀ hνc, one_smul]
    unfold v1Loc
    rw [hEt']
    have hloc := fderiv_eq_of_line (f := fun _ : ℂ => Tm.E j (blockPt j 0) (Ypoly j X')
        (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀)) (p := (0 : ℂ))
      (g := fun ψ : Fld d L N₁ m₁ k N => Tm.E j (blockPt j 0) (Ypoly j X') ψ
        (eFld d L N₁ m₁ k N i₀)) (q := eFld d L N₁ m₁ k N i₀) (v := (0 : ℂ))
      (w := blockDirV L j (blockPt j x) (Pi.single i₀ 1)) (differentiableAt_const _)
      hjh.differentiableAt (fun s => ?_)
    · rw [← hloc]; simp
    · refine ctx.sf.localE j _ _ _ _ _ _ (fun z hz => ⟨?_, rfl⟩)
      have hne' : ¬ cbase (L ^ j) z = blockPt j x := fun h => hxX (by
        have := (hcu z).1 h
        rw [← this]; exact hz)
      simp [blockDirV, hne']

open Balaban.SmallField.Def6v2 in
/-- **T3, sum over polymers, centre `0`.**  Let `Tm` be the class on the torus `N₁`, `St` a source
form of its terms in the variable `b = ν_j h` (the shape of `D1Corr.src_pos` at the centre `0`),
and suppose every polymer of `𝒟_j` through `0` is the torus polymer of a non-winding lattice
polymer (`hsurj`, the geometric fact that no polymer of this torus winds; it is a premise of this
theorem, not a landed statement).  Then for a centred site `x` the coefficient `aCoef` of the lifted
family `liftTF` equals the whole-torus coefficient `v1T` at the block corner of `x`:
`a(x) = v₁(0, x)`. -/
theorem aCoef_liftTF_eq_v1T_of_nonwinding (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) (St : SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N)
      (b : Fin N → ℂ), St.E j 0 Y Ψ (constFld b) =
        Tm.E j 0 Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (hsurj : ∀ Y ∈ polysAt P.m₀ j (0 : Localization.CTorus d L N₁ m₁ k),
      ∃ X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
        Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Y)
    (x : SmallField.Site d) (hx : CentredAt L N₁ m₁ k j x) :
    aCoef (liftTF P j i₀ (nuIdeal L k (ν k) j) ρ Tm) i₀ (nuIdeal L k (ν k) j) x =
      v1T P.m₀ St j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) 0 (blockPt j x) := by
  classical
  set T := liftTF P j i₀ (nuIdeal L k (ν k) j) ρ Tm with hT
  set S := liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j with hS
  have hfin : S.Finite := (shN_finite (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (j := j)
    (0 : SmallField.Site d)).subset fun X' hX' => ⟨hX'.1, hX'.2.1⟩
  have hpol : T.polys = S := rfl
  unfold aCoef v1T
  have h1 : ∑' X : T.polys, aCoefX T i₀ (nuIdeal L k (ν k) j) X.1 x =
      ∑ᶠ X' ∈ S, aCoefX T i₀ (nuIdeal L k (ν k) j) X' x := by
    change ∑' X : S, aCoefX T i₀ (nuIdeal L k (ν k) j) X.1 x = _
    rw [tsum_subtype S (fun X' => aCoefX T i₀ (nuIdeal L k (ν k) j) X' x), tsum_eq_finsum,
      finsum_mem_def]
    exact (hfin.subset (fun X' hX' => by
      by_contra hn
      exact hX' (by simp [Set.indicator_of_notMem hn])))
  rw [h1]
  have hbij : Set.BijOn (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j) S
      (polysAt P.m₀ j (0 : Localization.CTorus d L N₁ m₁ k)) := by
    refine ⟨fun X' hX' => ⟨hX'.2.2, zero_mem_Ypoly hX'.1⟩, ?_, fun Y hY => ?_⟩
    · have hdir : ∀ X₁ ∈ S, ∀ X₂ ∈ S,
          Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X₁ =
            Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X₂ → X₁ ⊆ X₂ := by
        intro X₁ h₁ X₂ h₂ he z hz
        have hm : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈
            Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X₂ :=
          he ▸ blockPt_mem_Ypoly ctx.jk h₁.2.1 hz
        have hbp : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z = ibase j z := by
          funext μ; simp only [blockPt, ibase]; congr 1; ring
        change unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j z) ∈ X₂ at hm
        rwa [hbp, unlift_ibase ctx.jk (h₁.2.1 z hz)] at hm
      intro X₁ h₁ X₂ h₂ he
      exact Finset.Subset.antisymm (hdir X₁ h₁ X₂ h₂ he) (hdir X₂ h₂ X₁ h₁ he.symm)
    · obtain ⟨X', hX', rfl⟩ := hsurj Y hY
      exact ⟨X', hX', rfl⟩
  rw [finsum_mem_eq_of_bijOn _ hbij (g := fun Y => v1Loc (St.E j 0 Y) j (nuIdeal L k (ν k) j)
    (Pi.single i₀ 1) (blockPt j x))]
  intro X' hX'
  exact aCoefX_liftTF_eq_v1Loc ctx hne hX' x hx _ (fun Ψ b => hsrc _ Ψ b)

open Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 in
/-- **T3 under the clause `D1Corr`**: the same identity with the hypothesis `hsrc` supplied by the
field `src_pos` of `D1Corr P.m₀ sf St hv vc` (the landed relation between `St` and `sf.Tm`),
at the torus `N₁`. -/
theorem aCoef_liftTF_eq_v1T_of_D1Corr {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d} {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} {j : ℕ} {ρ : ℝ} {i₀ i₁ : Fin N}
    (hD : D1Corr P.m₀ sf St hv vc)
    (ctx : LiftCtx P sf.β sf.ν sf.a (sf.Tm N₁) ρd Ek j ρ) (hne : i₁ ≠ i₀)
    (hpos : 0 < nuIdeal L k (sf.ν k) j)
    (hsurj : ∀ Y ∈ polysAt P.m₀ j (0 : Localization.CTorus d L N₁ m₁ k),
      ∃ X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
        Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Y)
    (x : SmallField.Site d) (hx : CentredAt L N₁ m₁ k j x) :
    aCoef (liftTF P j i₀ (nuIdeal L k (sf.ν k) j) ρ (sf.Tm N₁)) i₀ (nuIdeal L k (sf.ν k) j) x =
      v1T P.m₀ (St N₁) j (nuIdeal L k (sf.ν k) j) (Pi.single i₀ 1) 0 (blockPt j x) := by
  refine aCoef_liftTF_eq_v1T_of_nonwinding ctx hne (St N₁) (fun Y Ψ b => ?_) hsurj x hx
  exact hD.src_pos N₁ j ctx.j1 ctx.jk hpos 0 Y Ψ b

end Sum

end Balaban.LargeField.Def7v2
