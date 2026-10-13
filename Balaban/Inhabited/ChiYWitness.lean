module

public import Balaban.Inhabited.ParentDomainWitness
public import Balaban.Inhabited.SFCtxMulti
public import Balaban.LargeField.Def7v2Inhabited
public import Balaban.Inhabited.TopBlockTransportWitness
public import Balaban.LargeField.Background.CubeUnitBg
public import Balaban.LargeField.Background.LocalGenNeg
public import Balaban.LargeField.History.BondLiftY
public import Balaban.LargeField.History.D1ParentDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A non-vacuous instance of the `Y`-branch of the Q13 domain chain at a constant field

The landed class witness has tolerance `δ_k = deltaRun 0 … = 0` and cannot satisfy `0 < δ_k` or the
largeness condition of `EarlyMassRatio`; the landed small-field context `ctxMulti` has `M₁ = 1`,
where the cube `BgHyp` (`bgR0 ≤ minSep = 5 L M₁`) is impossible.  This file removes both obstacles
and exhibits the instance (Parts 1–2: `Balaban.LargeField.Def7`; Part 3: `Balaban.Inhabited.RipeGeo`).

## Part 1: the context `ctxY` (scale `k = 1`, `d = L = 3`, `N = 2`)

* the constants `csY`: those of the class witness `wCs` with the tolerances
  `δ_j = deltaRun A₀ p₀ (5/4) (β 3^j)` for `A₀ = 2 / λ_1^{p₀} > 0` (so `p₀(β_1) = A₀ λ_1^{p₀} = 2`),
  `λ_1 = log (β_1 a) ≥ 11` (from `anaThreshold ≥ 12`), hence `δ_1 = 2 e^{-λ_1/2} > 0` and
  `(d + 1) δ_1 ≤ 1`;
* the geometry `geoY`: `M₁ = 3^{a₁}`, `a₁ = ⌈R₀(3,3)/15⌉`, `c = 27`, `M = 27 M₁`, so `R₀(3,3) ≤ 5 L M₁`
  and the cube `BgHyp` holds (`hbY`: admissible weights `a_1 = 5/4`, mass `0`);
* the torus, radii and small-field data are those of `ctxMulti`.

## Part 2: the instance (the history without large-field cubes, `Y` the whole torus)

* `chiY_ctxY`: `χ_1(Y) = 1` at the constant unit field, for every `Y` (`chiY_const_eq_one`);
* `parentDomain_chiY_instance`: `inPsiTilde_genW_of_early_chiY_local` applies with every hypothesis
  (regime, `0 < δ_1`, `(d+1) δ_1 ≤ 1`, largeness `5/2 < 4`, `χ_Y ≠ 0`, cube `BgHyp`; the activity
  hypothesis is vacuous: no retained component) and gives `InPsiTilde`;
* `parentDomain_weighted_instance`: the same conclusion through the weighted integrand of (D1):
  `inPsiTilde_of_postWeighted2_ne_zero`, the weighted integrand being nonzero
  (`postWeighted2_ctxY_ne_zero`: empty product of operator weights, `χ_1(Y) = 1`, exponentials).

What this tests: the `Y`-branch, at one scale (`k = 1`), at a constant block field, with `Y` the
whole torus.  It does not test: a retained component with `ChiDomAt`, scales `k ≥ 2`, non-constant
fields, a nonzero small-field action.

## Part 3: a datum site over a retained component

`ctxR j`: a small-field context (zero small-field data) on the torus of the genuine-radii ripe
history `H0`, at every scale `j + 1 ≤ T`, with the geometry `g0`.  `retained_datum_site`: on the
lineage localization `H0.locRH T Z0` there are a scale `j + 1`, a non-removed component `C` of
`Z^pre_{j+1}` and a datum site `t` of `𝔹_{j+1}(W₂(Y))`, `Y = Z_{j+1}ᶜ`, over a cube of `C`; the cube
`BgHyp` of the context holds.  Hence the retained branch (`hActLoc`) of the parent-domain theorems
is exercised in the typing of its hypothesis; `ChiDomAt` at the component is not shown, and
`χ_Y ≠ 0` is not shown there (the context has the constants `csY`, whose tolerance is not tied to the
radii of `H0`).
-/

@[expose] public section


namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7.Wit
  RegionHistory Balaban.SmallField.Def6v2 Balaban.SmallField

/-- The lower bound `12 ≤ anaThreshold`. -/
theorem twelve_le_anaThreshold' : 12 ≤ JointWitness.anaThreshold := by
  refine le_trans ?_ (le_max_left _ _)
  have hx : (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) := by
    have h1 : ((3 / 4 : ℝ) ^ (10 : ℕ)) ≤ (1 / 2 : ℝ) := by norm_num
    have h2 : ((3 / 4 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((3 / 4 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = 3 / 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h4 : (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) = (1 / 2 : ℝ) ^ (1 / 10 : ℝ) := by
      rw [Real.rpow_neg (by norm_num), one_div (2 : ℝ), Real.inv_rpow (by norm_num)]
      norm_num
    rw [h4]; linarith
  have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) := by
    have : (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- The witness coupling is large: `log (5 β / 4) ≥ 11`. -/
theorem wβ_log_ge : 11 ≤ Real.log (wβ * (5 / 4)) := by
  have := wβ_spec.2.2
  have := twelve_le_anaThreshold'
  linarith

/-- `λ_1 = log (β_1 a)` with `β_1 = 3 β`, `a = 5/4`. -/
theorem runLam_one_ge : 11 ≤ runLam (5 / 4) wβs 1 := by
  unfold runLam wβs
  refine wβ_log_ge.trans (Real.log_le_log (by have := wβ_pos; positivity) ?_)
  have := wβ_pos
  norm_num
  nlinarith

/-- **The running coefficients of the witness** (`β_k = β 3^k`, `ν_k = ν₀ 9^k`, `ε = 0`,
`a = 5/4`, `d = L = 3`): `RunningHyp` for `β = wβ`, `ν₀ = 1/(27 β)`. -/
theorem wRunning : RunningHyp 3 3 wβ wν₀ (5 / 4) 0 wβs (fun k => wν₀ * (3 : ℝ) ^ (2 * k) * 1) where
  hd := by norm_num
  hL := by norm_num
  hβ := wβ_pos
  hν := wν₀_pos
  ha1 := by norm_num
  ha2 := by norm_num
  hε0 := le_rfl
  hε := by norm_num
  beta_eq := fun k => ⟨1, one_pos, by simp, by simp [wβs]⟩
  nu_eq := fun k => ⟨1, one_pos, by simp, rfl⟩

/-! ### The constants with positive `A₀` -/

/-- The first running logarithm `λ_1 = log (β_1 a)`. -/
noncomputable def lam1 : ℝ := runLam (5 / 4) wβs 1

theorem lam1_pos : 0 < lam1 := lt_of_lt_of_le (by norm_num) runLam_one_ge

/-- `A₀ = 2 / λ_1^{p₀}`, so that `p₀(β_1) = A₀ λ_1^{p₀} = 2`. -/
noncomputable def A0y : ℝ := 2 / lam1 ^ wS.p0

theorem A0y_pos : 0 < A0y := by
  unfold A0y; have := lam1_pos; positivity

/-- The Def-7 constants of the witness with `A₀ = 2 / λ_1^{p₀} > 0`. -/
noncomputable def wC7y : Consts7 := { wC7 with A0 := A0y }

/-- The running constants of the operators: those of the class witness `wCs` with the tolerance
`δ_j = deltaRun A₀ p₀ (5/4) (β 3^j)` for `A₀ > 0` in place of `A₀ = 0`. -/
noncomputable def csY : OpConsts :=
  { wCs wν₀ (kZero wS.d wS.L wβ wν₀) with
    delta := deltaRun A0y wS.p0 (5 / 4) wβs
    p0 := pZero A0y wS.p0 (5 / 4) wβs }

theorem csY_delta : csY.delta = deltaRun A0y wS.p0 (5 / 4) wβs := rfl

theorem csY_delta_one : csY.delta 1 = 2 * Real.exp (-lam1 / 2) := by
  have hb : 0 < wβs 1 * (5 / 4) := by
    have := wβ_pos; simp only [wβs]; positivity
  rw [csY_delta, deltaRun_eq A0y wS.p0 (5 / 4) wβs 1 hb]
  have : A0y * runLam (5 / 4) wβs 1 ^ wS.p0 = 2 := by
    have h0 : runLam (5 / 4) wβs 1 ^ wS.p0 ≠ 0 := pow_ne_zero _ lam1_pos.ne'
    unfold A0y lam1
    field_simp
  rw [this]
  unfold lam1
  ring

theorem csY_delta_one_pos : 0 < csY.delta 1 := by
  rw [csY_delta_one]; positivity

/-- `(d + 1) δ_1 = 4 δ_1 ≤ 1`: indeed `δ_1 = 2 e^{-λ_1/2}` and `λ_1 ≥ 11`. -/
theorem csY_delta_one_le : ((wS.d : ℝ) + 1) * csY.delta 1 ≤ 1 := by
  rw [csY_delta_one]
  have hd : (wS.d : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]
  rw [hd]
  have hl : 11 ≤ lam1 := runLam_one_ge
  have h1 : 1 + lam1 / 4 ≤ Real.exp (lam1 / 4) := by
    have := Real.add_one_le_exp (lam1 / 4); linarith
  have h2 : Real.exp (lam1 / 2) = Real.exp (lam1 / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : 8 ≤ Real.exp (lam1 / 2) := by
    rw [h2]; nlinarith
  have h4 : Real.exp (-lam1 / 2) = (Real.exp (lam1 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h4]
  have hpos : 0 < Real.exp (lam1 / 2) := Real.exp_pos _
  rw [show (3 + 1 : ℝ) * (2 * (Real.exp (lam1 / 2))⁻¹) = 8 / Real.exp (lam1 / 2) by field_simp; norm_num,
    div_le_one hpos]
  exact h3

/-! ### The context -/

/-- The exponent `a₁ = ⌈R₀(3,3) / 15⌉`; the unit of the generating sets is `M₁ = 3^{a₁}`. -/
noncomputable def a1 : ℕ := ⌈bgR0 3 3 / 15⌉₊

/-- The unit `M₁ = 3^{a₁}` of the generating sets, a power of `L` with `5 L M₁ ≥ R₀(3, 3)`. -/
noncomputable def M1y : ℕ := 3 ^ a1

instance : NeZero M1y := ⟨pow_ne_zero _ (by norm_num)⟩

instance : NeZero (27 * M1y) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne _)⟩

theorem bgR0_le_minSep_y : bgR0 3 3 ≤ minSep 3 M1y := by
  refine (bgR0_le_minSep_iff (by norm_num)).2 ?_
  have h1 : bgR0 3 3 / (5 * (3 : ℕ)) ≤ (a1 : ℝ) := by
    have := Nat.le_ceil (bgR0 3 3 / 15)
    unfold a1
    norm_num
    exact this
  have h2 : (a1 : ℝ) ≤ (M1y : ℝ) := by
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3) : a1 < 3 ^ a1).le
  exact h1.trans h2

/-- The geometric typing with `M₁ = 3^{a₁}`, `c = 27`, `M = 27 M₁` (the radii conditions are
those of `wGeo`). -/
noncomputable def geoY : Geo wS (sides wS.L 1 nMulti) wR (27 * M1y) where
  M1 := M1y
  c := 27
  neM1 := inferInstance
  nec := ⟨by norm_num⟩
  hM := rfl
  hc := by norm_num
  hRlow := (wGeo (sides wS.L 1 nMulti)).hRlow
  hRmono := (wGeo (sides wS.L 1 nMulti)).hRmono

theorem M_eq_pow_y : 27 * M1y = wS.L ^ (a1 + wC7.m₁) := by
  show 27 * 3 ^ a1 = 3 ^ (a1 + 3)
  ring

/-- **The small-field context with positive tolerance**: scale `k = 1` on the torus of `ctxMulti`
(horizon `K = 1`, `2 ⌊R_0⌋ + 4` cubes per side), small-field data `wSF ν₀ 3`, cube unit
`M₁ = 3^{a₁}` (so that `BgHyp` holds at the separation `5 L M₁`), `M = 27 M₁`, `N₁ = L^{a₁} n_1`,
and running constants `csY` with `A₀ > 0`. -/
noncomputable def ctxY :
    SFCtx wS (sides wS.L 1 nMulti) wR (27 * M1y) 1 2 1 wC7.m₁ (bgR0 3 3) where
  geo := geoY
  hnn := sides_hnn wS.L 1 nMulti
  hkK := le_rfl
  cs := csY
  m₀ := a1
  sf := wSF wν₀ 3
  N₁ := sfIdx wS.L a1 (sides wS.L 1 nMulti) 1
  hT := sfIdx_hT geoY M_eq_pow_y

theorem ctxY_weights_one : ctxY.weights 1 = 5 / 4 := by
  show Def6.aIdeal 3 1 (5 / 4) 1 = 5 / 4
  unfold Def6.aIdeal
  have : (1 - (((3 : ℕ) : ℝ) ^ 1)⁻¹ ^ 2 : ℝ) ≠ 0 := by norm_num
  field_simp

theorem ctxY_mu_one : ctxY.cs.mu 1 = 0 := by
  show bgMass (kZero wS.d wS.L wβ wν₀) wS.L (wνs wν₀) 1 = 0
  unfold bgMass
  have h : kZero wS.d wS.L wβ wν₀ = 1 := kZero_wν₀
  rw [h]
  simp

/-- **The cube `BgHyp` of the context**: `d = L = 3`, `R₀(3,3) ≤ 5 L M₁`, admissible weights
(`a_1 = 5/4`), mass `0`. -/
theorem hbY : BgHyp wS.d wS.L 1 (minSep wS.L ctxY.geo.M1) ctxY.weights (ctxY.cs.mu 1) where
  hd := le_of_eq rfl
  hL := le_of_eq rfl
  hϱ := bgR0_le_minSep_y
  weights := by
    intro j hj1 hj
    obtain rfl : j = 1 := by omega
    rw [ctxY_weights_one]
    constructor <;> norm_num
  mass := by rw [ctxY_mu_one]
  massLe := by rw [ctxY_mu_one]; norm_num

/-! ### The instance of the `Y`-branch -/

theorem whv_sum_sq : ∑ i, whv i ^ 2 = 1 := by simp [whv]

/-- **`χ_1(Y) = 1` at the constant unit field in `ctxY`, for every `Y`.** -/
theorem chiY_ctxY (Y : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :
    ctxY.chiY Y (fun _ => whv) whv = 1 :=
  chiY_const_eq_one ctxY Y whv whv_sum_sq hbY le_rfl csY_delta_one_pos

theorem chiY_ctxY_ne_zero (Y : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :
    ctxY.chiY Y (fun _ => whv) whv ≠ 0 := by
  rw [chiY_ctxY]; exact one_ne_zero

/-- The largeness condition `2 a E < A₀² λ_1^{2 p₀}` (`5/2 < 4`). -/
theorem hlam_y : 2 * (5 / 4 : ℝ) * Real.exp (2 * 0) <
    A0y ^ 2 * runLam (5 / 4) wβs (0 + 1) ^ (2 * wS.p0) := by
  have h0 : lam1 ^ wS.p0 ≠ 0 := pow_ne_zero _ lam1_pos.ne'
  have : A0y ^ 2 * runLam (5 / 4) wβs (0 + 1) ^ (2 * wS.p0) = 4 := by
    unfold A0y lam1
    rw [zero_add, pow_mul', div_pow]
    unfold lam1 at h0
    field_simp
    norm_num
  rw [this]
  norm_num

/-- **A genuine instance of the `Y`-branch of the parent-domain theorem**
(`inPsiTilde_genW_of_early_chiY_local`) at the constant unit field, in the context `ctxY` with
tolerance `δ_1 = 2 e^{-λ_1/2} > 0` (`A₀ > 0`), on the region history without large-field cubes
(`Y` the whole torus, no retained component, so the activity hypothesis is vacuous): the datum of
the small-field solver lies in `Ψ̃` with the radius `max (3 d L δ_0, 4 (d+1) δ_1)`. -/
theorem parentDomain_chiY_instance :
    InPsiTilde (ctxY.genW ((emptyHist.step (0 + 1)).Z)ᶜ)
      (sfBgMassAt wS.L (0 + 1) (wν₀ * (3 : ℝ) ^ (2 * (0 + 1)) * 1))
      (max (3 * wS.d * wS.L * ctxY.cs.delta 0) (4 * (wS.d + 1) * ctxY.cs.delta (0 + 1)))
      (parentPsi ctxY (fun _ => whv)) (fun i => whv i) := by
  refine inPsiTilde_genW_of_early_chiY_local (d := 3) emptyHist ctxY (fun _ => whv) whv
    (a := 5 / 4) (ε := 0) (b := wβs) (nr := fun k => wν₀ * (3 : ℝ) ^ (2 * k) * 1)
    (A0 := A0y) (p0 := wS.p0) wRunning (by unfold KZeroGenuine; have := wν₀_mul; nlinarith)
    (by rw [show kZero 3 wS.L wβ wν₀ = 1 from kZero_wν₀]) A0y_pos.le
    (by have := lam1_pos; exact this.le) hlam_y csY_delta whv_norm csY_delta_one_pos
    csY_delta_one_le (chiY_ctxY_ne_zero _) hbY ?_
  intro C hC ⟨t, ht, hq⟩
  exfalso
  have h := comp_subset C.2 hq
  rw [mem_finOf] at h
  exact (emptyFlow_Zpre 1 ▸ h : _)

/-! ### The instance through the weighted integrand of (D1) -/

/-- The labelled history without large-field cubes on the torus of `ctxY`. -/
noncomputable def ayHist : LabHist wS (sides wS.L 1 nMulti) wR 0 1 where
  H := emptyHist
  adm := fun k c hc => absurd hc (by simp [emptyHist])
  lab := fun _ _ => 0

/-- The representation with zero kernels and zero boundary terms over `geoY`, `csY`. -/
noncomputable def repY : Rep wS (sides wS.L 1 nMulti) wR 0 1 (27 * M1y) 2 geoY csY
    (budgetConsts wβ) 1 where
  hist := {ayHist}
  κK := fun _ _ => 0
  SD := zeroStepData geoY csY le_rfl rfl _
  KD := zeroKeptData geoY csY _ _
  B := fun _ _ _ _ _ _ => 0

theorem postComp_ayHist_empty : IsEmpty (PostComp ayHist (0 + 1)) :=
  ⟨fun c => by
    obtain ⟨x, hx⟩ := comp_nonempty c.1.2
    have h := comp_subset c.1.2 hx
    rw [mem_finOf] at h
    exact (emptyFlow_Zpre 1 ▸ h : _)⟩

/-- **The weighted integrand of (D1) is nonzero** at the constant unit field, for every internal
configuration (there is none: `Z_1 = ∅`), every coefficient data `vc` and every external field
`g`: the product of the operator weights over the empty set of components is `1`, and the
integrand is `e^{ℬ} χ_1(Y) exp(…)` with `χ_1(Y) = 1`. -/
theorem postWeighted2_ctxY_ne_zero (vc : Def7v2.CorrCoef wS.d)
    (g : GIdx wS (sides wS.L 1 nMulti) (27 * M1y) 1 2 → ℂ)
    (x : GCfg (fun c : PostComp ayHist (0 + 1) => ayHist.H.localHistory (27 * M1y) 1 (0 + 1) c.1)
      (0 + 1) (postOp geoY csY repY.SD repY.KD ayHist ctxY.hkK)) :
    postWeighted2 ctxY vc repY ayHist (fun _ => whv) whv g x ≠ 0 := by
  have := postComp_ayHist_empty
  unfold postWeighted2 gWeight Def7v2.integrand2 Def7v2.sfFactor2
  rw [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero ?_ (Complex.exp_ne_zero _))
  exact_mod_cast chiY_ctxY_ne_zero _

/-- **The same instance through the weighted integrand**: `inPsiTilde_of_postWeighted2_ne_zero`
applied to the representation `repY` and the history without large-field cubes. -/
theorem parentDomain_weighted_instance (vc : Def7v2.CorrCoef wS.d)
    (g : GIdx wS (sides wS.L 1 nMulti) (27 * M1y) 1 2 → ℂ)
    (x : GCfg (fun c : PostComp ayHist (0 + 1) => ayHist.H.localHistory (27 * M1y) 1 (0 + 1) c.1)
      (0 + 1) (postOp geoY csY repY.SD repY.KD ayHist ctxY.hkK)) :
    InPsiTilde (ctxY.genW ((ayHist.H.step (0 + 1)).Z)ᶜ)
      (sfBgMassAt wS.L (0 + 1) (wν₀ * (3 : ℝ) ^ (2 * (0 + 1)) * 1))
      (max (3 * wS.d * wS.L * ctxY.cs.delta 0) (4 * (wS.d + 1) * ctxY.cs.delta (0 + 1)))
      (parentPsi ctxY (fun _ => whv)) (fun i => whv i) :=
  inPsiTilde_of_postWeighted2_ne_zero (d := 3) (a := 5 / 4) (ε := 0) (b := wβs)
    (nr := fun k => wν₀ * (3 : ℝ) ^ (2 * k) * 1) (A0 := A0y) (p0 := wS.p0)
    ctxY repY ayHist (fun _ => whv) whv g vc rfl rfl wRunning
    (by unfold KZeroGenuine; have := wν₀_mul; nlinarith)
    (by rw [show kZero 3 wS.L wβ wν₀ = 1 from kZero_wν₀]) A0y_pos.le
    lam1_pos.le hlam_y csY_delta whv_norm csY_delta_one_pos csY_delta_one_le hbY x
    (postWeighted2_ctxY_ne_zero vc g x)

end Balaban.LargeField.Def7


namespace Balaban.Inhabited.RipeGeo

open Balaban Balaban.LargeField Balaban.Inhabited Balaban.Multiscale Balaban.Background
  Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit Balaban.SmallField Balaban.SmallField.Def6

/-- The zero small-field data of the witness (`wSF`) at an arbitrary scale `k` and arbitrary
`m₁`. -/
noncomputable def wSFk (k m₁ : ℕ) (ν : ℝ) : SFData 3 3 m₁ k 2 (bgR0 3 3) where
  β := wβs
  ν := wνs ν
  z := fun _ => 1
  a := witnessa
  E := fun _ => 0
  Tm := zeroFam 3 3 m₁ k 2 (bgR0 3 3)
  Rt := fun _ _ _ _ _ _ _ => 0
  corr := fun _ _ _ _ _ _ _ => 0

/-- The running constants of the retained-component context: those of `csY`, with the background
mass `0` up to the a priori index `k₀ = T` (the horizon). -/
noncomputable def csR : OpConsts :=
  { csY with mu := Balaban.LargeField.bgMass T S0.L (wνs wν₀) }

instance : NeZero (S0.M * n0 T) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩

/-- **A small-field context on the genuine-radii torus** of the ripe history `H0`: scale
`k = j + 1 ≤ T`, `M = S0.M = 14 M₁`, `c = 14`, `m₁ = 0`, `N₁ = M n_k`, the geometric typing `g0`,
the zero small-field data. -/
noncomputable def ctxR (j : ℕ) (hj : j + 1 ≤ T) :
    SFCtx S0 n0 RadiiSet.wR S0.M T 2 (j + 1) 0 (bgR0 3 3) where
  geo := g0
  hnn := H0.F.hnn
  hkK := hj
  cs := csR
  m₀ := 0
  sf := wSFk (j + 1) 0 wν₀
  N₁ := S0.M * n0 (j + 1)
  nz := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  hT := by
    have h := g0.hM
    rw [pow_zero, mul_one]
    calc S0.M * n0 (j + 1) * S0.L ^ (j + 1)
        = g0.c * g0.M1 * n0 (j + 1) * S0.L ^ (j + 1) := by rw [← h]
      _ = g0.M1 * (g0.c * n0 (j + 1)) * S0.L ^ (j + 1) := by ring

theorem inv_sq_pow_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 < (((3 : ℝ) ^ k)⁻¹) ^ 2 ∧ (((3 : ℝ) ^ k)⁻¹) ^ 2 ≤ 1 / 9 := by
  have h3 : (3 : ℝ) ≤ 3 ^ k := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hk
  refine ⟨by positivity, ?_⟩
  have h1 : ((3 : ℝ) ^ k)⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) h3
  have h2 : 0 ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
  calc (((3 : ℝ) ^ k)⁻¹) ^ 2 ≤ (3⁻¹ : ℝ) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = 1 / 9 := by norm_num

/-- The ideal weights `a_n = (5/4)(1 - L^{-2k})/(1 - L^{-2n})` lie in `[1/2, 2]` for
`1 ≤ n ≤ k`, `L = 3`. -/
theorem aIdeal_three_mem {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    aIdeal 3 k (5 / 4) n ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨hx0, hx1⟩ := inv_sq_pow_bounds hk
  obtain ⟨hy0, hy1⟩ := inv_sq_pow_bounds hn
  unfold aIdeal
  push_cast
  have hden : 0 < 1 - (((3 : ℝ) ^ n)⁻¹) ^ 2 := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

/-- **The cube `BgHyp` of the retained-component context**: `d = L = 3`, `R₀(3,3) ≤ 5 L M₁`,
admissible weights, mass `0` (the a priori index is `k₀ = T ≥ j + 1`). -/
theorem bgHyp_ctxR (j : ℕ) (hj : j + 1 ≤ T) :
    BgHyp S0.d S0.L (j + 1) (minSep S0.L (ctxR j hj).geo.M1) (ctxR j hj).weights
      ((ctxR j hj).cs.mu (j + 1)) where
  hd := le_of_eq rfl
  hL := le_of_eq rfl
  hϱ := by
    have := RadiiSet.bgR0_le_minSep
    show bgR0 3 3 ≤ 5 * ((3 : ℕ) : ℝ) * (RadiiSet.M1 : ℝ)
    push_cast at this ⊢
    linarith
  weights := fun n hn1 hn =>
    aIdeal_three_mem (Nat.succ_pos j) hn1
  mass := by
    show 0 ≤ Balaban.LargeField.bgMass T S0.L (wνs wν₀) (j + 1)
    unfold Balaban.LargeField.bgMass
    simp only [hj, ↓reduceIte]
    exact le_rfl
  massLe := by
    show Balaban.LargeField.bgMass T S0.L (wνs wν₀) (j + 1) * _ ≤ 1
    unfold Balaban.LargeField.bgMass
    simp only [hj, ↓reduceIte]
    norm_num

/-- **A datum site over a retained component, in a small-field context.**  On the lineage
localization of the genuine-radii ripe history, at a scale `j + 1 ≤ T` there are a non-removed
component `C` of `Z^pre_{j+1}` and a datum site `t` of the small-field generating set
`G_{j+1} = 𝔹_{j+1}(W₂(Y))`, `Y = Z_{j+1}ᶜ`, whose cube `parentSiteCube t` lies in `C`; the cube `BgHyp` of the context holds. -/
theorem retained_datum_site :
    ∃ j, ∃ hj : j + 1 ≤ T,
      BgHyp S0.d S0.L (j + 1) (minSep S0.L (ctxR j hj).geo.M1) (ctxR j hj).weights
        ((ctxR j hj).cs.mu (j + 1)) ∧
      ∃ C : (H0.locRH T Z0).Comp (j + 1), C.1 ∉ (H0.locRH T Z0).rem (j + 1) ∧
      ∃ t ∈ dataSites ((ctxR j hj).genW (((H0.locRH T Z0).step (j + 1)).Z)ᶜ),
        parentSiteCube (ctxR j hj) t ∈ C.1 := by
  obtain ⟨j, hjT, C, hC, q, hq, ⟨y, hy, hd⟩, -⟩ := topBlockTransport_witness
  refine ⟨j, hjT, bgHyp_ctxR j hjT, C, hC, ?_⟩
  set Cx := ctxR j hjT with hCx
  have hN : 0 < S0.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1) := by
    have := NeZero.ne S0.L
    have := NeZero.ne Cx.geo.c
    have := NeZero.ne Cx.geo.M1
    positivity
  obtain ⟨s, hs⟩ := Balaban.exists_blockMap_eq
    (show Cx.geo.M1 * (Cx.geo.c * n0 (j + 1)) * S0.L ^ (j + 1) =
      S0.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1) * n0 (j + 1) by ring) hN q
  have hq2 : q ∈ nbhd 2 {y} := mem_nbhd.mpr ⟨y, rfl, hd.trans (by norm_num)⟩
  have hW : q ∈ W2 RadiiSet.wR (((H0.locRH T Z0).step (j + 1)).Z)ᶜ :=
    nbhd_two_subset_W2 _ hy hq2
  have hs1 : s ∈ (Cx.genW (((H0.locRH T Z0).step (j + 1)).Z)ᶜ).Ω (j + 1) :=
    (genW_mem_top_iff Cx _).2 (hs ▸ hW)
  refine ⟨s, (mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j) hs1)), ?_⟩
  have : parentSiteCube Cx s = q := (cubeMap_bgToFine Cx s).trans hs
  rw [this]
  exact hq

end Balaban.Inhabited.RipeGeo
