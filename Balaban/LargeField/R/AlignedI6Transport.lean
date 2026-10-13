/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalAlignedSource
public import Balaban.LargeField.R.RadialCoefficientLimit
public import Balaban.LargeField.R.RadialCoefficientAvg
public import Balaban.SmallField.Def6BridgeInfDict
public import Balaban.SmallField.Def6AvgDens
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Transport of the scale-`j` decomposition to the aligned fine sites

Convention (Q13-ALIGN): a scale-`j` site is an `L^j`-aligned site of the fine torus, counted once,
with no factor `L^{-jd}` (P5 (1.8), P1 (3.104)).

## What is proved

* The dictionary (T1).  `blockPt j` sends the scale-`j` lattice `ℤ^d` to the aligned fine sites,
  `unlift j` is its inverse (`blockPt_unlift`), and
  `unlift j (blockPt j z - blockPt j z') = z - z'` exactly when the difference does not wind
  (`nonWind_singleton_iff`: `-n < 2 w_μ ≤ n` for every coordinate, `n = N₁ L^{m₁} L^{k-j}` the
  number of scale-`j` sites per side).  A scale-`j` polymer `X'` (a finite set of `ℤ^d`) has the fine
  thickening `Ypoly j X'`; its aligned sites are the points `blockPt j z`, `z ∈ X'`
  (`aligned_mem_Ypoly_iff`).  The size of the fine polymer is `sizeJ (Ypoly j X')`; the class bound
  on the coefficients of the scale-`j` family is stated with this very size, so the size dictionary
  has constant `1` (`sizeJ_Ypoly_le_dInf` compares it with the size `dInf` of `T∞`).
* The per-site coefficient bound and the locality of the torus coefficient (T3):
  `v1Loc_polymer` (one torus, from `tensA_EauxC_eq_v1Loc` and `norm_tensA_EauxC_le`) and
  `v1Loc_polyUniv` (at the physical axis `hC hv`).  Every polymer of `𝒟_j` through a site is the
  fine thickening of a non-winding scale-`j` polymer (`polysAt_eq_image`), so the winding of
  polymers needs no hypothesis in the bounds.
* The decomposition of the whole-torus coefficient into polymer contributions (T2):
  `v1T_eq_sum_polyUniv`.
* The assembly (T5): `groupedInputsSite_of_class` (an inhabitant of `GroupedInputsSite`, hence by
  `GroupedInputsSite.toAligned` of `GroupedInputsAligned`) and the corollary
  `EresJ2_sub_remainder_le_aligned_of_class_site` of `EresJ2_sub_remainder_le_aligned_of_class`.
  `translation covariance`: `v1T_translate_hC`.
* Non-vacuity.  No new structure is introduced.  The conclusion bundle is inhabited
  (`groupedInputsSite_nonempty`).  At the zero class (`RadialCoefficientLimitInhab.lean`) every
  coefficient, `v1Loc` and `v1T` is zero, so `hstab`, `hv2dec`, `hv2site` hold with `cv = 0`; a
  full instance of the constructor would need an `SFCtx` whose `sf` is that witness, which is not
  landed (the landed contexts use `wSF`, a different zero effective action).

## What is not proved (named hypotheses of the constructor)

* `hstab`: the whole-torus coefficient `v1T` of the torus `C.N₁` at the origin equals the
  thermodynamic limit `vc.v1 j ∘ unlift j` on aligned differences.  This is the periodic
  identification: `D1Corr.v1_lim` gives it only as a limit along `torusSeq`; on a finite torus
  the polymers winding around it contribute a defect, exponentially small in the side, which is
  not an identity.
* `v2_decomp`, `v2_site`: the `v₂` counterpart (the mixed second derivative `v2Loc`); no landed
  theorem bounds `v2Loc` or shows its locality, and there is no `v₂` analogue of
  `aCoef_avgFamilyA_eq_v1`.
* `hXi`: the composed field lies in the class domain on each polymer (the data of the class
  bound `boundE`); with it the field `E_bound` is derived.

The data bounds of `GroupedBase`, the count of centres, the regional energy identity and the common
complex tube are not treated.
-/

@[expose] public section

open Finset Real Balaban.LargeField.RegionEnergyAlgebra Balaban.LargeField.RegionalFlux

namespace Balaban.LargeField.AlignedI6Transport

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField.Def7v2 Balaban.LargeField.RegionalAligned

/-! ### The dictionary (T1) -/

section Dictionary

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
theorem blockPt_eq_ibase (j : ℕ) (z : SmallField.Site d) :
    blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z = ibase j z := by
  funext μ; simp only [blockPt, ibase]; congr 1; ring

/-- `unlift j` is the inverse of `blockPt j` on the aligned sites: every aligned site is the block
corner of its centred position. -/
theorem blockPt_unlift {j : ℕ} (hjk : j ≤ k) {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u) :
    blockPt j (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) = u := by
  rw [blockPt_eq_ibase]; exact ibase_unlift hjk hu

/-- The non-winding condition for one lattice point, exactly: `w` is its own centred
representative modulo `n = N₁ L^{m₁} L^{k-j}` (the number of scale-`j` sites per side) iff
`-n < 2 w_μ ≤ n` for every coordinate. -/
theorem nonWind_singleton_iff (j : ℕ) (w : SmallField.Site d) :
    NonWind L N₁ m₁ k j ({w} : Finset (SmallField.Site d)) ↔
      ∀ μ, (-(N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) < 2 * w μ ∧
        2 * w μ ≤ ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  unfold NonWind
  simp only [Finset.mem_singleton, forall_eq]
  refine forall_congr' fun μ => ?_
  rw [ZMod.valMinAbs_spec]
  constructor
  · rintro h
    have := h.2
    simp only [Set.mem_Ioc] at this
    constructor <;> linarith [this.1, this.2]
  · intro h
    refine ⟨rfl, ?_⟩
    simp only [Set.mem_Ioc]
    constructor <;> linarith [h.1, h.2]

/-- **Differences of block corners.**  For differences that do not wind,
`unlift j (blockPt j z - blockPt j z') = z - z'`. -/
theorem unlift_blockPt_sub {j : ℕ} (hjk : j ≤ k) {z z' : SmallField.Site d}
    (h : NonWind L N₁ m₁ k j ({z - z'} : Finset (SmallField.Site d))) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j z - blockPt j z') = z - z' := by
  rw [← blockPt_sub, blockPt_eq_ibase]
  exact unlift_ibase hjk (h (z - z') (Finset.mem_singleton_self _))

omit [NeZero L] [NeZero N₁] in
/-- The fine thickening `Ypoly j X'` of a scale-`j` polymer `X'` is the set of fine sites whose
block lies in `X'`. -/
theorem mem_Ypoly_iff (j : ℕ) (X' : Finset (SmallField.Site d)) (x : Localization.CTorus d L N₁ m₁ k) :
    x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ↔
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X' := Iff.rfl

/-- **The aligned sites of the fine polymer.**  For a polymer `X'` of the scale-`j` lattice that does
not wind, an aligned fine site lies in `Ypoly j X'` iff it is the block corner `blockPt j z` of a
point `z ∈ X'`. -/
theorem aligned_mem_Ypoly_iff {j : ℕ} (hjk : j ≤ k) {X' : Finset (SmallField.Site d)}
    (hnw : NonWind L N₁ m₁ k j X') {x : Localization.CTorus d L N₁ m₁ k} (hx : Aligned (L ^ j) x) :
    x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ↔ ∃ z ∈ X', x = blockPt j z := by
  constructor
  · intro h
    exact ⟨_, h, (blockPt_unlift hjk hx).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact blockPt_mem_Ypoly hjk hnw hz

/-- Differences of aligned sites that do not wind: `unlift (x - y) = unlift x - unlift y`. -/
theorem unlift_sub_aligned {j : ℕ} (hjk : j ≤ k) {x y : Localization.CTorus d L N₁ m₁ k}
    (hx : Aligned (L ^ j) x) (hy : Aligned (L ^ j) y)
    (h : NonWind L N₁ m₁ k j
      ({unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x -
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y} : Finset (SmallField.Site d))) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) =
      unlift j x - unlift j y := by
  have := unlift_blockPt_sub (N₁ := N₁) (m₁ := m₁) (k := k) hjk h
  rwa [blockPt_unlift hjk hx, blockPt_unlift hjk hy] at this

/-- **The size dictionary.**  On the `n`-th torus of the sequence, the size `sizeJ` of the fine
polymer of a good scale-`j` polymer `X'` is at most the size `dInf` of `X'` as a polymer of `T∞`
(constant `1`); the size used by the coefficient bounds of the class is `sizeJ` of the fine polymer
itself, so no constant enters the passage to the fine representatives. -/
theorem sizeJ_Ypoly_le_dInf {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (SmallField.Site d)} {n : ℕ}
    (hn : GoodAt L m₁ k m₀ j X' n) :
    haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
    sizeJ (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X') ≤
      dInf L m₁ k m₀ j X' :=
  sizeSeq_le_dInf hjk hn

end Dictionary

/-! ### The torus coefficient of one polymer: bound and locality (T3) -/

section Polymer

open Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **The radial coefficient of one torus polymer, at an aligned site.**  Let `X ∈ 𝒟_j` contain the
aligned centre `y`, and let `Et` be a source form of the class term `Tm.E j y X` (the shape of
`D1Corr.src_pos`).  For an aligned site `x`:
* if `x ∈ X`, the local coefficient `v1Loc Et` at the axis `e_{i₀}` is bounded by the Cauchy bound of
  the class, `E₀ e^{-κ sizeJ X} / ρ` (`ρ` the radius of the lifting context; it is the bound
  `tensA_le` of the scale-`j` family, transported through `tensA_EauxC_eq_v1Loc`);
* if `x ∉ X`, it vanishes (locality of the term). -/
theorem v1Loc_polymer (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {m₀ : ℕ} (hm₀ : m₀ = P.m₀) (hN : L ^ m₀ ∣ N₁)
    {y : Localization.CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    {X : Set (Localization.CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) (hyX : y ∈ X)
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j y X Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    {x : Localization.CTorus d L N₁ m₁ k} (hx : Aligned (L ^ j) x) :
    (x ∈ X → ‖v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) x‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ m₀ j X) / ρ) ∧
    (x ∉ X → v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) x = 0) := by
  subst hm₀
  have hjk := ctx.jk
  have hmem : X ∈ polysAt P.m₀ j y := ⟨hX, hyX⟩
  rw [polysAt_eq_image hjk hN y] at hmem
  obtain ⟨X', ⟨hyX', hnw, hpd⟩, rfl⟩ := hmem
  have hy0 : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) = y := blockPt_unlift hjk hy
  refine ⟨fun hxX => ?_, fun hxX => ?_⟩
  · have huX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X' := hxX
    have hEt' : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
        Et Ψ (constFld b) = Tm.E j (blockPt j (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y))
          (Ypoly j X') Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)) := by
      intro Ψ b; rw [hy0]; exact hEt Ψ b
    have key := tensA_EauxC_eq_v1Loc ctx (i₀ := i₀) hnw hpd hyX' hx huX Et hEt'
    rw [← key]
    exact norm_tensA_EauxC_le ctx i₀ hnw hpd hyX' ⟨_, huX⟩
  · exact v1Loc_eq_zero_of_not_mem ctx hpd hyX hx hxX Et hEt

end Polymer

/-! ### The whole-torus coefficient as a sum over the polymers of `polyUniv` (T2, T3) -/

section Class

open Balaban.SmallField.Def6v2 Balaban.LargeField.RegionShrink Balaban.LargeField.Def7
  Balaban.LargeField.RegionalGroupedBound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  {vc : CorrCoef S.d} {hv : EuclideanSpace ℝ (Fin N)}

/-- **The torus coefficient of one polymer at the physical axis** (T3, per site).  For the class
family `hF`, a `D1Corr` datum, an aligned centre `y`, a polymer `X ∈ 𝒟_j` through `y` and an aligned
site `x`: `v1Loc ((St C.N₁).E j y X)` at the direction `hC hv` of the physical field is bounded by
`E₀ e^{-κ sizeJ X} / ρ_j` if `x ∈ X` (the per-site form `tensA_le`), and vanishes if `x ∉ X`. -/
theorem v1Loc_polyUniv {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ : Fin N} (hhv : ‖hv‖ = 1)
    (hN : S.L ^ C.m₀ ∣ C.N₁)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : Aligned (S.L ^ j) y)
    {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hX : IsPolyDom C.m₀ j X) (hyX : y ∈ X)
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : Aligned (S.L ^ j) x) :
    (x ∈ X → ‖v1Loc ((St C.N₁).E j y X) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) x‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ C.m₀ j X) / liftRadius S.d S.L N P j) ∧
    (x ∉ X → v1Loc ((St C.N₁).E j y X) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) x = 0) := by
  have hpos := nuIdeal_pos' (L := S.L) hF.coeff.nu_pos j
  have hε := eps_pos (d := S.d) (L := S.L) (P := P) hF.admissible.α₀_pos j
  have ctx := hF.liftCtx C.N₁ hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk
    (liftRadius_pos (d := S.d) (L := S.L) (N := N) hε i₀)
    (liftRadius_spec (d := S.d) (L := S.L) (N := N) hε i₀ hn.hsmall)
  have hsrc : ∀ (Ψ : Fld S.d S.L C.N₁ m₁ k N) (b : Fin N → ℂ),
      (St C.N₁).E j y X Ψ (constFld b) =
        (C.sf.Tm C.N₁).E j y X Ψ (constFld (((nuIdeal S.L k (C.sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun Ψ b => hD.src_pos C.N₁ j hn.hj1 hn.hjk hpos y X Ψ b
  obtain ⟨Q, hQ, hw⟩ := exists_rot_axis i₀ hv hhv
  have hX' : IsPolyDom P.m₀ j X := hP ▸ hX
  have hax := v1Loc_axis_eq ctx hQ hX' hyX hpos ((St C.N₁).E j y X) hsrc hw x
  have hbd := v1Loc_polymer ctx i₀ hP.symm hN hy hX hyX ((St C.N₁).E j y X) hsrc hx
  rw [hax]
  exact hbd

open Classical in
/-- **The whole-torus coefficient is the sum of the polymer contributions** (T2).  For aligned `y`
and `x`, `v₁^{(j)}(y, x)` of the torus `C.N₁` (`v1T`, the sum over the polymers through `y` of the
whole torus) is the sum over the polymers `X ∈ 𝒟_j` through `y` and `x` of the local coefficients
`v1Loc`; the polymers not containing `x` do not contribute. -/
theorem v1T_eq_sum_polyUniv {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ : Fin N} (hhv : ‖hv‖ = 1)
    (hN : S.L ^ C.m₀ ∣ C.N₁)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : Aligned (S.L ^ j) y)
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : Aligned (S.L ^ j) x) :
    v1T C.m₀ (St C.N₁) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) y x =
      ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X),
        v1Loc ((St C.N₁).E j y X) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) x := by
  have hset : polysAt (d := S.d) (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) C.m₀ j y =
      ((polyUniv C j).filter (fun X => y ∈ X) : Set _) := by
    ext X
    simp only [polysAt, Set.mem_ofPred_eq, Finset.coe_filter, RegionalTails.mem_polyUniv]
  unfold v1T
  rw [hset, finsum_mem_coe_finset, ← Finset.filter_filter]
  refine (Finset.sum_filter_of_ne fun X hX hne => ?_).symm
  have hX' := Finset.mem_filter.1 hX
  by_contra hxX
  exact hne ((v1Loc_polyUniv C hP hD hF hn (i₀ := i₀) hhv hN hy ((RegionalTails.mem_polyUniv C).1 hX'.1) hX'.2 hx).2 hxX)

/-- **Translation covariance of the torus coefficient at the physical axis.**  For an aligned centre
`y`, `v₁^{(j)}(y, x) = v₁^{(j)}(0, x - y)` on the torus `C.N₁` (from `eucEloc`, the covariance of the
sum over the polymers through the centre, and the independence of the axis). -/
theorem v1T_translate_hC {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ : Fin N} (hhv : ‖hv‖ = 1)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : Aligned (S.L ^ j) y)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    v1T C.m₀ (St C.N₁) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) y x =
      v1T C.m₀ (St C.N₁) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) 0 (x - y) := by
  have hpos := nuIdeal_pos' (L := S.L) hF.coeff.nu_pos j
  have hε := eps_pos (d := S.d) (L := S.L) (P := P) hF.admissible.α₀_pos j
  have ctx := hF.liftCtx C.N₁ hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk
    (liftRadius_pos (d := S.d) (L := S.L) (N := N) hε i₀)
    (liftRadius_spec (d := S.d) (L := S.L) (N := N) hε i₀ hn.hsmall)
  have hsrc : ∀ (y : Localization.CTorus S.d S.L C.N₁ m₁ k)
      (Y : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (Ψ : Fld S.d S.L C.N₁ m₁ k N)
      (b : Fin N → ℂ), (St C.N₁).E j y Y Ψ (constFld b) =
        (C.sf.Tm C.N₁).E j y Y Ψ (constFld (((nuIdeal S.L k (C.sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun y Y Ψ b => hD.src_pos C.N₁ j hn.hj1 hn.hjk hpos y Y Ψ b
  obtain ⟨Q, hQ, hw⟩ := exists_rot_axis i₀ hv hhv
  have h1 := v1T_axis_eq ctx hQ (St C.N₁) hpos hsrc hw y x
  have h2 := v1T_axis_eq ctx hQ (St C.N₁) hpos hsrc hw 0 (x - y)
  have h3 := v1T_translate ctx i₀ (St C.N₁) hpos hsrc hy x
  rw [hP] at h1 h2 h3
  rw [h1, h2, h3]

open Classical in
/-- **`AlignedI6Transport`: the inputs of the aligned grouped bound from the class.**  For the
class family `hF` with a `D1Corr` datum, the bundle `GroupedInputsSite` for the aligned kernel
`alignedKernel (aCoef (avgFamilyA …) ∘ unlift j)`, the polymer coefficients
`c X y x = v1Loc ((St C.N₁).E j y X) … (hC hv) x` (the local coefficient of the term of the polymer
`X` at the aligned site `x`) and the activity `polyTerm`, is obtained from `GroupedBase` and the
following hypotheses, none of which is a step of the proof:
* `hstab` (the periodic identification): on the torus `C.N₁` the whole-torus coefficient at the
  origin is the thermodynamic limit `vc.v1 j ∘ unlift j` on aligned differences;
* `hv2dec`, `hv2site` (the `v₂` fields, with the coefficients `cv`; the `v₂` counterpart of the
  radial-coefficient theorem is not landed);
* `hXi` (the composed field lies in the class domain on every polymer through a centre), which gives
  `E_bound` from the class clause `boundE`;
* the constants: `P.E₀ ≤ E₀`, `κ ≤ P.κ`, `ε_j / K_r ≤` the radius of the lifting context.

Derived from the class: `a_supp` (by construction), `a_decomp` (`aCoef_avgFamilyA_eq_v1`,
`hstab`, translation covariance and `v1T_eq_sum_polyUniv`), `a_site` (`v1Loc_polyUniv`), `E_bound`. -/
theorem groupedInputsSite_of_class {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (hN : S.L ^ C.m₀ ∣ C.N₁) {R' Bc : Finset (SiteT C)} {ψ : Fld S.d S.L C.N₁ m₁ k N}
    (hR : ∀ y ∈ R', Aligned (S.L ^ j) y)
    (hstab : ∀ w : Localization.CTorus S.d S.L C.N₁ m₁ k, Aligned (S.L ^ j) w →
      v1T C.m₀ (St C.N₁) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) 0 w = vc.v1 j (unlift j w))
    {cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv2dec : ∀ y ∈ R', ∀ x, Aligned (S.L ^ j) x → vc.v2 j (unlift j (x - y)) =
      ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), cv X y x)
    (hv2site : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X → ∀ x ∈ X, Aligned (S.L ^ j) x →
      ‖cv X y x‖ ≤ (4 * E₀ / (εj / K_r) ^ 2) * Real.exp (-κ * Def6.sizeJ C.m₀ j X))
    (hXi : ∀ y ∈ R', ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      XiDom ((C.sf.Tm C.N₁).gs j X) (aIdeal S.L k (C.sf.a k))
        (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)) j (P.eps S.d S.L j) ψ (constFld (hC hv)))
    (hE : P.E₀ ≤ E₀) (hκ : κ ≤ P.κ) (hr : εj / K_r ≤ liftRadius S.d S.L N P j) (hη : 0 < η)
    (g : GroupedBase C j R' Bc ψ (hC hv) (nuIdeal S.L k (C.sf.ν k) j) E₀ (κ - η) κ₀ Rs dd α₃ α₁ α C₀
      K_r K_R B εj εq) :
    GroupedInputsSite C j R' Bc ψ (hC hv) (nuIdeal S.L k (C.sf.ν k) j)
      (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
        (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
        (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)))
      (fun y x => vc.v2 j (unlift j (x - y)))
      (fun X y x => v1Loc ((St C.N₁).E j y X) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) x) cv
      (polyTerm C hv j ψ) E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq := by
  have : NeZero (S.L ^ j) := neZero_pow_L
  have hjk := hn.hjk
  have hdvd := pow_dvd_side C hjk
  have hD' : D1Corr P.m₀ C.sf St hv vc := hP ▸ hD
  have hE0 : 0 ≤ P.E₀ := hF.admissible.E₀_nonneg
  have hrpos : 0 < εj / K_r := div_pos g.εj_pos g.K_r_pos
  have hrad : 0 < liftRadius S.d S.L N P j := lt_of_lt_of_le hrpos hr
  have hsz : ∀ X : Set (SiteT C), Def6.IsPolyDom C.m₀ j X → 0 ≤ Def6.sizeJ C.m₀ j X :=
    fun X hX => (polyUniv_weights C hN hjk).1 X ((RegionalTails.mem_polyUniv C).2 hX)
  -- comparison of the class bound with the bound of the bundle
  have hcmp : ∀ X : Set (SiteT C), Def6.IsPolyDom C.m₀ j X →
      P.E₀ * Real.exp (-P.κ * Def6.sizeJ C.m₀ j X) / liftRadius S.d S.L N P j ≤
        E₀ / (εj / K_r) * Real.exp (-κ * Def6.sizeJ C.m₀ j X) := by
    intro X hX
    have hs := hsz X hX
    have h1 : Real.exp (-P.κ * Def6.sizeJ C.m₀ j X) ≤ Real.exp (-κ * Def6.sizeJ C.m₀ j X) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hE0' : 0 ≤ E₀ := hE0.trans hE
    calc P.E₀ * Real.exp (-P.κ * Def6.sizeJ C.m₀ j X) / liftRadius S.d S.L N P j
        = (P.E₀ / liftRadius S.d S.L N P j) * Real.exp (-P.κ * Def6.sizeJ C.m₀ j X) := by ring
      _ ≤ (E₀ / (εj / K_r)) * Real.exp (-κ * Def6.sizeJ C.m₀ j X) := by
          refine mul_le_mul ?_ h1 (Real.exp_pos _).le (by positivity)
          calc P.E₀ / liftRadius S.d S.L N P j ≤ P.E₀ / (εj / K_r) :=
                div_le_div_of_nonneg_left hE0 hrpos hr
            _ ≤ E₀ / (εj / K_r) := div_le_div_of_nonneg_right hE hrpos.le
  refine
  { toGroupedBase := g
    η_pos := hη
    a_supp := fun z hz => alignedKernel_of_not C _ hz
    a_decomp := ?_
    a_site := ?_
    v2_decomp := hv2dec
    v2_site := hv2site
    E_bound := ?_ }
  · intro y hy x hx
    have hyal := hR y hy
    have hal : Aligned (S.L ^ j) (x - y) := aligned_sub hdvd hx hyal
    rw [alignedKernel_of_aligned C _ hal,
      aCoef_avgFamilyA_eq_v1 hD' hF hn hne hhv (unlift j (x - y)), ← hstab _ hal,
      ← v1T_translate_hC C hP hD hF hn (i₀ := i₀) hhv hyal x]
    exact v1T_eq_sum_polyUniv C hP hD hF hn (i₀ := i₀) hhv hN hyal hx
  · intro y hy X hX hyX x hxX hx
    exact ((v1Loc_polyUniv C hP hD hF hn (i₀ := i₀) hhv hN (hR y hy) hX hyX hx).1 hxX).trans
      (hcmp X hX)
  · intro y hy X hX hyX
    have hb := (hF.torus C.N₁).boundE j hn.hj1 hjk y X (hP ▸ hX) hyX ψ (constFld (hC hv))
      (hXi y hy X hX hyX)
    rw [hP] at hb
    refine hb.trans ?_
    have hs := hsz X hX
    have h1 : Real.exp (-P.κ * Def6.sizeJ C.m₀ j X) ≤ Real.exp (-κ * Def6.sizeJ C.m₀ j X) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul hE h1 (Real.exp_pos _).le (hE0.trans hE)

open Classical in
/-- **The deliverable `EresJ2_sub_remainder_le_aligned_of_class` with the derived fields removed
from its hypotheses.**  The activity coefficients `c` of the kernel (`a_decomp`, `a_site`) and the
bound of the activity (`E_bound`) are derived from the class; what is left are `hstab` (the periodic
identification), the `v₂` fields (`hv2dec`, `hv2site`), the domain membership `hXi` of the composed
field, the constants, and the data fields of `GroupedBase`.  The rate is `κ - η` and the constant
`Γ_η E₀`, `Γ_η = rowFactor`. -/
theorem EresJ2_sub_remainder_le_aligned_of_class_site {P : Consts}
    {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) →
      (Fin N → ℝ) → (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (hN : S.L ^ C.m₀ ∣ C.N₁) (Y : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hstab : ∀ w : Localization.CTorus S.d S.L C.N₁ m₁ k, Aligned (S.L ^ j) w →
      v1T C.m₀ (St C.N₁) j (nuIdeal S.L k (C.sf.ν k) j) (hC hv) 0 w = vc.v1 j (unlift j w))
    {cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E₀ κ η κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (hv2dec : ∀ y ∈ C.alignedIn j Y, ∀ x, Aligned (S.L ^ j) x → vc.v2 j (unlift j (x - y)) =
      ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), cv X y x)
    (hv2site : ∀ y ∈ C.alignedIn j Y, ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      ∀ x ∈ X, Aligned (S.L ^ j) x →
      ‖cv X y x‖ ≤ (4 * E₀ / (εj / K_r) ^ 2) * Real.exp (-κ * Def6.sizeJ C.m₀ j X))
    (hXi : ∀ y ∈ C.alignedIn j Y, ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      XiDom ((C.sf.Tm C.N₁).gs j X) (aIdeal S.L k (C.sf.a k))
        (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)) j (P.eps S.d S.L j) (C.psiJ Y ψk hv j)
        (constFld (hC hv)))
    (hE : P.E₀ ≤ E₀) (hκ : κ ≤ P.κ) (hr : εj / K_r ≤ liftRadius S.d S.L N P j) (hη : 0 < η)
    (g : GroupedBase C j (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.psiJ Y ψk hv j) (hC hv)
      (nuIdeal S.L k (C.sf.ν k) j) E₀ (κ - η) κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresJ2 C vc Y ψk hv j -
        ∑ y ∈ C.alignedIn j Y, (Efull (polyUniv C j) (polyTerm C hv j (C.psiJ Y ψk hv j)) y -
          AtermCentre (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a
            C.sf.Tm j i₀ (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
            (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)))
            (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) y)‖ ≤
      (C.alignedIn j Y).card * ((RegionalGroupedBound.farConst C (κ - η) κ₀ Rs dd α₃ C₀ K_r K_R +
        RegionalGroupedBound.v2Const (S := S) (κ - η) κ₀ B C₀ K_r K_R +
        RegionalGroupedBound.tailConst C (κ - η) κ₀ Rs dd α₃) *
          (rowFactor S C.m₀ m₁ η * E₀) * scaleJ S.L k j ^ (dd + α₃)) := by
  have hjk := hn.hjk
  have gs := groupedInputsSite_of_class C hP hD hF hn hne hhv hN
    (R' := C.alignedIn j Y) (Bc := C.alignedIn j (thickY R Y)) (ψ := C.psiJ Y ψk hv j)
    (fun y hy => aligned_of_mem_alignedIn hy) hstab hv2dec hv2site hXi hE hκ hr hη g
  exact RegionalAlignedSource.EresJ2_sub_remainder_le_aligned_of_class C vc hv hP hD hF hn hne hhv hN Y ψk
    (gs.toAligned hN hjk)

end Class

end Balaban.LargeField.AlignedI6Transport
