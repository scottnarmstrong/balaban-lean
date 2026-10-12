/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RadiiWitness
public import Balaban.LargeField.R.HgeoDischarge
public import Balaban.LargeField.Operators.QuietLocalInput

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The genuine-radii witness: geometry, radii and operator constants

On the history `H0` of `RadiiWitness` (radii `R_j = R_base λ_j²`, one ripe component at `k₀ = T`):

* `radiiGeo : Geo` (`M = 14 M₁`, `c = 14`, `R_j ≥ R_base`, `⌊R_{j-1}⌋ ≤ ⌊R_j⌋`);
* `radii_hR`, `radii_radiusHyp`, `radii_stepRadii`, `radii_stepGeom`: `RadiusHyp` and `StepRadii`
  for the history's own radii;
* `radii_margin`, `radii_hgeo_five`, `radii_hgeo_two`: the margin `ZzeroDD_nbhd_margin` and the
  geometric premises of the small factors (Lemma III.5.0), applied to `H0` with the operative-radii
  premise `hR` discharged;
* `radiiCs : OpConsts` with `BgHyp` at the generating-set separation `minSep L M₁` for every scale
  (`radiiCs_bgHyp`) and all the scalar premises of `quiet_locOp_pkgBound'`
  (`radiiCs_scalar`).
-/

@[expose] public section

namespace Balaban.Inhabited
namespace RadiiWit

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness Balaban.Background RadiiHist
  RegionHistory

instance : NeZero RadiiSet.wS.M := ⟨by
  show 14 * RadiiSet.M1 ≠ 0
  have := RadiiSet.M1_pos; omega⟩

/-- The geometric typing on the tori of the witness history. -/
noncomputable abbrev radiiGeo : Geo S0 (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf)
    RadiiSet.wR S0.M :=
  RadiiSet.wGeo _

theorem radiiGeo_c : radiiGeo.c = 14 := rfl

theorem radii_hR (j : ℕ) : RadiiSet.wR j = S0.Rb * S0.lam j ^ 2 := RadiiSet.wR_eq j

theorem radii_radiusHyp : RadiusHyp S0.L S0.Rb S0.lam RadiiSet.wR := RadiiSet.wRH

/-- `StepRadii` for the radii of the history, at every step. -/
theorem radii_stepRadii (k : ℕ) :
    StepRadii S0.L (omegaW S0.L S0.Rb S0.lam (k + 1)) (radiusUnit S0.Rb S0.lam k)
      (RadiiSet.wR (k - 1)) (RadiiSet.wR k) := by
  refine RadiiSet.wRH.stepRadii (by show 2 ≤ 3; norm_num) k rfl ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using RadiiSet.wRH.le 0
  · exact RadiiSet.wRH.prev_le hk

/-- The step geometry of the history, with its own radii. -/
theorem radii_stepGeom {k : ℕ} (hk : k < F0.kf) :
    StepGeom S0.L (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf k)
      (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf (k + 1)) (S0.omega k) (S0.omega (k + 1))
      (S0.r k) (RadiiSet.wR (k - 1)) (RadiiSet.wR k) :=
  H0.stepGeom hk

/-- The margin `(Z''₀)^{∼3} ⊆ Ω^c_{k₃+1} ⊆ Z` (Lemma III.5.0 (b)) on the witness history. -/
theorem radii_margin {k : ℕ} (hkK : k ≤ F0.kf) (hk : 1 ≤ k) (Z : H0.Comp k)
    {x : Torus S0.d (S0.M * RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf k * S0.L ^ k)}
    (hx : cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M k k x ∈
      nbhd 3 (H0.ZzeroDD k Z)) :
    cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M k (S0.kThree k + 1) x ∉
        ((H0.locRH k Z).step (S0.kThree k)).Omega ∧
      cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M k (S0.kThree k + 1) x ∈
        ((H0.locRH k Z).step (S0.kThree k + 1)).Z ∧
      cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M k k x ∈ Z.1 :=
  H0.ZzeroDD_nbhd_margin radii_hR hkK hk Z hx

/-- Lemma III.5.0 (b), item 5 (`hgeo` of `smallFactor_five_ripe`), on the witness history. -/
theorem radii_hgeo_five {k : ℕ} (hkK : k ≤ F0.kf) (hk : 1 ≤ k) (Z : H0.Comp k) :
    ∀ y0 ∈ cubeFin (S := S0) (chiZDDCubes (H0.localHistory S0.M F0.kf k Z) k
        (fineSet (S := S0) (n := RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.M F0.kf k
          (H0.ZzeroDD k Z))),
      ∀ x : Torus S0.d (S0.M * RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf F0.kf * S0.L ^ F0.kf),
        cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M F0.kf k x ∈ nbhd 3 {y0} →
          cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M F0.kf k x ∈ Z.1 :=
  H0.hgeo_five_fine radii_hR hkK hk Z

/-- Lemma III.5.0 (a), item 2 (`hgeo` of `smallFactor_two_ripe`), on the witness history. -/
theorem radii_hgeo_two {k : ℕ} (hkK : k ≤ F0.kf) (hk : 1 ≤ k) (Z : H0.Comp k) :
    ∀ y0 ∈ cubeFin (S := S0) (chiSCubes (H0.localHistory S0.M F0.kf k Z) k
        (fineSet (S := S0) (n := RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.M F0.kf k
          (H0.ZzeroDD k Z))),
      ∀ x : Torus S0.d (S0.M * RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf F0.kf * S0.L ^ F0.kf),
        cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M F0.kf k x ∈ nbhd 3 {y0} →
          cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M F0.kf k x ∈ Z.1 ∧
            x ∉ H0.fineZzero k Z :=
  H0.hgeo_two_fine hkK hk Z


/-- The unique ripe component at scale `T` satisfies the margin of Lemma III.5.0 (b): a ripe
component, `1 ≤ T ≤ k₀`, together with the margin for it (the premise `hR` discharged). -/
theorem radii_ripe_margin :
    ∃ (k : ℕ) (c : H0.Comp k), 1 ≤ k ∧ k ≤ F0.k0 ∧ S0.Ripe k (H0.bk k c) ∧
      ∀ x : Torus S0.d (S0.M * RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf k * S0.L ^ k),
        cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M k k x ∈
          nbhd 3 (H0.ZzeroDD k c) →
        cubeMap (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) S0.L S0.M k k x ∈ c.1 := by
  obtain ⟨k, c, h1, h2, -, h3⟩ := radiiWitness_ripe
  refine ⟨k, c, h1, h2, h3, fun x hx => ?_⟩
  have h4 : k ≤ F0.kf := (show k ≤ F0.k0 from h2).trans (F0_k0.le.trans T_le_kf)
  exact (radii_margin h4 h1 c hx).2.2

/-! ### Operator constants -/

/-- `δ`: small enough for the shell-volume premises at `N = 2`. -/
noncomputable def deltaR : ℝ := 1 / (54 * (1 + cShell 2))

theorem cShell_nonneg (N : ℕ) : 0 ≤ cShell N := by
  unfold cShell
  positivity

theorem deltaR_pos : 0 < deltaR := by
  have := cShell_nonneg 2
  unfold deltaR; positivity

theorem deltaR_mul : 54 * (1 + cShell 2) * deltaR = 1 := by
  have h : 0 < 54 * (1 + cShell 2) := by have := cShell_nonneg 2; positivity
  unfold deltaR
  exact mul_one_div_cancel h.ne'

/-- Concrete running constants: weights `a_n = 1`, background mass `μ = 0`, `β_k = β 3^k`,
`ν_k = ν 9^k`, `z_k = 1`, `δ_k = δ`, `C_b = B_0 = 0`. -/
noncomputable def radiiCs : OpConsts where
  aw := fun _ => 1
  mu := fun _ => 0
  muAct := fun _ => 0
  nu := fun j => RadiiRipe.nuT β0 * 9 ^ j
  delta := fun _ => deltaR
  p0 := fun _ => 0
  Cpsi := 1
  beta := fun k => β0 * 3 ^ k
  z := fun _ => 1
  aKer := 1
  Cb := 0
  B0 := 0

/-- **`BgHyp` at `L = 3`** at the generating-set separation `minSep L M₁` of the geometry, for
every scale and the constants `radiiCs`. -/
theorem radiiCs_bgHyp (q : ℕ) :
    BgHyp S0.d S0.L q (minSep S0.L radiiGeo.M1) radiiCs.aw (radiiCs.mu q) where
  hd := le_rfl
  hL := le_rfl
  hϱ := by
    have h := RadiiSet.bgR0_le_minSep
    show bgR0 3 3 ≤ 5 * ((3 : ℕ) : ℝ) * (RadiiSet.M1 : ℝ)
    push_cast at h ⊢
    linarith
  weights := fun j _ _ => ⟨by show (1 / 2 : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ 2; norm_num⟩
  mass := le_rfl
  massLe := by simp [radiiCs]

theorem radiiCs_log (k : ℕ) : 0 ≤ Real.log (radiiCs.beta k) := by
  apply Real.log_nonneg
  have h1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have h2 := hβ0
  show 1 ≤ β0 * 3 ^ k
  nlinarith

theorem radiiCs_beta_pos (k : ℕ) : 0 < radiiCs.beta k := by
  have := hβ0
  show 0 < β0 * 3 ^ k
  positivity

/-- **All scalar premises of `quiet_locOp_pkgBound'`** (`N = 2`, `c₁ = c₂ = 0`) hold for
`radiiCs` on the geometry `radiiGeo`. -/
theorem radiiCs_scalar :
    (∀ k, 0 ≤ radiiCs.z (k + 1)) ∧
    (∀ k, 0 ≤ radiiCs.beta k * radiiCs.aKer * (S0.L : ℝ) ^ (S0.d - 2)) ∧
    (∀ k, 0 ≤ radiiCs.beta (k + 1)) ∧ (∀ n, 0 ≤ radiiCs.aw n) ∧
    (∀ k, 0 ≤ radiiCs.muAct (k + 1)) ∧
    (∀ q, BgHyp S0.d S0.L q (minSep S0.L radiiGeo.M1) radiiCs.aw (radiiCs.mu q)) ∧
    2 ≤ 2 ∧ radiiCs.Cb ≤ 0 ∧ radiiCs.Cb * radiiCs.B0 ≤ 0 ∧
    (∀ k, 0 ≤ Real.log (radiiCs.beta k)) ∧
    (∀ k, 0 < radiiCs.beta k * radiiCs.aKer * (S0.L : ℝ) ^ (S0.d - 2)) ∧
    (∀ k, 0 < radiiCs.delta k) ∧
    (∀ k, 3 * S0.d * S0.L * radiiCs.delta k ≤ 1 / 2) ∧
    (∀ k, 3 * S0.d * S0.L * cShell 2 * radiiCs.delta k ≤ 1 / 2) ∧
    0 ≤ radiiCs.Cb ∧ 0 ≤ radiiCs.B0 ∧ (∀ k, 0 < radiiCs.z (k + 1)) := by
  have hd : ∀ k, 0 < radiiCs.delta k := fun _ => deltaR_pos
  have hc := cShell_nonneg 2
  have hm := deltaR_mul
  have hdp := deltaR_pos
  refine ⟨fun k => by simp [radiiCs], fun k => ?_, fun k => (radiiCs_beta_pos _).le,
    fun n => by simp [radiiCs], fun k => by simp [radiiCs], radiiCs_bgHyp, le_rfl, le_rfl,
    by simp [radiiCs], radiiCs_log, fun k => ?_, hd, fun k => ?_, fun k => ?_, le_rfl, le_rfl,
    fun k => by simp [radiiCs]⟩
  · have := radiiCs_beta_pos k
    have hL : (0 : ℝ) < (S0.L : ℝ) := by show (0 : ℝ) < ((3 : ℕ) : ℝ); norm_num
    have h : (0 : ℝ) < (S0.L : ℝ) ^ (S0.d - 2) := pow_pos hL _
    show 0 ≤ radiiCs.beta k * 1 * _
    positivity
  · have := radiiCs_beta_pos k
    have hL : (0 : ℝ) < (S0.L : ℝ) := by show (0 : ℝ) < ((3 : ℕ) : ℝ); norm_num
    have h : (0 : ℝ) < (S0.L : ℝ) ^ (S0.d - 2) := pow_pos hL _
    show 0 < radiiCs.beta k * 1 * _
    positivity
  · show 3 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) * deltaR ≤ 1 / 2
    push_cast
    nlinarith
  · show 3 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) * cShell 2 * deltaR ≤ 1 / 2
    push_cast
    nlinarith


theorem nonempty_radiiWitness : Nonempty FlowCounterWitness := ⟨radiiWitness⟩

/-- **All constraints at the one parameter choice** `d = L = 3`, `M = 14 M₁`, radii
`R_j = R_base λ_j²` (so `R_j ≥ R_base > 0`, not `0`): `Setting.Good`, `Geo`, `RadiusHyp`,
`StepRadii` at every step, `k₀ ≥ 1`, a ripe component at a scale `1 ≤ k ≤ k₀` of the witness
history, `BgHyp` at the separation `minSep L M₁` for `radiiCs`. -/
theorem radii_constraints :
    radiiWitness.R = RadiiSet.wR ∧ (∀ j, S0.Rb ≤ RadiiSet.wR j) ∧ 0 < S0.Rb ∧
    radiiWitness.S.L = 3 ∧ radiiWitness.S.d = 3 ∧ Nonempty radiiWitness.S.Good ∧
    Nonempty (Geo S0 radiiWitness.n radiiWitness.R S0.M) ∧
    RadiusHyp S0.L S0.Rb S0.lam radiiWitness.R ∧
    (∀ k, ∃ ω r : ℕ, StepRadii S0.L ω r (radiiWitness.R (k - 1)) (radiiWitness.R k)) ∧
    1 ≤ radiiWitness.F.k0 ∧ radiiWitness.F.k0 < radiiWitness.F.kf ∧
    (∃ (k : ℕ) (c : radiiWitness.H.Comp k), 1 ≤ k ∧ k ≤ radiiWitness.F.k0 ∧
      radiiWitness.S.Ripe k (radiiWitness.H.bk k c)) ∧
    (∀ q, BgHyp S0.d S0.L q (minSep S0.L radiiGeo.M1) radiiCs.aw (radiiCs.mu q)) := by
  refine ⟨rfl, radiiGeo.hRlow, by show (0 : ℝ) < 32; norm_num, rfl, rfl, ⟨radiiWitness.G⟩,
    ⟨radiiGeo⟩, radii_radiusHyp, fun k => ⟨_, _, radii_stepRadii k⟩, radiiWitness_k0_pos.1,
    radiiWitness_k0_pos.2, ?_, radiiCs_bgHyp⟩
  obtain ⟨k, c, h1, h2, -, h3⟩ := radiiWitness_ripe
  exact ⟨k, c, h1, h2, h3⟩

end RadiiWit
end Balaban.Inhabited
