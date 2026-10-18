/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.D1ParentDomain
public import Balaban.LargeField.History.LateYDirection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The late parent domain from the extended direction stencil (`LateParentR3`)

Ruling R2 (route R-YM′, `notes/phase1/Q13-YM.md` §5 leaves 4 and 6; `notes/phase1/Q13-LATE.md`
package 4).  The direction test of the small-field cubes reaches `□^{∼ρ_k}`,
`ρ_k = 2⌊R_{k-1}⌋ + 3` (`chiKLong`, `SFCtx.chiY`, `dirRadius`).  Every data site of the
background of the step, `G = 𝔹_k(W₂(Y))`, `Y = Z_kᶜ`, lies within `ρ_k` cubes of a cube of `Y`
(`dataSite_cube_mem_nbhd`), so its datum is tested.  Above `k₀` (cube mass `ν_k L^{-2k}`):

* `parentPsi_dir_of_chiY_ne_zero` (the bound (RD) of `Q13-LATE.md` at all data sites, with
  constant `1`): `χ_Y ≠ 0` gives `‖Ψ(s) - h‖ < δ_k / √ν_k` at every data site `s` of `G`;
* `r3_of_dir_sphere`: the direction bound and the sphere bound give the clause `r3` of the real
  domain;
* `inPsiTilde_genW_of_factors_local_r3`: the assembly of the real domain with a direction bound at
  every data site in place of the early mass bound `hmass`;
* `inPsiTilde_genW_of_late_chiY_local` (**`LateParentR3`**): the parent domain at the scales above
  `k₀`, from `χ_Y ≠ 0`, the cube `BgHyp`, the local activity factor and the identification of the
  cube mass with the physical mass;
* `inPsiTilde_of_postTerm2_ne_zero_late`, `postTerm2_eq_zero_or_inPsiTilde_late`: the same under
  the integral of (D1) (second version), the late counterpart of `inPsiTilde_of_postTerm2_ne_zero`.

Together with the early theorems of `D1ParentDomain` this covers every scale.  The radius is that
of P5 (1.4) (`W₂(Y) = Y^{≈2}`); no hypothesis states a domain or a direction bound.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2

section Dir

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **(RD) at every data site** (ruling R2, the extended direction stencil).  If `χ_Y ≠ 0` and
the cube mass is `ν L^{-2k}` with `ν > 0`, then `‖Ψ(s) - h‖ < δ_k / √ν` at every data site `s`
of `G = 𝔹_k(W₂(Y))`. -/
theorem parentPsi_dir_of_chiY_ne_zero (hL : 2 ≤ S.L) (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {ν : ℝ} (hν : 0 < ν)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW Y)) :
    rn (fun i => parentPsi Cx ψk s i - hv i) < Cx.cs.delta (j + 1) / Real.sqrt ν := by
  have hcube := dataSite_cube_mem_nbhd Cx hL Y hs
  rw [cubeMap_bgToFine] at hcube
  obtain ⟨y₀, hy₀, hd⟩ := mem_nbhd.mp hcube
  have hy₀' : y₀ ∈ cubeFin Y := by simp [cubeFin, hy₀]
  have hD := dataDirClose_of_chiY_ne_zero Cx Y ψk hv h hy₀'
  have hmass : Cx.cs.mu (j + 1) * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν := by
    rw [hμ]; exact physMass_mul_sq _ _
  rw [hmass] at hD
  have hx : s ∈ cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1))
      (dirRadius R (j + 1)) y₀ :=
    mem_cubePre.2 (mem_nbhd.mpr ⟨y₀, rfl, hd⟩)
  have key := (hD hν).1 s hx
  have e : (fun i => (((blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s) i : ℝ) : ℂ) -
        ((hv i : ℝ) : ℂ)) = fun i => ((parentPsi Cx ψk s i - hv i : ℝ) : ℂ) := by
    funext i
    push_cast
    rfl
  rw [e, vn_ofReal] at key
  exact key

/-- **The clause `r3` from a direction bound and a sphere bound.**  For a unit `h`, a datum `a`
with `|a · a - 1| ≤ 1/2`, a fine mass `m` and a level `ℓ ≤ k`:
`m L^{2ℓ} |1 - a · h / ‖a‖| ≤ 2 m L^{2k} ‖a - h‖²`. -/
theorem r3_of_dir_sphere {L ℓ k : ℕ} (hLpos : 1 ≤ L) (hℓ : ℓ ≤ k) (a h : Fin N → ℝ)
    (hh : ∑ i, h i ^ 2 = 1) (hsph : |∑ i, a i ^ 2 - 1| ≤ 1 / 2) {m : ℝ} (hm : 0 ≤ m) :
    m * ((L : ℝ) ^ ℓ) ^ 2 * |1 - (∑ i, a i * h i) / rn a| ≤
      2 * (m * ((L : ℝ) ^ k) ^ 2) * rn (fun i => a i - h i) ^ 2 := by
  have hr : 1 / 4 ≤ rn a := by
    have h1 : rn a ^ 2 = ∑ i, a i ^ 2 := rn_sq a
    have h2 : 1 / 2 ≤ ∑ i, a i ^ 2 := by linarith [(abs_le.1 hsph).1]
    have h0 : 0 ≤ rn a := Real.sqrt_nonneg _
    nlinarith
  have hx := one_sub_dot_le a h hh hr
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hℓk : ((L : ℝ) ^ ℓ) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hℓ) 2
  have hX0 : 0 ≤ |1 - (∑ i, a i * h i) / rn a| := abs_nonneg _
  calc m * ((L : ℝ) ^ ℓ) ^ 2 * |1 - (∑ i, a i * h i) / rn a|
      ≤ m * ((L : ℝ) ^ k) ^ 2 * |1 - (∑ i, a i * h i) / rn a| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓk hm) hX0
    _ ≤ m * ((L : ℝ) ^ k) ^ 2 * (2 * rn (fun i => a i - h i) ^ 2) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by ring

end Dir

section Assembly

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
  (ν ηY : ℝ)

/-- **The domain statement with a direction bound at every data site.**  As
`inPsiTilde_genW_of_factors_local`, with the early mass bound `hmass` replaced by the direction
bound `hdir` at every data site (the clause `r3` then follows from the sphere bound, which is
derived from the other hypotheses, and `η ≤ 1/2`). -/
theorem inPsiTilde_genW_of_factors_local_r3 (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1) (hηY : 0 < ηY)
    (hη : max (3 * S.d * S.L * Cx.cs.delta j) ηY ≤ 1 / 2)
    (hdir : ∀ s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ),
      2 * (ν * ((S.L : ℝ) ^ (j + 1)) ^ 2) * rn (fun i => parentPsi Cx ψk s i - hv i) ^ 2 <
        (max (3 * S.d * S.L * Cx.cs.delta j) ηY) ^ 2)
    (hActLoc : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x)
    (hR2Y : ∀ s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ),
      parentSiteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ → |∑ i, parentPsi Cx ψk s i ^ 2 - 1| < ηY)
    (hR1Y : ∀ s s', IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s' →
      parentSiteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ → parentSiteCube Cx s' ∈ ((H.step (j + 1)).Z)ᶜ →
      rn (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) < ηY) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) ν (max (3 * S.d * S.L * Cx.cs.delta j) ηY)
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hηC : 3 * S.d * S.L * Cx.cs.delta j ≤ max (3 * S.d * S.L * Cx.cs.delta j) ηY :=
    le_max_left _ _
  have hηYle : ηY ≤ max (3 * S.d * S.L * Cx.cs.delta j) ηY := le_max_right _ _
  have hη0 : 0 < max (3 * S.d * S.L * Cx.cs.delta j) ηY := lt_of_lt_of_le hηY hηYle
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  have hR2 : ∀ x ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ),
      |∑ i, parentPsi Cx ψk x i ^ 2 - 1| < max (3 * S.d * S.L * Cx.cs.delta j) ηY := by
    intro x hx
    rcases siteCube_dichotomy H Cx x with hY | ⟨C, hC, hq⟩
    · exact (hR2Y x hx hY).trans_le hηYle
    · obtain ⟨A, xs, hχ⟩ := hActLoc C hC ⟨x, hx, hq⟩
      exact (parentPsi_sphere_of_chiDomAt_local H Cx hC ψk hχ hx hq).trans_le hηC
  refine ⟨parentPsi_layerConst Cx _ ψk, ?_, hR2, ?_, ?_⟩
  · intro x x' hp
    rcases interface_pair_cases H Cx x x' with ⟨t, hts, C, hC, hq⟩ | ⟨h1, h2⟩
    · obtain ⟨A, xs, hχ⟩ := hActLoc C hC
        ⟨t, by rcases hts with rfl | rfl; exacts [hp.1, hp.2.1], hq⟩
      exact (parentPsi_pair_of_chiDomAt_local H Cx hC ψk hχ hp hts hq).trans_le hηC
    · exact (hR1Y x x' hp h1 h2).trans_le hηYle
  · intro x hx
    have hsph : |∑ i, parentPsi Cx ψk x i ^ 2 - 1| ≤ 1 / 2 := ((hR2 x hx).trans_le hη).le
    have hL1 : 1 ≤ S.L := Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
    exact (r3_of_dir_sphere hL1 (layerIndex_le_k _ x) (parentPsi Cx ψk x) (fun i => hv i)
      hsum hsph hν).trans_lt (hdir x hx)
  · simp only [hsum, sub_self, abs_zero, mul_zero]
    positivity

/-- **`LateParentR3`: the parent domain above `k₀`** (ruling R2).  At a scale `k = j + 1` whose
cube mass is the physical mass (`hμ : μ_k = ν L^{-2k}`, `ν > 0`; above `k₀` this is
`Def7.FieldClauses.mu_eq` with `Coh.nu_cs`), from `χ_Y ≠ 0` (with the extended direction stencil),
the cube `BgHyp` and the local activity factor, the datum lies in the real domain of the
complete background with `η = max (3 d L δ_j) (4 (d + 1) δ_k) ≤ 1/2`.  No mass smallness
`2 ν L^{2k} < η²` is assumed. -/
theorem inPsiTilde_genW_of_late_chiY_local (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν)
    (hunit : ‖hv‖ = 1) (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hη : max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)) ≤ 1 / 2)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hχ : Cx.chiY ((H.step (j + 1)).Z)ᶜ ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hActLoc : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) ν)
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  have hm0 : 0 ≤ sfBgMassAt S.L (j + 1) ν := by
    unfold sfBgMassAt physMass; positivity
  have hε : 0 ≤ (S.d + 1) * Cx.cs.delta (j + 1) := by positivity
  have hsm : (S.d + 1) * Cx.cs.delta (j + 1) * (2 + (S.d + 1) * Cx.cs.delta (j + 1)) ≤
      4 * (S.d + 1) * Cx.cs.delta (j + 1) := by
    have := mul_le_mul_of_nonneg_left (show 2 + (S.d + 1) * Cx.cs.delta (j + 1) ≤ 4 by linarith) hε
    linarith
  refine inPsiTilde_genW_of_factors_local_r3 H Cx ψk hv _ (4 * (S.d + 1) * Cx.cs.delta (j + 1))
    hm0 hunit (by positivity) hη ?_ hActLoc ?_ ?_
  · intro s hs
    have hdir := parentPsi_dir_of_chiY_ne_zero Cx hL _ ψk hv hχ hν hμ hs
    have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
    have hmL : sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν := physMass_mul_sq _ _
    rw [hmL]
    have h1 : rn (fun i => parentPsi Cx ψk s i - hv i) * Real.sqrt ν < Cx.cs.delta (j + 1) :=
      (lt_div_iff₀ hsq).1 hdir
    have h0 : 0 ≤ rn (fun i => parentPsi Cx ψk s i - hv i) * Real.sqrt ν :=
      mul_nonneg (Real.sqrt_nonneg _) hsq.le
    have h2 : (rn (fun i => parentPsi Cx ψk s i - hv i) * Real.sqrt ν) ^ 2 <
        Cx.cs.delta (j + 1) ^ 2 := pow_lt_pow_left₀ h1 h0 two_ne_zero
    rw [mul_pow, Real.sq_sqrt hν.le] at h2
    have h4 : 4 * Cx.cs.delta (j + 1) ≤
        max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)) :=
      le_trans (by nlinarith) (le_max_right _ _)
    have h5 : (4 * Cx.cs.delta (j + 1)) ^ 2 ≤
        (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h4 2
    nlinarith
  · intro s _ hY
    exact (parentPsi_sphere_over_Y Cx _ ψk hv hχ HB hY).trans_le hsm
  · intro s s' hp hY _
    refine (parentPsi_pair_over_Y Cx _ ψk hv hχ hp (Or.inl hY)).trans_le ?_
    nlinarith

end Assembly

section D1

open Balaban.LargeField.Def7v2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) (rep : Rep S n R k0 K M N geo cs P (j + 1))
  (A : LabHist S n R k0 K)
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
  (g : GIdx S n M K N → ℂ) (vc : CorrCoef S.d)

/-- **The late parent domain under the integral of (D1)** (second version; ruling R2): if the
second-version post term of the history `A` is nonzero at `ψ_k`, then above `k₀` (cube mass
`ν L^{-2k}`, `ν > 0`) the datum lies in the real domain.  The late counterpart of
`inPsiTilde_of_postTerm2_ne_zero`. -/
theorem inPsiTilde_of_postTerm2_ne_zero_late (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hη : max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)) ≤ 1 / 2)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hT : postTerm2 Cx vc rep A ψk hv g ≠ 0) :
    InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) ν)
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  obtain ⟨x, hx⟩ := exists_postWeighted2_ne_zero_of_postTerm2_ne_zero Cx vc rep A ψk hv g hT
  exact inPsiTilde_genW_of_late_chiY_local A.H Cx ψk hv hL hν hunit hδ hδ1 hη hμ
    (chiY_ne_zero_of_postWeighted2_ne_zero Cx vc rep A ψk hv g x hx) HB
    (hActLoc_of_forall Cx rep A hgeo hcs ψk x
      (chiDomAt_of_postWeighted2_ne_zero Cx vc rep A ψk hv g x hx))

/-- **The late dichotomy** (second version): at every `ψ_k` the post term vanishes or the datum
lies in the real domain. -/
theorem postTerm2_eq_zero_or_inPsiTilde_late (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hη : max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)) ≤ 1 / 2)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1))) :
    postTerm2 Cx vc rep A ψk hv g = 0 ∨
      InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) ν)
        (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
        (parentPsi Cx ψk) (fun i => hv i) := by
  by_cases h : postTerm2 Cx vc rep A ψk hv g = 0
  · exact Or.inl h
  · exact Or.inr (inPsiTilde_of_postTerm2_ne_zero_late Cx rep A ψk hv g vc hgeo hcs hL hν hunit
      hδ hδ1 hη hμ HB h)

end D1

end Balaban.LargeField
