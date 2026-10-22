/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepActComp
public import Balaban.Fluctuation.HoleStep
public import Balaban.Fluctuation.DecBgAgreeCore

/-!
# Locality of the composed field of the step on a region at one unit point (reading HS-1)

Under the reading HS-1 of `notes/phase1/PLAN-B.md` the composed field of P5 (2.39) at a unit point
`b` of `Ω_{k+1}` is built from the decoupled background, multiplier and covariance root of the one
pair `(coverOf G′, G′)` at the localization vector of `b`.  For two vectors `v`, `v'` whose factors
agree on the active closure (`actComp`) of a common larger vector, the decoupled objects agree on the
block hull `T` of the closure (the cross lemmas of `Fluctuation/LocalPairDecBg.lean` and
`Localization/DecCovCross.lean` for the pair compared with itself), hence so does the composed field
at `b` when the block of `b` lies in `T`.

* `base_mem_intBox`: the base of a cube lies in its interaction box;
* `subI_or_disjI_actHull`, `mem_actHull_of_nbhd`: the dichotomy and row hypotheses of the cross lemmas
  for the hull `T` and its `L^{k+1}`-neighbourhood `Y`;
* `decBg_agree_of_hull`: **the decoupled backgrounds and multipliers at `v` and `v'` agree** (on `Y`,
  resp. `T`), for data in the domain of Theorem I-4b;
* `unitRep_mem_top`: the representative of a unit point lies in the top layer;
* `shiftLoc_eq_of_hull`: **the fluctuation part `β_k^{-1/2} (C^{1/2}_loc ψ̂)(b)` of the composed field
  agrees** at a unit point whose block lies in `T`, for hat variables agreeing on the unit blocks of
  `T` (`Dec2.localLift_eq_localLift_on_component` for the pair compared with itself), under the
  standing conditions of the covariance at the two vectors (`AdmPot`, `IsUnit` of `1 - 𝒦_x` and of
  `M_x`);
* `composeField_congr`, `psiLoc_eq_of_hull`, `composed_eq_of_hull`: the background part, and **the
  composed field of P5 (2.39) agrees at the unit point**.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

section Geometry

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The base of a cube lies in its interaction box. -/
theorem base_mem_intBox (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : q.2 ∈ intBox q := by
  rw [mem_intBox]
  intro μ
  refine ⟨0, ?_⟩
  have hL : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have h0 : (0 : ℝ) ≤ ((L : ℝ) ^ (q.1 + m₁) - 1) / 2 := by linarith
  rw [abs_lt]
  constructor <;> push_cast <;> nlinarith

variable {C : DecCover d L N₁ m₁ (k + 1)} {ϱ : ℝ} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The dichotomy hypothesis of the cross lemmas for the hull. -/
theorem subI_or_disjI_actHull {D : ℕ} (hD : 2 * L ^ (k + 1) ≤ D)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q) :
    SubI H (intBox q) (actHull C D s seed) ∨ DisjI H (intBox q) (actHull C D s seed) := by
  have hD0 : 0 + 2 * L ^ (k + 1) ≤ D := by omega
  rcases actC_dich hD0 (seed := seed) hq with h | h
  · exact Or.inl fun x hx => h x hx
  · refine Or.inr fun x hx hxT => ?_
    have := h x hx x hxT
    rw [supDist_self] at this
    exact lt_irrefl 0 this

/-- The row hypothesis of the cross lemmas: a site of an active interaction box within `L^{k+1}` of
the hull lies in the hull. -/
theorem mem_actHull_of_nbhd {D : ℕ} (hD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q) {x y : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox q) (hy : y ∈ actHull C D s seed) (hxy : supDist y x ≤ L ^ (k + 1)) :
    x ∈ actHull C D s seed := by
  rcases actC_dich (r := L ^ (k + 1)) hD (seed := seed) hq with h | h
  · exact h x hx
  · have := h x hx y hy
    rw [supDist_comm] at hxy
    omega

end Geometry

/-! ### The decoupled backgrounds at two vectors -/

section Background

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- The `L^{k+1}`-neighbourhood of a set of sites (the set `Y` of the cross lemmas). -/
noncomputable def nbhdSup (r : ℕ) (T : Finset (CTorus d L N₁ m₁ K)) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => ∃ y ∈ T, supDist y x ≤ r

theorem mem_nbhdSup {r : ℕ} {T : Finset (CTorus d L N₁ m₁ K)} {x : CTorus d L N₁ m₁ K} :
    x ∈ nbhdSup r T ↔ ∃ y ∈ T, supDist y x ≤ r := by
  classical
  simp [nbhdSup]

theorem subset_nbhdSup (r : ℕ) (T : Finset (CTorus d L N₁ m₁ K)) : T ⊆ nbhdSup r T := fun x hx =>
  mem_nbhdSup.2 ⟨x, hx, by rw [supDist_self]; exact Nat.zero_le _⟩

end Background

section Inner

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **An inner active centre of the hull lies in the closure of a larger vector**: if `T` is the
hull of the closure of `t` and `t`'s active centres are active for `smax`, every centre of the cover
of `G` with its interaction box (sites of `Ω₁`) in `T` and active for `t` belongs to the closure of
`smax` (its base is a site of `Ω₁` in `T`). -/
theorem mem_actComp_of_inner {D : ℕ} (hD : 2 * L ^ (k + 1) ≤ D)
    {t smax : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    (ht : ∀ q, ActC (coverOf G) t q → ActC (coverOf G) smax q)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ Dec2.innerCentres (coverOf G) G (actHull (coverOf G) D t seed))
    (hne : (coverOf G).sProd t q ≠ 0) : q ∈ actComp (coverOf G) D smax seed := by
  classical
  have hqC : q ∈ (coverOf G).cubeIdx := (Finset.mem_filter.1 hq).1
  have hsub : SubI G (intBox q) (actHull (coverOf G) D t seed) := (Finset.mem_filter.1 hq).2
  have hqC' : q ∈ cubeIdx G := hqC
  have hmem := (mem_cubeIdx G).1 hqC'
  have hq2 : q.2 ∈ G.Ω 1 := G.layer_subset hmem.1.1 hmem.1.2 hmem.2.1
  have hq2T := hsub ⟨q.2, hq2⟩ (base_mem_intBox q)
  have hD0 : 0 + 2 * L ^ (k + 1) ≤ D := by omega
  exact actComp_mono ht seed (mem_actComp_of_near hD0 ⟨hqC, hne⟩
    (base_mem_intBox q) hq2T (by rw [supDist_self]))

end Inner

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The decoupled backgrounds and multipliers of the pair `(coverOf G′, G′)` at two vectors agree
on the hull** (P3 (4.47), Theorem I-4b (iv) for the pair compared with itself).  Let `v`, `v'` be
vectors with `|v_P|, |v'_P| ≤ e^κ`, whose active centres are active for a vector `smax`, with the
same factors on the active closure of `smax` from a seed; let `T` be the block hull of the closure of
`v` (`D ≥ 3 L^{k+1}`), whose `2 L^{k+1}`-neighbourhood lies in `Ω₁(G′)`.  For the datum of the step
in the domain of Theorem I-4b, the multipliers agree on `T` and the fields on its
`L^{k+1}`-neighbourhood. -/
theorem decBg_agree_of_hull {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' S.a S.ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ' S.a S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' smax : Dec2.DecParams (coverOf S.G')}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC S.G' S.ν δ ε S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D) (seed : Finset (CTorus d L N₁ m₁ (k + 1)))
    (hsup : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v) q → ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hsup' : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v') q →
      ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hcomp : ∀ q ∈ actComp (coverOf S.G') D (Dec2.extS _ smax) seed,
      (coverOf S.G').sProd (Dec2.extS _ v) q = (coverOf S.G').sProd (Dec2.extS _ v') q)
    (hdeep : ∀ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed, ∀ z : CTorus d L N₁ m₁ (k + 1),
      supDist y z ≤ 2 * L ^ (k + 1) → z ∈ S.G'.Ω 1) :
    (∀ (x : CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ S.G'.Ω 1),
        x ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed →
        Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D' ⟨x, hx⟩ =
          Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D' ⟨x, hx⟩) ∧
      ∀ (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ S.G'.Ω 1),
        y ∈ nbhdSup (L ^ (k + 1)) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) → ∀ i : Fin N,
        Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D' (⟨y, hy⟩, i) =
          Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D' (⟨y, hy⟩, i) := by
  classical
  have hTT' : actHull (coverOf S.G') D (Dec2.extS _ v') seed =
      actHull (coverOf S.G') D (Dec2.extS _ v) seed :=
    (actHull_eq_of_sProd_eq hsup hsup' hcomp).symm
  have hres : ∀ x ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed, x ∈ S.G'.Ω 1 →
      ∀ y ∈ resSites S.G' x, y ∈ S.G'.Ω 1 ∧
        y ∈ nbhdSup (L ^ (k + 1)) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) := by
    intro x hx _ y hy
    have hd := supDist_le_of_mem_resSites hy
    exact ⟨hdeep x hx y (by omega), mem_nbhdSup.2 ⟨x, hx, hd⟩⟩
  have hD2 : 2 * L ^ (k + 1) ≤ D := by omega
  have hdich : ∀ q ∈ (coverOf S.G').cubeIdx, (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 →
      SubI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∨
        DisjI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) :=
    fun q hq hne => subI_or_disjI_actHull hD2 ⟨hq, hne⟩
  have hdich' : ∀ q ∈ (coverOf S.G').cubeIdx, (coverOf S.G').sProd (Dec2.extS _ v') q ≠ 0 →
      SubI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∨
        DisjI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) := by
    intro q hq hne
    rw [← hTT']
    exact subI_or_disjI_actHull hD2 ⟨hq, hne⟩
  have hrow : ∀ q ∈ (coverOf S.G').cubeIdx, (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ nbhdSup (L ^ (k + 1)) (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
        x ∈ intBox q → x ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed := by
    intro q hq hne x hxY hxq
    obtain ⟨y, hyT, hyx⟩ := mem_nbhdSup.1 hxY
    exact mem_actHull_of_nbhd hDD ⟨hq, hne⟩ hxq hyT hyx
  have hrow' : ∀ q ∈ (coverOf S.G').cubeIdx, (coverOf S.G').sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ nbhdSup (L ^ (k + 1)) (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
        x ∈ intBox q → x ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed := by
    intro q hq hne x hxY hxq
    obtain ⟨y, hyT, hyx⟩ := mem_nbhdSup.1 hxY
    rw [← hTT'] at hyT ⊢
    exact mem_actHull_of_nbhd hDD ⟨hq, hne⟩ hxq hyT hyx
  have hin : ∀ q ∈ Dec2.innerCentres (coverOf S.G') S.G'
        (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
      (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf S.G') S.G' (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∧
        (coverOf S.G').sProd (Dec2.extS _ v') q = (coverOf S.G').sProd (Dec2.extS _ v) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ S.G'.layer n ↔ y ∈ S.G'.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf S.G').chi q x = (coverOf S.G').chi q x) :=
    fun q hq hne => ⟨hq, (hcomp q (mem_actComp_of_inner hD2 hsup hq hne)).symm,
      fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩
  have hin' : ∀ q ∈ Dec2.innerCentres (coverOf S.G') S.G'
        (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
      (coverOf S.G').sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf S.G') S.G' (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∧
        (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 := by
    intro q hq hne
    have hq' := hq
    rw [← hTT'] at hq'
    exact ⟨hq, by rw [hcomp q (mem_actComp_of_inner hD2 hsup' hq' hne)]; exact hne⟩
  exact decBg_agree_core S.G' S.a S.ν S.D' hS Sb HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD'
    (subset_nbhdSup _ _) hdich hdich' hrow hrow' hin hin' hres

/-- The representative of a unit point lies in the top layer (`Ω_{k+1}` is a union of
`(k+1)`-blocks). -/
theorem unitRep_mem_top (b : S.U) : (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ S.G'.layer (k + 1) := by
  obtain ⟨x, hx, hxb⟩ := (mem_unitPts S.G').1 b.2
  have hlay : S.G'.layer (k + 1) = S.G'.Ω (k + 1) := by
    unfold GeneratingSet.layer
    rw [S.G'.top, Finset.sdiff_empty]
  rw [hlay] at hx ⊢
  have hblk : jBlock d L (N₁ * L ^ m₁) (k + 1) k x =
      jBlock d L (N₁ * L ^ m₁) (k + 1) k (unitRep b) := by
    have h1 : unitBlock x = unitBlock (unitRep b) := by rw [hxb, unitBlock_unitRep]
    exact h1
  have hblk' : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (unitRep b) :=
    jBlock_eq_of_le (Nat.le_succ k) le_rfl hblk
  exact (S.G'.blockUnion (k + 1) (Nat.succ_pos k) le_rfl x (unitRep b) hblk').1 hx

/-- **The fluctuation part of the composed field agrees at a unit point of the hull** (P5 (2.35),
(2.39); P3 (4.22)–(4.24) for the pair `(coverOf G′, G′)` compared with itself at two vectors): under the
hypotheses of `decBg_agree_of_hull`, the standing conditions of the decoupled covariance at the two
vectors, a unit point `b` whose representative lies in the hull, and hat variables agreeing on the
unit points of the hull, `β_k^{-1/2} (C^{1/2}(v) ψ̂)(b) = β_k^{-1/2} (C^{1/2}(v') ψ̂')(b)`. -/
theorem shiftLoc_eq_of_hull {Kc Cx Cx₂ c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' S.a S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' S.a S.a₁ S.ν Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' S.a S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' smax : Dec2.DecParams (coverOf S.G')}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC S.G' S.ν δ ε S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D) (seed : Finset (CTorus d L N₁ m₁ (k + 1)))
    (hsup : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v) q → ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hsup' : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v') q →
      ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hcomp : ∀ q ∈ actComp (coverOf S.G') D (Dec2.extS _ smax) seed,
      (coverOf S.G').sProd (Dec2.extS _ v) q = (coverOf S.G').sProd (Dec2.extS _ v') q)
    (hdeep : ∀ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed, ∀ z : CTorus d L N₁ m₁ (k + 1),
      supDist y z ≤ 2 * L ^ (k + 1) → z ∈ S.G'.Ω 1)
    (hadm : AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D'))
    (hadm' : AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D'))
    (hU : ∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)))
    (hU' : ∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') (Dec2.extS _ v')))
    (hMu : ∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D'))))
    (hMu' : ∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') (Dec2.extS _ v')
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D'))))
    {sloc sloc' : S.U → Dec2.DecParams (coverOf S.G')} {b : S.U} (hb : sloc b = v)
    (hb' : sloc' b = v')
    (hbT : (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed)
    {ψhat ψhat' : S.U → Fin N → ℂ}
    (hψ : ∀ b' : S.U, (∃ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed,
      y ∈ S.G'.layer (k + 1) ∧ unitBlock y = (b' : UnitTorus d L N₁ m₁ k)) → ψhat b' = ψhat' b') :
    S.shiftLoc (coverOf S.G') (rho4 d L N BG κ) sloc ψhat b =
      S.shiftLoc (coverOf S.G') (rho4 d L N BG κ) sloc' ψhat' b := by
  classical
  obtain ⟨hαT, hφY⟩ := S.decBg_agree_of_hull hS Sb HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD' hDD
    seed hsup hsup' hcomp hdeep
  have hTT' : actHull (coverOf S.G') D (Dec2.extS _ v') seed =
      actHull (coverOf S.G') D (Dec2.extS _ v) seed :=
    (actHull_eq_of_sProd_eq hsup hsup' hcomp).symm
  have hD2 : 2 * L ^ (k + 1) ≤ D := by omega
  have hdich : ∀ q ∈ (coverOf S.G').cubeIdx, (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 →
      SubI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∨
        DisjI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) :=
    fun q hq hne => subI_or_disjI_actHull hD2 ⟨hq, hne⟩
  have hdich' : ∀ q ∈ (coverOf S.G').cubeIdx, (coverOf S.G').sProd (Dec2.extS _ v') q ≠ 0 →
      SubI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∨
        DisjI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) := by
    intro q hq hne
    rw [← hTT']
    exact subI_or_disjI_actHull hD2 ⟨hq, hne⟩
  have hin : ∀ q ∈ Dec2.innerCentres (coverOf S.G') S.G'
        (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
      (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf S.G') S.G' (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∧
        (coverOf S.G').sProd (Dec2.extS _ v') q = (coverOf S.G').sProd (Dec2.extS _ v) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ S.G'.layer n ↔ y ∈ S.G'.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf S.G').chi q x = (coverOf S.G').chi q x) :=
    fun q hq hne => ⟨hq, (hcomp q (mem_actComp_of_inner hD2 hsup hq hne)).symm,
      fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩
  have hin' : ∀ q ∈ Dec2.innerCentres (coverOf S.G') S.G'
        (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
      (coverOf S.G').sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf S.G') S.G' (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∧
        (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 := by
    intro q hq hne
    have hq' := hq
    rw [← hTT'] at hq'
    exact ⟨hq, by rw [hcomp q (mem_actComp_of_inner hD2 hsup' hq' hne)]; exact hne⟩
  have hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ S.G'.Ω 1) (hx' : x₀ ∈ S.G'.Ω 1),
      x₀ ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed →
      Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D' ⟨x₀, hx⟩ =
        Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D' ⟨x₀, hx'⟩ :=
    fun x₀ hx _ hxT => (hαT x₀ hx hxT).symm
  have hφ : ∀ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed,
      svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') y =
        svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') y := by
    intro y hyT
    funext i
    by_cases hy : y ∈ S.G'.Ω 1
    · have h1 := svec_of_mem S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v'
        S.D') ⟨y, hy⟩ i
      have h2 := svec_of_mem S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v
        S.D') ⟨y, hy⟩ i
      simp only at h1 h2
      rw [h1, h2]
      exact hφY y hy (subset_nbhdSup _ _ hyT) i
    · rw [svec_of_not_mem _ _ hy, svec_of_not_mem _ _ hy]
  have hH : ∀ x : ℝ, 0 < x → Dec2.HRespects (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
      (actHull (coverOf S.G') D (Dec2.extS _ v) seed) :=
    fun x _ => hRespects_actHull _ _ _ _ _ hDD _ _
  have hH' : ∀ x : ℝ, 0 < x → Dec2.HRespects (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') (Dec2.extS _ v')
      (actHull (coverOf S.G') D (Dec2.extS _ v) seed) := by
    intro x _
    rw [← hTT']
    exact hRespects_actHull _ _ _ _ _ hDD _ _
  have hψ' : ∀ (b'' : UnitTorus d L N₁ m₁ k) (hb₁ : b'' ∈ unitPts S.G') (hb₂ : b'' ∈ unitPts S.G'),
      (∃ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed, y ∈ S.G'.layer (k + 1) ∧
        unitBlock y = b'') → ∀ j : Fin N,
        ψhat' ⟨b'', hb₂⟩ j = ψhat ⟨b'', hb₁⟩ j :=
    fun b'' hb₁ _ hex j => (congrFun (hψ ⟨b'', hb₁⟩ hex) j).symm
  funext i
  have key := Dec2.localLift_eq_localLift_on_component (H := S.G') (H' := S.G')
    (α := Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D')
    (α' := Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D')
    (s := Dec2.extS _ v) (s' := Dec2.extS _ v')
    (φ := svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D'))
    (φ' := svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D'))
    (T := actHull (coverOf S.G') D (Dec2.extS _ v) seed)
    SX SX hadm hadm' (fun _ _ _ _ _ => Iff.rfl) hU hU' hdich hdich' hin hin' hα hφ hH hH' hMu
    hMu' (isBlockUnion_actHull _ _ _) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    (fun q => ψhat q.1 q.2) (fun q => ψhat' q.1 q.2) hψ' hbT (S.unitRep_mem_top b) i
  have hub : unitBlock (unitRep b) ∈ unitPts S.G' := by rw [unitBlock_unitRep]; exact b.2
  have hsub : (⟨unitBlock (unitRep b), hub⟩ : S.U) = b := Subtype.ext (unitBlock_unitRep b)
  simp only [hub, ↓reduceDIte, hsub] at key
  unfold shiftLoc covSqrtAt
  rw [hb, hb']
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at key
  exact key.symm

/-- **The background part of the composed field agrees at a unit point of the hull**: under the
hypotheses of `decBg_agree_of_hull` and with the representative of `b` in the hull,
`ψ^{(k)}_loc(θ)(b)` is the same at the localization vectors `v` and `v'` (the composed datum reads
the background on the blocks of `G` and `G′` of the representative, inside its `(k+1)`-block). -/
theorem psiLoc_eq_of_hull {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' S.a S.ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ' S.a S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' smax : Dec2.DecParams (coverOf S.G')}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC S.G' S.ν δ ε S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D) (seed : Finset (CTorus d L N₁ m₁ (k + 1)))
    (hsup : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v) q → ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hsup' : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v') q →
      ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hcomp : ∀ q ∈ actComp (coverOf S.G') D (Dec2.extS _ smax) seed,
      (coverOf S.G').sProd (Dec2.extS _ v) q = (coverOf S.G').sProd (Dec2.extS _ v') q)
    (hdeep : ∀ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed, ∀ z : CTorus d L N₁ m₁ (k + 1),
      supDist y z ≤ 2 * L ^ (k + 1) → z ∈ S.G'.Ω 1)
    {sloc sloc' : S.U → Dec2.DecParams (coverOf S.G')} {b : S.U} (hb : sloc b = v)
    (hb' : sloc' b = v')
    (hbT : (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed) :
    S.psiLoc (coverOf S.G') (rho4 d L N BG κ) sloc b =
      S.psiLoc (coverOf S.G') (rho4 d L N BG κ) sloc' b := by
  classical
  obtain ⟨-, hφY⟩ := S.decBg_agree_of_hull hS Sb HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD' hDD
    seed hsup hsup' hcomp hdeep
  set x := (unitRep b : CTorus d L N₁ m₁ (k + 1)) with hxdef
  have hx1 : x ∈ S.G.Ω 1 := by
    have h1 : x ∈ S.G'.Ω (k + 1) := ((S.G'.mem_layer).1 (S.unitRep_mem_top b)).1
    have h2 : x ∈ S.G.Ω k := S.topIn h1
    exact S.G.Ω_antitone le_rfl S.hk1 (by omega) h2
  -- the blocks read by the composition lie in the `(k+1)`-block of `x`, hence in the hull
  have hblk : ∀ (n : ℕ), n ≤ k + 1 → ∀ y, jBlock d L (N₁ * L ^ m₁) (k + 1) n y =
      jBlock d L (N₁ * L ^ m₁) (k + 1) n x → y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed := by
    intro n hn y hy
    have h := jBlock_eq_of_le hn le_rfl hy
    exact (isBlockUnion_actHull D (Dec2.extS _ v) seed y x h).2 hbT
  have hsv : ∀ y, y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed → ∀ i : Fin N,
      svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') y i =
        svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') y i := by
    intro y hyT i
    by_cases hy : y ∈ S.G'.Ω 1
    · have h1 := svec_of_mem S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v'
        S.D') ⟨y, hy⟩ i
      have h2 := svec_of_mem S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v
        S.D') ⟨y, hy⟩ i
      simp only at h1 h2
      rw [h1, h2]
      exact (hφY y hy (subset_nbhdSup _ _ hyT) i).symm
    · rw [svec_of_not_mem _ _ hy, svec_of_not_mem _ _ hy]
  have hG : S.G.layerIndex x ≤ k + 1 := layerIndex_le_of_Ω_empty S.G S.G.top x
  have hG' : S.G'.layerIndex x ≤ k + 1 := layerIndex_le_of_Ω_empty S.G' S.G'.top x
  unfold psiLoc psiKdAt
  rw [hb, hb']
  funext i
  show composeField S.G S.G' S.a _ S.D'.Ψ x i = composeField S.G S.G' S.a _ S.D'.Ψ x i
  unfold composeField
  simp only [hx1, ↓reduceIte]
  unfold blockMean
  congr 2
  · refine Finset.sum_congr rfl fun y hy => hsv y (hblk _ hG y (GeneratingSet.mem_blk.1 hy)) i
  · congr 2
    refine Finset.sum_congr rfl fun y hy => hsv y (hblk _ hG' y (GeneratingSet.mem_blk.1 hy)) i

/-- **The composed field of P5 (2.39) agrees at a unit point of the hull** (reading HS-1, the locality of the
substitution at one point): under the hypotheses of `decBg_agree_of_hull` and the standing
conditions of the covariance at the two localization vectors, with the representative of `b` in the
hull and hat variables agreeing on the unit points of the hull,
`ψ_k(b) = ψ^{(k)}_loc(θ)(b) + β_k^{-1/2} (C^{(k)1/2}_loc ψ̂)(b)` is the same at `sloc` and `sloc'`. -/
theorem composed_eq_of_hull {Kc Cx Cx₂ c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' S.a S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' S.a S.a₁ S.ν Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' S.a S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v v' smax : Dec2.DecParams (coverOf S.G')}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC S.G' S.ν δ ε S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D) (seed : Finset (CTorus d L N₁ m₁ (k + 1)))
    (hsup : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v) q → ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hsup' : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v') q →
      ActC (coverOf S.G') (Dec2.extS _ smax) q)
    (hcomp : ∀ q ∈ actComp (coverOf S.G') D (Dec2.extS _ smax) seed,
      (coverOf S.G').sProd (Dec2.extS _ v) q = (coverOf S.G').sProd (Dec2.extS _ v') q)
    (hdeep : ∀ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed, ∀ z : CTorus d L N₁ m₁ (k + 1),
      supDist y z ≤ 2 * L ^ (k + 1) → z ∈ S.G'.Ω 1)
    (hadm : AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D'))
    (hadm' : AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D'))
    (hU : ∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)))
    (hU' : ∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') (Dec2.extS _ v')))
    (hMu : ∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D'))))
    (hMu' : ∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D') (Dec2.extS _ v')
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v' S.D'))))
    {sloc sloc' : S.U → Dec2.DecParams (coverOf S.G')} {b : S.U} (hb : sloc b = v)
    (hb' : sloc' b = v')
    (hbT : (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed)
    {ψhat ψhat' : S.U → Fin N → ℂ}
    (hψ : ∀ b' : S.U, (∃ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) seed,
      y ∈ S.G'.layer (k + 1) ∧ unitBlock y = (b' : UnitTorus d L N₁ m₁ k)) → ψhat b' = ψhat' b') :
    S.composed (coverOf S.G') (rho4 d L N BG κ) sloc ψhat b =
      S.composed (coverOf S.G') (rho4 d L N BG κ) sloc' ψhat' b := by
  have h1 := S.psiLoc_eq_of_hull hS Sb HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD' hDD seed hsup hsup'
    hcomp hdeep hb hb' hbT
  have h2 := S.shiftLoc_eq_of_hull hS Sb SX HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD' hDD seed hsup
    hsup' hcomp hdeep hadm hadm' hU hU' hMu hMu' hb hb' hbT hψ
  funext i
  unfold composed
  rw [h1, h2]

end HoleStep

end Balaban.Fluctuation
