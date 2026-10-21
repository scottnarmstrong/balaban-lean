/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepActComp
public import Balaban.Fluctuation.HoleStep

/-!
# Locality of the composed field of the step on a region at one unit point (R12)

Under the reading R12 of `notes/phase1/PLAN-B.md` the composed field of P5 (2.39) at a unit point
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
  resp. `T`), for data in the domain of Theorem I-4b.
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
  obtain ⟨φ, α, hsol, huniq, -⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM hv hδ0 hδε hε hδ hνε hD'
  obtain ⟨φ', α', hsol', huniq', -⟩ :=
    Dec2.i4b_exists_unique hS Sb HB hκ hM hv' hδ0 hδε hε hδ hνε hD'
  obtain ⟨hφ, hα⟩ := Dec2.decBg_eq hsol huniq
  obtain ⟨hφ', hα'⟩ := Dec2.decBg_eq hsol' huniq'
  rw [hφ, hα, hφ', hα']
  have hTT' : actHull (coverOf S.G') D (Dec2.extS _ v') seed =
      actHull (coverOf S.G') D (Dec2.extS _ v) seed :=
    (actHull_eq_of_sProd_eq hsup hsup' hcomp).symm
  -- the inner active centres of `v` and of `v'` belong to the closure of `smax`
  have hinner : ∀ (t : Dec2.DecParams (coverOf S.G')),
      (∀ q, ActC (coverOf S.G') (Dec2.extS _ t) q → ActC (coverOf S.G') (Dec2.extS _ smax) q) →
      actHull (coverOf S.G') D (Dec2.extS _ t) seed =
        actHull (coverOf S.G') D (Dec2.extS _ v) seed →
      ∀ q ∈ Dec2.innerCentres (coverOf S.G') S.G' (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
        (coverOf S.G').sProd (Dec2.extS _ t) q ≠ 0 →
        q ∈ actComp (coverOf S.G') D (Dec2.extS _ smax) seed := by
    intro t ht hTt q hq hne
    have hqC : q ∈ (coverOf S.G').cubeIdx := (Finset.mem_filter.1 hq).1
    have hsub : SubI S.G' (intBox q) (actHull (coverOf S.G') D (Dec2.extS _ v) seed) :=
      (Finset.mem_filter.1 hq).2
    have hqC' : q ∈ cubeIdx S.G' := hqC
    have hmem := (mem_cubeIdx S.G').1 hqC'
    have hq2 : q.2 ∈ S.G'.Ω 1 := S.G'.layer_subset hmem.1.1 hmem.1.2 hmem.2.1
    have hq2T := hsub ⟨q.2, hq2⟩ (base_mem_intBox q)
    rw [← hTt] at hq2T
    have hD0 : 0 + 2 * L ^ (k + 1) ≤ D := by omega
    exact actComp_mono ht seed (mem_actComp_of_near hD0 ⟨hqC, hne⟩
      (base_mem_intBox q) hq2T (by rw [supDist_self]))
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
    fun q hq hne => ⟨hq, (hcomp q (hinner v hsup rfl q hq hne)).symm,
      fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩
  have hin' : ∀ q ∈ Dec2.innerCentres (coverOf S.G') S.G'
        (actHull (coverOf S.G') D (Dec2.extS _ v) seed),
      (coverOf S.G').sProd (Dec2.extS _ v') q ≠ 0 →
      q ∈ Dec2.innerCentres (coverOf S.G') S.G' (actHull (coverOf S.G') D (Dec2.extS _ v) seed) ∧
        (coverOf S.G').sProd (Dec2.extS _ v) q ≠ 0 :=
    fun q hq hne => ⟨hq, by rw [hcomp q (hinner v' hsup' hTT' q hq hne)]; exact hne⟩
  have h := Dec2.decBg_component_cross (C := coverOf S.G') (C' := coverOf S.G') (H := S.G')
    (H' := S.G') (s := v) (s' := v') (D := S.D') (D' := S.D')
    (T := actHull (coverOf S.G') D (Dec2.extS _ v) seed)
    (Y := nbhdSup (L ^ (k + 1)) (actHull (coverOf S.G') D (Dec2.extS _ v) seed))
    hS Sb Sb HB HB hκ hM hv hv' hδ0 hδε hε hδ hνε hδ0 hδε hε hδ hνε hD' hD' (subset_nbhdSup _ _)
    (fun _ _ _ _ _ => Iff.rfl) hdich hdich' hrow hrow' hin hin' hres
    (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => ⟨rfl, rfl⟩) hsol hsol'
  exact ⟨fun x hx hxT => h.1 x hx hx hxT, fun y hy hyY i => h.2 y hy hy hyY i⟩

end HoleStep

end Balaban.Fluctuation
