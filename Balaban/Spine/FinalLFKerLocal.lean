/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFHistFactor
public import Balaban.LargeField.Operators.Invariance
public import Balaban.LargeField.Operators.QuietLocalRest
public import Balaban.LargeField.Budget.Injective

/-!
# The operators of a component are functions of its record (A6-4, kernel locality)

The operator `𝕋_k(Z, 𝔸 ∩ Z)` of a component `Z` of scale `k` of a labelled history (`locOp`, the
operators `postOp` of the last integral) is a function of the record of `Z` (`compRec`: its cubes,
its localized history and its labelled kept positions): the operators of two components of two
histories with the same record correspond, with corresponding integrated variables and equal
kernels and exponents at corresponding configurations. This is the identity case of Lemma II.5.10
along the lineages (`locOp_euclid_of_corr` at the identity symmetry `LatTorusSym.refl`).

* `val_mem_comps_old`, `mem_parts_of_mem_comps_old`: the old parts of `Z'` are the components of
  `Z^pre_k` whose cubes form a component of the old cubes of `Z'`;
* `RecCorr`: components with the same cubes, localized history and labelled kept positions;
  `recCorr_parts`: the old parts of `RecCorr` components are matched by a bijection of `RecCorr`
  parts (`record_forward`);
* **`locOp_corr_of_compRec_eq`**: components with the same record have corresponding operators.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

section Parts

variable (H : RegionHistory S n R k0 K)

/-- The cubes of an old part of `Z'` form a component of the old cubes of `Z'`. -/
theorem val_mem_comps_old {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1)) {Y : H.Comp k}
    (hY : Y ∈ H.parts k Z') : Y.1 ∈ comps (S.omega k) (H.oldCubes k Z') := by
  classical
  rw [← H.parts_image_eq_comps hk Z']
  exact Finset.mem_image_of_mem _ hY

/-- A component of `Z^pre_k` whose cubes form a component of the old cubes of `Z'` is an old part
of `Z'`. -/
theorem mem_parts_of_mem_comps_old {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1)) (Y : H.Comp k)
    (hY : Y.1 ∈ comps (S.omega k) (H.oldCubes k Z')) : Y ∈ H.parts k Z' := by
  classical
  rw [← H.parts_image_eq_comps hk Z', Finset.mem_image] at hY
  obtain ⟨Y'', hY'', e⟩ := hY
  rwa [Subtype.ext e] at hY''

/-- A component of `Z^pre_k` given by a component of the old cubes of `Z'` is an old part of `Z'`. -/
theorem mk_mem_parts (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1))
    (Y : Finset (Torus S.d (n k))) (hY : Y ∈ comps (S.omega k) (H.oldCubes k Z')) :
    (⟨Y, mem_Zp_of_old H hk Z' hY⟩ : H.Comp k) ∈ H.parts k Z' :=
  mem_parts_of_mem_comps_old H hk Z' _ hY

/-- The cubes of an old part of `Z₁` form a component of the old cubes of `Z₂` when the old cubes
are the same. -/
theorem val_mem_comps_old_of_eq {H₁ H₂ : RegionHistory S n R k0 K} {k : ℕ} (hk : k < K)
    (Z₁ : H₁.Comp (k + 1)) (Z₂ : H₂.Comp (k + 1)) (hold : H₁.oldCubes k Z₁ = H₂.oldCubes k Z₂)
    (Y : ↥(H₁.parts k Z₁)) : Y.1.1 ∈ comps (S.omega k) (H₂.oldCubes k Z₂) :=
  hold ▸ val_mem_comps_old H₁ hk Z₁ Y.2

/-- The old parts of two components with the same old cubes are matched by their cubes. -/
def partsMapOfOld {H₁ H₂ : RegionHistory S n R k0 K} {k : ℕ} (hk : k < K) (Z₁ : H₁.Comp (k + 1))
    (Z₂ : H₂.Comp (k + 1)) (hold : H₁.oldCubes k Z₁ = H₂.oldCubes k Z₂) (Y : ↥(H₁.parts k Z₁)) :
    ↥(H₂.parts k Z₂) :=
  ⟨⟨Y.1.1, mem_Zp_of_old H₂ hk Z₂ (val_mem_comps_old_of_eq hk Z₁ Z₂ hold Y)⟩,
    mk_mem_parts H₂ hk Z₂ Y.1.1 (val_mem_comps_old_of_eq hk Z₁ Z₂ hold Y)⟩

theorem partsMapOfOld_val {H₁ H₂ : RegionHistory S n R k0 K} {k : ℕ} (hk : k < K)
    (Z₁ : H₁.Comp (k + 1)) (Z₂ : H₂.Comp (k + 1)) (hold : H₁.oldCubes k Z₁ = H₂.oldCubes k Z₂)
    (Y : ↥(H₁.parts k Z₁)) : (partsMapOfOld hk Z₁ Z₂ hold Y).1.1 = Y.1.1 := by
  unfold partsMapOfOld
  rw [Subtype.coe_mk, Subtype.coe_mk]

theorem partsMapOfOld_fst {H₁ H₂ : RegionHistory S n R k0 K} {k : ℕ} (hk : k < K)
    (Z₁ : H₁.Comp (k + 1)) (Z₂ : H₂.Comp (k + 1)) (hold : H₁.oldCubes k Z₁ = H₂.oldCubes k Z₂)
    (Y : ↥(H₁.parts k Z₁)) :
    (partsMapOfOld hk Z₁ Z₂ hold Y).1 =
      ⟨Y.1.1, mem_Zp_of_old H₂ hk Z₂ (val_mem_comps_old_of_eq hk Z₁ Z₂ hold Y)⟩ :=
  Subtype.ext (partsMapOfOld_val hk Z₁ Z₂ hold Y)

/-- **The bijection of the old parts of two components with the same old cubes.** -/
def partsEquivOfOld {H₁ H₂ : RegionHistory S n R k0 K} {k : ℕ} (hk : k < K) (Z₁ : H₁.Comp (k + 1))
    (Z₂ : H₂.Comp (k + 1)) (hold : H₁.oldCubes k Z₁ = H₂.oldCubes k Z₂) :
    ↥(H₁.parts k Z₁) ≃ ↥(H₂.parts k Z₂) where
  toFun := partsMapOfOld hk Z₁ Z₂ hold
  invFun := partsMapOfOld hk Z₂ Z₁ hold.symm
  left_inv Y := Subtype.ext (Subtype.ext
    ((partsMapOfOld_val hk Z₂ Z₁ hold.symm _).trans (partsMapOfOld_val hk Z₁ Z₂ hold Y)))
  right_inv Y := Subtype.ext (Subtype.ext
    ((partsMapOfOld_val hk Z₁ Z₂ hold _).trans (partsMapOfOld_val hk Z₂ Z₁ hold.symm Y)))

end Parts

section Corr

variable (M : ℕ) [NeZero M]

/-- **Corresponding components of two labelled histories**: components of scale `j ≤ K` with the
same cubes, the same localized history and the same labelled kept positions. -/
def RecCorr (A B : LabHist S n R k0 K) (j : ℕ) (Y : A.H.Comp j) (Y' : B.H.Comp j) : Prop :=
  j ≤ K ∧ Y.1 = Y'.1 ∧ A.H.localHistory M K j Y = B.H.localHistory M K j Y' ∧
    labSet A Y = labSet B Y'

/-- **The old parts of corresponding components correspond**: the old cubes of the two components
are the same (`record_forward`), hence their old parts have the same cubes, the same localized
histories, and (being in the lineage) the same labelled kept positions. -/
theorem recCorr_parts {A B : LabHist S n R k0 K} {k : ℕ} {Z : A.H.Comp (k + 1)}
    {Z' : B.H.Comp (k + 1)} (hc : RecCorr M A B (k + 1) Z Z') :
    ∃ eqv : ↥(A.H.parts k Z) ≃ ↥(B.H.parts k Z'), ∀ Y, RecCorr M A B k Y.1 (eqv Y).1 := by
  classical
  obtain ⟨hkK, -, hlh, hlab⟩ := hc
  obtain ⟨-, hold, -, hfam⟩ := record_forward hkK Z Z' hlh
  have hk : k < K := by omega
  refine ⟨partsEquivOfOld hk Z Z' hold, fun Y => ?_⟩
  have hYc : Y.1.1 ∈ comps (S.omega k) (A.H.oldCubes k Z) := val_mem_comps_old A.H hk Z Y.2
  have e1 := partsMapOfOld_fst hk Z Z' hold Y
  have hlhY : A.H.localHistory M K k Y.1 =
      B.H.localHistory M K k (partsEquivOfOld hk Z Z' hold Y).1 := by
    show _ = B.H.localHistory M K k (partsMapOfOld hk Z Z' hold Y).1
    rw [e1]
    exact hfam Y.1.1 Y.1.2 _ hYc
  refine ⟨by omega, (partsMapOfOld_val hk Z Z' hold Y).symm, hlhY, ?_⟩
  have hkp : A.H.keptPos k Y.1 = B.H.keptPos k (partsEquivOfOld hk Z Z' hold Y).1 :=
    keptPos_eq_of_localHistory_eq k (by omega) A.H B.H Y.1 _ hlhY
  unfold labSet
  rw [← hkp]
  refine Finset.image_congr fun p hpA => ?_
  have hpZ : p ∈ A.H.keptPos (k + 1) Z := by
    rw [keptPos_succ, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inl ⟨Y.1, Y.2, hpA⟩
  have hm : (p, A.lab p.1 p.2) ∈ labSet B Z' := by
    rw [← hlab]; exact mem_labSet.2 ⟨hpZ, rfl⟩
  simp only [(mem_labSet.1 hm).2]

variable [NeZero S.L] {N : ℕ} (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)

/-- **The operators of components with the same record correspond** (kernel locality): the
integrated variables correspond under the identity (`SubCorr`), and the kernels and exponents are
equal at corresponding outputs, configurations and sources. -/
theorem locOp_corr_of_compRec_eq {k : ℕ} (hkK : k ≤ K) {A B : LabHist S n R k0 K}
    (c : A.H.Comp k) (c' : B.H.Comp k) (h : compRec M A c = compRec M B c') :
    ∃ hI : HistImage (LatTorusSym.refl S n M K).toTorusSym (A.H.localHistory M K k c)
        (B.H.localHistory M K k c'),
      SubCorr hI hkK (locOp geo cs SD KD A.adm (fun j c => A.lab j c.1) k hkK c).A
          (locOp geo cs SD KD B.adm (fun j c => B.lab j c.1) k hkK c').A ∧
        ∀ o o' (x : SubCfg N (A.H.localHistory M K k c) k
            (locOp geo cs SD KD A.adm (fun j c => A.lab j c.1) k hkK c).A)
          (x' : SubCfg N (B.H.localHistory M K k c') k
            (locOp geo cs SD KD B.adm (fun j c => B.lab j c.1) k hkK c').A) hv
          (g g' : GIdx S n M K N → ℂ),
          RelOut (LatTorusSym.refl S n M K).toTorusSym o o' → RelVal hI hkK x x' →
          RelG (LatTorusSym.refl S n M K).toTorusSym g g' →
          (locOp geo cs SD KD B.adm (fun j c => B.lab j c.1) k hkK c').T.K o' x' hv =
              (locOp geo cs SD KD A.adm (fun j c => A.lab j c.1) k hkK c).T.K o x hv ∧
            (locOp geo cs SD KD B.adm (fun j c => B.lab j c.1) k hkK c').T.b o' x' hv g' =
              (locOp geo cs SD KD A.adm (fun j c => A.lab j c.1) k hkK c).T.b o x hv g := by
  have hc : RecCorr M A B k c c' := ⟨hkK, congrArg Prod.fst h,
    congrArg (fun r : CRec S n M K k => r.2.1) h, congrArg (fun r : CRec S n M K k => r.2.2) h⟩
  have hloc : ∀ j, j ≤ K → ∀ (Y : A.H.Comp j) (Y' : B.H.Comp j), RecCorr M A B j Y Y' →
      HistImage (LatTorusSym.refl S n M K).toTorusSym (A.H.localHistory M K j Y)
        (B.H.localHistory M K j Y') := fun j _ Y Y' hY => by
    rw [hY.2.2.1]; exact histImage_refl _
  have hkept : ∀ j (Y : A.H.Comp j) (Y' : B.H.Comp j), RecCorr M A B j Y Y' →
      (IsKept B.H j Y' ↔ IsKept A.H j Y) := fun j Y Y' hY =>
    (isKeptEvent_iff_of_localHistory_eq hY.1 Y Y' hY.2.2.1).symm
  have hlab : ∀ j (Y : A.H.Comp j) (Y' : B.H.Comp j), RecCorr M A B j Y Y' → IsKept A.H j Y →
      (fun j (c : B.H.Comp j) => B.lab j c.1) j Y' = (fun j (c : A.H.Comp j) => A.lab j c.1) j Y := by
    intro j Y Y' hY hk
    have hp : (⟨j, Y.1⟩ : KeptPos S n) ∈ A.H.keptPos j Y := mem_keptPos_of_desc A.H (Desc.refl Y) hk
    have hm : ((⟨j, Y.1⟩ : KeptPos S n), A.lab j Y.1) ∈ labSet B Y' :=
      hY.2.2.2 ▸ mem_labSet.2 ⟨hp, rfl⟩
    have e := (mem_labSet.1 hm).2
    show B.lab j Y'.1 = A.lab j Y.1
    rw [← hY.2.1]
    exact e
  exact ⟨hloc k hkK c c' hc, locOp_euclid_of_corr geo cs SD KD (σ := LatTorusSym.refl S n M K)
    (hH := A.adm) (hH' := B.adm) (RecCorr M A B) hloc hkept hlab
    (fun j Z Z' hZ => recCorr_parts M hZ) k hkK c c' hc⟩

end Corr

end Balaban.RootFSpine
