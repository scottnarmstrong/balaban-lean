/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfGauss

/-!
# The small-field factor on the whole torus

A6-3 (a) for the empty cut `Y = univ` (`notes/phase1/SPINE-PLAN.md`): the restricted
objects of the class (`ℰ_k`, `ℱ_k`, `ℛ^{(k)}`) are sums over polymers `X ⊂ Y^≈`; on the whole torus
every polymer qualifies, and the sums are the densities of Def-6:

* `EresJ2_univ`, `EresK2_univ`: `ℰ^{(j)}(univ) = Edens_j(ψ^{(j)}_k, h)` minus the full double sum of
  the correction `corrSum`, so `F_{k_f} = ∑_{j ≤ k} Edens` (FINALPHYS3 §8); the correction vanishes
  for symmetric coefficients (`EresJ2_univ_of_symm`, P5 (1.8)), which `CorrCoef` does not state;
* `Fres_univ`: `ℱ_k = ⟨g, φ̄_k⟩ + ∑_{j ≤ k} Floc_j` with the `Floc` of Def-6;
* `Rres_univ`: `ℛ^{(k)}` is the sum over all polymers of `𝒟_k`.
-/

@[expose] public section

open MeasureTheory Matrix Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6

namespace Balaban.RootFSpine

section Univ

open Classical

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
  (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

theorem sset_univ : C.sset Set.univ = Set.univ := by
  ext x; simp [SFCtx.sset, sfSet]

omit [NeZero S.L] in
theorem thickY_univ : thickY R (Set.univ : Set (Torus S.d (n k))) = Set.univ :=
  Set.univ_subset_iff.1 (Set.univ_subset_iff.2 rfl |>.trans (subset_nbhd _ _))

theorem alignedIn_univ (j : ℕ) :
    C.alignedIn j Set.univ = Finset.univ.filter (Localization.Aligned (S.L ^ j)) := by
  classical
  ext y; simp [SFCtx.alignedIn, sset_univ]

theorem alignedIn_thickY_univ (j : ℕ) :
    C.alignedIn j (thickY R (Set.univ : Set (Torus S.d (n k)))) =
      Finset.univ.filter (Localization.Aligned (S.L ^ j)) := by
  rw [thickY_univ]; exact alignedIn_univ C j

/-- **`ℰ^{(j)}` on the whole torus is `Edens` up to the correction sum** (A6-3 (a), `F_{k_f} =
∑_j Edens`, FINALPHYS3 §8): for the cut `Y = univ` the first sum of `EresJ2` is the density
`Edens` of the terms `ℰ^{(j)}` at the field `ψ^{(j)}_k`, and the second is the full double sum
of `corrSum`. -/
theorem EresJ2_univ (j : ℕ) :
    EresJ2 C vc Set.univ ψk hv j =
      Def6.Edens C.m₀ (C.sf.Tm C.N₁) j (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv)) -
        corrSum (fun y x => vc.v1 j (Def6.unlift j (x - y))) (fun y x => vc.v2 j (Def6.unlift j (x - y)))
          (nuIdeal S.L k (C.sf.ν k) j) (Finset.univ.filter (Localization.Aligned (S.L ^ j)))
          (Finset.univ.filter (Localization.Aligned (S.L ^ j))) (C.psiJ Set.univ ψk hv j) (hC hv) := by
  classical
  unfold EresJ2
  rw [alignedIn_univ, alignedIn_thickY_univ, thickY_univ, sset_univ]
  congr 1
  unfold Def6.Edens Def6.Eloc
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  ext X
  simp [Def6.polysAt]

/-- **`ℰ_k` on the whole torus**: `F_{k_f} = ∑_{j ≤ k} Edens` up to the correction sums
(FINALPHYS3 §8). -/
theorem EresK2_univ :
    EresK2 C vc Set.univ ψk hv =
      ∑ j ∈ Finset.Icc 1 k,
        (Def6.Edens C.m₀ (C.sf.Tm C.N₁) j (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv)) -
          corrSum (fun y x => vc.v1 j (Def6.unlift j (x - y)))
            (fun y x => vc.v2 j (Def6.unlift j (x - y)))
            (nuIdeal S.L k (C.sf.ν k) j) (Finset.univ.filter (Localization.Aligned (S.L ^ j)))
            (Finset.univ.filter (Localization.Aligned (S.L ^ j))) (C.psiJ Set.univ ψk hv j)
            (hC hv)) :=
  Finset.sum_congr rfl fun j _ => EresJ2_univ C vc ψk hv j

/-- With symmetric coefficients the correction sum of the whole torus vanishes (P5 (1.8): "it
vanishes after the full torus double sum"), and `ℰ^{(j)}` is `Edens`. -/
theorem EresJ2_univ_of_symm (j : ℕ)
    (h1 : ∀ y x : Localization.CTorus S.d S.L C.N₁ m₁ k,
      vc.v1 j (Def6.unlift j (x - y)) = vc.v1 j (Def6.unlift j (y - x)))
    (h2 : ∀ y x : Localization.CTorus S.d S.L C.N₁ m₁ k,
      vc.v2 j (Def6.unlift j (x - y)) = vc.v2 j (Def6.unlift j (y - x))) :
    EresJ2 C vc Set.univ ψk hv j =
      Def6.Edens C.m₀ (C.sf.Tm C.N₁) j (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv)) := by
  rw [EresJ2_univ, corrSum_self_eq_zero (v₁ := fun y x => vc.v1 j (Def6.unlift j (x - y)))
    (v₂ := fun y x => vc.v2 j (Def6.unlift j (x - y))) h1 h2, sub_zero]

theorem MresJ_univ (j : ℕ) (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    C.MresJ Set.univ ψk hv g j x =
      Def6.Mloc C.m₀ (C.sf.Tm C.N₁) j x (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv))
        (sfG C.geo C.hnn C.hkK C.hT g) := by
  unfold SFCtx.MresJ Def6.Mloc
  rw [thickY_univ, sset_univ]
  have : {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
      Def6.IsPolyDom C.m₀ j X ∧ x ∈ X ∧ X ⊆ Set.univ} = Def6.polysAt C.m₀ j x := by
    ext X; simp [Def6.polysAt]
  rw [this]

/-- **The source term on the whole torus**: `ℱ_k = ⟨g, φ̄_k⟩ + ∑_{j ≤ k} Floc` with
`Floc = ⟨g, ℳ^{(j)}⟩` of Def-6. -/
theorem Fres_univ :
    C.Fres Set.univ ψk hv g =
      (∑ x : BgT C.geo k, ∑ i : Fin N,
          g (bgToFine C.geo C.hnn C.hkK x, i) * (((C.phiBar Set.univ ψk hv x) i : ℝ) : ℂ)) +
        ∑ j ∈ Finset.Icc 1 k,
          Def6.Floc C.m₀ (C.sf.Tm C.N₁) j (C.psiJ Set.univ ψk hv j) (Def6.constFld (hC hv))
            (sfG C.geo C.hnn C.hkK C.hT g) := by
  unfold SFCtx.Fres
  have hb : C.bgSet (Set.univ : Set (Torus S.d (n k))) = Finset.univ := by
    ext x; simp [SFCtx.bgSet]
  rw [hb]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Def6.Floc
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [sset_univ, Set.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MresJ_univ]

open Classical in
/-- The remainder term on the whole torus: the sum over all polymers of `𝒟_k`. -/
theorem Rres_univ :
    C.Rres Set.univ ψk hv g =
      ∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁), ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
          Def6.IsPolyDom C.m₀ k X},
        C.sf.Rt C.N₁ nn X (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv))
          (sfG C.geo C.hnn C.hkK C.hT g) := by
  unfold SFCtx.Rres
  rw [sset_univ]
  simp only [Set.subset_univ, and_true]

end Univ
end Balaban.RootFSpine
