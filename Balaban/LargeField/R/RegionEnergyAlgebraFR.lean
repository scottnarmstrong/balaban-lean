/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionShrink
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The region-shrink identity for `Rres` and `Fres` (P5 (1.10)-(1.17))

For `Y' ⊆ Y` the landed small-field terms `Rres` and `Fres` change by exact finite-sum
differences, in the style of `RegionShrink.shrink_identity`.

* `Rres_shrink`: the summands of `Rres` do not depend on `Y`; `Rres Y - Rres Y'` is the sum over
  the admissible polymers `X ⊆ sset Y`, `X ⊄ sset Y'`, for each `nn`.  All sums are finite
  (`polyUniv`).
* `Fres_shrink`: `Fres` depends on `Y` also through `phiBar Y`, `MresJ Y` (via `psiJ Y` and the
  thickened region); the identity keeps this dependence as explicit re-evaluation terms
  `Σ_{x ∈ bgSet Y'} (f_Y - f_{Y'})` and `Σ_{x ∈ sset Y'} (m_Y - m_{Y'})`.

Nothing here is a bound on any term.
-/

@[expose] public section

open Finset

namespace Balaban.LargeField.RegionShrink

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField.Def7 Balaban.LargeField.Def7v2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
  (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- The summand of `Rres` for the index `nn` and polymer `X` (it does not depend on `Y`). -/
noncomputable def RresTerm (nn : ℕ) (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) : ℂ :=
  C.sf.Rt C.N₁ nn X (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv))
    (sfG C.geo C.hnn C.hkK C.hT g)

open Classical in
/-- The finsum over polymers supported in `A` is a finite sum over the universe. -/
theorem finsum_polys_eq (A : Set (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (F : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ) :
    ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
      Def6.IsPolyDom C.m₀ k X ∧ X ⊆ A}, F X =
      ∑ X ∈ (polyUniv C k).filter (fun X => X ⊆ A), F X := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext X
  simp [polyUniv]

open Classical in
/-- **Region shrink for `Rres`**: for `Y' ⊆ Y`, `Rres Y - Rres Y'` is, for each `nn`, the sum over
admissible polymers `X ⊆ sset Y` with `X ⊄ sset Y'` of the (`Y`-independent) summand. -/
theorem Rres_shrink (Y Y' : Set (Torus S.d (n k))) (hY : Y' ⊆ Y) :
    C.Rres Y ψk hv g - C.Rres Y' ψk hv g =
      ∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁),
        ∑ X ∈ (polyUniv C k).filter (fun X => X ⊆ C.sset Y ∧ ¬ X ⊆ C.sset Y'),
          RresTerm C ψk hv g nn X := by
  unfold SFCtx.Rres
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun nn _ => ?_
  have h1 := finsum_polys_eq C (C.sset Y) (RresTerm C ψk hv g nn)
  have h2 := finsum_polys_eq C (C.sset Y') (RresTerm C ψk hv g nn)
  change (∑ᶠ X ∈ {X | Def6.IsPolyDom C.m₀ k X ∧ X ⊆ C.sset Y}, RresTerm C ψk hv g nn X) -
      (∑ᶠ X ∈ {X | Def6.IsPolyDom C.m₀ k X ∧ X ⊆ C.sset Y'}, RresTerm C ψk hv g nn X) = _
  have hsub : C.sset Y' ⊆ C.sset Y := sset_mono C hY
  rw [h1, h2, sub_eq_iff_eq_add', ← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext X
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hu, hA⟩
      by_cases hB : X ⊆ C.sset Y'
      · exact Or.inl ⟨hu, hB⟩
      · exact Or.inr ⟨hu, hA, hB⟩
    · rintro (⟨hu, hA⟩ | ⟨hu, hA, _⟩)
      · exact ⟨hu, fun a ha => hsub (hA ha)⟩
      · exact ⟨hu, hA⟩
  · rw [Finset.disjoint_left]
    intro X h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h2.2.2 h1.2

/-- The summand of the background part of `Fres` at the fine site `x`:
`Σ_i g(x, i) φ̄(x)_i`, with the background `φ̄ = phiBar Y` of the region `Y`. -/
noncomputable def FresBgTerm (Y : Set (Torus S.d (n k))) (x : BgT C.geo k) : ℂ :=
  ∑ i : Fin N, g (bgToFine C.geo C.hnn C.hkK x, i) * (((C.phiBar Y ψk hv x) i : ℝ) : ℂ)

/-- The summand of the `ℳ` part of `Fres` at the site `x` and scale `j`:
`Σ_i G(x, i) ℳ^{(j)}(x, Y)_i` (the polymer sum `MresJ Y` depends on `Y`). -/
noncomputable def FresMTerm (Y : Set (Torus S.d (n k))) (j : ℕ)
    (x : Localization.CTorus S.d S.L C.N₁ m₁ k) : ℂ :=
  ∑ i : Fin N, sfG C.geo C.hnn C.hkK C.hT g x i * C.MresJ Y ψk hv g j x i

open Classical in
/-- **Region shrink for `Fres`** (`Y' ⊆ Y`).  `Fres Y - Fres Y'` is the sum of
* the background sum over the fine sites `bgSet Y \ bgSet Y'` (at `Y`),
* the re-evaluation of the background on `bgSet Y'` (`φ̄` depends on the region),
* the `ℳ` sum over the sites `sset Y \ sset Y'` (at `Y`), over `j = 1, …, k`,
* the re-evaluation of `ℳ^{(j)}` on `sset Y'` (`MresJ Y` depends on the region through `psiJ Y`
  and `thickY R Y`), over `j = 1, …, k`.
The re-evaluation terms are not bounded here. -/
theorem Fres_shrink (Y Y' : Set (Torus S.d (n k))) (hY : Y' ⊆ Y) :
    C.Fres Y ψk hv g - C.Fres Y' ψk hv g =
      ∑ x ∈ C.bgSet Y \ C.bgSet Y', FresBgTerm C ψk hv g Y x +
      ∑ x ∈ C.bgSet Y', (FresBgTerm C ψk hv g Y x - FresBgTerm C ψk hv g Y' x) +
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Y ∧ x ∉ C.sset Y' then FresMTerm C ψk hv g Y j x else 0) +
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Y' then FresMTerm C ψk hv g Y j x - FresMTerm C ψk hv g Y' j x else 0) := by
  have hbg : C.bgSet Y' ⊆ C.bgSet Y := by
    intro x hx
    simp only [SFCtx.bgSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hY hx
  have hsub : C.sset Y' ⊆ C.sset Y := sset_mono C hY
  have e1 : ∑ x ∈ C.bgSet Y, FresBgTerm C ψk hv g Y x -
      ∑ x ∈ C.bgSet Y', FresBgTerm C ψk hv g Y' x =
      ∑ x ∈ C.bgSet Y \ C.bgSet Y', FresBgTerm C ψk hv g Y x +
      ∑ x ∈ C.bgSet Y', (FresBgTerm C ψk hv g Y x - FresBgTerm C ψk hv g Y' x) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_sdiff hbg]
    ring
  have e2 : ∀ j x, (if x ∈ C.sset Y then FresMTerm C ψk hv g Y j x else 0) -
      (if x ∈ C.sset Y' then FresMTerm C ψk hv g Y' j x else 0) =
      (if x ∈ C.sset Y ∧ x ∉ C.sset Y' then FresMTerm C ψk hv g Y j x else 0) +
      (if x ∈ C.sset Y' then FresMTerm C ψk hv g Y j x - FresMTerm C ψk hv g Y' j x else 0) := by
    intro j x
    by_cases h1 : x ∈ C.sset Y'
    · have h2 : x ∈ C.sset Y := hsub h1
      simp [h1, h2]
    · by_cases h2 : x ∈ C.sset Y <;> simp [h1, h2]
  unfold SFCtx.Fres
  change (∑ x ∈ C.bgSet Y, FresBgTerm C ψk hv g Y x +
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        if x ∈ C.sset Y then FresMTerm C ψk hv g Y j x else 0) -
    (∑ x ∈ C.bgSet Y', FresBgTerm C ψk hv g Y' x +
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        if x ∈ C.sset Y' then FresMTerm C ψk hv g Y' j x else 0) = _
  have e3 : ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Y then FresMTerm C ψk hv g Y j x else 0) -
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Y' then FresMTerm C ψk hv g Y' j x else 0) =
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Y ∧ x ∉ C.sset Y' then FresMTerm C ψk hv g Y j x else 0) +
      ∑ j ∈ Finset.Icc 1 k, ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ k,
        (if x ∈ C.sset Y' then FresMTerm C ψk hv g Y j x - FresMTerm C ψk hv g Y' j x else 0) := by
    simp_rw [← Finset.sum_sub_distrib, e2, Finset.sum_add_distrib]
  linear_combination e1 + e3

end Balaban.LargeField.RegionShrink
