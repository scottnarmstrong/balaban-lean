/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairGs

/-!
# CrossI4a: the decoupled perturbed systems of two pairs on one torus

The fourth input of the replacement of P3 pp. 78-79: the solutions of the decoupled perturbed
system `δα = 𝒩_s(δα)` of Theorem I-4a (both modes; mode U with `α₀ = 0` is the decoupled
background problem of Theorem I-4b) for a pair `(C, H)` and for a second pair `(C', H')` on the same
torus agree on a block set `T`, and their corrections `δφ(δα) = G_s(α₀ + δα)(F_s - δα φ₀)` agree on
a set `Y ⊇ T`, when the decoupled Green's operators agree there (`Dec2.Gs_rows_cross_of_subset`),
the layers of `H` and `H'` agree on the rows `resSites x` of the sites `x ∈ T`, these rows lie in
`Y`, and the data `(α₀, φ₀, δΨ, f₁)` agree on `T` and its rows.  As for one pair
(`i4a_local_fp`) or two tori (`decSol_component_unique`), the proof compares the Picard iterations
from `0` of the two rescaled maps (`fixed_agree_of_step_transport`), with the landed contraction on
each side; no gluing of fields across the two index spaces is used.

* `layerIndex_cross`, `spacing_cross`, `resSites_cross`: the layer index, the spacing and the row
  sites of a site where the layers agree;
* `dirichletOperator_pot_apply_cross`: the entries of `H_D(α)`;
* `pertSource_apply_cross`: the source `F_s = Q* a δΨ + 𝔟(δΨ) + f₁` at a site whose stencil has
  the same layers (the collar sites adjacent to it are then the same);
* `Dec2.decFixed_rows_cross`: the rows of `𝒩(δφ(δα))` on `T` and the corrections on `Y`;
* `Dec2.decFixed_picard_cross`: the rescaled maps `Smap` on `T`;
* `Dec2.decFixed_component_cross`: two fixed points in the balls `c₆'`;
* `Dec2.decSol_value_cross`: the values of maps with the defining property of the analytic solution
  of Theorem I-4a (the form of `hSol`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Balaban.Polymer.TwoTorusStep

section Cross

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- The layer index agrees at a site of `Ω₁(H)` whose layers agree. -/
theorem layerIndex_cross {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n)) :
    H'.layerIndex x = H.layerIndex x := by
  obtain ⟨h1, h2, h3⟩ := H.layerIndex_spec hx
  exact H'.layerIndex_eq h1 h2 ((hlx _ h1 h2).1 h3)

theorem spacing_cross {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n)) :
    H'.spacing x = H.spacing x := by
  unfold GeneratingSet.spacing
  rw [layerIndex_cross hx hlx]

/-- The row sites (the block of the layer, the site and its neighbours) agree at a site of
`Ω₁(H)` whose layers agree. -/
theorem resSites_cross {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n)) :
    resSites H' x = resSites H x := by
  unfold resSites
  rw [layerIndex_cross hx hlx]
  rfl

/-- **The entries of `H_D(α)`** of two generating sets agree at two sites whose layers agree, for
potentials agreeing at the row site. -/
theorem dirichletOperator_pot_apply_cross (a : ℕ → ℝ) (ν : ℝ) {α : H.Ω 1 → ℂ}
    {α' : H'.Ω 1 → ℂ} {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1)
    (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hαx : α' ⟨x, hx'⟩ = α ⟨x, hx⟩) :
    dirichletOperator H' a ν α' ⟨x, hx'⟩ ⟨y, hy'⟩ = dirichletOperator H a ν α ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [← cutOperator_empty, ← cutOperator_empty]
  exact cutOperator_apply_cross a ν hx hx' hy hy' (fun μ => ⟨Iff.rfl, Iff.rfl⟩) (fun μ => Iff.rfl)
    hlx hly hαx

/-- A neighbour `z` of a site of `Ω₁` lies in the collar exactly when it is not in `Ω₁`. -/
theorem mem_collar_iff_of_adj {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {x z : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (hxz : Adj x z) : z ∈ collar G ↔ z ∉ G.Ω 1 :=
  ⟨fun h => ((mem_collar G).1 h).1, fun h => (mem_collar G).2 ⟨h, x, hx, hxz⟩⟩

/-- **The source `F_s = Q* a δΨ + 𝔟(δΨ) + f₁`** of two generating sets agrees at a site of both
`Ω₁` whose stencil has the same layers, for perturbations agreeing on the stencil and sources
agreeing at the site (the collar sites adjacent to the site are the neighbours outside `Ω₁`, the
same for both). -/
theorem pertSource_apply_cross {N : ℕ} (a : ℕ → ℝ) {δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {f₁' : H'.Ω 1 × Fin N → ℂ} {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1)
    (hnb : ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hΨ : ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) → δΨ y = δΨ' y)
    (hf : ∀ i, f₁ (⟨x, hx⟩, i) = f₁' (⟨x, hx'⟩, i)) (i : Fin N) :
    pertSource H' a δΨ' f₁' (⟨x, hx'⟩, i) = pertSource H a δΨ f₁ (⟨x, hx⟩, i) := by
  classical
  have hli := layerIndex_cross hx (hnb x (Or.inl rfl))
  have hcp : ∀ μ : Fin d, (x + Pi.single μ 1 ∈ collar H' ↔ x + Pi.single μ 1 ∈ collar H) := by
    intro μ
    rw [mem_collar_iff_of_adj hx' ⟨μ, Or.inl rfl⟩, mem_collar_iff_of_adj hx ⟨μ, Or.inl rfl⟩,
      mem_Ω_one_cross (hnb _ (Or.inr ⟨μ, Or.inl rfl⟩))]
  have hcm : ∀ μ : Fin d, (x - Pi.single μ 1 ∈ collar H' ↔ x - Pi.single μ 1 ∈ collar H) := by
    intro μ
    have hadj : Adj x (x - Pi.single μ 1) := ⟨μ, Or.inr (sub_add_cancel x _).symm⟩
    rw [mem_collar_iff_of_adj hx' hadj, mem_collar_iff_of_adj hx hadj,
      mem_Ω_one_cross (hnb _ (Or.inr ⟨μ, Or.inr rfl⟩))]
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply]
  rw [hli, hf i, hΨ x (Or.inl rfl)]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [hcp μ, hcm μ, hΨ _ (Or.inr ⟨μ, Or.inl rfl⟩), hΨ _ (Or.inr ⟨μ, Or.inr rfl⟩)]

/-- The stencil of a site lies in its row sites. -/
theorem stencil_subset_resSites {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {x y : CTorus d L N₁ m₁ K}
    (hy : y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) :
    y ∈ resSites G x := by
  rcases hy with rfl | ⟨μ, rfl | rfl⟩
  · exact mem_resSites_self _
  · exact add_single_mem_resSites G x μ
  · exact sub_single_mem_resSites G x μ

end Cross

namespace Dec2

section Pair

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {C C' : DecCover d L N₁ m₁ K}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **CrossI4a, rows.**  For two pairs `(C, H)`, `(C', H')` with `Dec2.CoverBase` (the same
constants) and parameters `|s_P|, |s'_P| ≤ e^κ`, let `T ⊆ Y` be sets of sites with: `Y` in
`Ω₁(H)` exactly where in `Ω₁(H')`; for both pairs, every interaction cube with a non-zero factor
lies inside `T` or avoids it and meets `Y` only inside `T`; the cubes inside `T` with a non-zero
factor are common, with the same factors, the same layers on their stencils and the same partition
functions (`hin`, `hin'`); at the sites `x ∈ T` the layers agree on the rows `resSites x`, which lie
in `Y` (`hres`).  Let the data agree: `α₀` on `T`, `φ₀` and `δΨ` on the rows of `T`, `f₁` on `T`,
and let candidate multipliers `δα`, `δα'` with `|α₀ + δα|₂, |α₀' + δα'|₂ ≤ γ₁/8` agree on `T`.  Then
the rows of `𝒩(δφ(δα))` agree on `T` and the corrections `δφ(δα)` agree on `Y`. -/
theorem decFixed_rows_cross {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG)
    (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams C} {s' : DecParams C'} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {Y T : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hYΩ : ∀ x ∈ Y, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd (extS C s) q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd (extS C' s') q = C.sProd (extS C s) q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd (extS C' s') q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd (extS C s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      (∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧ (y ∈ H.Ω 1 → y ∈ Y))
    (ιU : Bool) {α₀ : H.Ω 1 → ℂ} {α₀' : H'.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {f₁' : H'.Ω 1 × Fin N → ℂ}
    (hα0 : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α₀ ⟨x, hx⟩ = α₀' ⟨x, hx'⟩)
    (hφ0 : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, φ₀ y = φ₀' y)
    (hΨ : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, δΨ y = δΨ' y)
    (hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ∀ i, f₁ (⟨x, hx⟩, i) = f₁' (⟨x, hx'⟩, i))
    {δα : H.Ω 1 → ℂ} {δα' : H'.Ω 1 → ℂ}
    (hsm : Small H (α₀ + δα) (gamma1 d / 8)) (hsm' : Small H' (α₀' + δα') (gamma1 d / 8))
    (hδ : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      δα ⟨x, hx⟩ = δα' ⟨x, hx'⟩) :
    (∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      Nmap H' (dirichletOperator H' a ν α₀') ιU φ₀' (pertSource H' a δΨ' f₁')
          (dphi H' (decG C' H' a ν s') α₀' φ₀' (pertSource H' a δΨ' f₁') δα') ⟨x, hx'⟩ =
        Nmap H (dirichletOperator H a ν α₀) ιU φ₀ (pertSource H a δΨ f₁)
          (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα) ⟨x, hx⟩) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1), y ∈ Y → ∀ i : Fin N,
      dphi H' (decG C' H' a ν s') α₀' φ₀' (pertSource H' a δΨ' f₁') δα' (⟨y, hy'⟩, i) =
        dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (⟨y, hy⟩, i)) := by
  classical
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 C H S hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 C' H' S' hκ hM hs' N
  have hA := admPot_of_small hd0 hsm
  have hA' := admPot_of_small hd0 hsm'
  have hTΩ : ∀ x ∈ T, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1) := fun x hx => hYΩ x (hTY hx)
  -- the source on `T`
  have hFs : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ∀ i, pertSource H' a δΨ' f₁' (⟨x, hx'⟩, i) = pertSource H a δΨ f₁ (⟨x, hx⟩, i) :=
    fun x hx hx' hxT i => pertSource_apply_cross a hx hx'
      (fun y hy => (hres x hxT hx y (stencil_subset_resSites hy)).1)
      (fun y hy => hΨ x hxT hx y (stencil_subset_resSites hy)) (hf x hx hx' hxT) i
  -- the corrections on `Y`
  have hdphi : ∀ (y : CTorus d L N₁ m₁ K) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1), y ∈ Y →
      ∀ i : Fin N,
      dphi H' (decG C' H' a ν s') α₀' φ₀' (pertSource H' a δΨ' f₁') δα' (⟨y, hy'⟩, i) =
        dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (⟨y, hy⟩, i) := by
    intro y hy hy' hyY i
    unfold dphi decG
    rw [liftOp_mulVec, liftOp_mulVec]
    refine (Gs_rows_cross_of_subset S S' hA hA' hTΩ (hunit hA) (hunit' hA') hdich hdich' hrow
      hrow' hin hin' (fun x hx hx' hxT => ?_) (fun x hx hx' hxT => ?_) hy hy' hyY).symm
    · simp only [Pi.add_apply]
      rw [hα0 x hx hx' hxT, hδ x hx hx' hxT]
    · simp only [Fsrc]
      rw [hFs x hx hx' hxT i, hδ x hx hx' hxT, hφ0 x hxT hx x (mem_resSites_self x)]
  refine ⟨fun x hx hx' hxT => ?_, hdphi⟩
  have hlx := (hres x hxT hx x (mem_resSites_self x)).1
  have hR : resSites H' x = resSites H x := resSites_cross hx hlx
  have hΩr : ∀ y ∈ resSites H x, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1) := fun y hy =>
    mem_Ω_one_cross (hres x hxT hx y hy).1
  obtain ⟨ι, hι⟩ : ∃ ι : H.Ω 1 → H'.Ω 1, ∀ w : H.Ω 1, ι w =
      if h : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1 then ⟨w, h⟩ else ⟨x, hx'⟩ := ⟨_, fun _ => rfl⟩
  have hιv : ∀ (w : H.Ω 1) (hw : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1), ι w = ⟨w, hw⟩ := by
    intro w hw
    rw [hι, dite_eq_left hw]
  rw [Nmap_explicit, Nmap_explicit]
  refine Nexp_transport ιU (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ K) ∈ resSites H x)
    (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ K) ∈ resSites H' x) ι
    (fun y₁ y₂ h₁ h₂ h => ?_) (fun y hy => ?_) (fun y' hy' => ?_) (fun y hy => ?_)
    (fun y hy => ?_) (fun y hy => ?_) (fun i => ?_) (fun i => hFs x hx hx' hxT i)
    (fun i => hdphi x hx hx' (hTY hxT) i) (fun y hy hne => ?_)
  · rw [hιv y₁ ((hΩr _ h₁).1 y₁.2), hιv y₂ ((hΩr _ h₂).1 y₂.2)] at h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  · show ((ι y : H'.Ω 1) : CTorus d L N₁ m₁ K) ∈ resSites H' x
    rw [hιv y ((hΩr _ hy).1 y.2), hR]; exact hy
  · have hy'' : (y' : CTorus d L N₁ m₁ K) ∈ resSites H x := by
      rw [← hR]; exact hy'
    exact ⟨⟨y', (hΩr _ hy'').2 y'.2⟩, hy'', hιv _ y'.2⟩
  · by_contra hne
    exact hy (mem_resSites_of_entry_ne_zero (x := ⟨x, hx⟩) hne)
  · by_contra hne
    exact hy (mem_resSites_of_entry_ne_zero (G := H') (x := ⟨x, hx'⟩) hne)
  · rw [hιv y ((hΩr _ hy).1 y.2)]
    exact dirichletOperator_pot_apply_cross a ν hx hx' y.2 _ hlx (hres x hxT hx y hy).1
      (hα0 x hx hx' hxT).symm
  · exact congrFun (hφ0 x hxT hx x (mem_resSites_self x)).symm i
  · have hyΩ' := (hΩr _ hy).1 y.2
    rw [hιv y hyΩ']
    refine ⟨fun i => (congrFun (hφ0 x hxT hx y hy) i).symm, fun i => ?_⟩
    exact hdphi y y.2 hyΩ' ((hres x hxT hx y hy).2 y.2) i

/-- **CrossI4a, the rescaled maps.**  Under the hypotheses of `decFixed_rows_cross` on the
geometry and the data, with `|α₀|₂ ≤ δ₀`, `|α₀'|₂ ≤ δ₀'` and `δ₀ + ρ, δ₀' + ρ ≤ γ₁/8`, the rescaled
maps `ξ ↦ ℓ² 𝒩(δφ(ξ/ℓ²))` of the two pairs agree on `T` at arguments `‖ξ‖_∞, ‖ξ'‖_∞ ≤ ρ` that
agree on `T`. -/
theorem decFixed_picard_cross {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG)
    (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams C} {s' : DecParams C'} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {Y T : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hYΩ : ∀ x ∈ Y, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd (extS C s) q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd (extS C' s') q = C.sProd (extS C s) q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd (extS C' s') q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd (extS C s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      (∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧ (y ∈ H.Ω 1 → y ∈ Y))
    (ιU : Bool) {α₀ : H.Ω 1 → ℂ} {α₀' : H'.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {f₁' : H'.Ω 1 × Fin N → ℂ}
    (hα0 : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α₀ ⟨x, hx⟩ = α₀' ⟨x, hx'⟩)
    (hφ0 : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, φ₀ y = φ₀' y)
    (hΨ : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, δΨ y = δΨ' y)
    (hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ∀ i, f₁ (⟨x, hx⟩, i) = f₁' (⟨x, hx'⟩, i))
    {δ₀ δ₀' ρ : ℝ} (hα0s : Small H α₀ δ₀) (hα0s' : Small H' α₀' δ₀')
    (hρ : δ₀ + ρ ≤ gamma1 d / 8) (hρ' : δ₀' + ρ ≤ gamma1 d / 8)
    {ξ : H.Ω 1 → ℂ} {ξ' : H'.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hξ' : ∀ x, ‖ξ' x‖ ≤ ρ)
    (hξξ : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ξ ⟨x, hx⟩ = ξ' ⟨x, hx'⟩) :
    ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      Smap H (decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀
          (pertSource H a δΨ f₁) ξ ⟨x, hx⟩ =
        Smap H' (decG C' H' a ν s') (dirichletOperator H' a ν α₀') ιU α₀' φ₀'
          (pertSource H' a δΨ' f₁') ξ' ⟨x, hx'⟩ := by
  intro x hx hx' hxT
  have hsm : Small H (α₀ + toAlpha H ξ) (gamma1 d / 8) := fun z =>
    ((Small.add hα0s (small_toAlpha H ξ hξ)) z).trans hρ
  have hsm' : Small H' (α₀' + toAlpha H' ξ') (gamma1 d / 8) := fun z =>
    ((Small.add hα0s' (small_toAlpha H' ξ' hξ')) z).trans hρ'
  have hsp : ∀ (z : CTorus d L N₁ m₁ K), z ∈ T → z ∈ H.Ω 1 → H'.spacing z = H.spacing z :=
    fun z hzT hz => spacing_cross hz (hres z hzT hz z (mem_resSites_self z)).1
  have hα : ∀ (z : CTorus d L N₁ m₁ K) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1), z ∈ T →
      toAlpha H ξ ⟨z, hz⟩ = toAlpha H' ξ' ⟨z, hz'⟩ := fun z hz hz' hzT => by
    unfold toAlpha
    simp only
    rw [hξξ z hz hz' hzT, hsp z hzT hz]
  unfold Smap
  simp only
  rw [hsp x hxT hx]
  congr 1
  exact ((decFixed_rows_cross hF S S' hκ hM hs hs' hTY hYΩ hdich hdich' hrow hrow' hin hin' hres
    ιU hα0 hφ0 hΨ hf hsm hsm' hα).1 x hx hx' hxT).symm

/-- **CrossI4a, component comparison.**  Let `δα`, `δα'` be fixed points of `Dec2.DecFixed` in the
balls `|δα|₂ ≤ c₆'` for data with the hypotheses `DecHyp` of Theorem I-4a for the two pairs (with
`δ₀, δ₁, δ₀', δ₁' ≤ δ*'`), under the hypotheses of `decFixed_rows_cross` on the geometry and the
data.  Then the multipliers agree on `T` and the corrections `δφ` agree on `Y`. -/
theorem decFixed_component_cross {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG)
    (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams C} {s' : DecParams C'} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {Y T : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hYΩ : ∀ x ∈ Y, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd (extS C s) q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd (extS C' s') q = C.sProd (extS C s) q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd (extS C' s') q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd (extS C s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      (∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧ (y ∈ H.Ω 1 → y ∈ Y))
    (ιU : Bool) {α₀ : H.Ω 1 → ℂ} {α₀' : H'.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {f₁' : H'.Ω 1 × Fin N → ℂ} {δ₀ δ₁ δ₀' δ₁' : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (Hh' : DecHyp H' a ν ιU α₀' φ₀' δΨ' f₁' δ₀' δ₁')
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁' : δ₁' ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hα0 : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α₀ ⟨x, hx⟩ = α₀' ⟨x, hx'⟩)
    (hφ0 : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, φ₀ y = φ₀' y)
    (hΨ : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, δΨ y = δΨ' y)
    (hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ∀ i, f₁ (⟨x, hx⟩, i) = f₁' (⟨x, hx'⟩, i))
    {δα : H.Ω 1 → ℂ} {δα' : H'.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C' H' a ν s' ιU α₀' φ₀' (pertSource H' a δΨ' f₁') δα')
    (hsm' : Small H' δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      δα' ⟨x, hx'⟩ = δα ⟨x, hx⟩) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1), y ∈ Y → ∀ i : Fin N,
      dphi H' (decG C' H' a ν s') α₀' φ₀' (pertSource H' a δΨ' f₁') δα' (⟨y, hy'⟩, i) =
        dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (⟨y, hy⟩, i)) := by
  classical
  have hd0 : 0 < d := by have := S.hd; omega
  have hBG := hF.2.1
  set Bc : ℝ := famConst d L BG κ with hBc
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ Bc := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  have hC' := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh'.δ₀_nn Hh'.δ₁_nn hδ₀' hδ₁'
  obtain ⟨⟨hfam, -⟩, -⟩ := hF.2.2 C H S hκ hM hs N
  obtain ⟨⟨hfam', -⟩, -⟩ := hF.2.2 C' H' S' hκ hM hs' N
  obtain ⟨ξ, -, -, hξuniq, hit⟩ := smap_fixed_iterates hfam Hh.setup hC
  obtain ⟨ξ', -, -, hξuniq', hit'⟩ := smap_fixed_iterates hfam' Hh'.setup hC'
  have e1 : toAlpha H ξ = δα := toAlpha_eq_of_decFixed2 hC.ρ_nn hξuniq hfix hsm
  have e2 : toAlpha H' ξ' = δα' := toAlpha_eq_of_decFixed2 hC.ρ_nn hξuniq' hfix' hsm'
  have hpoly : δ₀ + c6' d L N Bc Γ ≤ Γ := by linarith [hC.poly, hC.ρ_nn]
  have hpoly' : δ₀' + c6' d L N Bc Γ ≤ Γ := by linarith [hC'.poly, hC'.ρ_nn]
  have hTΩ : ∀ x ∈ T, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1) := fun x hx => hYΩ x (hTY hx)
  -- the transport of the sites of `T`
  by_cases hne : Nonempty (H'.Ω 1)
  swap
  · exact ⟨fun x _ hx' _ => absurd ⟨⟨x, hx'⟩⟩ hne, fun y _ hy' _ => absurd ⟨⟨y, hy'⟩⟩ hne⟩
  obtain ⟨v₀⟩ := hne
  obtain ⟨ι, hι⟩ : ∃ ι : H.Ω 1 → H'.Ω 1, ∀ w : H.Ω 1, ι w =
      if h : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1 then ⟨w, h⟩ else v₀ := ⟨_, fun _ => rfl⟩
  have hιv : ∀ (w : H.Ω 1) (hw : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1), ι w = ⟨w, hw⟩ := by
    intro w hw
    rw [hι, dite_eq_left hw]
  -- the iterations agree on `T`
  have hagreeξ : ∀ w : H.Ω 1, (w : CTorus d L N₁ m₁ K) ∈ T → ξ w = ξ' (ι w) := by
    refine fixed_agree_of_step_transport ι
      (T := fun w : H.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ T)
      (fun u v hu hv huv w hw => ?_) hit hit' hC.ρ_nn
    rw [hιv w ((hTΩ w hw).1 w.2)]
    refine decFixed_picard_cross hF S S' hκ hM hs hs' hTY hYΩ hdich hdich' hrow hrow' hin hin'
      hres ιU hα0 hφ0 hΨ hf Hh.alpha0 Hh'.alpha0 hpoly hpoly' hu hv
      (fun z hz hz' hzT => ?_) w w.2 _ hw
    have := huv ⟨z, hz⟩ hzT
    rw [hιv ⟨z, hz⟩ hz'] at this
    exact this
  have hsp : ∀ (z : CTorus d L N₁ m₁ K), z ∈ T → z ∈ H.Ω 1 → H'.spacing z = H.spacing z :=
    fun z hzT hz => spacing_cross hz (hres z hzT hz z (mem_resSites_self z)).1
  have hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      δα ⟨x, hx⟩ = δα' ⟨x, hx'⟩ := by
    intro x hx hx' hxT
    rw [← e1, ← e2]
    unfold toAlpha
    simp only
    rw [hagreeξ ⟨x, hx⟩ hxT, hιv ⟨x, hx⟩ hx', hsp x hxT hx]
  -- the corrections on `Y`
  have hsmA : Small H (α₀ + δα) Γ := fun z => ((Small.add Hh.alpha0 hsm) z).trans hpoly
  have hsmB : Small H' (α₀' + δα') Γ := fun z => ((Small.add Hh'.alpha0 hsm') z).trans hpoly'
  have hrows := decFixed_rows_cross hF S S' hκ hM hs hs' hTY hYΩ hdich hdich' hrow hrow' hin hin'
    hres ιU hα0 hφ0 hΨ hf hsmA hsmB hα
  exact ⟨fun x hx hx' hxT => (hα x hx hx' hxT).symm, hrows.2⟩

/-- **CrossI4a, values.**  Let `Sol`, `Sol'` be maps with the defining property of the analytic
solution of Theorem I-4a for the two pairs (the form of `Dec2.i4a_analytic` and of the hypothesis
`hSol` of `point_facts_fl`): on parameters with `|s_P| < e^κ` and data `e` with the strict
inequalities `StrictDataM`, `(Sol (s, e)).1 = δφ((Sol (s, e)).2)` and `(Sol (s, e)).2` is a fixed
point of `Dec2.DecFixed` in the ball `c₆'`, with the bounds and the uniqueness.  Under the
hypotheses of `decFixed_rows_cross` on the geometry and on the data `e = (φ₀, α₀, δΨ, f₁)`, `e'`,
the multipliers `(Sol p).2` agree on `T` and the corrections `(Sol p).1` agree on `Y`. -/
theorem decSol_value_cross {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG)
    (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (ιU : Bool) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {Sol : DecParams C × Edat H N → (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)}
    {Sol' : DecParams C' × Edat H' N → (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ)}
    (hSol : ∀ p : DecParams C × Edat H N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM H N ιU δ₀ δ₁ p.2 →
        (Sol p).1 = dphi H (decG C H a ν p.1) p.2.2.1 p.2.1
          (pertSource H a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        DecFixed C H a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource H a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small H (Sol p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small H (Sol p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds H (Sol p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : H.Ω 1 → ℂ, Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          DecFixed C H a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource H a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : DecParams C' × Edat H' N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM H' N ιU δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi H' (decG C' H' a ν p.1) p.2.2.1 p.2.1
          (pertSource H' a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        DecFixed C' H' a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource H' a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small H' (Sol' p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small H' (Sol' p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds H' (Sol' p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : H'.Ω 1 → ℂ, Small H' δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          DecFixed C' H' a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource H' a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {s : DecParams C} {s' : DecParams C'} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ) {e : Edat H N} {e' : Edat H' N}
    (he : StrictDataM H N ιU δ₀ δ₁ e) (he' : StrictDataM H' N ιU δ₀ δ₁ e')
    {Y T : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hYΩ : ∀ x ∈ Y, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd (extS C s) q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd (extS C' s') q = C.sProd (extS C s) q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd (extS C' s') q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd (extS C s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      (∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧ (y ∈ H.Ω 1 → y ∈ Y))
    (hα0 : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      e.2.1 ⟨x, hx⟩ = e'.2.1 ⟨x, hx'⟩)
    (hφ0 : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, e.1 y = e'.1 y)
    (hΨ : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, e.2.2.1 y = e'.2.2.1 y)
    (hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ∀ i, e.2.2.2 (⟨x, hx⟩, i) = e'.2.2.2 (⟨x, hx'⟩, i)) :
    (∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      (Sol' (s', e')).2 ⟨x, hx'⟩ = (Sol (s, e)).2 ⟨x, hx⟩) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1), y ∈ Y → ∀ i : Fin N,
      (Sol' (s', e')).1 (⟨y, hy'⟩, i) = (Sol (s, e)).1 (⟨y, hy⟩, i)) := by
  set Bc : ℝ := famConst d L BG κ with hBc
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hle1 : δ₀ ≤ 1 := hδ₀.trans (by
    have := (min_le_right (min (cTau' d L N Bc / 3) (Γ / 4))
      (min (min 1 (c6' d L N Bc Γ / (2 * cN' d L N Bc))) (cTau' d L N Bc / (3 * cF d L))))
    exact this.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have Hh := StrictDataM.hyp S.toOpSetting.toGreen h0 h1 hle1 he
  have Hh' := StrictDataM.hyp S'.toOpSetting.toGreen h0 h1 hle1 he'
  obtain ⟨hfld, hfix, hsm, -⟩ := hSol (s, e) hs he
  obtain ⟨hfld', hfix', hsm', -⟩ := hSol' (s', e') hs' he'
  obtain ⟨hα, hcorr⟩ := decFixed_component_cross hF S S' hκ hM (fun P => (hs P).le)
    (fun P => (hs' P).le) hTY hYΩ hdich hdich' hrow hrow' hin hin' hres ιU Hh Hh' hδ₀ hδ₁ hδ₀ hδ₁
    hα0 hφ0 hΨ hf hfix hsm hfix' hsm'
  refine ⟨hα, fun y hy hy' hyY i => ?_⟩
  rw [hfld, hfld']
  exact hcorr y hy hy' hyY i

end Pair

end Dec2

end Balaban.Localization
