/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.RootPavingMap
public import Balaban.SmallField.Def6BridgeGeom

/-!
# The mark fibre on `sitesOf`

`markFibre_sitesOf`: at the whole lattice (`Ω = univ`, level `K`), the map `T ↦ sitesOf T` from sets
of cubes to sets of sites has, on the active cube sets (those with `sitesOf T` a polymer), the
properties needed to regroup mark terms indexed by `T` into terms indexed by polymers `X`: the
image is a legal polymer (`IsDj`) of size exactly `dExt T`, the map is injective, and it commutes
with the paving symmetries.  Hence a family `e T` bounded by `B exp(-λ dExt T)` and supported on the
active sets regroups, with at most one term per `X`, into terms bounded by `B exp(-λ sizeJ X)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- **The mark fibre on `sitesOf`.**  Let `L^{m₀} ∣ N₁`.
(1) For every cube set `T` with `sitesOf T` a polymer, `sitesOf T` is `IsDj` and
`dExt T = sizeJ (sitesOf T)`.
(2) `T ↦ sitesOf T` is injective.
(3) `sitesOf (r • T) = r '' sitesOf T` for the paving symmetries `r`.
(4) For `e : Finset 𝔅 → E` supported on the active sets with `‖e T‖ ≤ B exp(-λ dExt T)`,
the regrouped term `∑_{sitesOf T = X} e T` has norm at most `B exp(-λ sizeJ X)` for every `X`
(no rate is lost), it equals `e T` when `X = sitesOf T`, and the total sum of `e` is the sum of the
regrouped terms over the image of `sitesOf`. -/
theorem markFibre_sitesOf (hN : L ^ m₀ ∣ N₁) :
    (∀ T : Finset 𝔅, IsPolyDom m₀ K (sitesOf T) →
      IsDj m₀ K (sitesOf T) ∧ dExt T = sizeJ m₀ K (sitesOf T)) ∧
    (∀ T T' : Finset 𝔅, sitesOf T = sitesOf T' → T = T') ∧
    (∀ {r : Equiv.Perm (CTorus d L N₁ m₁ K)},
      r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K →
      ∀ T : Finset 𝔅, sitesOf (cubeAct r T) = r '' sitesOf T) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] (e : Finset 𝔅 → E) (B lam : ℝ), 0 ≤ B →
      (∀ T, IsPolyDom m₀ K (sitesOf T) → ‖e T‖ ≤ B * Real.exp (-lam * dExt T)) →
      (∀ T, ¬ IsPolyDom m₀ K (sitesOf T) → e T = 0) →
      (∀ X : Set (CTorus d L N₁ m₁ K), ∀ T : Finset 𝔅, sitesOf T = X →
        (Finset.univ.filter fun T' : Finset 𝔅 => sitesOf T' = X) = {T}) ∧
      (∀ X : Set (CTorus d L N₁ m₁ K),
        ‖∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e T‖ ≤
          B * Real.exp (-lam * sizeJ m₀ K X)) ∧
      ∑ T, e T = ∑ X ∈ Finset.univ.image (fun T : Finset 𝔅 => sitesOf T),
        ∑ T ∈ Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X), e T := by
  classical
  have hinj : ∀ T T' : Finset 𝔅, sitesOf T = sitesOf T' → T = T' :=
    fun T T' h => sitesOf_injective (K := K) hN le_rfl h
  have hfib : ∀ X : Set (CTorus d L N₁ m₁ K), ∀ T : Finset 𝔅, sitesOf T = X →
      (Finset.univ.filter fun T' : Finset 𝔅 => sitesOf T' = X) = {T} := by
    intro X T hT
    ext T'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hinj _ _ (h.trans hT.symm), fun h => h ▸ hT⟩
  refine ⟨fun T hT => ⟨isDj_of_isPolyDom hT, dExt_eq_sizeJ_of_isPolyDom hT⟩, hinj,
    fun hr T => sitesOf_cubeAct hN hr T, ?_⟩
  intro E _ e B lam hB hbd hsupp
  refine ⟨hfib, fun X => ?_, (Finset.sum_fiberwise_of_maps_to (g := fun T : Finset 𝔅 => sitesOf T)
    (fun T _ => Finset.mem_image_of_mem _ (Finset.mem_univ T)) e).symm⟩
  · by_cases hX : ∃ T : Finset 𝔅, sitesOf T = X
    · obtain ⟨T, hT⟩ := hX
      rw [hfib X T hT, Finset.sum_singleton]
      by_cases hp : IsPolyDom m₀ K (sitesOf T)
      · rw [← hT, ← dExt_eq_sizeJ_of_isPolyDom hp]
        exact hbd T hp
      · rw [hsupp T hp, norm_zero]
        positivity
    · have : (Finset.univ.filter fun T' : Finset 𝔅 => sitesOf T' = X) = ∅ := by
        ext T'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        exact fun h => hX ⟨T', h⟩
      rw [this, Finset.sum_empty, norm_zero]
      positivity
