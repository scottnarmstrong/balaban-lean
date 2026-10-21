/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.FootprintMargin
public import Balaban.Fluctuation.CriticalPoint

/-!
# The read sets of a generating set near a site whose neighbourhood lies in its top layer

For a generating set `Gb` and the level set `Gp` of the same level `K`, the reads of the residual of
the approximate field (`resDep`) at a site `x` coincide when the sup-neighbourhood of radius
`3 L^K` of `x` lies in the top layer of `Gb`: the blocks active near `x` are the top blocks of both
sets (`active_eq_of_top`), so are the approximate-field reads (`approxDep_eq_of_top`) and the
residual sites (`resSites_eq_of_top`).  Used for the locality of the determinant part of the
coefficient recomputed on a local generating set (route R-LOC, L5).

* `active_eq_of_top`, `approxDep_eq_of_top`, `resSites_eq_of_top`, `resDep_eq_of_top`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Top

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb : ℝ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) K ϱb} {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The blocks active at a site whose `2 L^K`-neighbourhood lies in the top layer of `Gb` are
those of the level set**. -/
theorem active_eq_of_top (hGp : IsLevel Gp K) (hK : 1 ≤ K) {u : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hlay : ∀ y : Torus d (N₁ * L ^ m₁ * L ^ K),
      (∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ K) (2 * (L : ℝ) ^ K) (y μ) (u μ)) → y ∈ Gb.layer K) :
    active Gb u = active Gp u := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hnear : ∀ q : ℕ × Torus d (N₁ * L ^ m₁ * L ^ K), q.1 ≤ K →
      (q ∈ active Gb u ∨ q ∈ active Gp u) → q.2 ∈ Gb.layer K := by
    intro q hqK hq
    refine hlay q.2 fun μ => ?_
    have hb : CoordNear (N₁ * L ^ m₁ * L ^ K) (2 * (L : ℝ) ^ q.1 - 1) (u μ) (q.2 μ) := by
      rcases hq with hq | hq
      · exact coordNear_base_of_mem_active hq μ
      · exact coordNear_base_of_mem_active hq μ
    have hLq : (L : ℝ) ^ q.1 ≤ (L : ℝ) ^ K := pow_le_pow_right₀ hL1 hqK
    exact hb.symm.mono (by linarith)
  ext q
  constructor
  · intro hq
    obtain ⟨hqb, hne⟩ := (mem_active Gb).1 hq
    obtain ⟨⟨hq1, hqK⟩, hql, hbase⟩ := (mem_blockIdx Gb).1 hqb
    have hqtop := hnear q hqK (Or.inl hq)
    have hq1K : q.1 = K := by
      by_contra hne'
      exact Gb.layer_disjoint hq1 hqK hK le_rfl hne' hql hqtop
    refine (mem_active Gp).2 ⟨(mem_blockIdx Gp).2 ⟨⟨hq1, hqK⟩, ?_, hbase⟩, hne⟩
    rw [hq1K]
    exact hGp.mem_layer q.2
  · intro hq
    obtain ⟨hqb, hne⟩ := (mem_active Gp).1 hq
    obtain ⟨⟨hq1, hqK⟩, hql, hbase⟩ := (mem_blockIdx Gp).1 hqb
    have hq1K : q.1 = K := by
      by_contra hne'
      exact Gp.layer_disjoint hq1 hqK hK le_rfl hne' hql (hGp.mem_layer q.2)
    refine (mem_active Gb).2 ⟨(mem_blockIdx Gb).2 ⟨⟨hq1, hqK⟩, ?_, hbase⟩, hne⟩
    rw [hq1K]
    exact hnear q hqK (Or.inr hq)

/-- **The approximate-field reads at a site whose `2 L^K`-neighbourhood lies in the top layer of
`Gb` are those of the level set.** -/
theorem approxDep_eq_of_top (hGp : IsLevel Gp K) (hK : 1 ≤ K) {u : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hlay : ∀ y : Torus d (N₁ * L ^ m₁ * L ^ K),
      (∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ K) (2 * (L : ℝ) ^ K) (y μ) (u μ)) → y ∈ Gb.layer K) :
    approxDep Gb u = approxDep Gp u := by
  classical
  unfold approxDep
  rw [active_eq_of_top hGp hK hlay]

/-- **The residual sites at a site of the top layer of `Gb` are those of the level set.** -/
theorem resSites_eq_of_top (hGp : IsLevel Gp K) (hK : 1 ≤ K) {x : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hx : x ∈ Gb.layer K) : resSites Gb x = resSites Gp x := by
  classical
  have h1 : Gb.layerIndex x = K := Gb.layerIndex_eq hK le_rfl hx
  have h2 : Gp.layerIndex x = K := Gp.layerIndex_eq hK le_rfl (hGp.mem_layer x)
  unfold resSites
  rw [h1, h2]
  rfl

/-- **The reads of the residual at a site whose `3 L^K`-neighbourhood lies in the top layer of
`Gb` are those of the level set.** -/
theorem resDep_eq_of_top (hGp : IsLevel Gp K) (hK : 1 ≤ K) {x : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hlay : ∀ y : Torus d (N₁ * L ^ m₁ * L ^ K),
      (∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ K) (3 * (L : ℝ) ^ K) (y μ) (x μ)) → y ∈ Gb.layer K) :
    resDep Gb x = resDep Gp x := by
  classical
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ K := by positivity
  have hx : x ∈ Gb.layer K := hlay x fun μ => CoordNear.refl (by positivity) _
  have hxp : Gp.layerIndex x = K := Gp.layerIndex_eq hK le_rfl (hGp.mem_layer x)
  unfold resDep
  rw [resSites_eq_of_top hGp hK hx]
  refine Finset.biUnion_congr rfl fun u hu => approxDep_eq_of_top hGp hK fun y hy => ?_
  refine hlay y fun μ => ?_
  have hux := resSites_coord_bound_of le_rfl hxp hu μ
  exact ((hy μ).trans hux).mono (by linarith)

end Top

end Balaban.Localization
