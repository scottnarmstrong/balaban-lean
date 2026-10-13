module

public import Balaban.LargeField.R.RRawHoleComponent
public import Balaban.LargeField.History.InhabitedRemoval

/-!
# Non-vacuity of the raw-hole component results

On `remRegionHistory` (the only landed region history with a removed component, `Rem_1 = {C}`,
`k₀ = 1`) the results of `R/RRawHoleComponent.lean` apply at `k = 1 = k₀`: the raw hole lies in
`Z^pre_1`, the removed set is non-empty, but `Ω_1^pre` is everything (`Z_0 = ∅` gives `P = ∅`,
`U' = ∅`), so the raw hole and `A_X` are empty for every `X`.  A witness with a non-empty raw hole
meeting a removed component is not landed.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Witness

theorem remRegionHistory_OmegaCube_one :
    Def7.OmegaCube remRegionHistory 1 = Set.univ := by
  show (remStep0 2).Omega = Set.univ
  have hL : 0 < setting.L := by show 0 < 2; norm_num
  simp [RegionStep.Omega, RegionStep.OmegaPrime, remStep0, Region.Omega, Region.OmegaPrime,
    Region.Uprime, Region.U, thick, nbhd_empty, opening_empty_eq_univ hL, openingIn_empty_univ hL]

/-- The raw-hole hypotheses of `RRawHoleComponent` hold on a history with a removed component. -/
theorem remRegionHistory_rawHole :
    (Def7.OmegaCube remRegionHistory 1)ᶜ ⊆ remRegionHistory.F.Zpre 1 ∧
      (remRegionHistory.rem 1).Nonempty ∧ (1 : ℕ) ≤ 1 ∧ (1 : ℕ) ≤ 1 :=
  ⟨remRegionHistory.OmegaCube_compl_subset_Zpre le_rfl, ⟨remComp 1 2, by
    rw [remRegionHistory_rem_one]; exact Finset.mem_singleton_self _⟩, le_rfl, le_rfl⟩

/-- On this history the newly active set is empty for every label `X` (the raw hole is empty). -/
theorem remRegionHistory_newlyActive_one (X : Finset (Torus setting.d (sideLen 2 1))) :
    remRegionHistory.newlyActive X = ∅ := by
  ext x
  simp [remRegionHistory.mem_newlyActive, remRegionHistory_OmegaCube_one]

end Balaban.LargeField
