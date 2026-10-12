module

public import Balaban.LargeField.Operators.QuietEuclid
public import Balaban.LargeField.Region.SymmLoc
public import Balaban.LargeField.Operators.Invariance

/-!
# Lemma II.5.10, lattice part: the quiet kernel and the main action under `HistIso`

For a lattice symmetry `σ` (`LatTorusSym`) that maps the region history `H` to `H'` (`HistIso`, the
landed matching of components and localized histories, and `RegionIso`, the correspondence of the
steps), the quiet step kernel and the main action of the lineage localizations of corresponding
components `Z`, `e Z` take the same value at corresponding output and internal configurations
(`quietKernel_euclid_histIso`, `mainActionLoc_euclid_histIso`).  This discharges, for quiet steps, the
data-covariance hypothesis of `locOp_euclid_invariant` (`StepData.euclid_K` for the kernel
`quietKernel`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {H H' : RegionHistory S n R k0 K} (hiso : HistIso H H' σ.toTorusSym) (hglob : RegionIso σ H H')
  (k : ℕ) (hk : k + 1 ≤ K) (Z : H.Comp (k + 1)) (cs : OpConsts)

theorem HistIso.regionIso_loc (hiso : HistIso H H' σ.toTorusSym) (hglob : RegionIso σ H H')
    (k : ℕ) (hk : k + 1 ≤ K) (Z : H.Comp (k + 1)) :
    RegionIso σ (H.locRH (k + 1) Z) (H'.locRH (k + 1) (hiso.e (k + 1) Z)) :=
  RegionIso.locRH σ hglob (lin_image_of_histImage σ hk (hiso.loc (k + 1) hk Z))

theorem HistIso.comp_eq (hiso : HistIso H H' σ.toTorusSym) (k : ℕ) (hk : k + 1 ≤ K)
    (Z : H.Comp (k + 1)) :
    ((hiso.e (k + 1) Z).1 : Set (Torus S.d (n (k + 1)))) =
      σ.ec (k + 1) '' (Z.1 : Set (Torus S.d (n (k + 1)))) := by
  have := lin_image_of_histImage σ hk (hiso.loc (k + 1) hk Z) (k + 1) le_rfl
  rwa [lin_self, lin_self] at this

variable (hiso : HistIso H H' σ.toTorusSym) (hglob : RegionIso σ H H')
  (k : ℕ) (hk : k + 1 ≤ K) (Z : H.Comp (k + 1))
  {o : OutT N R (locHist (H.locRH (k + 1) Z) M K (k + 1) Z.1) (k + 1)}
  {o' : OutT N R (locHist (H'.locRH (k + 1) (hiso.e (k + 1) Z)) M K (k + 1)
    (hiso.e (k + 1) Z).1) (k + 1)}
  {x : NewCfg N (locHist (H.locRH (k + 1) Z) M K (k + 1) Z.1) k}
  {x' : NewCfg N (locHist (H'.locRH (k + 1) (hiso.e (k + 1) Z)) M K (k + 1)
    (hiso.e (k + 1) Z).1) k}
  (ho : RelOut (k := k + 1) σ.toTorusSym o o')
  (hx : RelVal (hiso.loc (k + 1) hk Z) hk x x') (hv : EuclideanSpace ℝ (Fin N))

include hglob ho hx in
/-- **Lemma II.5.10 (lattice part) for the quiet kernel, in terms of `HistIso`.** -/
theorem quietKernel_euclid_histIso :
    quietKernel g (H'.locRH (k + 1) (hiso.e (k + 1) Z)) k (hiso.e (k + 1) Z).1
        (locComp_mem H' hk (hiso.e (k + 1) Z)) hk cs (locRH_rem _ _) o' x' hv =
      quietKernel g (H.locRH (k + 1) Z) k Z.1 (locComp_mem H hk Z) hk cs (locRH_rem _ _) o x hv :=
  quietKernel_euclid σ g (hiso.regionIso_loc σ hglob k hk Z) k (locComp_mem H hk Z)
    (locComp_mem H' hk (hiso.e (k + 1) Z)) hk (hiso.comp_eq σ k hk Z) (hiso.loc (k + 1) hk Z) ho hx hv cs
    (locRH_rem _ _) (locRH_rem _ _)

include hglob ho hx in
/-- **Lemma II.5.10 (lattice part) for the main action, in terms of `HistIso`.** -/
theorem mainActionLoc_euclid_histIso :
    mainActionLoc g (H'.locRH (k + 1) (hiso.e (k + 1) Z)) k (hiso.e (k + 1) Z).1
        (locComp_mem H' hk (hiso.e (k + 1) Z)) hk cs (locRH_rem _ _) o' x' hv =
      mainActionLoc g (H.locRH (k + 1) Z) k Z.1 (locComp_mem H hk Z) hk cs (locRH_rem _ _) o x hv :=
  mainActionLoc_euclid σ g (hiso.regionIso_loc σ hglob k hk Z) k (locComp_mem H hk Z)
    (locComp_mem H' hk (hiso.e (k + 1) Z)) hk (hiso.comp_eq σ k hk Z) (hiso.loc (k + 1) hk Z) ho hx hv cs
    (locRH_rem _ _) (locRH_rem _ _)

end Balaban.LargeField
