module

public import Balaban.LargeField.Operators.QuietLocalIso
public import Balaban.LargeField.Operators.QuietIndep

/-!
# Covariance and locality of the quiet remainder in terms of localized histories

* `quietRest_euclid`: the quiet kernel without its Gaussian factor is covariant under a lattice
  symmetry mapping `Hl` to `Hl'` (the part of `quietKernel_euclid` after the Gaussian factor);
* `quietRest_of_histImage`: the same with only the localized histories related by a `HistImage`
  (no global `HistIso`);
* `quietRest_eq_of_hist`: locality (S4), the remainder at `(H, Z')` depends only on the localized
  history `a = 𝔥(Z')` (the case of the identity symmetry).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Rest

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl') (k : ℕ)
  {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hZc' : Zc' ∈ comps (S.omega (k + 1)) (Hl'.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set (Torus S.d (n (k + 1)))))
  (hI : HistImage σ.toTorusSym (locHist Hl M K (k + 1) Zc) (locHist Hl' M K (k + 1) Zc'))
  {o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1)}
  {o' : OutT N R (locHist Hl' M K (k + 1) Zc') (k + 1)}
  {x : NewCfg N (locHist Hl M K (k + 1) Zc) k} {x' : NewCfg N (locHist Hl' M K (k + 1) Zc') k}
  (ho : RelOut (k := k + 1) σ.toTorusSym o o') (hx : RelVal hI hk x x')
  (hv : EuclideanSpace ℝ (Fin N)) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅) (hrem' : ∀ j, Hl'.rem j = ∅)

open Classical in
include hiso hZ ho hx hrem hrem' in
/-- **Lattice covariance of the quiet remainder** (the quiet kernel without its Gaussian factor). -/
theorem quietRest_euclid :
    quietRest g Hl' k Zc' hZc' hk cs hrem' o' x' hv =
      quietRest g Hl k Zc hZc hk cs hrem o x hv := by
  have hnn := Hl.F.hnn
  unfold quietRest
  rw [quietProd1_euclid σ g hiso k hk hZ hI ho hx hv cs,
    quietProdPrime_euclid σ g hiso k hk hZ hI ho hx hv cs
      (quietA2 (locHist Hl M K (k + 1) Zc) k) (quietA2 (locHist Hl' M K (k + 1) Zc') k)
      (HistImage.quietA2_eq σ hI hnn hk),
    quietProdPrime_euclid σ g hiso k hk hZ hI ho hx hv cs
      (quietA3 (locHist Hl M K (k + 1) Zc) k) (quietA3 (locHist Hl' M K (k + 1) Zc') k)
      (HistImage.quietA3_eq σ hI hnn hk),
    quietProd4_euclid σ g hiso k hk hZ hI ho hx hv cs,
    quietChiNew_euclid σ g hiso k hk hZ hI ho hx cs hrem hrem',
    quietIndicator_euclid σ g hiso k hZc hZc' hk hZ hI ho hx hv cs,
    mainActionLoc_euclid σ g hiso k hZc hZc' hk hZ hI ho hx hv cs hrem hrem']

end Rest

section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M) (cs : OpConsts)
  {H H' : RegionHistory S n R k0 K} {k : ℕ} (hk : k + 1 ≤ K)
  (Z : H.Comp (k + 1)) (Z' : H'.Comp (k + 1))
  (hI : HistImage σ.toTorusSym (H.localHistory M K (k + 1) Z) (H'.localHistory M K (k + 1) Z'))

include hk hI in
theorem comp_image_of_histImage :
    (Z'.1 : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Z.1 : Set (Torus S.d (n (k + 1)))) := by
  have := lin_image_of_histImage σ hk hI (k + 1) le_rfl
  rwa [lin_self, lin_self] at this

variable {o : OutT N R (H.localHistory M K (k + 1) Z) (k + 1)}
  {o' : OutT N R (H'.localHistory M K (k + 1) Z') (k + 1)}
  {x : NewCfg N (H.localHistory M K (k + 1) Z) k} {x' : NewCfg N (H'.localHistory M K (k + 1) Z') k}
  (ho : RelOut (k := k + 1) σ.toTorusSym o o') (hx : RelVal hI hk x x')
  (hv : EuclideanSpace ℝ (Fin N))

include ho hx in
/-- The quiet remainder is covariant between components whose localized histories are related by
a lattice symmetry (no global region isomorphism needed). -/
theorem quietRest_of_histImage :
    quietRest g (H'.locRH (k + 1) Z') k Z'.1 (locComp_mem H' hk Z') hk cs (locRH_rem _ _) o' x' hv =
      quietRest g (H.locRH (k + 1) Z) k Z.1 (locComp_mem H hk Z) hk cs (locRH_rem _ _) o x hv :=
  quietRest_euclid σ g (regionIso_of_histImage σ hk hI) k (locComp_mem H hk Z)
    (locComp_mem H' hk Z') hk (comp_image_of_histImage σ hk Z Z' hI) hI ho hx hv cs
    (locRH_rem _ _) (locRH_rem _ _)

include ho hx in
/-- The quiet kernel is covariant between components whose localized histories are related by a
lattice symmetry (replaces the `HistIso` hypothesis of `quietKernel_euclid_histIso`). -/
theorem quietKernel_of_histImage :
    quietKernel g (H'.locRH (k + 1) Z') k Z'.1 (locComp_mem H' hk Z') hk cs (locRH_rem _ _) o' x' hv =
      quietKernel g (H.locRH (k + 1) Z) k Z.1 (locComp_mem H hk Z) hk cs (locRH_rem _ _) o x hv :=
  quietKernel_euclid σ g (regionIso_of_histImage σ hk hI) k (locComp_mem H hk Z)
    (locComp_mem H' hk Z') hk (comp_image_of_histImage σ hk Z Z' hI) hI ho hx hv cs
    (locRH_rem _ _) (locRH_rem _ _)

end Hist

section Transport

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {a b : LocalHistory S n M K}

/-- Transport of an output configuration along an equality of localized histories. -/
def transOut {j : ℕ} (h : a = b) (o : OutT N R a j) : OutT N R b j := h ▸ o

/-- Transport of the new internal variables along an equality of localized histories. -/
def transNew {k : ℕ} (h : a = b) (x : NewCfg N a k) : NewCfg N b k := h ▸ x

theorem histImage_refl (a : LocalHistory S n M K) :
    HistImage (LatTorusSym.refl S n M K).toTorusSym a a := by
  constructor <;> intro j <;> simp [LatTorusSym.refl]

theorem relOut_trans {j : ℕ} (h : a = b) (o : OutT N R a j) :
    RelOut (k := j) (LatTorusSym.refl S n M K).toTorusSym o (transOut h o) := by
  subst h
  intro y
  rfl

theorem relVal_trans {k : ℕ} (h : a = b) (hI : HistImage (LatTorusSym.refl S n M K).toTorusSym a b)
    (hk : k + 1 ≤ K) (x : NewCfg N a k) : RelVal hI hk x (transNew h x) := by
  subst h
  intro p hp hp'
  exact sub_congr x (Subtype.ext rfl) hp' hp

end Transport

section Local

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (cs : OpConsts)
  {H H2 : RegionHistory S n R k0 K} {k : ℕ} (hk : k + 1 ≤ K)

/-- **Locality (S4) of the quiet remainder** (Lemma I.3.9 (d)): if the localized histories of
`(H, Z)` and `(H2, Z2)` agree, the quiet remainders agree at the corresponding configurations. -/
theorem quietRest_eq_of_hist (Z : H.Comp (k + 1)) (Z2 : H2.Comp (k + 1))
    (heq : H2.localHistory M K (k + 1) Z2 = H.localHistory M K (k + 1) Z)
    (o : OutT N R (H.localHistory M K (k + 1) Z) (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z) k) (hv : EuclideanSpace ℝ (Fin N)) :
    quietRest g (H2.locRH (k + 1) Z2) k Z2.1 (locComp_mem H2 hk Z2) hk cs (locRH_rem _ _)
        (transOut heq.symm o) (transNew heq.symm x) hv =
      quietRest g (H.locRH (k + 1) Z) k Z.1 (locComp_mem H hk Z) hk cs (locRH_rem _ _) o x hv := by
  have hI : HistImage (LatTorusSym.refl S n M K).toTorusSym (H.localHistory M K (k + 1) Z)
      (H2.localHistory M K (k + 1) Z2) := by
    rw [heq]; exact histImage_refl _
  exact quietRest_of_histImage (LatTorusSym.refl S n M K) g cs hk Z Z2 hI
    (relOut_trans heq.symm o) (relVal_trans heq.symm hI hk x) hv

include hk in
/-- Quietness depends only on the localized history. -/
theorem isQuiet_of_hist (Z : H.Comp (k + 1)) (Z2 : H2.Comp (k + 1))
    (heq : H.localHistory M K (k + 1) Z = H2.localHistory M K (k + 1) Z2)
    (hq : IsQuiet (H.locRH (k + 1) Z) k Z.1) : IsQuiet (H2.locRH (k + 1) Z2) k Z2.1 := by
  have hI : HistImage (LatTorusSym.refl S n M K).toTorusSym (H.localHistory M K (k + 1) Z)
      (H2.localHistory M K (k + 1) Z2) := by
    rw [heq]; exact histImage_refl _
  exact isQuiet_of_regionIso (LatTorusSym.refl S n M K) (regionIso_of_histImage _ hk hI) hk
    (comp_image_of_histImage _ hk Z Z2 hI) hq

end Local

end Balaban.LargeField
