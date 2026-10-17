/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreConn

/-!
# The radii of the region history and the connectivity of halos (W870, blocker 4)

The radii `R_j` of a region history are data: `FlowSteps` and `RegionHistory` take an arbitrary
sequence `R` with `RadiusHyp`, that is `0 ≤ R_j ≤ R_base λ_j²` (the radii are given to the region
steps `RegionStep d L n0 n1 (R (k-1)) (R k)` as parameters).  The sequence `R_j = 0`
(`History/Inhabited`) and the maximal sequence `R_j = R_base λ_j²` (`radiusHyp_nonempty`) both
satisfy `RadiusHyp`, so the radius actually used is a free choice below the maximum; the widths
`ω_j = 2⌊R_base λ_{j-1}²⌋ + L + 11` (`Setting.omega`) always use the maximum.

* `radiusHyp_maximal`: the maximal radii `R_j = R_base λ_j²` satisfy `RadiusHyp` for every
  nondecreasing `λ ≥ 1` and `R_base ≥ 4L + 20`; hence every landed consumer of `RadiusHyp`
  applies at the maximal radii.
* `RegionHistory.omega_le_halo_of_maximal_radius`: for a history with maximal radii,
  `ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)`.
* `gas_activity_bound_physical_of_D7BdryPost_halo_of_floor_eq`: the gas bound with the connectivity
  of the removed cores, the hypothesis `ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)` replaced by
  `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

/-- **The maximal radii satisfy the radius hypotheses.**  For `λ` nondecreasing with `λ_j ≥ 1` and
`R_base ≥ 4L + 20`, the sequence `R_j = R_base λ_j²` satisfies `RadiusHyp`. -/
theorem radiusHyp_maximal {L : ℕ} {Rbase : ℝ} {lam : ℕ → ℝ} (hmono : Monotone lam)
    (hone : ∀ j, 1 ≤ lam j) (hbase : (4 * L + 20 : ℝ) ≤ Rbase) :
    RadiusHyp L Rbase lam (fun j => Rbase * lam j ^ 2) where
  mono := hmono
  one_le := hone
  nonneg := fun j => by
    have : 0 ≤ Rbase := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    positivity
  le := fun _ => le_rfl
  base := hbase

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

include H in
/-- **At the maximal radii the component width is at most the halo diameter:** if
`R_j = R_base λ_j²` for all `j`, then `ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)` for `k ≥ 1`. -/
theorem RegionHistory.omega_le_halo_of_maximal_radius (hk : 1 ≤ k)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) :
    S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4) :=
  H.omega_le_halo_of_floor_eq hk (by rw [hR])

end Region

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The physical large-field gas bound with the connectivity of the removed cores, for the
radius `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋`** (in particular for the maximal radii).  As
`gas_activity_bound_physical_of_D7BdryPost_halo`, with the hypothesis
`ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)` replaced by its source `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋`
(`omega_le_halo_of_floor_eq`). -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo_of_floor_eq {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁}
    {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
    {rep : Rep S n R k0 K M N geo cs P k} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    (hD : D7BdryPost Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {hext : Fin N → ℂ} (hhB : hext ∈ hSetB hv)
    (p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ))
    (labY : Yt → Finset (Torus S.d (n k))) (hlabY : Function.Injective labY)
    (hlabYv : ∀ y, labY y ∈ bdryDomsPost Fr A k (Zof A))
    (hp : ∀ y, H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (labY y : Set (Torus S.d (n k)))) aw μs ε ε1 νs hext
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    (labZ : Zt → Finset (Torus S.d (n k))) (hlabZ : Function.Injective labZ)
    (hDjZ : ∀ z, IsDj m₀ k (d7Pull Fr k (labZ z : Set (Torus S.d (n k)))))
    {cy zs cr : _ → Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))}
    (hXY : ∀ y, d7Pull Fr k (labY y : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (cy y)))
    (hXZ : ∀ z, d7Pull Fr k (labZ z : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (zs z)))
    (hk : 1 ≤ k) (hR : ⌊R (k - 1)⌋₊ = ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊)
    (cz : Zt → A.H.Comp k) (hcz : ∀ z, (cz z).1 ∈ A.H.rem k)
    (hlabZ' : ∀ z, (labZ z : Set (Torus S.d (n k))) =
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4) ((cz z).1 : Set (Torus S.d (n k))))
    {κ' p' h' : ℝ} (hfac : 0 ≤ fac) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ rate) (hp' : 0 ≤ p')
    (hκ : aEnt S.d S.L + 1 ≤ rate - κ')
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (β : Yt → ℂ) (hβ : ∀ y, β y = rep.B A (labY y) (extK p.1) (extK p.2.1) hext p.2.2)
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p' - h' * (zs z).card))
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) :=
  gas_activity_bound_physical_of_D7BdryPost_halo (hω := A.H.omega_le_halo_of_floor_eq hk hR) hD hA hhB
    p labY hlabY hlabYv hp labZ hlabZ hDjZ hXY hXZ hk cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ
    hτ hh X

end Instance

end Balaban.LargeField
