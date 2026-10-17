/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreInputs
public import Balaban.LargeField.R.RHaloSep
public import Balaban.LargeField.Geometry.DomainsModBridge
public import Balaban.LargeField.History.OmegaPost

/-!
# The core of the gas bound for removed components, with arbitrary labels (W872, blocker 4)

The gas bound `gas_activity_bound_physical_of_D7BdryPost` needs, for each heavy object `z`, that the
cells `zs z` of its core are site-connected.  When the label `labZ z` of the object has a fine set
in `𝒟_k` (`hDjZ`) and lies in `Ω_k^post`, the cells of the core are exactly the fine set of the
label, hence site-connected, and no further information on the label is needed.  This file proves
the gas bound in that form (`gas_activity_bound_physical_of_D7BdryPost_labels`), the inclusion of
every neighbourhood of radius `< ω_k` of a removed component in `Ω_k^post`
(`RegionHistory.nbhd_subset_omegaPost`), and the scalar step which turns the source bound (3.10) on
the removed operator into the bound `exp(-p' - h' |zs|)` of the gas bound
(`tau_bound_of_removed_factor`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

include H in
/-- **A neighbourhood of radius `< ω_k` of a removed component lies in `Ω_k^post`** (any `k`): it
misses every other component of `Z^pre_k` (they are at distance `≥ ω_k`), and `(Ω_k^post)ᶜ` lies in
the union of the retained components. -/
theorem RegionHistory.nbhd_subset_omegaPost (c : H.Comp k) (hc : c.1 ∈ H.rem k)
    {r : ℕ} (hr : r < S.omega k) :
    nbhd r (c.1 : Set (Torus S.d (n k))) ⊆ H.omegaPost k := by
  intro x hx
  by_contra hn
  have hZ := H.omegaPost_compl_subset_Z k hn
  rw [H.Z_eq] at hZ
  obtain ⟨hzp, hnrem⟩ := hZ
  obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega k) (X := H.F.Zp k) (mem_finOf.2 hzp)
  by_cases hcY : (⟨Y, hY⟩ : H.Comp k) = c
  · apply hnrem
    rw [Set.mem_iUnion₂]
    refine ⟨c.1, hc, ?_⟩
    have : Y = c.1 := congrArg Subtype.val hcY
    rw [← this]; exact hxY
  · have hd := H.halo_disjoint_of_comp_sep (Ne.symm hcY) (a := r) (b := 0) (by omega)
    have h0 : nbhd 0 (Y : Set (Torus S.d (n k))) = Y := by
      ext y; rw [mem_nbhd]
      constructor
      · rintro ⟨x, hx, hxy⟩
        rwa [supDist_eq_zero.1 (Nat.le_zero.1 hxy)]
      · intro hy; exact ⟨y, hy, by rw [supDist_self]⟩
    exact Set.disjoint_left.1 hd hx (by rw [h0]; exact hxY)

end Region

section Cells

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]

/-- The cells of the core of a label inside `Ω` are the fine set of the label. -/
theorem sitesOf_eq_d7Pull_of_Yhat (Fr : FineSizeFrame S n M K m₀ m₁) {k : ℕ}
    {Om : Set (Torus S.d (n k))} {lab : Set (Torus S.d (n k))} (hsub : lab ⊆ Om)
    {zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k (d7Pull Fr k Om))}
    (hXZ : d7Pull Fr k lab = Yhat (d7Pull Fr k Om) (sitesOf zs)) :
    sitesOf zs = d7Pull Fr k lab := by
  ext x
  constructor
  · intro hx
    rw [hXZ]; exact Or.inl hx
  · intro hx
    have hx' := hx
    rw [hXZ] at hx'
    rcases hx' with h | ⟨z, -, -, hy⟩
    · exact h
    · exact absurd (d7Pull_mono Fr k hsub hx) hy.1

end Cells

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The physical large-field gas bound for labels in `𝒟_k` inside `Ω_k^post`.**  As
`gas_activity_bound_physical_of_D7BdryPost`, with the site-connectedness `hconnZ` of the cores
replaced by `labZ z ⊆ Ω_k^post`: with `hDjZ` and `hXZ` the cells of the core are the fine set of the
label, which is site-connected because it lies in `𝒟_k`. -/
theorem gas_activity_bound_physical_of_D7BdryPost_labels {m₀ m₁ : ℕ}
    {Fr : FineSizeFrame S n M K m₀ m₁}
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
    (hsubZ : ∀ z, (labZ z : Set (Torus S.d (n k))) ⊆ A.H.omegaPost k)
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
  gas_activity_bound_physical_of_D7BdryPost hD hA hhB p labY hlabY hlabYv hp labZ hlabZ hDjZ hXY hXZ
    (fun z => by
      rw [sitesOf_eq_d7Pull_of_Yhat Fr (hsubZ z) (hXZ z)]
      exact (hDjZ z).2.2)
    hfac hκ' hκ'' hp' hκ hz hcr β hβ hτ hh X

end Instance

/-- **The scalar step from the removed factor (3.10) to the gas bound.**  If the removed operator
satisfies `‖τ‖ ≤ exp(-p₂ - H c)` with `H, c ≥ 0`, the number of cells is at most `N`, and
`p' + h' N ≤ p₂`, then `‖τ‖ ≤ exp(-p' - h' · cells)`. -/
theorem tau_bound_of_removed_factor {τ : ℂ} {p₂ H c p' h' N cells : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hh' : 0 ≤ h') (hrem : ‖τ‖ ≤ Real.exp (-p₂ - H * c)) (hcells : cells ≤ N)
    (hpay : p' + h' * N ≤ p₂) : ‖τ‖ ≤ Real.exp (-p' - h' * cells) := by
  refine hrem.trans (Real.exp_le_exp.2 ?_)
  have h5 : 0 ≤ H * c := mul_nonneg hH hc
  nlinarith [mul_le_mul_of_nonneg_left hcells hh']

end Balaban.LargeField
