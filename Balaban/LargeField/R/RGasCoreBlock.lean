/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreBlockGeom
public import Balaban.LargeField.R.RGasCoreTau

/-!
# Block-completed halo labels of removed components (W872, blocker 4)

`notes/phase1/VMOD-43.md`.  The halo `nbhd (2⌊R_{k-1}⌋ + 4) c` of a removed component `c` of
`Z^pre_k` is a nonempty site-connected set of cubes, but the gas bound needs the fine set of a label
to be a union of `π'_k`-cubes (`IsDj`, field `IsPiPrimeUnion`: every fine site of the label lies in
an aligned box of `L` cells inside the label).  The block completion of the halo, the union of the
boxes of `L^d` cubes based at the points of the halo, has this property.

* `RegionHistory.exists_block_halo_label`: for a removed component `c` there is a set `labZ` of cubes
  with `nbhd m c ⊆ labZ ⊆ nbhd (m + L - 1) c` (`m = 2⌊R_{k-1}⌋ + 4`) whose fine set is in `𝒟_k`
  (`IsDj`), when `ω_k ≤ 2m` (true for `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋`).
* `RegionHistory.block_halo_subset_omegaPost`, `block_halo_disjoint_comp`: every label between the
  halo and radius `m + L - 1` lies in `Ω_k^post` and misses every other component of `Z^pre_k`
  (`m + L - 1 < ω_k`).
* `RegionHistory.card_block_halo_cells_le`: the cells of the core of such a label number at most
  `(2(m + L - 1) + 1)^d |c|`.
* `gas_activity_bound_physical_of_D7BdryPost_block_removed_factor`: the gas bound for labels
  `labZ z ⊆ nbhd (m + L - 1) (cz z)` with fine sets in `𝒟_k`, with the removed factor in the source
  form (3.10).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

section Label

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ} {M m₀ m₁ : ℕ}

include H in
/-- The radius `2⌊R_{k-1}⌋ + 4 + L - 1` of the block completion of the halo is below `ω_k`. -/
theorem RegionHistory.block_halo_radius_lt_omega (hk : 1 ≤ k) :
    2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1 < S.omega k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : ⌊R j⌋₊ ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.floor_le_floor (H.F.RH.le j)
  rw [Setting.omega_eq_omegaW, omegaW_succ]
  simp only [Nat.add_sub_cancel]
  have := Nat.pos_of_ne_zero (NeZero.ne S.L)
  omega

include H in
/-- **Existence of block-completed halo labels** (blocker 4).  For a removed component `c` of
`Z^pre_k` with `ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)`, there is a set `labZ` of cubes of `𝕋_k` with
`nbhd (2⌊R_{k-1}⌋+4) c ⊆ labZ ⊆ nbhd (2⌊R_{k-1}⌋ + 4 + L - 1) c` whose fine set `d7Pull labZ` is in
`𝒟_k`: nonempty, a union of `π'_k`-cubes (the union of the boxes of `L^d` cubes based at the halo
cubes) and site-connected (the halo is connected and each box is connected and meets the halo). -/
theorem RegionHistory.exists_block_halo_label (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (c : H.Comp k)
    (hω : S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4)) :
    ∃ labZ : Finset (Torus S.d (n k)),
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))) ⊆ (labZ : Set (Torus S.d (n k))) ∧
      (labZ : Set (Torus S.d (n k))) ⊆
        nbhd (2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) (c.1 : Set (Torus S.d (n k))) ∧
      IsDj m₀ k (d7Pull Fr k (labZ : Set (Torus S.d (n k)))) := by
  have hLpos : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  obtain ⟨B, h1, h2, h3, h4⟩ := exists_block_completion (c.1 : Set (Torus S.d (n k)))
    (2 * ⌊R (k - 1)⌋₊ + 4) S.L hLpos
  have hconn := h4 (H.halo_reach c hω)
  refine ⟨B, h1, by
    have : 2 * ⌊R (k - 1)⌋₊ + 4 + (S.L - 1) = 2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1 := by omega
    rwa [this] at h2, ?_⟩
  have hN := fine_side_eq Fr hnn hkK
  have : NeZero (cellSide S.L m₀ m₁ k) := ⟨(cellSide_pos m₀ m₁ k).ne'⟩
  rw [d7Pull_eq_preimage_siteCube]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := comp_nonempty c.2
    obtain ⟨z, hz⟩ := siteCube_surj' hN x
    exact ⟨z, by rw [Set.mem_preimage, hz]; exact h1 (mem_nbhd.2 ⟨x, hx, by rw [supDist_self]; omega⟩)⟩
  · intro z hz
    obtain ⟨b, hb1, hb2, hb3⟩ := box_fibre hN (B : Set (Torus S.d (n k))) h3 z hz
    exact ⟨b, hb1, hb2, hb3⟩
  · have := siteConnected_d7Pull Fr hnn hkK (B : Set (Torus S.d (n k))) hconn
    rwa [d7Pull_eq_preimage_siteCube] at this

include H in
/-- **A label between the halo and radius `2⌊R_{k-1}⌋ + 4 + L - 1` lies in `Ω_k^post`.** -/
theorem RegionHistory.block_halo_subset_omegaPost (hk : 1 ≤ k) (c : H.Comp k) (hc : c.1 ∈ H.rem k)
    {lab : Set (Torus S.d (n k))}
    (hlab : lab ⊆ nbhd (2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) (c.1 : Set (Torus S.d (n k)))) :
    lab ⊆ H.omegaPost k :=
  hlab.trans (H.nbhd_subset_omegaPost c hc (H.block_halo_radius_lt_omega hk))

include H in
/-- **Such a label misses every other component of `Z^pre_k`.** -/
theorem RegionHistory.block_halo_disjoint_comp (hk : 1 ≤ k) {c c' : H.Comp k} (hne : c ≠ c')
    {lab : Set (Torus S.d (n k))}
    (hlab : lab ⊆ nbhd (2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) (c.1 : Set (Torus S.d (n k)))) :
    Disjoint lab (c'.1 : Set (Torus S.d (n k))) := by
  have hd := H.halo_disjoint_of_comp_sep hne (a := 2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) (b := 0)
    (by have := H.block_halo_radius_lt_omega hk; omega)
  have h0 : nbhd 0 (c'.1 : Set (Torus S.d (n k))) = c'.1 := by
    ext y; rw [mem_nbhd]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rwa [supDist_eq_zero.1 (Nat.le_zero.1 hxy)]
    · intro hy; exact ⟨y, hy, by rw [supDist_self]⟩
  rw [h0] at hd
  exact hd.mono_left hlab

include H in
/-- **The number of cells of the core of a block-completed label.**  If the label `lab` lies in
`nbhd r c` and `sitesOf zs ⊆ d7Pull lab`, then `|zs| ≤ (2r+1)^d |c|`. -/
theorem RegionHistory.card_block_halo_cells_le (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (c : H.Comp k) (r : ℕ)
    {lab : Finset (Torus S.d (n k))}
    (hlab : (lab : Set (Torus S.d (n k))) ⊆ nbhd r (c.1 : Set (Torus S.d (n k))))
    {zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (H.omegaPost k)))}
    (hsub : sitesOf zs ⊆ d7Pull Fr k (lab : Set (Torus S.d (n k)))) :
    zs.card ≤ (2 * r + 1) ^ S.d * c.1.card := by
  refine (card_cells_le_card_of_sitesOf_subset Fr hnn hkK lab zs hsub).trans ?_
  refine card_le_pow_mul_card_of_near r c.1 lab fun y hy => ?_
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 (hlab (Finset.mem_coe.2 hy))
  exact ⟨x, Finset.mem_coe.1 hx, by rwa [supDist_comm]⟩

end Label

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The physical large-field gas bound for block-completed halo labels, with the removed factor
(3.10) in the source form.**  The domain `labZ z` of the heavy object `z` is any set of cubes inside
`nbhd (2⌊R_{k-1}⌋ + 4 + L - 1) (cz z)` whose fine set is in `𝒟_k` (`hDjZ`; by
`exists_block_halo_label` such labels exist and contain the halo), `cz z` a removed component of
`Z^pre_k`.  `hrem` is P7 (3.10), `‖τ z‖ ≤ exp(-p₂ - H |c_z|)`, and `hpay` says that one copy of `p₂`
pays `h'` times the bound `(2(2⌊R_{k-1}⌋+4+L-1)+1)^d (2ρ_k+10)^d` of the number of cells. -/
theorem gas_activity_bound_physical_of_D7BdryPost_block_removed_factor {m₀ m₁ : ℕ}
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
    (hk : 1 ≤ k)
    (cz : Zt → A.H.Comp k) (hcz : ∀ z, (cz z).1 ∈ A.H.rem k)
    (hlabZ' : ∀ z, (labZ z : Set (Torus S.d (n k))) ⊆
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) ((cz z).1 : Set (Torus S.d (n k))))
    {κ' p' h' : ℝ} (hfac : 0 ≤ fac) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ rate) (hp' : 0 ≤ p')
    (hκ : aEnt S.d S.L + 1 ≤ rate - κ')
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (β : Yt → ℂ) (hβ : ∀ y, β y = rep.B A (labY y) (extK p.1) (extK p.2.1) hext p.2.2)
    (G : S.Good) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j)
    {p₂ H : ℝ} (hH : 0 ≤ H) (hh' : 0 ≤ h')
    (hrem : ∀ z, ‖τ z‖ ≤ Real.exp (-p₂ - H * ((cz z).1.card : ℝ)))
    (hpay : p' + h' * (((2 * (2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) + 1) ^ S.d *
      (2 * S.rho k + 10) ^ S.d : ℕ) : ℝ) ≤ p₂)
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) := by
  refine gas_activity_bound_physical_of_D7BdryPost_labels hD hA hhB p labY hlabY hlabYv hp labZ hlabZ
    hDjZ hXY hXZ (fun z => A.H.block_halo_subset_omegaPost hk (cz z) (hcz z) (hlabZ' z)) hfac hκ'
    hκ'' hp' hκ hz hcr β hβ ?_ hh X
  intro z
  have hsub : sitesOf (zs z) ⊆ d7Pull Fr k (labZ z : Set (Torus S.d (n k))) := by
    intro x hx
    rw [hXZ z]; exact Or.inl hx
  have h1 := A.H.card_block_halo_cells_le Fr hnn hkK (cz z) _ (hlabZ' z) hsub
  have h2 := RegionHistory.removed_card_le G hT A.adm hkK (hcz z)
  have h3 : (zs z).card ≤ (2 * (2 * ⌊R (k - 1)⌋₊ + 4 + S.L - 1) + 1) ^ S.d *
      (2 * S.rho k + 10) ^ S.d := h1.trans (Nat.mul_le_mul_left _ h2)
  exact tau_bound_of_removed_factor hH (Nat.cast_nonneg _) hh' (hrem z) (by exact_mod_cast h3) hpay

end Instance

end Balaban.LargeField
