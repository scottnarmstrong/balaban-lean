/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreHaloDj
public import Balaban.LargeField.R.D7ReserveArithmetic

/-!
# The payment condition `hpay` for the halo of a removed component (W873, blocker 4)

`notes/phase1/VMOD-43.md`, `VMOD-40.md` §3.  The gas bound needs, for the removed factor
`‖τ z‖ ≤ exp(-p₂ - H |c_z|)`, a payment `p' + h' N ≤ p₂(β_k)` where `N` bounds the number of cells
of the halo of a removed component.

* The product count `N = (2m+1)^d crit_k^d` (`m = 2⌊R_{k-1}⌋ + 4`) has degree `4d` in `λ_k`
  (`m ≍ R_base λ²`, `crit_k ≍ λ²`), while the landed constraints give only `p₂ ≥ 2d + 3`
  (`Typing.Ok.p2_ge`) with `p₂(β) = A₂ (log β)^{p₂}`: for `d ≥ 3`, `2d + 3 < 4d`, and then the
  condition fails for large `β` as soon as `λ_k ≍ log β_k`.  The condition with the product count
  would need `p₂ > 4d`.
* A removed component is a box of sides `≤ crit_k`, so its halo lies in a box of sides
  `≤ crit_k + 2m` and `N' = (crit_k + 2m)^d` has degree `2d` in `λ_k`.  With `N'` the condition
  holds for all large `log β_k` under the landed constraint `p₂ ≥ 2d + 1`
  (`halo_pay_le_p2Run`), and the gas bound is
  `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_box`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

section Geometry

variable {d n : ℕ} [NeZero n]

/-- **The `m`-neighbourhood of a box lies in a box with sides enlarged by `2m`.** -/
theorem nbhd_box_subset_enlarged (a : Torus d n) (sd : Fin d → ℕ) (m : ℕ) :
    nbhd m (Balaban.LargeField.box a sd : Set (Torus d n)) ⊆
      Balaban.LargeField.box (a - fun _ => (m : ZMod n)) (fun i => sd i + 2 * m) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy
  intro i
  obtain ⟨j, hj, hxj⟩ := hx i
  obtain ⟨t, ht, htc⟩ := (cycNorm_le_iff _ _).1 (supDist_le_iff.1 hxy i)
  refine ⟨(m + t + j).toNat, ?_, ?_⟩
  · have := (abs_le.1 ht).1; have := (abs_le.1 ht).2; show (m + t + j : ℤ).toNat < sd i + 2 * m; omega
  · have h2 : (((m + t + j).toNat : ℕ) : ZMod n) = ((m + t + j : ℤ) : ZMod n) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := (abs_le.1 ht).1; omega)]
    rw [h2]
    have : y i = x i + (t : ZMod n) := by rw [htc]; ring
    rw [this, hxj]; push_cast; simp only [Pi.sub_apply]; ring

end Geometry

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ} {M m₀ m₁ : ℕ}

include H in
/-- **The cells of the halo core of a removed component, by the box count.**  If the domain `lab`
is the halo `nbhd m c` of a removed component and `sitesOf zs ⊆ d7Pull lab`, then
`|zs| ≤ (crit_k + 2m)^d`. -/
theorem RegionHistory.card_cells_le_box (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible)
    (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (c : H.Comp k)
    (hc : c.1 ∈ H.rem k) {m : ℕ} {lab : Finset (Torus S.d (n k))}
    (hlab : (lab : Set (Torus S.d (n k))) = nbhd m (c.1 : Set (Torus S.d (n k))))
    {zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (H.omegaPost k)))}
    (hsub : sitesOf zs ⊆ d7Pull Fr k (lab : Set (Torus S.d (n k)))) :
    zs.card ≤ (S.crit k + 2 * m) ^ S.d := by
  obtain ⟨a, sd, hbox, hsd⟩ := RegionHistory.removed_eq_box G hT hadm hkK hc
  refine (card_cells_le_card_of_sitesOf_subset Fr hnn hkK lab zs hsub).trans ?_
  rw [← Set.ncard_coe_finset, hlab, hbox]
  refine (Set.ncard_le_ncard (nbhd_box_subset_enlarged a sd m) (Set.toFinite _)).trans ?_
  refine (ncard_box_le _ _).trans ?_
  calc ∏ i, (sd i + 2 * m) ≤ ∏ _i : Fin S.d, (S.crit k + 2 * m) :=
        Finset.prod_le_prod fun i _ => Nat.add_le_add_right (hsd i).2 _
    _ = (S.crit k + 2 * m) ^ S.d := by simp

end Region

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The halo gas bound with the removed factor (3.10) in source form, paid by the box count.**
A removed component is a box of sides `≤ crit_k` (`removed_eq_box`), so its halo of radius
`m = 2⌊R_{k-1}⌋ + 4` lies in a box of sides `≤ crit_k + 2m` and the core has at most
`(crit_k + 2m)^d` cells.  As `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_raw`
with `hpay` carrying this count, which is of degree `2d` in `λ_k` (the product count
`(2m+1)^d crit_k^d` has degree `4d`). -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_box {m₀ m₁ : ℕ}
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
    (G : S.Good) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j)
    {p₂ H : ℝ} (hH : 0 ≤ H) (hh' : 0 ≤ h')
    (hrem : ∀ z, ‖τ z‖ ≤ Real.exp (-p₂ - H * ((cz z).1.card : ℝ)))
    (hpay : p' + h' * (((S.crit k + 2 * (2 * ⌊R (k - 1)⌋₊ + 4)) ^ S.d : ℕ) : ℝ) ≤ p₂)
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) := by
  refine gas_activity_bound_physical_of_D7BdryPost_halo_of_floor_eq hD hA hhB p labY hlabY hlabYv hp
    labZ hlabZ (fun z => ?_) hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ ?_ hh X
  · rw [hlabZ' z]
    exact A.H.isDj_d7Pull_halo Fr hnn hkK hk (cz z) hR
  intro z
  have hsub : sitesOf (zs z) ⊆ d7Pull Fr k (labZ z : Set (Torus S.d (n k))) := by
    intro x hx
    rw [hXZ z]; exact Or.inl hx
  have h1 := A.H.card_cells_le_box G hT A.adm Fr hnn hkK (cz z) (hcz z) (hlabZ' z) hsub
  have h4 : ((zs z).card : ℝ) ≤
      (((S.crit k + 2 * (2 * ⌊R (k - 1)⌋₊ + 4)) ^ S.d : ℕ) : ℝ) := by exact_mod_cast h1
  exact tau_bound_of_removed_factor hH (Nat.cast_nonneg _) hh' (hrem z) h4 hpay

end Instance

end Balaban.LargeField
