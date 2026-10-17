/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRadiusMax
public import Balaban.LargeField.R.RRipeCard

/-!
# The small factor (3.10) of a removed component on its halo core (W871, blocker 4)

The halo gas bound `gas_activity_bound_physical_of_D7BdryPost_halo_of_floor_eq` leaves the
hypothesis `hτ : ‖τ z‖ ≤ exp(-p' - h' |zs z|)`, where `zs z` is the set of cells of the halo
`nbhd (2⌊R_{k-1}⌋ + 4)` of the removed component `cz z`.  The source (P7 (3.10)) bounds the removed
operator by `exp(-p₂ - H_k |Z|)`, `|Z|` the number of cubes of the component, `H_k = H₀ λ_k`.
This file proves the geometric conversion between the two sizes and composes it with the halo gas
bound.

* `card_le_pow_mul_card_of_near`: a finite set of tori points within sup-distance `m` of a finite
  set `X` has at most `(2m+1)^d |X|` points.
* `card_cells_le_card_of_sitesOf_subset`: the cells `zs` with `sitesOf zs ⊆ d7Pull lab` number at
  most `|lab|`.
* `card_halo_cells_le`: the cells of the halo core of a component `c` number at most
  `(2(2⌊R_{k-1}⌋ + 4) + 1)^d |c|`.
* `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor`: the halo gas bound with `hτ`
  replaced by the source form `‖τ z‖ ≤ exp(-p₂ - H |c_z|)` (conditional on it, since no landed
  statement produces this bound) together with the payment `p' + h' N ≤ p₂`, where `N` is the bound
  of the number of cells of the halo of a removed box of side `≤ crit_k`.  The inequality `hh` is
  met by taking `h'` equal to its left side.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

section Count

variable {d n : ℕ} [NeZero n]

/-- **Counting in a sup-distance neighbourhood.**  A finite set `B` of points of the torus within
sup-distance `m` of points of `X` has at most `(2m+1)^d |X|` points. -/
theorem card_le_pow_mul_card_of_near (m : ℕ) (X B : Finset (Torus d n))
    (hB : ∀ y ∈ B, ∃ x ∈ X, supDist x y ≤ m) : B.card ≤ (2 * m + 1) ^ d * X.card := by
  classical
  let ball : Torus d n → Finset (Torus d n) := fun x =>
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(m : ℤ)) (m : ℤ)).image
      (fun e => x + fun i => (e i : ZMod n))
  have hball : ∀ x, (ball x).card ≤ (2 * m + 1) ^ d := by
    intro x
    refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    rw [this]
  have hsub : B ⊆ X.biUnion ball := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hB y hy
    rw [Finset.mem_biUnion]
    refine ⟨x, hx, ?_⟩
    have hi : ∀ i, ∃ t : ℤ, (t.natAbs ≤ m) ∧ (t : ZMod n) = x i - y i := by
      intro i
      obtain ⟨t, ht, htc⟩ := (cycNorm_le_iff _ _).1 (supDist_le_iff.1 hxy i)
      exact ⟨t, by rw [Int.abs_eq_natAbs] at ht; exact_mod_cast ht, htc⟩
    choose t ht1 ht2 using hi
    simp only [ball, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨fun i => -t i, fun i => ?_, ?_⟩
    · have := ht1 i
      beta_reduce
      constructor <;> omega
    · funext i
      simp [ht2 i]
  calc B.card ≤ (X.biUnion ball).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ X, (ball x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ X, (2 * m + 1) ^ d := Finset.sum_le_sum fun x _ => hball x
    _ = (2 * m + 1) ^ d * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end Count

section Cells

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]

/-- **The cells of a set of cubes are at most as many as the cubes.**  If `zs` is a set of
`π_k`-cells with `sitesOf zs ⊆ d7Pull lab`, then `|zs| ≤ |lab|` (a cell is determined by its cube
index). -/
theorem card_cells_le_card_of_sitesOf_subset (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {Om : Set _} (lab : Finset (Torus S.d (n k)))
    (zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k Om))
    (hsub : sitesOf zs ⊆ d7Pull Fr k (lab : Set (Torus S.d (n k)))) :
    zs.card ≤ lab.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun b => cubeIdx Fr k b.1) (fun b hb => ?_) (fun b hb b' hb' h => ?_)
  · have hin : b.1 ∈ sitesOf zs :=
      mem_sitesOf.2 ⟨b, hb, mem_box_self _ (cellSide_pos m₀ m₁ k)⟩
    exact Finset.mem_coe.1 ((d7Pull_iff Fr k _ _).1 (hsub hin))
  · exact Subtype.ext (cubeIdx_injOn Fr hnn hkK b.2.1 b'.2.1 h)

end Cells

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ} {M m₀ m₁ : ℕ}

include H in
/-- **The number of cells of the halo core of a component.**  If the domain `lab` is the halo
`nbhd m c` of the component `c` and `sitesOf zs ⊆ d7Pull lab`, then `|zs| ≤ (2m+1)^d |c|`. -/
theorem RegionHistory.card_halo_cells_le (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (c : H.Comp k) (m : ℕ)
    {lab : Finset (Torus S.d (n k))}
    (hlab : (lab : Set (Torus S.d (n k))) = nbhd m (c.1 : Set (Torus S.d (n k))))
    {zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (H.omegaPost k)))}
    (hsub : sitesOf zs ⊆ d7Pull Fr k (lab : Set (Torus S.d (n k)))) :
    zs.card ≤ (2 * m + 1) ^ S.d * c.1.card := by
  refine (card_cells_le_card_of_sitesOf_subset Fr hnn hkK lab zs hsub).trans ?_
  refine card_le_pow_mul_card_of_near m c.1 lab fun y hy => ?_
  have hy' : y ∈ nbhd m (c.1 : Set (Torus S.d (n k))) := hlab ▸ Finset.mem_coe.2 hy
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.1 hy'
  exact ⟨x, Finset.mem_coe.1 hx, by rwa [supDist_comm]⟩

end Region

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The halo gas bound with the small factor (3.10) in the source form** (conditional on it).
`hrem` is P7 (3.10) for the removed component `cz z`, as the scalar bound
`‖τ z‖ ≤ exp(-p₂ - H |c_z|)` with `|c_z|` the number of cubes of the component and `H ≥ 0`
(`H = H_k = H₀ λ_k`); no landed statement produces it.  The cells of the halo core of a removed
box number at most `(2(2⌊R_{k-1}⌋+4)+1)^d (2ρ_k+10)^d` (`card_halo_cells_le`,
`removed_card_le`), and `hpay` says that one copy of `p₂` pays `h'` times this number:
`p' + h' N ≤ p₂`.  The size term `H |c_z|` is dropped (`H ≥ 0`), so no relation between `H` and `h'`
is needed. -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor {m₀ m₁ : ℕ}
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
    (hpay : p' + h' * (((2 * (2 * ⌊R (k - 1)⌋₊ + 4) + 1) ^ S.d * (2 * S.rho k + 10) ^ S.d : ℕ) : ℝ)
      ≤ p₂)
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
    labZ hlabZ hDjZ hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ ?_ hh X
  intro z
  have hsub : sitesOf (zs z) ⊆ d7Pull Fr k (labZ z : Set (Torus S.d (n k))) := by
    intro x hx
    rw [hXZ z]; exact Or.inl hx
  have h1 := A.H.card_halo_cells_le Fr hnn hkK (cz z) _ (hlabZ' z) hsub
  have h2 := RegionHistory.removed_card_le G hT A.adm hkK (hcz z)
  have h3 : (zs z).card ≤ (2 * (2 * ⌊R (k - 1)⌋₊ + 4) + 1) ^ S.d * (2 * S.rho k + 10) ^ S.d :=
    h1.trans (Nat.mul_le_mul_left _ h2)
  have h4 : ((zs z).card : ℝ) ≤
      (((2 * (2 * ⌊R (k - 1)⌋₊ + 4) + 1) ^ S.d * (2 * S.rho k + 10) ^ S.d : ℕ) : ℝ) := by
    exact_mod_cast h3
  refine (hrem z).trans (Real.exp_le_exp.2 ?_)
  have h5 : 0 ≤ H * ((cz z).1.card : ℝ) := mul_nonneg hH (Nat.cast_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left h4 hh']

end Instance

end Balaban.LargeField
