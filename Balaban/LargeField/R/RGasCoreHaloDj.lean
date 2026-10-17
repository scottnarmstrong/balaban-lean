/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreBlock
public import Balaban.LargeField.R.ChainWalk

/-!
# The raw halo of a removed component is in the domain class (W873, blocker 4)

`notes/phase1/VMOD-43.md`.  `IsPiPrimeUnion` asks that every fine site of the label lie in a box of
`L` cells (side `L * cellSide`, corner on the cell grid) inside the label, i.e. that the label be a
union of boxes of `L^d` cubes of level `k` at arbitrary cube offsets.  The halo
`nbhd m c` is a union of such boxes as soon as `L ≤ 2m + 1`: a cube `q` at sup-distance `≤ m` from
`y ∈ c` lies in a box of side `L` all of whose points are at sup-distance `≤ m` from `y`.

* `exists_lbox_in_nbhd`: every point of `nbhd m X` lies in a box of side `s` inside `nbhd m X`
  when `s ≤ 2m + 1`.
* `RegionHistory.isDj_d7Pull_halo`: the fine set of the halo of a component is in `𝒟_k`.
* `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_raw`: the gas bound for halo
  labels with the removed factor (3.10) in source form and no domain hypothesis.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

local notation "lbox" => Balaban.Localization.box

section Cube

variable {d n : ℕ} [NeZero n]

/-- **Every point of a neighbourhood lies in a box inside it.**  For `1 ≤ s ≤ 2m + 1` each point of
`nbhd m X` lies in a box of side `s` contained in `nbhd m X`. -/
theorem exists_lbox_in_nbhd (X : Set (Torus d n)) (m s : ℕ) (hs : 0 < s) (hsm : s ≤ 2 * m + 1) :
    ∀ q ∈ nbhd m X, ∃ x, q ∈ lbox x s ∧ lbox x s ⊆ nbhd m X := by
  intro q hq
  obtain ⟨y, hy, hqy⟩ := mem_nbhd.1 hq
  have hi : ∀ i, ∃ t : ℤ, |t| ≤ m ∧ (t : ZMod n) = q i - y i := fun i =>
    (cycNorm_le_iff _ _).1 (supDist_le_iff.1 hqy i)
  choose t ht1 ht2 using hi
  set f : Fin d → ℤ := fun i => min (t i) ((m : ℤ) - s + 1) with hf
  have hf1 : ∀ i, -(m : ℤ) ≤ f i := fun i => by
    have := (abs_le.1 (ht1 i)).1
    simp only [hf]; omega
  have hf2 : ∀ i, f i + (s : ℤ) - 1 ≤ m := fun i => by simp only [hf]; omega
  have hf3 : ∀ i, f i ≤ t i := fun i => by simp only [hf]; omega
  have hf4 : ∀ i, t i - f i ≤ (s : ℤ) - 1 := fun i => by
    have := (abs_le.1 (ht1 i)).2
    simp only [hf]; omega
  refine ⟨y + fun i => (f i : ZMod n), ⟨fun i => (t i - f i).toNat, fun i => ?_, ?_⟩, ?_⟩
  · have := hf3 i; have := hf4 i
    show (t i - f i).toNat < s
    omega
  · funext i
    have h1 := ht2 i
    have h2 : (((t i - f i).toNat : ℕ) : ZMod n) = ((t i - f i : ℤ) : ZMod n) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := hf3 i; omega)]
    simp only [Pi.add_apply, natT]
    rw [h2]; push_cast
    rw [h1]; ring
  · rintro z ⟨w, hw, rfl⟩
    refine mem_nbhd.2 ⟨y, hy, supDist_le_iff.2 fun i => ?_⟩
    refine (cycNorm_le_iff _ _).2 ⟨f i + (w i : ℤ), ?_, ?_⟩
    · have := hw i; have := hf1 i; have := hf2 i
      rw [abs_le]; constructor <;> omega
    · simp only [Pi.add_apply, natT]; push_cast; ring

end Cube

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ} {M m₀ m₁ : ℕ}

include H in
/-- **The fine set of the halo of a component is in `𝒟_k`.**  For `k ≥ 1` and
`⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋` (in particular at the maximal radii), the pull-back of the halo
`nbhd (2⌊R_{k-1}⌋ + 4) c` is nonempty, a union of `π'_k`-cubes and site-connected. -/
theorem RegionHistory.isDj_d7Pull_halo (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (hk : 1 ≤ k) (c : H.Comp k)
    (hR : ⌊R (k - 1)⌋₊ = ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊) :
    IsDj m₀ k (d7Pull Fr k (nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))))) := by
  have hω := H.omega_le_halo_of_floor_eq hk hR
  have hLpos : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hLm : S.L ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4) + 1 := by
    have := L_add_eleven_le_omega S k; omega
  have hN := fine_side_eq Fr hnn hkK
  have : NeZero (cellSide S.L m₀ m₁ k) := ⟨(cellSide_pos m₀ m₁ k).ne'⟩
  rw [d7Pull_eq_preimage_siteCube]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := comp_nonempty c.2
    obtain ⟨z, hz⟩ := siteCube_surj' hN x
    exact ⟨z, by
      rw [Set.mem_preimage, hz]; exact mem_nbhd.2 ⟨x, hx, by rw [supDist_self]; omega⟩⟩
  · intro z hz
    exact box_fibre hN _ (exists_lbox_in_nbhd _ _ S.L hLpos hLm) z hz
  · have := siteConnected_d7Pull Fr hnn hkK _ (H.halo_reach c hω)
    rwa [d7Pull_eq_preimage_siteCube] at this

end Region

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The halo gas bound with the removed factor (3.10) in source form and the domain hypothesis
discharged.**  As `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor` without
`hDjZ`: the domain of the heavy object `z` is the raw halo `nbhd (2⌊R_{k-1}⌋ + 4) (cz z)` of a
removed component, whose fine set is in `𝒟_k` by `RegionHistory.isDj_d7Pull_halo`. -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_raw {m₀ m₁ : ℕ}
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
  refine gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor hD hA hhB p labY hlabY
    hlabYv hp labZ hlabZ (fun z => ?_) hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ G
    hT hH hh' hrem hpay hh X
  rw [hlabZ' z]
  exact A.H.isDj_d7Pull_halo Fr hnn hkK hk (cz z) hR

end Instance

end Balaban.LargeField
