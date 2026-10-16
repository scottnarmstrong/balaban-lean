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
# Connectivity of the cores of removed components (blocker 4)

`notes/phase1/VMOD-43.md` §5d.  `dExt_le_card_of_connected` needs the core of a removed component
to be nearest-neighbour connected, while components of `Z^pre_k` are only classes of cubes at
index distance `< ω_k`.

* `halo_reach_of_linked`: if any two cubes of a set `c` are linked by a chain of steps of length
  `< ω` and `ω ≤ 2m`, then `nbhd m c` is nearest-neighbour connected.  The neighbourhoods of
  radius `m` of two cubes at distance `< ω ≤ 2m` meet.
* `halo_subset_omegaPost`: the halo `nbhd (2⌊R_{k-1}⌋ + 4)` of a removed component lies in
  `Ω_k^post`, so the cells of the halo are all cells of the polymer.
* `siteConnected_d7Pull`: a nearest-neighbour connected set of cubes has site-connected fine set.
* `siteConnected_sitesOf_halo`: the cells of a core whose domain is the halo of a removed
  component form a site-connected set.  This needs `ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)`, which holds when
  `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋` (`omega_le_halo_sum`) and fails for small radii.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

section Cube

variable {d n : ℕ} [NeZero n]

theorem nnAdj_symm {a b : Torus d n} (h : NNAdj a b) : NNAdj b a := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

theorem supDist_add_cast (x : Torus d n) (e : Fin d → ℤ) (m : ℕ) (he : ∀ i, (e i).natAbs ≤ m) :
    supDist x (x + fun i => (e i : ZMod n)) ≤ m := by
  rw [supDist_le_iff]
  intro i
  rw [cycNorm_le_iff]
  refine ⟨-e i, ?_, ?_⟩
  · rw [abs_neg, Int.abs_eq_natAbs]; exact_mod_cast he i
  · simp

theorem ball_reach_aux (x : Torus d n) (m : ℕ) :
    ∀ N : ℕ, ∀ e : Fin d → ℤ, (∀ i, (e i).natAbs ≤ m) → ∑ i, (e i).natAbs = N →
      Relation.ReflTransGen (fun u v => supDist x u ≤ m ∧ supDist x v ≤ m ∧ NNAdj u v) x
        (x + fun i => (e i : ZMod n)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro e he hN
    by_cases h0 : ∀ i, e i = 0
    · have : (fun i => (e i : ZMod n)) = 0 := by funext i; simp [h0 i]
      rw [this]; simp only [add_zero]; exact Relation.ReflTransGen.refl
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      obtain ⟨s, hs, hlt⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (e i - s).natAbs < (e i).natAbs := by
        rcases lt_or_gt_of_ne hi with h | h
        · exact ⟨-1, Or.inr rfl, by omega⟩
        · exact ⟨1, Or.inl rfl, by omega⟩
      set e' : Fin d → ℤ := Function.update e i (e i - s) with he'
      have he'm : ∀ j, (e' j).natAbs ≤ m := by
        intro j
        by_cases hj : j = i
        · subst hj; simp only [he', Function.update_self]; exact hlt.le.trans (he j)
        · simp only [he', Function.update_of_ne hj]; exact he j
      have hsum : ∑ j, (e' j).natAbs < N := by
        rw [← hN]
        refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
        · by_cases hj : j = i
          · subst hj; simp only [he', Function.update_self]; exact hlt.le
          · simp only [he', Function.update_of_ne hj]; exact le_rfl
        · simp only [he', Function.update_self]; exact hlt
      refine (ih _ hsum e' he'm rfl).tail ⟨supDist_add_cast x e' m he'm,
        supDist_add_cast x e m he, ?_⟩
      have key : (x + fun j => (e j : ZMod n)) =
          (x + fun j => (e' j : ZMod n)) + Pi.single i (s : ZMod n) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [he']; ring
        · simp [he', hj]
      rcases hs with rfl | rfl
      · exact ⟨i, Or.inl (by simpa using key)⟩
      · refine ⟨i, Or.inr ?_⟩
        have : (x + fun j => (e' j : ZMod n)) =
            (x + fun j => (e j : ZMod n)) + Pi.single i (1 : ZMod n) := by
          rw [key]; funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [hj]
        exact this

/-- Cubes at index distance `≤ m` are joined by nearest-neighbour steps staying within index
distance `m` of the first. -/
theorem ball_reach {x y : Torus d n} {m : ℕ} (h : supDist x y ≤ m) :
    Relation.ReflTransGen (fun u v => supDist x u ≤ m ∧ supDist x v ≤ m ∧ NNAdj u v) x y := by
  have hi : ∀ i, ∃ t : ℤ, (t.natAbs ≤ m) ∧ (t : ZMod n) = x i - y i := by
    intro i
    obtain ⟨t, ht, htc⟩ := (cycNorm_le_iff _ _).1 (supDist_le_iff.1 h i)
    exact ⟨t, by rw [Int.abs_eq_natAbs] at ht; exact_mod_cast ht, htc⟩
  choose t ht1 ht2 using hi
  have hy : y = x + fun i => (((-t i : ℤ)) : ZMod n) := by
    funext i; simp [ht2 i]
  rw [hy]
  exact ball_reach_aux x m _ (fun i => -t i) (fun i => by simpa using ht1 i) rfl

/-- **The halo of a chain-linked set is nearest-neighbour connected.**  If any two cubes of `c`
are linked inside `c` by steps of index distance `< ω`, and `ω ≤ 2m`, then `nbhd m c` is
connected by nearest-neighbour steps inside it. -/
theorem halo_reach_of_linked {c : Set (Torus d n)} {m ω : ℕ} (hω : ω ≤ 2 * m)
    (hc : ∀ x ∈ c, ∀ y ∈ c, Linked ω c x y) :
    ∀ u ∈ nbhd m c, ∀ v ∈ nbhd m c, Relation.ReflTransGen
      (fun a b => a ∈ nbhd m c ∧ b ∈ nbhd m c ∧ NNAdj a b) u v := by
  have hsymm : ∀ a b : Torus d n, (a ∈ nbhd m c ∧ b ∈ nbhd m c ∧ NNAdj a b) →
      (b ∈ nbhd m c ∧ a ∈ nbhd m c ∧ NNAdj b a) :=
    fun _ _ h => ⟨h.2.1, h.1, nnAdj_symm h.2.2⟩
  have hA : ∀ x ∈ c, ∀ u, supDist x u ≤ m → Relation.ReflTransGen
      (fun a b => a ∈ nbhd m c ∧ b ∈ nbhd m c ∧ NNAdj a b) x u := by
    intro x hx u hu
    refine Relation.ReflTransGen.mono (fun a b hab => ⟨?_, ?_, hab.2.2⟩) _ _ (ball_reach hu)
    · exact mem_nbhd.2 ⟨x, hx, by rw [supDist_comm]; exact hab.1⟩
    · exact mem_nbhd.2 ⟨x, hx, by rw [supDist_comm]; exact hab.2.1⟩
  have hB : ∀ x ∈ c, ∀ y ∈ c, Relation.ReflTransGen
      (fun a b => a ∈ nbhd m c ∧ b ∈ nbhd m c ∧ NNAdj a b) x y := by
    intro x hx y hy
    have hl := hc x hx y hy
    induction hl with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      obtain ⟨ha, hb, hd⟩ := hab
      obtain ⟨z, hz1, hz2⟩ := exists_split (x := a) (z := b) (a := m) (b := m) (by omega)
      refine (ih ha).trans ((hA a ha z hz1).trans ?_)
      exact rtg_symm hsymm (hA b hb z (by rw [supDist_comm]; exact hz2))
  intro u hu v hv
  obtain ⟨x, hx, hux⟩ := mem_nbhd.1 hu
  obtain ⟨y, hy, hvy⟩ := mem_nbhd.1 hv
  refine (rtg_symm hsymm (hA x hx u (by rw [supDist_comm]; exact hux))).trans
    ((hB x hx y hy).trans (hA y hy v (by rw [supDist_comm]; exact hvy)))

end Cube

section Fine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]

/-- The fine set of a set of cubes is the preimage under the cube index `siteCube`. -/
theorem d7Pull_eq_preimage_siteCube (Fr : FineSizeFrame S n M K m₀ m₁) (k : ℕ)
    (A : Set (Torus S.d (n k))) :
    d7Pull Fr k A = siteCube (cellSide S.L m₀ m₁ k) (n k) ⁻¹' A := by
  have hcs : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
    unfold cellSide; rw [Fr.hM, ← pow_add]; congr 1; ring
  ext x
  rw [Set.mem_preimage, d7Pull_iff]
  have : cubeIdx Fr k x = siteCube (cellSide S.L m₀ m₁ k) (n k) x := by
    funext μ
    rw [cubeIdx_apply, hcs]; rfl
  rw [this]

/-- **A nearest-neighbour connected set of cubes has a site-connected fine set.** -/
theorem siteConnected_d7Pull (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (A : Set (Torus S.d (n k)))
    (hA : ∀ x ∈ A, ∀ y ∈ A, Relation.ReflTransGen (fun u v => u ∈ A ∧ v ∈ A ∧ NNAdj u v) x y) :
    SiteConnected (d7Pull Fr k A) := by
  have : NeZero (cellSide S.L m₀ m₁ k) := ⟨(cellSide_pos m₀ m₁ k).ne'⟩
  rw [d7Pull_eq_preimage_siteCube]
  intro x hx y hy
  exact reach_up (fine_side_eq Fr hnn hkK) A (hA _ hx _ hy) hx rfl rfl

end Fine

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

/-- The cubes of one component of `Z^pre_k` are linked to each other inside the component. -/
theorem RegionHistory.comp_linked (c : H.Comp k) {x y : Torus S.d (n k)} (hx : x ∈ c.1)
    (hy : y ∈ c.1) : Linked (S.omega k) ((c.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))
      x y := by
  have hl := ((mem_comp_iff c.2 hx).1 hy).2
  induction hl with
  | refl => exact Linked.refl _
  | @tail a b hxa hab ih =>
    have ha : a ∈ c.1 := (mem_comp_iff c.2 hx).2 ⟨hab.1, hxa⟩
    have hb : b ∈ c.1 := (mem_comp_iff c.2 hx).2 ⟨hab.2.1, hxa.tail hab⟩
    exact (ih ha).trans (Linked.single ha hb hab.2.2)

include H in
/-- **The halo of a component of `Z^pre_k` is nearest-neighbour connected** as soon as
`ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)`: two cubes of a component at distance `< ω_k` have overlapping halos of
radius `2⌊R_{k-1}⌋ + 4`. -/
theorem RegionHistory.halo_reach (c : H.Comp k)
    (hω : S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4)) :
    ∀ u ∈ nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))),
      ∀ v ∈ nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))),
      Relation.ReflTransGen (fun a b => a ∈ nbhd (2 * ⌊R (k - 1)⌋₊ + 4)
        (c.1 : Set (Torus S.d (n k))) ∧ b ∈ nbhd (2 * ⌊R (k - 1)⌋₊ + 4)
        (c.1 : Set (Torus S.d (n k))) ∧ NNAdj a b) u v :=
  halo_reach_of_linked hω fun _ hx _ hy => H.comp_linked c hx hy

include H in
/-- **The halo of a removed component lies in `Ω_k^post`** (`k ≥ 1`). -/
theorem RegionHistory.halo_subset_omegaPost (hk : 1 ≤ k) (c : H.Comp k) (hc : c.1 ∈ H.rem k) :
    nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))) ⊆ H.omegaPost k := by
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
  · have hd := H.halo_disjoint_comp hk (c := c) (c' := ⟨Y, hY⟩) (Ne.symm hcY)
    rw [RegionHistory.halo_eq_nbhd] at hd
    exact Set.disjoint_left.1 hd hx hxY


variable {M m₀ m₁ : ℕ}

include H in
/-- **The cells of the core of a removed component form a site-connected set.**  Let `c` be a
removed component of `Z^pre_k`, `k ≥ 1`, with `ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)`, and let the domain `lab`
of a heavy object be the halo `(c^{≈2})^{∼2} = nbhd (2⌊R_{k-1}⌋ + 4) c` (`halo_eq_nbhd`).  If
`zs` is the set of cells of `d7Pull Ω_k^post` with `Ŷ(sitesOf zs)` the fine set of `lab`, then
`sitesOf zs` is the fine set of `lab` and is nearest-neighbour connected. -/
theorem RegionHistory.siteConnected_sitesOf_halo (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (hk : 1 ≤ k) (c : H.Comp k)
    (hc : c.1 ∈ H.rem k) (hω : S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4))
    {lab : Finset (Torus S.d (n k))}
    (hlab : (lab : Set (Torus S.d (n k))) =
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))))
    {zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (H.omegaPost k)))}
    (hXZ : d7Pull Fr k (lab : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (H.omegaPost k)) (sitesOf zs)) :
    sitesOf zs = d7Pull Fr k (lab : Set (Torus S.d (n k))) ∧ SiteConnected (sitesOf zs) := by
  have hsub : (lab : Set (Torus S.d (n k))) ⊆ H.omegaPost k :=
    hlab ▸ H.halo_subset_omegaPost hk c hc
  have heq : sitesOf zs = d7Pull Fr k (lab : Set (Torus S.d (n k))) := by
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
  refine ⟨heq, ?_⟩
  rw [heq, hlab]
  exact siteConnected_d7Pull Fr hnn hkK _ (H.halo_reach c hω)

include H in
/-- The hypothesis on the radius holds when `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋`
(`omega_le_halo_sum`); for smaller radii it can fail, and then the halos of two cubes of one
component at distance `< ω_k` need not meet. -/
theorem RegionHistory.omega_le_halo_of_floor_eq (hk : 1 ≤ k)
    (hR : ⌊R (k - 1)⌋₊ = ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊) :
    S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4) := by
  rw [hR]; exact H.omega_le_halo_sum hk


include H in
/-- **The size of the core of a removed component is at most its number of cells** (`c2 = 1`,
volume-free): the cells `zs` of the core of a removed component with halo domain `lab` are
nonempty and site-connected (`siteConnected_sitesOf_halo`), so `dExt zs ≤ |zs|`
(`dExt_le_card_of_connected`) once `d7Pull lab ∈ 𝒟_k`. -/
theorem RegionHistory.dExt_removed_core_le_card (Fr : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hkK : k ≤ K) (hk : 1 ≤ k) (c : H.Comp k)
    (hc : c.1 ∈ H.rem k) (hω : S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4))
    {lab : Finset (Torus S.d (n k))}
    (hlab : (lab : Set (Torus S.d (n k))) =
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4) (c.1 : Set (Torus S.d (n k))))
    {zs : Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (H.omegaPost k)))}
    (hXZ : d7Pull Fr k (lab : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (H.omegaPost k)) (sitesOf zs))
    (hz : zs.Nonempty) (hDj : IsDj m₀ k (d7Pull Fr k (lab : Set (Torus S.d (n k))))) :
    dExt (d := S.d) zs ≤ 1 * (zs.card : ℝ) :=
  dExt_le_card_of_connected Fr.divN₁ hkK zs hz
    (H.siteConnected_sitesOf_halo Fr hnn hkK hk c hc hω hlab hXZ).2 (by rw [← hXZ]; exact hDj)

end Region

section Instance

open Balaban.Polymer RegionHistory Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **The physical large-field gas bound with the connectivity of the removed cores discharged**
(`notes/phase1/VMOD-43.md` §5d).  The instance `gas_activity_bound_physical_of_D7BdryPost` with
`hconnZ` replaced by its source: the domain `labZ z` of the heavy object `z` is the halo
`nbhd (2⌊R_{k-1}⌋ + 4)` of a removed component `cz z` of `Z^pre_k` (`k ≥ 1`), and
`ω_k ≤ 2(2⌊R_{k-1}⌋ + 4)` (true for `⌊R_{k-1}⌋ = ⌊R_base λ_{k-1}²⌋`,
`omega_le_halo_of_floor_eq`).  The constant of the size bound is `c2 = 1`, independent of the
torus, of `k` and of the component. -/
theorem gas_activity_bound_physical_of_D7BdryPost_halo {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁}
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
    (hk : 1 ≤ k) (hω : S.omega k ≤ 2 * (2 * ⌊R (k - 1)⌋₊ + 4))
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
  gas_activity_bound_physical_of_D7BdryPost hD hA hhB p labY hlabY hlabYv hp labZ hlabZ hDjZ hXY hXZ
    (fun z => (A.H.siteConnected_sitesOf_halo Fr hnn hkK hk (cz z) (hcz z) hω (hlabZ' z)
      (hXZ z)).2) hfac hκ' hκ'' hp' hκ hz hcr β hβ hτ hh X

end Instance

end Balaban.LargeField
