/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerHullPlusSize
public import Balaban.Inhabited.StepTowerNewLevelFibreRate
public import Balaban.Fluctuation.DetOutputTerms

/-!
# `hsum` for the labels with the thickened polymer `Y⁺` (`StepTowerHullPlus`)

The label of the cube set `T′` of index one is attached to the polymer
`Y⁺(T′) = sitesOf (piHull m₀ (thickSet G (sitesOf T′)))`, which contains the read set
`thickSet G (sitesOf T′)` of the coefficient (`subset_sitesOf_piHull`).  The hull map
`T′ ↦ Y⁺(T′)` satisfies the two properties of the generic cores
(`weighted_fibre_le_of_hull`, `newLabels_hsum_of_chain_bound_hull`): it contains the cubes of `T′`,
and `d_{m₀}(Y⁺(T′)) ≤ α′ (1 + dExt T′)` with `α′ = 1 + 3^d L^{2d} c₁ · 6 d L`
(`sizeJ_piHull_thick_le_dExt`).  Hence `newLabels_hsum_of_chain_bound_thick` is the statement of
`newLabels_hsum_of_chain_bound'` for `Y⁺` with `α′` in place of `α`, and
`tower_entropy_rate_thick` gives, at `d = L = 3`, the admissible range `κ ≤ 1/200` for the tower
(`α′ = 3587226751`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Localization Balaban.Polymer Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Thick

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {ϱ : ℝ}

open Classical in
/-- **The size of the hull of a thickened set against `dExt`.**  With
`α′ = 1 + 3^d L^{2d} c₁ · 6 d L`, `d_{m₀}(hull X) ≤ α′ (1 + dExt S)`. -/
theorem sizeJ_piHull_thick_le_dExt (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀) (hL : 3 ≤ L)
    (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ))
    {X : Set (CTorus d L N₁ m₁ K)} (hSX : sitesOf S ⊆ X)
    (hnear : ∀ s ∈ X, ∃ x ∈ sitesOf S, CellNear (L := L) (N₁ := N₁) (m₁ := m₁) m₀ K x s)
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ X))) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ X)) ≤
      (1 + ((L ^ d * L ^ d * 3 ^ d : ℕ) : ℝ) * c1 d L * (6 * d * L)) * (1 + dExt S) := by
  have hc1 := one_le_c1 d L
  have hq : (0 : ℝ) ≤ ((L ^ d * L ^ d * 3 ^ d : ℕ) : ℝ) * c1 d L * (6 * d * L) := by positivity
  have hd0 := dExt_nonneg S
  by_cases htop : dOmega 1 K Set.univ (sitesOf S) = ⊤
  · have hM' : dExt S = Mbig d L N₁ m₁ K := dExt_eq_Mbig htop
    have h1 := sizeJ_le_ncard_sq hY
    have h2 : (sitesOf (piHull m₀ X)).ncard ≤ Fintype.card (CTorus d L N₁ m₁ K) := by
      calc _ ≤ (Set.univ : Set (CTorus d L N₁ m₁ K)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = _ := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    have h3 : ((sitesOf (piHull m₀ X)).ncard : ℝ) ^ 2 ≤ Mbig d L N₁ m₁ K := by
      unfold Mbig
      have : ((sitesOf (piHull m₀ X)).ncard : ℝ) ≤ Fintype.card (CTorus d L N₁ m₁ K) := by
        exact_mod_cast h2
      nlinarith [Nat.cast_nonneg (α := ℝ) (sitesOf (piHull m₀ X)).ncard]
    rw [hM'] at hd0 ⊢
    nlinarith
  · have hne : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      exact htop (h ▸ dOmega_empty)
    obtain ⟨hS, hdE⟩ := isPolyDom_and_dExt_eq_sizeJ hne htop
    have h1 := sizeJ_piHull_thick_le hN hM hL hS hSX hnear hY
    have h2 := card_le_dExt (m₀ := 1) (j := K) (Ω := Set.univ) ((pow_dvd_pow L hM).trans hN)
      le_rfl S
    have h2' : ((L ^ d * L ^ d * (S.card * 3 ^ d) : ℕ) : ℝ) ≤
        ((L ^ d * L ^ d * 3 ^ d : ℕ) : ℝ) * (c1 d L * (1 + dExt S)) := by
      push_cast
      have := mul_le_mul_of_nonneg_left h2
        (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ d * (L : ℝ) ^ d * 3 ^ d)
      linarith
    have h4 : (0 : ℝ) ≤ 6 * d * L := by positivity
    have := mul_le_mul_of_nonneg_right h2' h4
    nlinarith

/-- **The thickened set of a cube set lies near its cells.**  For a generating set of level `K`
and `3 ≤ L^{m₀ + m₁}`, every site of `thickSet G (sitesOf T′)` lies in a cell of side `a_{m₀}` equal
or `*`-adjacent to the cell of a site of `sitesOf T′`. -/
theorem thickSet_near_sitesOf {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K)
    (hN : L ^ m₀ ∣ N₁) (h3 : 3 ≤ L ^ (m₀ + m₁))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)) :
    ∀ s ∈ thickSet G (sitesOf T), ∃ x ∈ sitesOf T,
      CellNear (L := L) (N₁ := N₁) (m₁ := m₁) m₀ K x s :=
  fun _ hv => thickSet_cellNear hG hN (detDepRadius_lt_cellSide h3 K) _ hv

open Classical in
/-- **`hsum` of the new-level theorem for the labels attached to `Y⁺`, for the two-term bound of the
class chain.**  The statement of `newLabels_hsum_of_chain_bound'` with the polymer
`Y⁺(T′) = sitesOf (piHull m₀ (thickSet G (sitesOf T′)))` and
`α′ = 1 + 3^d L^{2d} c₁ · 6 d L` in place of `α`. -/
theorem newLabels_hsum_of_chain_bound_thick
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K)
    (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀) (hL : 3 ≤ L) (h3 : 3 ≤ L ^ (m₀ + m₁))
    (b : RootIdx d L N₁ m₁ K → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) 1 K Set.univ) → ℝ)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) →
      CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (thickSet G (sitesOf T))) = Y then b (blockIndex y) T else 0)
    {A₁ A₂ ρ₁ ρ₂ ρ κ E₀ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hρ : aEnt d L + 1 ≤ ρ)
    (hρ₁ : ρ ≤ ρ₁) (hρ₂ : ρ ≤ ρ₂)
    (hb : ∀ z T, b z T ≤ A₁ * Real.exp (-ρ₁ * dExt T) + A₂ * Real.exp (-ρ₂ * dExt T))
    (hκ : κ < (ρ - (aEnt d L + 1)) /
      (1 + ((L ^ d * L ^ d * 3 ^ d : ℕ) : ℝ) * c1 d L * (6 * d * L)))
    (hE₀ : (A₁ + A₂) * ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) *
      (K0 d L (aEnt d L + 1) + 1) *
      (1 + 1 / ((ρ - (aEnt d L + 1)) /
        (1 + ((L ^ d * L ^ d * 3 ^ d : ℕ) : ℝ) * c1 d L * (6 * d * L)) - κ)) *
      Real.exp (ρ - (aEnt d L + 1)) ≤ E₀) :
    ∀ y (Y : Set (CTorus d L N₁ m₁ K)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y → y ∈ Y →
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y ≤
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  have hc1 := one_le_c1 d L
  have hq : (0 : ℝ) ≤ ((L ^ d * L ^ d * 3 ^ d : ℕ) : ℝ) * c1 d L * (6 * d * L) := by positivity
  have hsub : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K
      Set.univ), sitesOf T ⊆ thickSet G (sitesOf T) := fun _ _ hx => Or.inl hx
  refine newLabels_hsum_of_chain_bound_hull hN hM
    (fun T => sitesOf (piHull m₀ (thickSet G (sitesOf T)))) (α := 1 + ((L ^ d * L ^ d * 3 ^ d : ℕ) :
      ℝ) * c1 d L * (6 * d * L)) (by linarith) (fun T β hβ x hx =>
      subset_sitesOf_piHull hN _ (hsub T (mem_sitesOf.2 ⟨β, hβ, hx⟩)))
    (fun T y hy => ?_) (fun T hT => ?_) b EbE hEbE hA₁ hA₂ hρ hρ₁ hρ₂ hb hκ hE₀
  · rw [sitesOf_piHull hN] at hy
    obtain ⟨_, ⟨_, s, _, hs⟩, _⟩ := Set.mem_iUnion₂.1 hy
    rcases hs with hs | ⟨x, hx, _⟩
    · obtain ⟨β, hβ, _⟩ := mem_sitesOf.1 hs
      exact ⟨β, hβ⟩
    · obtain ⟨β, hβ, _⟩ := mem_sitesOf.1 hx
      exact ⟨β, hβ⟩
  · exact sizeJ_piHull_thick_le_dExt hN hM hL T (hsub T) (thickSet_near_sitesOf hG hN h3 T) hT

end Thick

/-- **The rate of the entropy count with `Y⁺` at the tower.**  For `d = L = 3` and `κ′` of a
`StepTower`, `1/200 < (κ′ - a_ent - 1)/α′`, `α′ = 1 + (3^3 · 3^3 · 3^3) c₁ (6 · 3 · 3)`
`= 3587226751`; every class `κ ∈ (0, 1/200]` is admissible. -/
theorem tower_entropy_rate_thick {κmin : ℝ} (T : StepTower κmin) :
    aEnt 3 3 + 1 ≤ T.κ' ∧ (1 : ℝ) / 200 < (T.κ' - (aEnt 3 3 + 1)) /
      (1 + ((3 ^ 3 * 3 ^ 3 * 3 ^ 3 : ℕ) : ℝ) * c1 3 3 * (6 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) := by
  have hc : c1 3 3 = 3375 := by unfold c1; norm_num
  have hge := aEnt_three_ge
  have e1 := T.κ'_eq
  have e2 := T.κdec_eq
  have e3 := T.κ0_eq
  have hα : (1 + ((3 ^ 3 * 3 ^ 3 * 3 ^ 3 : ℕ) : ℝ) * c1 3 3 *
      (6 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) = 3587226751 := by rw [hc]; norm_num
  rw [hα]
  refine ⟨by rw [e1, e2, e3, hc]; nlinarith, ?_⟩
  rw [lt_div_iff₀ (by norm_num)]
  rw [e1, e2, e3, hc]
  nlinarith

end Balaban.Inhabited
