/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivRelabel
public import Balaban.Localization.I5Param
public import Balaban.Polymer.TwoTorusDet
public import Balaban.Polymer.TwoTorusLift
public import Balaban.Polymer.TwoTorusDomainFamilies
public import Balaban.Fluctuation.MarkedVRawY
public import Balaban.Fluctuation.MarkedFanAnalytic
public import Balaban.Fluctuation.MarkedVBlockDec
public import Balaban.Fluctuation.MarkedFluctRows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked energy coefficients on two tori

## D1: the coefficients under a partial relabelling of the parameters

* `eq_of_sum_powerset_eq_of_subset`: a function on the subsets of a finite set `C` is determined
  by its sums over the powersets of the subsets of `C`.
* `coef_relabel_injOn`: if `e : ι → ι'` is injective on a finite family `C` of parameters and
  `f' (s') = f (s)` whenever `s` vanishes off `C` with `|s_i| < R` and `s'` vanishes off `e C`
  with `s' (e i) = s i` on `C`, then `coef f' (e C) = coef f C` (`f` analytic on the polydisc of
  radius `R > 1`).  This is `coef_relabel` for a map that is a bijection only between `C` and its
  image; the values of `f` and `f'` off the cut points `supN C R` are not compared.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis

/-! ### D1: the coefficients under a partial relabelling -/

section Relabel

variable {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']

omit [Fintype ι] in
/-- A function on the subsets of a finite set `C` is determined by its sums over the powersets of
the subsets of `C` (`eq_of_sum_powerset_eq` restricted to the subsets of `C`). -/
theorem eq_of_sum_powerset_eq_of_subset {g h : Finset ι → ℂ} {C : Finset ι}
    (hgh : ∀ A ⊆ C, ∑ B ∈ A.powerset, g B = ∑ B ∈ A.powerset, h B) :
    ∀ A ⊆ C, g A = h A := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hAC
    have e := hgh A hAC
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self A),
      ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self A)] at e
    have : ∑ B ∈ A.powerset.erase A, g B = ∑ B ∈ A.powerset.erase A, h B :=
      Finset.sum_congr rfl fun B hB => by
        obtain ⟨hne, hsub⟩ := Finset.mem_erase.1 hB
        have hBA := Finset.mem_powerset.1 hsub
        exact ih B (Finset.ssubset_iff_subset_ne.2 ⟨hBA, hne⟩) (hBA.trans hAC)
    rw [this] at e
    exact add_right_cancel e

/-- **D1: the coefficients under a relabelling that is a bijection between `C` and its image.**
Let `e : ι → ι'` be injective on the finite family `C`, `f` analytic on the polydisc of radius
`R > 1`, and assume `f' (s') = f (s)` for every `s` vanishing off `C` with `|s_i| < R` and every
`s'` vanishing off `e C` with `s' (e i) = s i` for `i ∈ C`.  Then `coef f' (e C) = coef f C`.
Proof: `coef f' (e C)` reads `f'` only on `supN (e C) R` (`coef_congr_near`), where `f'` is the
analytic function `g = f ∘ e^*`, `e^* w = (i ↦ 1_C(i) w (e i))`; the coefficients of `g` on the
subsets of `e C` and of `f` on the subsets of `C` have the same sums over powersets (the values at
the indicator points, `sum_coef_unit`), hence agree (`eq_of_sum_powerset_eq_of_subset`). -/
theorem coef_relabel_injOn {R : ℝ} (hR : 1 < R) (e : ι → ι') {C : Finset ι}
    (he : Set.InjOn e C) {f : (ι → ℂ) → ℂ} {f' : (ι' → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hff : ∀ s ∈ supN C R, ∀ s' : ι' → ℂ, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → f' s' = f s) :
    coef f' (C.image e) = coef f C := by
  classical
  have hR0 : 0 < R := by linarith
  -- the pull-back of the parameters
  set pb : (ι' → ℂ) → (ι → ℂ) := fun w i => if i ∈ C then w (e i) else 0 with hpb
  set g : (ι' → ℂ) → ℂ := fun w => f (pb w) with hg
  have h1 : coef f' (C.image e) = coef g (C.image e) := by
    refine coef_congr_near hR fun w hw => ?_
    refine hff (pb w) ⟨fun i hi => by simp [hpb, hi], fun i => ?_⟩ w hw.1
      (fun i hi => by simp [hpb, hi])
    by_cases hi : i ∈ C
    · simp only [hpb, hi, ↓reduceIte]; exact hw.2 _
    · simp only [hpb, hi, ↓reduceIte, norm_zero]; exact hR0
  rw [h1]
  -- `g` is analytic on the polydisc
  have hpbA : ∀ w, AnalyticAt ℂ pb w := by
    intro w
    rw [analyticAt_pi_iff]
    intro i
    by_cases hi : i ∈ C
    · have : (fun w : ι' → ℂ => pb w i) = fun w => w (e i) := by
        funext w; simp [hpb, hi]
      rw [this]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι' => ℂ) (e i)).analyticAt w
    · have : (fun w : ι' → ℂ => pb w i) = fun _ => 0 := by
        funext w; simp [hpb, hi]
      rw [this]
      exact analyticAt_const
  have hpbP : ∀ w ∈ polydisc (0 : ι' → ℂ) (fun _ => R), pb w ∈ polydisc (0 : ι → ℂ) (fun _ => R) := by
    intro w hw i
    by_cases hi : i ∈ C
    · simpa [hpb, hi] using hw (e i)
    · simpa [hpb, hi] using hR0
  have hgA : AnalyticOnNhd ℂ g (polydisc (0 : ι' → ℂ) (fun _ => R)) := fun w hw =>
    (hf (pb w) (hpbP w hw)).comp (hpbA w)
  -- the indicator points
  have key : ∀ A ⊆ C, g (indic (A.image e)) = f (indic A) := by
    intro A hAC
    simp only [hg]
    congr 1
    funext i
    by_cases hi : i ∈ C
    · have hiff : e i ∈ A.image e ↔ i ∈ A := by
        constructor
        · intro h
          obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 h
          have := he (Finset.mem_coe.2 (hAC ha)) (Finset.mem_coe.2 hi) hae
          exact this ▸ ha
        · intro h; exact Finset.mem_image_of_mem e h
      simp only [hpb, hi, ↓reduceIte, indic, hiff]
    · have hiA : i ∉ A := fun h => hi (hAC h)
      simp [hpb, hi, indic, hiA]
  have hsum : ∀ A ⊆ C, ∑ B ∈ A.powerset, coef g (B.image e) =
      ∑ B ∈ A.powerset, coef f B := by
    intro A hAC
    have e1 : ∑ B ∈ A.powerset, coef g (B.image e) =
        ∑ B' ∈ (A.image e).powerset, coef g B' := by
      refine Finset.sum_nbij' (fun B => B.image e) (fun B' => A.filter fun i => e i ∈ B')
        (fun B hB => ?_) (fun B' hB' => ?_) (fun B hB => ?_) (fun B' hB' => ?_) (fun B _ => rfl)
      · exact Finset.mem_powerset.2 (Finset.image_subset_image (Finset.mem_powerset.1 hB))
      · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
      · have hBA := Finset.mem_powerset.1 (Finset.mem_coe.1 hB)
        ext i
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hiA, b, hb, hbe⟩
          have := he (Finset.mem_coe.2 (hAC (hBA hb))) (Finset.mem_coe.2 (hAC hiA)) hbe
          exact this ▸ hb
        · intro hi
          exact ⟨hBA hi, i, hi, rfl⟩
      · have hB'A := Finset.mem_powerset.1 (Finset.mem_coe.1 hB')
        ext j
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨-, hi⟩, rfl⟩; exact hi
        · intro hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hB'A hj)
          exact ⟨i, ⟨hi, hj⟩, rfl⟩
    rw [e1, ← sum_coef_unit hR hgA, ← sum_coef_unit hR hf, key A hAC]
  exact eq_of_sum_powerset_eq_of_subset hsum C subset_rfl

end Relabel

open scoped Classical

open Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### The block energy on two tori -/

section Energy

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)

/-- The extended field `svec` of `levelGS k` at corresponding sites (every site lies in `Ω₁`). -/
theorem svec_levelGS_boxMap (hk : 1 ≤ k) {δφ : (HA).Ω 1 × Fin N → ℂ}
    {δφ' : (HB).Ω 1 × Fin N → ℂ} {y : CTorus d L N₁ m₁ (k + 1)}
    (h : ∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) = y →
      (w' : CTorus d L N₁' m₁ (k + 1)) = bm y → ∀ i, δφ' (w', i) = δφ (w, i)) (i : Fin N) :
    svec (HB) δφ' (bm y) i = svec (HA) δφ y i := by
  have hy : y ∈ (HA).Ω 1 := levelGS_mem_Ω_one hk (Nat.le_succ k) y
  have hy' : bm y ∈ (HB).Ω 1 := levelGS_mem_Ω_one hk (Nat.le_succ k) _
  rw [svec_of_mem' _ hy, svec_of_mem' _ hy']
  exact h ⟨y, hy⟩ ⟨bm y, hy'⟩ rfl rfl i

/-- The `k`-block mean of `levelGS k` at corresponding sites.  Margin:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem blockMean_levelGS_boxMap {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {f : CTorus d L N₁ m₁ (k + 1) → ℂ} {f' : CTorus d L N₁' m₁ (k + 1) → ℂ}
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hf : ∀ y ∈ (HA).blk k x, f' (bm y) = f y) :
    blockMean (HB) k f' (bm x) = blockMean (HA) k f x := by
  have hK : L ^ k ≤ L ^ (k + 1) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ k)
  have hbox : ∀ z ∈ box (cbase (L ^ k) x) (L ^ k),
      InBox d (ρ + L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1)) z :=
    fun z hz => inBox_of_mem_cell (by omega) hx hz
  have hblk := blk_image (r := ρ + L ^ k) (j := k) (N₁' := N₁') (HA) (HB) (Nat.le_succ k)
    (by omega) x hbox
  have hblkF : ((HA).blk k x).image bm = (HB).blk k (bm x) := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact hblk
  have hmem : ∀ y ∈ (HA).blk k x, InBox d (ρ + L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1)) y :=
    fun y hy => hbox y ((jBlock_eq_iff_mem_box (Nat.le_succ k) y x).1
      (GeneratingSet.mem_blk.1 hy))
  unfold blockMean
  rw [← hblkF, Finset.sum_image]
  · congr 1
    exact Finset.sum_congr rfl fun y hy => hf y hy
  · intro y hy y' hy' h
    exact boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ k) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
      (hmem y hy) (hmem y' hy') h

/-- **The energy density at corresponding sites.**  If the multipliers correspond at `x`, the
fluctuation fields at `x`, its right neighbours and its `k`-block, and the tangents at `x`, the
energy densities at `x` and `bm x` are equal.  Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and
for `N₁'`). -/
theorem energyDensity_levelGS_boxMap (hk : 1 ≤ k) {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (a : ℕ → ℝ) (ν : ℝ) {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    {δφ : (HA).Ω 1 × Fin N → ℂ} {δφ' : (HB).Ω 1 × Fin N → ℂ}
    {ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {ψ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hα : ∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) = x →
      (y' : CTorus d L N₁' m₁ (k + 1)) = bm x → α' y' = α y)
    (hδ : ∀ (w : (HA).Ω 1) (w' : (HB).Ω 1),
      ((w : CTorus d L N₁ m₁ (k + 1)) = x ∨
        (∃ μ : Fin d, (w : CTorus d L N₁ m₁ (k + 1)) = x + Pi.single μ 1) ∨
        (w : CTorus d L N₁ m₁ (k + 1)) ∈ (HA).blk k x) →
      (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
      ∀ i, δφ' (w', i) = δφ (w, i))
    (hψ : ψ' (bm x) = ψ x) :
    energyDensity (GB) (HB) a ν k α' δφ' ψ' (bm x) =
      energyDensity (GA) (HA) a ν k α δφ ψ x := by
  have hxH : x ∈ (HA).Ω 1 := levelGS_mem_Ω_one hk (Nat.le_succ k) x
  have hxH' : bm x ∈ (HB).Ω 1 := levelGS_mem_Ω_one hk (Nat.le_succ k) _
  have hxG : x ∈ (GA).Ω 1 := levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl x
  have hxG' : bm x ∈ (GB).Ω 1 := levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl _
  have hsv : ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ (HA).blk k x) →
      ∀ i, svec (HB) δφ' (bm y) i = svec (HA) δφ y i := by
    intro y hy i
    refine svec_levelGS_boxMap hk (fun w w' hw hw' i => hδ w w' ?_ ?_ i) i
    · rw [hw]; exact hy
    · rw [hw]; exact hw'
  have h0 : ∀ i, svec (HB) δφ' (bm x) i = svec (HA) δφ x i := fun i => hsv x (Or.inl rfl) i
  have h1 : ∀ (μ : Fin d) (i : Fin N), svec (HB) δφ' (bm x + Pi.single μ 1) i =
      svec (HA) δφ (x + Pi.single μ 1) i := by
    intro μ i
    rw [← boxMap_add_single (by omega) (by omega) hx μ]
    exact hsv _ (Or.inr (Or.inl ⟨μ, rfl⟩)) i
  have hb : ∀ i, blockMean (HB) k (fun y => svec (HB) δφ' y i) (bm x) =
      blockMean (HA) k (fun y => svec (HA) δφ y i) x := fun i =>
    blockMean_levelGS_boxMap hn hn' hx (fun y hy => hsv y (Or.inr (Or.inr hy)) i)
  have hz : zeroExt ((GB).Ω 1) α' (bm x) = zeroExt ((GA).Ω 1) α x := by
    simp only [zeroExt, hxG, hxG', dite_true]
    exact hα _ _ rfl rfl
  unfold energyDensity
  simp only [hxH, hxH', ↓reduceIte, h0, h1, hb, hz, hψ]

/-- **The block energy at corresponding blocks.**  For a site `x₀` of the box of radius `ρ`, the
block energies of the `(k+1)`-blocks of `x₀` and of `bm x₀` are equal when the multipliers and the
tangents correspond on the block and the fluctuation fields on the read sites `readSites`.
Margin: `2 (ρ + L^(k+1)) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem energyBlock_levelGS_boxMap (hk : 1 ≤ k) {ρ : ℕ}
    (hn : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (a : ℕ → ℝ) (ν : ℝ) {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    {δφ : (HA).Ω 1 × Fin N → ℂ} {δφ' : (HB).Ω 1 × Fin N → ℂ}
    {ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {ψ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    (hα : ∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈
        blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) →
      (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) → α' y' = α y)
    (hδ : ∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈
        readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) →
      (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
      ∀ i, δφ' (w', i) = δφ (w, i))
    (hψ : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀),
      ψ' (bm x) = ψ x) :
    energyBlock (GB) (HB) a ν k α' δφ' ψ' (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀)) =
      energyBlock (GA) (HA) a ν k α δφ ψ (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  set S := blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) with hS
  have hSbox : ∀ x ∈ S, InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    have hxj : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀ := (Finset.mem_filter.1 hx).2
    exact inBox_of_jBlock_eq le_rfl (by omega) hx₀ hxj
  have hx₀' : InBox d ρ ((N₁' * L ^ m₁) * L ^ (k + 1)) (bm x₀) := inBox_boxMap (by omega) hx₀
  have himg : S.image bm = Finset.univ.filter (fun x' : CTorus d L N₁' m₁ (k + 1) =>
      jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) x' =
        jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀)) := by
    ext x'
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxj : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
          jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀ := (Finset.mem_filter.1 hx).2
      exact (jBlock_boxMap_iff (ρ := ρ + L ^ (k + 1)) le_rfl (by omega) (by omega) (hSbox x hx)
        (inBox_mono (Nat.le_add_right _ _) hx₀)).1 hxj
    · intro hx'
      have hx'R : InBox d (ρ + L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) x' :=
        inBox_of_jBlock_eq (N₁ := N₁') le_rfl (by omega) hx₀' hx'
      have hback : bm (bm' x') = x' := boxMap_boxMap (by omega) hx'R
      have hyR : InBox d (ρ + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) (bm' x') :=
        inBox_boxMap (by omega) hx'R
      refine ⟨bm' x', ?_, hback⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      refine (jBlock_boxMap_iff (ρ := ρ + L ^ (k + 1)) le_rfl (by omega) (by omega) hyR
        (inBox_mono (Nat.le_add_right _ _) hx₀)).2 ?_
      rw [hback]; exact hx'
  unfold energyBlock
  rw [← himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun x hx => ?_
    refine energyDensity_levelGS_boxMap hk hn hn' a ν (hSbox x hx)
      (fun y y' hy hy' => hα y y' (by rw [hy]; exact hx) (by rw [hy']; rw [hy]))
      (fun w w' hw hw' i => hδ w w' ⟨x, hx, hw⟩ hw' i) (hψ x hx)
  · intro x hx x' hx' h
    exact boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ (k + 1)) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
      (hSbox x hx) (hSbox x' hx') h

/-- **The block functional at corresponding blocks** (the two-torus form of
`blockEnergyFun_local_sharp`): it reads the multiplier and the tangent on the block, the
fluctuation field on `readSites`. -/
theorem blockEnergyFun_levelGS_boxMap (hk : 1 ≤ k) {ρ : ℕ}
    (hn : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (a : ℕ → ℝ) (ν : ℝ)
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    {t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    {t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))}
    (hα : ∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈
        (↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) :
          Set (CTorus d L N₁ m₁ (k + 1))) →
      (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) → t'.1.2 y' = t.1.2 y)
    (hδ : ∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈
        readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) →
      (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
      ∀ i, t'.2.1 (w', i) = t.2.1 (w, i))
    (hψ : ∀ x ∈ (↑(blockSites d L N₁ m₁ (k + 1) k
        (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) : Set (CTorus d L N₁ m₁ (k + 1))),
      t'.2.2.2 (bm x) = t.2.2.2 x) :
    blockEnergyFun (GB) (HB) a ν k (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀))
        t'.1 t'.2.1 t'.2.2 =
      blockEnergyFun (GA) (HA) a ν k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)
        t.1 t.2.1 t.2.2 :=
  energyBlock_levelGS_boxMap hk hn hn' a ν hx₀ (fun y y' hy hy' => hα y y' hy hy') hδ
    (fun x hx => hψ x hx)

end Energy

/-! ### The masked tangent on two tori -/

section Tangent

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)

/-- **The decoupled square root `C^{1/2}(s)` at the decoupled background, on two tori** (the
two-torus form of `hatSqrtF_rows_of_bgAgree`).  Let `D`, `D'` be data of the charts
`Ξ^c(𝔹_{k+1}; 1, ε)` of the top levels of the two tori (`FlCore` on each torus), `F₁`, `F₁'` maps
with the defining property of the decoupled background pair, `s`, `s'` cut parameters in the
polydisc of radius `e^κ`, and `(Y, S_Y)`, `(Y', S_{Y'})` corresponding components of the cut with
corresponding cut factors, `Y` a union of complete `(k+1)`-blocks.  If the raw data agree on
`RowsDep (S_Y)` and the hat variables at the unit points whose block lies in `Y`, the rows of
`hatSqrtF s' (rawOf D') ψ̂'` and `hatSqrtF s (rawOf D) ψ̂` agree at these unit points.  The
background values are `decBg_value_twoTorus`, the read sites of the `x`-variant rows
`rowsCov_R_mem_Y_and_rowsDep`, the standing hypotheses `covStanding_of_mem` at `decDom_of_isDecBg`,
and the rows `decCovSqrt_rows_transport_of_complete`.  Margin:
`4 R + 12 L^(k+1+m₁) + 7 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem hatSqrtF_rows_twoTorus {ϱm ϱm' : ℝ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {s : DecParams (GA)} {s' : DecParams (GB)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → extS (GA) s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → extS (GB) s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) (extS (GB) s') (Prod.map id bm q) = sProd (GA) (extS (GA) s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | RowsDep (GA) (compWeight L a₁) ν (SY (GA) X₁ 𝒞 Y) z} (rawOf D)
      (rawOf D'))
    (hcomp : CompleteBlocks (GA) Y)
    (ψh : unitPts (GA) × Fin N → ℂ) (ψh' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b : unitPts (GA), UnitOut (GA) Y b → ∀ i, ψh' (ιu b, i) = ψh (b, i))
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) (i : Fin N) :
    (hatSqrtF (GB) a₁ ν F₁' s' (rawOf D') *ᵥ ψh') (ιu b, i) =
      (hatSqrtF (GA) a₁ ν F₁ s (rawOf D) *ᵥ ψh) (b, i) := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC'.HBp hC'.small1 hD'
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨φ', α', hI', -⟩ := i4b_exists_unique hC'.hS hC'.Sp hC'.HBp hC'.hκ.le hC'.hM
    (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom'
  have hU := inUnionDomainC_of_xiCData hC hD
  have hU' := inUnionDomainC_of_xiCData hC' hD'
  have hFeq := hF₁ s D hs hU φ α hI
  have hFeq' := hF₁' s' D' hs' hU' φ' α' hI'
  obtain ⟨hmult, -, hfld, -⟩ := decBg_value_twoTorus hj1 le_rfl hC.hS hC.Sp hC'.Sp hconn hconn'
    hC.HBp hC.hκ.le hC.hM hF₁ hF₁' hs hs' hU hU' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hraw
  rw [hFeq, hFeq'] at hmult hfld
  have hX : XSetting (GA) (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hX' : XSetting (GB) (compWeight L a₁) a₁ ν := xSetting_of_flCore hC' hk
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have St := covStanding_of_mem (N := N) (Q := unitQ (GA)) (P := unitP (GA)) hX hC.hκ.le hMX hδc
    hsm (isUnitLatticeB_unit (G := GA)).toIsUnitLattice (decDom_of_isDecBg hC hs hD hI hmar hαK)
  have St' := covStanding_of_mem (N := N) (Q := unitQ (GB)) (P := unitP (GB)) hX' hC'.hκ.le hMX
    hδc hsm (isUnitLatticeB_unit (G := GB)).toIsUnitLattice
    (decDom_of_isDecBg hC' hs' hD' hI' hmar hαK)
  unfold hatSqrtF
  rw [hFeq, hFeq']
  refine decCovSqrt_rows_transport_of_complete hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR
    (by omega) (by omega) (fun x hx => hmult x hx) (fun u hu => ?_) St.fam St'.fam St.field
    St'.field St.nonneg St.small hcomp ψh ψh' hh hb i
  obtain ⟨huY, hdep⟩ := rowsCov_R_mem_Y_and_rowsDep (a := compWeight L a₁) (ν := ν) hX hu
  funext i
  simp only [barField, levelGS_mem_Ω_one hj1 le_rfl, ↓reduceDIte]
  exact hfld ⟨u, levelGS_mem_Ω_one hj1 le_rfl u⟩ huY (fun z hz => hraw z (hdep z hz)) i

/-- **The masked tangent at corresponding sites.**  If the masks correspond at the unit point of a
site `x` of the box and the rows of the square roots `hatSqrtF *ᵥ ψ̂` correspond at it, the masked
tangents `markedHatPsiF` agree at `x` and `bm x`.  Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem markedHatPsiF_boxMap {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (a₁ ν : ℝ) (cc : ℂ)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    {Z : Finset (unitPts (GA))} {Z' : Finset (unitPts (GB))} (u t : ℂ)
    {s : DecParams (GA)} {s' : DecParams (GB)} {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    {Θ' : RawData d L (N₁' * L ^ m₁) (k + 1) N}
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hZ : unitPt hGB (bm x) ∈ Z' ↔ unitPt hGA x ∈ Z)
    (hrow : ∀ i, (hatSqrtF (GB) a₁ ν F₁' s' Θ' *ᵥ ψh') (ιu (unitPt hGA x), i) =
      (hatSqrtF (GA) a₁ ν F₁ s Θ *ᵥ ψh) (unitPt hGA x, i)) :
    markedHatPsiF a₁ ν hGB cc F₁' Z' u t s' Θ' ψh' (bm x) =
      markedHatPsiF a₁ ν hGA cc F₁ Z u t s Θ ψh x := by
  funext i
  rw [markedHatPsiF_apply, markedHatPsiF_apply]
  have hu := unitPt_boxMap hn hGA hGB hx
  have hpsi : hatPsiF (GB) a₁ ν hGB cc F₁' s' Θ' ψh' (bm x) i =
      hatPsiF (GA) a₁ ν hGA cc F₁ s Θ ψh x i := by
    unfold hatPsiF
    simp only [liftC_apply, Pi.smul_apply, smul_eq_mul]
    rw [hu, hrow i]
  rw [hpsi]
  by_cases h : unitPt hGA x ∈ Z
  · simp [h, hZ.2 h]
  · simp [h, mt hZ.1 h]

end Tangent

/-! ### D2: the marked functional at transported cut parameters -/

section Slice

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

/-- `extS_extParams_boxMap` at the top level, for a set `S'` of the second torus equal to the
image `bm '' X₁` (the parameter type `ParIdx GB S'` is not rewritten). -/
theorem extS_extParams_boxMap_of_eq {R : ℕ}
    (hn : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {S' : Set (CTorus d L N₁' m₁ (k + 1))} (hS' : S' = bm '' X₁)
    (σ : ParIdx (GA) X₁ → ℂ) (σ' : ParIdx (GB) S' → ℂ)
    (hσ : ∀ (i : ParIdx (GA) X₁) (i' : ParIdx (GB) S'),
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2 → i'.1.1 = Prod.map id bm i.1.1 →
        σ' i' = σ i)
    {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx (GA))
    (hP0 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2) :
    extS (GB) (extParams (GB) S' σ') (Prod.map id bm P) =
      extS (GA) (extParams (GA) X₁ σ) P := by
  subst hS'
  exact extS_extParams_boxMap (Nat.le_add_left 1 k) le_rfl hn hn' hX σ σ' hσ hP hP0

/-- **D2: the marked functional at transported cut parameters.**  On two tori with the top level
`GA = levelGS (k+1)` and the lower level `HA = levelGS k` (the pair of a step, `FlCore` on each
torus with the same constants), let `X₁f` be the set `X₁` of a covering setup on the first torus
and `X₁f.image bm` that of a covering setup on the second torus, `C` a finite family of parameter
cubes, and `X₁f` and the cubes of `C` in the box of radius `R`.  Let `s` be a cut parameter
vector vanishing off `C` with `|s_i| < e^κ`, and `s'` its transport: `s' = 0` at the indices that
are not images of indices of `C`, and `s' i' = s i` when the centre of `i'` is the image of the
centre of `i ∈ C`.  Let `D`, `D'` be data of the charts whose raw parts agree on the box of radius
`R + 3 L^(k+1)`, `ψ̂`, `ψ̂'` hat variables (bounded by `c_ψ`) agreeing at the unit points of the
sites of the box of radius `R`, the masks `Zm`, `Zm'` corresponding at these unit points, and the
marks `(um, tm)` in the radius set.  Let `Φ`, `Φ'` be block functionals that read the multiplier
on `Rα` (with the margin `BlockMargin` against `X₁f`), the fluctuation field on `Rδ ⊆ X₁f` and
the tangent on `Rψ ⊆ X₁f`, and take equal values on corresponding inputs (`hΦ`).  Then the marked
functional `FFmarked` of the second torus at `s'` equals that of the first torus at `s`, for any
maps `F₁`, `Sol` (and `F₁'`, `Sol'`) with the defining properties of the decoupled background
pair and of the decoupled fluctuation solution.

The cut configuration is `𝒞 = {centres of C}`, `Y = V(X₁f, 𝒞)` (all of it; a union of components
of the cut and of complete `(k+1)`-blocks); the background values are `decBg_value_twoTorus`, the
fluctuation values `decSol_value_twoTorus_of_decBg` (with the incidence unions of
`incUnion_of_nnComp`), the tangents `hatSqrtF_rows_twoTorus` and `markedHatPsiF_boxMap`.
Margins: `4 R + 12 L^(k+1+m₁) + 7 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and
`2 ρ₁ + 5 L · cellSide L 0 m₁ (k+1) < N₁ L^m₁ L^(k+1)`,
`ρ₁ = R + (3 L^(k+1+m₁) + 3 L^(k+3)) + L^(k+1+m₁)` (and for `N₁'`). -/
theorem FFmarked_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hrow : RowInHat (coverOf (GA)) (HA) (compWeight L a₁) ν)
    (hrow' : RowInHat (coverOf (GB)) (HB) (compWeight L a₁) ν)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {Φ : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) X₁f Rα)
    (hRδ : Rδ ⊆ ↑X₁f) (hRψ : Rψ ⊆ ↑X₁f)
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) → t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    {R : ℕ} (hXR : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (C : Finset (ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))))
    (hCR : ∀ i ∈ C, ∀ x ∈ Pset m₁ i.1.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {s : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ} (hs : s ∈ supN C (Real.exp κ))
    {s' : ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) → ℂ}
    (hs'0 : ∀ i', (∀ i ∈ C, i'.1.1 ≠ Prod.map id bm i.1.1) → s' i' = 0)
    (hss' : ∀ i ∈ C, ∀ i', i'.1.1 = Prod.map id bm i.1.1 → s' i' = s i)
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    FFmarked (X₁f.image bm) a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm (rawOf D', ψh') s' =
      FFmarked X₁f a₁ ν hGA cc F₁ Sol Φ Zm um tm (rawOf D, ψh) s := by
  classical
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hΩA : ∀ x : CTorus d L N₁ m₁ (k + 1), x ∈ (GA).Ω 1 := levelGS_mem_Ω_one hj1 le_rfl
  have hΩB : ∀ x : CTorus d L N₁' m₁ (k + 1), x ∈ (GB).Ω 1 := levelGS_mem_Ω_one hj1 le_rfl
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hkK : L ^ k ≤ L ^ (k + 1) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ k)
  have hcs : L ^ (k + 1 + m₁) ≤ L * cellSide L 0 m₁ (k + 1) := by
    unfold cellSide
    rw [Nat.add_zero]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  -- the cut parameters
  have hs'b : ∀ i', ‖s' i'‖ < Real.exp κ := by
    intro i'
    by_cases h : ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1
    · obtain ⟨i, hi, he⟩ := h
      rw [hss' i hi i' he]
      exact hs.2 i
    · rw [hs'0 i' (fun i hi he => h ⟨i, hi, he⟩), norm_zero]
      exact Real.exp_pos κ
  set σ := extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s with hσdef
  set σ' := extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s' with hσ'def
  have hσb : ∀ P, ‖σ P‖ < Real.exp κ := norm_extParams_lt hE1 (fun i => hs.2 i)
  have hσb' : ∀ P, ‖σ' P‖ < Real.exp κ := norm_extParams_lt hE1 hs'b
  -- the cut configuration
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) :=
    C.image (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) with h𝒞
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) :=
    (Vset X₁f 𝒞).filter fun x => x ∈ (GA).Ω 1 with hYdef
  have hYV : Y = Vset X₁f 𝒞 := Finset.filter_true_of_mem fun x _ => hΩA x
  have h𝒞I : ∀ P ∈ 𝒞, P ∈ cubeIdx (GA) := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact i.1.2
  have h𝒞R : ∀ P ∈ 𝒞, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP
    exact hCR i hi _ (self_mem_Pset _)
  have hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    rw [hYV] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hXR x hx
    · obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP
      have hxP' : x ∈ ((cubeP i.1.1 : Finset (CTorus d L N₁ m₁ (k + 1))) :
          Set (CTorus d L N₁ m₁ (k + 1))) := Finset.mem_coe.2 hxP
      rw [coe_cubeP_eq_Pset] at hxP'
      exact hCR i hi x hxP'
  have hXY : ∀ x ∈ X₁f, x ∈ Y := fun x hx => by
    rw [hYV]; exact Finset.mem_union_left _ hx
  have hρS : 2 * R + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hVimg : Vset (X₁f.image bm) (𝒞.image (Prod.map id bm)) = (Vset X₁f 𝒞).image bm :=
    vset_image_top (N₁' := N₁') hρS X₁f fun P hP => ⟨h𝒞I P hP, h𝒞R P hP⟩
  have hYA : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ (GA).Ω 1) Y :=
    ⟨subset_rfl, fun _ _ y hy _ => hy⟩
  have hYB : IsNnComp ((Vset (X₁f.image bm) (𝒞.image (Prod.map id bm))).filter
      fun x => x ∈ (GB).Ω 1) (Y.image bm) := by
    rw [Finset.filter_true_of_mem fun x _ => hΩB x, hVimg, ← hYV]
    exact ⟨subset_rfl, fun _ _ y hy _ => hy⟩
  have hX₁cell : IsCellUnion (L ^ (k + 1)) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    rw [hX₁]; exact X1_isCellUnion_unit hcov.hN
  have hcomp : CompleteBlocks (GA) Y := completeBlocks_of_isNnComp hGA hX₁cell h𝒞I hYA
  -- the cut parameters vanish off the family
  obtain ⟨-, -, hs0E, -⟩ := compY_geometry hcov hX₁ C s s (fun i hi => hs.1 i hi)
    (fun i hi => hs.1 i hi) (fun _ _ _ => rfl)
    (Finset.univ.filter fun x => x ∈ compY
      (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) (fun x => by simp)
  have hs0 : ∀ P ∈ parCubes (GA) X₁f, P ∉ 𝒞 → extS (GA) σ P = 0 :=
    fun P hP hP𝒞 => (hs0E P hP hP𝒞).1
  set C'' : Finset (ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1)))) :=
    Finset.univ.filter fun i' => ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1 with hC''
  obtain ⟨-, -, hs0E', -⟩ := compY_geometry hcov' hX₁' C'' s' s'
    (fun i' hi' => hs'0 i' (fun i hi he => hi' (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, he⟩)))
    (fun i' hi' => hs'0 i' (fun i hi he => hi' (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, he⟩)))
    (fun _ _ _ => rfl)
    (Finset.univ.filter fun x => x ∈ compY
      (fun i : ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) => i.1.1)
      (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) C'') (fun x => by simp)
  have hs0' : ∀ P ∈ parCubes (GB) (X₁f.image bm), P ∉ 𝒞.image (Prod.map id bm) →
      extS (GB) σ' P = 0 := by
    intro P hP hP𝒞
    refine (hs0E' P hP fun h => hP𝒞 ?_).1
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 h
    obtain ⟨i, hi, he⟩ := (Finset.mem_filter.1 hi').2
    rw [he]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hi)
  -- the parameters correspond on the box
  have hcorr : ∀ (i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (i' : ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1)))),
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2 → i'.1.1 = Prod.map id bm i.1.1 →
        s' i' = s i := by
    intro i i' hi hii'
    by_cases hiC : i ∈ C
    · exact hss' i hiC i' hii'
    · rw [hs.1 i hiC]
      refine hs'0 i' fun i₂ hi₂ he => hiC ?_
      have hi₂R : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) i₂.1.1.2 :=
        inBox_mono (by omega) (hCR i₂ hi₂ _ (self_mem_Pset _))
      have hc : i.1.1 = i₂.1.1 := injOn_idxMap (N₁' := N₁') (ρ := ρ₁) (by omega) hi hi₂R
        (hii'.symm.trans he)
      have : i = i₂ := Subtype.ext (Subtype.ext hc)
      exact this ▸ hi₂
  have hXRs : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx => hXR x (Finset.mem_coe.1 hx)
  have hσP : ∀ P ∈ cubeIdx (GA), InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 →
      extS (GB) σ' (Prod.map id bm P) = extS (GA) σ P := fun P hP hP0 =>
    extS_extParams_boxMap_of_eq hnS hnS' hXRs Finset.coe_image s s' hcorr hP hP0
  have hB' := SY_image (ϱ := ϱ) (N₁' := N₁') hj1 le_rfl hnS hnS' hXR h𝒞R hYR
  have hagree := hagree_boxMap (ϱ := ϱ) (N₁' := N₁') hj1 le_rfl hnS hnS'
    (SY_subset_levelGS (ϱ := ϱ) (X₁ := X₁f) (𝒞 := 𝒞) hj1 le_rfl) hYR hσP
  have hrawY : RawBoxAgree {z | RowsDep (GA) (compWeight L a₁) ν (SY (GA) X₁f 𝒞 Y) z}
      (rawOf D) (rawOf D') := fun z hz => hraw z (inBox_of_rowsDep_top hC.Sp hYR (by omega) hz)
  -- the decoupled backgrounds and the strict data
  have hψb := markedHatPsiF_mem_flBallLC hC hk hHA hGA cc hcψ hMX hmar hαK hsm hF₁ hσb hD hψh Zm hum
  have hψb' := markedHatPsiF_mem_flBallLC hC' hk hHB hGB cc hcψ hMX hmar hαK hsm hF₁' hσb' hD' hψh'
    Zm' hum
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, -⟩ :=
    point_facts_core hC hF₁ hSol hσb (extParams_hs1 s) hD hψb.1
  obtain ⟨φ', α', δφ', δα', hI', hFeq', hstrict', hSeq', -⟩ :=
    point_facts_core hC' hF₁' hSol' hσb' (extParams_hs1 s') hD' hψb'.1
  have hU := inUnionDomainC_of_xiCData hC hD
  have hU' := inUnionDomainC_of_xiCData hC' hD'
  -- the hat variables on the unit points of `Y`
  have hhatU : ∀ b : unitPts (GA), UnitOut (GA) Y b → ∀ i, ψh' (ιu b, i) = ψh (b, i) := by
    intro b hb i
    obtain ⟨x, -, hxb⟩ := (mem_unitPts (GA)).1 b.2
    have hxY : x ∈ Y := hb ⟨x, hΩA x⟩ (by simp only [hxb])
    have hbx : b = unitPt hGA x := Subtype.ext hxb.symm
    have h := hhat x (hYR x hxY) i
    rw [unitPt_boxMap (by omega) hGA hGB (hYR x hxY), ← hbx] at h
    exact h
  -- the tangents on `Y`
  have hψeq : ∀ x ∈ Y, markedHatPsiF a₁ ν hGB cc F₁' Zm' um tm σ' (rawOf D') ψh' (bm x) =
      markedHatPsiF a₁ ν hGA cc F₁ Zm um tm σ (rawOf D) ψh x := by
    intro x hx
    have hxR := hYR x hx
    refine markedHatPsiF_boxMap (by omega) hGA hGB a₁ ν cc um tm hxR (hZm x hxR) fun i => ?_
    refine hatSqrtF_rows_twoTorus hC hC' hk hMX hmar hαK hsm hconn hconn' hF₁ hF₁' hσb hσb' hD hD'
      hYA hYB hs0 hs0' rfl hB' hagree hYR hn hn' hrawY hcomp ψh ψh' hhatU (fun y' hy' => ?_) i
    exact hcomp ⟨x, hΩA x⟩ y' hx hy'
  -- the background values
  obtain ⟨hαSY, -, -, -⟩ := decBg_value_twoTorus hj1 le_rfl hC.hS hC.Sp hC'.Sp hconn hconn'
    hC.HBp hC.hκ.le hC.hM hF₁ hF₁' hσb hσb' hU hU' hYA hYB hs0 hs0' rfl hB' hagree hYR hn hn' hrawY
  -- the fluctuation values
  have h𝒞I' : ∀ P ∈ 𝒞.image (Prod.map id bm), P ∈ (coverOf (GB)).cubeIdx := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP
    exact mem_cubeIdx_image_top (h𝒞I Q hQ)
  obtain ⟨A, hIU, -⟩ := incUnion_of_nnComp (Dec2.coverLocal_self hC.Sp) hconn
    (fun x hx => hC.hPmp.mem_Ω1 hx) hrow h𝒞I hYA
  obtain ⟨A', hIU', -⟩ := incUnion_of_nnComp (Dec2.coverLocal_self hC'.Sp) hconn'
    (fun x hx => hC'.hPmp.mem_Ω1 hx) hrow' h𝒞I' hYB
  have hBF' := SYF_image (ϱ := ϱ) (N₁' := N₁') hk (Nat.le_add_right k 1) le_rfl (compWeight L a₁) ν hnS
    hnS' (by omega) (by omega) hXR h𝒞R hYR
  have hSYFY : Dec2.SYF (coverOf (GA)) (HA) (compWeight L a₁) ν X₁f 𝒞 Y ⊆ Y :=
    SYF_subset_levelGS (ϱ := ϱ) (ϱp := ϱ) (a := compWeight L a₁) (ν := ν) (𝒞 := 𝒞) (X₁ := X₁f)
      (Y := Y) hk (Nat.le_add_right k 1) le_rfl
  have hagreeF := hagree2_boxMap (ϱ := ϱ) (ϱp := ϱ) (N₁' := N₁') hk (Nat.le_add_right k 1) le_rfl hnS hnS'
    hSYFY hYR hσP
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) := by
    have hd0 : 0 < d := by have := hC.HBp.hd; omega
    have hε := hC.eps_pos
    have hc1 := one_le_xiC1 d
    have h4 : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
    positivity
  have he : StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
      (flEdat (GA) (HA) (F₁ (σ, rawOf D)) D.Ψ
        (markedHatPsiF a₁ ν hGA cc F₁ Zm um tm σ (rawOf D) ψh)) := by
    rw [hFeq]; exact hstrict
  have he' : StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
      (flEdat (GB) (HB) (F₁' (σ', rawOf D')) D'.Ψ
        (markedHatPsiF a₁ ν hGB cc F₁' Zm' um tm σ' (rawOf D') ψh')) := by
    rw [hFeq']; exact hstrict'
  obtain ⟨-, hδφY⟩ := decSol_value_twoTorus_of_decBg (ϱ := ϱ) (ϱp := ϱ) hk (Nat.le_add_right k 1) le_rfl
    hC.hS hC.Sp hC'.Sp hconn hconn' hC.HBp hC.hκ.le hC.hM hF₁ hF₁' hσb hσb' hU hU' hYA hYB hs0
    hs0' rfl hB' hagree hYR hn hn' hrawY hC.hS2.fam hC.SM.toCoverBase hC'.SM.toCoverBase
    hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le hSol hSol' hσb hσb' he he' hIU hIU'
    hs0 hs0' hBF' hagreeF (fun x hx => (hψeq x (hSYFY hx)).symm)
  -- the block functional
  have hRα : ∀ y : (GA).Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
      (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁f 𝒞 Y := by
    intro y hy
    obtain ⟨z, hz, hyz, hQ, hhatz⟩ := hBM y hy y.2
    exact Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, fun P hP hPpar => absurd hPpar (hQ P hP),
      fun x hx => hXY _ (hhatz x hx)⟩, hyz⟩
  show Φ' (F₁' (σ', rawOf D'))
      (Sol' (σ', flEdat (GB) (HB) (F₁' (σ', rawOf D')) D'.Ψ
        (markedHatPsiF a₁ ν hGB cc F₁' Zm' um tm σ' (rawOf D') ψh'))).1
      (rawOf D', markedHatPsiF a₁ ν hGB cc F₁' Zm' um tm σ' (rawOf D') ψh') =
    Φ (F₁ (σ, rawOf D))
      (Sol (σ, flEdat (GA) (HA) (F₁ (σ, rawOf D)) D.Ψ
        (markedHatPsiF a₁ ν hGA cc F₁ Zm um tm σ (rawOf D) ψh))).1
      (rawOf D, markedHatPsiF a₁ ν hGA cc F₁ Zm um tm σ (rawOf D) ψh)
  refine hΦ (F₁ (σ, rawOf D), (Sol (σ, flEdat (GA) (HA) (F₁ (σ, rawOf D)) D.Ψ
      (markedHatPsiF a₁ ν hGA cc F₁ Zm um tm σ (rawOf D) ψh))).1,
      (rawOf D, markedHatPsiF a₁ ν hGA cc F₁ Zm um tm σ (rawOf D) ψh))
    (F₁' (σ', rawOf D'), (Sol' (σ', flEdat (GB) (HB) (F₁' (σ', rawOf D')) D'.Ψ
      (markedHatPsiF a₁ ν hGB cc F₁' Zm' um tm σ' (rawOf D') ψh'))).1,
      (rawOf D', markedHatPsiF a₁ ν hGB cc F₁' Zm' um tm σ' (rawOf D') ψh'))
    (fun y y' hy hy' => ?_) (fun w w' hw hw' i => ?_) (fun x hx => hψeq x (hXY x (hRψ hx)))
  · have hy'e : y' = ⟨bm (y : CTorus d L N₁ m₁ (k + 1)), hΩB _⟩ := Subtype.ext hy'
    rw [hy'e]
    exact hαSY y (hRα y hy)
  · have hw'e : w' = ⟨bm (w : CTorus d L N₁ m₁ (k + 1)),
        levelGS_mem_Ω_one hk (Nat.le_succ k) _⟩ := Subtype.ext hw'
    rw [hw'e]
    exact hδφY w (hXY _ (hRδ hw)) i

end Slice

/-! ### The marked functional does not depend on the choice of the pair; analyticity -/

section PairAnalytic

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **Two pairs with the defining properties give the same marked functional** at data of the
chart and cut parameters of the polydisc: both maps `F₁` take the value of the decoupled
background pair (Theorem I-4b), and both maps `Sol` the unique small fixed point of the
fluctuation problem (Theorem I-4a, mode P) at the strict data of that pair. -/
theorem FFmarked_eq_of_pair (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ F₁a : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁a : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁a (s, rawOf D) = (φ, α))
    {Sol Sola : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSola : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sola p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sola p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sola p).2 ∧
        Small Hm (Sola p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sola p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sola p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sola p).2))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gp)) {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ} (hs : ∀ i, ‖s i‖ < Real.exp κ) :
    FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm (rawOf D, ψh) s =
      FFmarked X₁f a₁ ν hG' cc F₁a Sola Φ Zm um tm (rawOf D, ψh) s := by
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  set σ := extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s with hσdef
  have hσ : ∀ P, ‖σ P‖ < Real.exp κ := norm_extParams_lt hE1 hs
  have hψb := markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁a hσ hD hψh Zm hum
  obtain ⟨φ, α, δφ, δα, hI, hFa, hstrict, -, -⟩ :=
    point_facts_core hC hF₁a hSola hσ (extParams_hs1 s) hD hψb.1
  have hU := inUnionDomainC_of_xiCData hC hD
  have hF := hF₁ σ D hσ hU φ α hI
  have hψ : markedHatPsiF a₁ ν hG' cc F₁ Zm um tm σ (rawOf D) ψh =
      markedHatPsiF a₁ ν hG' cc F₁a Zm um tm σ (rawOf D) ψh := by
    unfold markedHatPsiF hatPsiF hatSqrtF
    rw [hF, hFa]
  set ψ := markedHatPsiF a₁ ν hG' cc F₁a Zm um tm σ (rawOf D) ψh with hψdef
  have hSeq : Sol (σ, flEdat Gp Hm (φ, α) D.Ψ ψ) = Sola (σ, flEdat Gp Hm (φ, α) D.Ψ ψ) := by
    obtain ⟨hfld, hfix, hs6, -, -, -⟩ := hSol (σ, flEdat Gp Hm (φ, α) D.Ψ ψ) hσ hstrict
    obtain ⟨hflda, -, -, -, -, huniq⟩ := hSola (σ, flEdat Gp Hm (φ, α) D.Ψ ψ) hσ hstrict
    have h2 : (Sol (σ, flEdat Gp Hm (φ, α) D.Ψ ψ)).2 = (Sola (σ, flEdat Gp Hm (φ, α) D.Ψ ψ)).2 :=
      huniq _ hs6 hfix
    refine Prod.ext ?_ h2
    rw [hfld, hflda, h2]
  show Φ (F₁ (σ, rawOf D))
      (Sol (σ, flEdat Gp Hm (F₁ (σ, rawOf D)) D.Ψ
        (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm σ (rawOf D) ψh))).1
      (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm σ (rawOf D) ψh) =
    Φ (F₁a (σ, rawOf D)) (Sola (σ, flEdat Gp Hm (F₁a (σ, rawOf D)) D.Ψ ψ)).1 (rawOf D, ψ)
  rw [hψ, hF, hFa, hSeq]

/-- **The marked functional is analytic in the cut parameters**, at data of the chart and hat
variables of the ball, for any pair `(F₁, Sol)` with the defining properties: it agrees on the
polydisc with the functional of the analytic pair of Theorems I-4b and I-4a
(`FFmarked_eq_of_pair`), which is analytic (`fanH_analytic_marked`). -/
theorem analyticOnNhd_FFmarked (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (Zm : Finset (unitPts Gp)) {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    AnalyticOnNhd ℂ (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm (rawOf D, ψh))
      (polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  obtain ⟨F₁a, hF₁an, hF₁a⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sola, hSolan, hSola⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  set W : Set (ℂ × ℂ) := {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
    (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} with hWdef
  have hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}, ∀ w ∈ W,
      markedHatPsiF a₁ ν hG' cc F₁a Zm w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    intro σ hσ D hD ψh hψh w hw
    have hs' : ∀ i, ‖σ i‖ < Real.exp κ := fun i => by simpa using hσ i
    exact (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁a
      (norm_extParams_lt hE1 hs') hD hψh Zm hw).1
  have hanaW := fanH_analytic_marked (X₁f := X₁f) hC hk hG' cc
    {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} Zm W
    hMX hmar hα hsm hF₁an hF₁a hSolan hSola hΦan hSup
  have hDraw : rawOf D ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have hslice : AnalyticOnNhd ℂ (FFmarked X₁f a₁ ν hG' cc F₁a Sola Φ Zm um tm (rawOf D, ψh))
      (polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)) :=
    hanaW.comp (f := fun s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ =>
      (((rawOf D, ψh), s), (um, tm)))
      (fun _ _ => (analyticAt_const.prod analyticAt_id).prod analyticAt_const)
      (fun s hs => ⟨⟨⟨hDraw, hψh⟩, hs⟩, hum⟩)
  refine hslice.congr (isOpen_polydisc _ _) fun s hs => ?_
  exact (FFmarked_eq_of_pair hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁ hF₁a hSol hSola Φ Zm hum hD
    hψh (fun i => by simpa using hs i)).symm

end PairAnalytic

/-! ### D3: the marked energy coefficient `evDec` on two tori -/

section Coef

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

/-- The coefficient of the empty family is the value at `0`. -/
theorem coef_empty_eq {ι : Type*} [DecidableEq ι] [Fintype ι] (f : (ι → ℂ) → ℂ) :
    coef f ∅ = f 0 := by
  have h : (Finset.univ.toList.filter (· ∈ (∅ : Finset ι))) = [] := by simp
  unfold coef
  rw [h]
  rfl

/-- `evTerm_boxMap` at the top level, for a set `S'` of the second torus equal to the image
`bm '' X₁` (the parameter type `ParIdx GB S'` is not rewritten). -/
theorem evTerm_boxMap_of_eq {U U' : Type*} {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {S' : Set (CTorus d L N₁' m₁ (k + 1))} (hS' : S' = bm '' X₁)
    (F : U → (ParIdx (GA) X₁ → ℂ) → ℂ) (F' : U' → (ParIdx (GB) S' → ℂ) → ℂ) (u : U) (u' : U')
    (hcoef : ∀ C ∈ connFams (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ Y,
      ∀ C' : Finset (ParIdx (GB) S'),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) →
        coef (F' u') C' = coef (F u) C) :
    evTerm (fun i : ParIdx (GB) S' => i.1.1) (GB) m₀ S' F' (bm '' Y) u' =
      evTerm (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ F Y u := by
  subst hS'
  exact evTerm_boxMap hN hN' le_rfl hn hn' (Nat.le_add_left 1 k) hX hY F F' u u' hcoef

/-- **D3: the marked energy coefficient on two tori.**  Under the hypotheses of
`FFmarked_twoTorus` with the box of radius `R` containing `X₁f` and the domain `Y` (so that every
connected family `𝒞` with `Y[𝒞] = Y` has its cubes in the box), the analyticity of the block
functional `Φ` on the realizable triples, and the margin `2 R + 5 L · cellSide L m₀ m₁ (k+1) <
N₁ L^m₁ L^(k+1)` of the families (`evTerm_boxMap`), the coefficients `evDec` of `bm '' Y` on the
second torus and of `Y` on the first torus are equal.  Proof: `evTerm_boxMap` reindexes the
connected families; for corresponding families `C`, `C'` the coefficients are equal by D1
(`coef_relabel_injOn`, with the relabelling `C → C'` of the centres and the analyticity of the
marked functional in the cut parameters, `analyticOnNhd_FFmarked`) and D2 (`FFmarked_twoTorus`)
at the cut points of `C`. -/
theorem evDec_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hrow : RowInHat (coverOf (GA)) (HA) (compWeight L a₁) ν)
    (hrow' : RowInHat (coverOf (GB)) (HB) (compWeight L a₁) ν)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {Φ : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) X₁f Rα)
    (hRδ : Rδ ⊆ ↑X₁f) (hRψ : Rψ ⊆ ↑X₁f)
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) → t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal (GA) (HA) a₁ ν BG κ eps X₁f BG₂ δ₁))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (X₁f.image bm) m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm (bm '' Y) (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  unfold evDec
  rw [← hX₁, ← hX₁']
  refine evTerm_boxMap_of_eq hcov.hN hcov'.hN hnF hnF' (fun x hx => hX₁R x (Finset.mem_coe.1 hx))
    hYR Finset.coe_image _ _ _ _ ?_
  intro C hCm C' h2 h1
  have hYC := ((mem_connFams (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
    i.1.1)).1 hCm).2
  have hCR : ∀ i ∈ C, ∀ x ∈ Pset m₁ i.1.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro i hi x hx
    apply hYR
    rw [← hYC]
    right
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, Pset_subset_Dsites hcov.hU hcov.hN i.1.2 hx⟩
  by_cases hCe : C = ∅
  · subst hCe
    have hC'e : C' = ∅ := Finset.eq_empty_of_forall_notMem fun i' hi' => by
      obtain ⟨i, hi, -⟩ := h1 i' hi'
      simp at hi
    subst hC'e
    rw [coef_empty_eq, coef_empty_eq]
    exact FFmarked_twoTorus hC hC' hk hGA hGB cc hcψ hconn hconn' hrow hrow' hMX hmar hαK hsm hF₁
      hF₁' hSol hSol' hcov hX₁ hcov' hX₁' hBM hRδ hRψ hΦ hX₁R ∅ (fun i hi => by simp at hi) hn hn'
      hnS hnS' ⟨fun i _ => rfl, fun i => by simpa using Real.exp_pos κ⟩ (fun _ _ => rfl)
      (fun i hi => by simp at hi) hD hD' hraw hψh hψh' hhat hZm hum
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_of_ne_empty hCe
    obtain ⟨i₀', -, -⟩ := h2 i₀ hi₀
    choose f hf using h2
    set e : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
        ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) :=
      fun i => if hi : i ∈ C then f i hi else i₀' with he_def
    have he : ∀ i ∈ C, e i ∈ C' ∧ (e i).1.1 = Prod.map id bm i.1.1 := by
      intro i hi
      simp only [he_def, hi, ↓reduceDIte]
      exact hf i hi
    have hcen : ∀ i ∈ C, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2 :=
      fun i hi => hCR i hi _ (self_mem_Pset _)
    have hinj : Set.InjOn e ↑C := by
      intro i hi i₂ hi₂ hii
      have hc : Prod.map id bm i.1.1 = Prod.map id bm i₂.1.1 := by
        rw [← (he i hi).2, ← (he i₂ hi₂).2, hii]
      exact Subtype.ext (Subtype.ext (injOn_idxMap (N₁' := N₁') (ρ := R) (by omega)
        (hcen i hi) (hcen i₂ hi₂) hc))
    have hCimg : C.image e = C' := by
      ext i'
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
        exact (he i hi).1
      · intro hi'
        obtain ⟨i, hi, hc⟩ := h1 i' hi'
        exact Finset.mem_image.2 ⟨i, hi, Subtype.ext (Subtype.ext ((he i hi).2.trans hc.symm))⟩
    rw [← hCimg]
    refine coef_relabel_injOn hE1 e hinj (analyticOnNhd_FFmarked hC hk hHA hGA cc hcψ hMX hmar hαK
      hsm hF₁ hSol hΦan Zm hum hD hψh) (fun s hs s' hs' hss => ?_)
    refine FFmarked_twoTorus hC hC' hk hGA hGB cc hcψ hconn hconn' hrow hrow' hMX hmar hαK hsm hF₁
      hF₁' hSol hSol' hcov hX₁ hcov' hX₁' hBM hRδ hRψ hΦ hX₁R C hCR hn hn' hnS hnS' hs
      (fun i' hi' => hs' i' ?_) (fun i hi i' hc => ?_) hD hD' hraw hψh hψh' hhat hZm hum
    · intro hmem
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hmem
      exact hi' i hi (he i hi).2
    · have : i' = e i := Subtype.ext (Subtype.ext (hc.trans (he i hi).2.symm))
      rw [this]
      exact hss i hi


/-- **D3 for the block energy** (`Φ = blockEnergyFun … k z`, the `V`-part of the localized
interaction): the coefficients `evDec` of the block `z = B_{k+1}(x₀)` on the first torus and of
the block of `bm x₀` on the second torus are equal, when the sites read by the block energy lie in
`X₁f` (`hZ`) and the block has the margin `BlockMargin` against `X₁f`.  The reads of the block
functional are `blockEnergyFun_levelGS_boxMap`, its analyticity `blockEnergyFun_analytic`. -/
theorem evDec_blockEnergy_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hrow : RowInHat (coverOf (GA)) (HA) (compWeight L a₁) ν)
    (hrow' : RowInHat (coverOf (GB)) (HB) (compWeight L a₁) ν)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {x₀ : CTorus d L N₁ m₁ (k + 1)}
    (hZ : readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) ⊆ ↑X₁f)
    (hBM : BlockMargin (GA) X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) :
        Set (CTorus d L N₁ m₁ (k + 1))))
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (X₁f.image bm) m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k
          (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀))) Zm' um tm (bm '' Y) (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k
          (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) Zm um tm Y (rawOf D, ψh) := by
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hB : ∀ y ∈ blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀),
      y ∈ X₁f := fun y hy => Finset.mem_coe.1 (hZ (readSites_of_blockSites hy))
  have hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀ :=
    hX₁R x₀ (hB x₀ (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩))
  exact evDec_twoTorus hC hC' hk hGA hGB cc hcψ hconn hconn' hrow hrow' hMX hmar hαK hsm hF₁ hF₁'
    hSol hSol' hcov hX₁ hcov' hX₁' hBM hZ (fun y hy => hZ (readSites_of_blockSites hy))
    (fun t t' hα hδ hψ => blockEnergyFun_levelGS_boxMap hk (by omega) (by omega) (compWeight L a₁) ν
      hx₀ hα hδ hψ) hX₁R hYR hn hn' hnS hnS' hnF hnF'
    ((blockEnergyFun_analytic (compWeight L a₁) ν k _).mono (Set.subset_univ _)) hD hD' hraw hψh
    hψh' hhat hZm hum


/-- **D3, the site term `Ev`.**  The localized terms of the expansion along the fluctuation field
`hatPsiF` (`expansion_of_AE_hat_dir_exposed`: `Ev Y = evTerm … Y` of the fan functional) on two
tori: by `FFmarked_one_zero` the fan functional is the marked functional at the marks `(1, 0)`
(with empty masks), and `evDec_twoTorus` applies.  The radius condition is `markedRad < δ₁`. -/
theorem Ev_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hrow : RowInHat (coverOf (GA)) (HA) (compWeight L a₁) ν)
    (hrow' : RowInHat (coverOf (GB)) (HB) (compWeight L a₁) ν)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {Φ : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) X₁f Rα)
    (hRδ : Rδ ⊆ ↑X₁f) (hRψ : Rψ ⊆ ↑X₁f)
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) → t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal (GA) (HA) a₁ ν BG κ eps X₁f BG₂ δ₁))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evTerm (fun i : ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ j 𝒦X')
        (fun u s => Φ' (F₁' (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s,
          u.1))
          (Sol' (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s,
            flEdat (GB) (HB) (F₁' (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1)))
              s, u.1)) u.1.1 (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s) u.1 u.2))
        (bm '' Y) (rawOf D', ψh') =
      evTerm (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (GA) m₀
        (X1 (GA) m₀ j 𝒦X)
        (fun u s => Φ (F₁ (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          (Sol (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))
        Y (rawOf D, ψh) := by
  have h := evDec_twoTorus hC hC' hk hGA hGB cc hcψ hconn hconn' hrow hrow' hMX hmar hαK hsm hF₁
    hF₁' hSol hSol' hcov hX₁ hcov' hX₁' hBM hRδ hRψ hΦ hX₁R hYR hn hn' hnS hnS' hnF hnF' hΦan hD
    hD' hraw hψh hψh' hhat (Zm := ∅) (Zm' := ∅) (fun x _ => by simp) (um := 1) (tm := 0)
    (by rw [norm_one, norm_zero, add_zero, one_mul]; exact hrad)
  unfold evDec at h
  rw [FFmarked_one_zero, FFmarked_one_zero] at h
  exact h

/-- **D3, the site term `Ev` for the block energy** (`Ev_twoTorus` with
`Φ = blockEnergyFun … k z`). -/
theorem Ev_blockEnergy_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hrow : RowInHat (coverOf (GA)) (HA) (compWeight L a₁) ν)
    (hrow' : RowInHat (coverOf (GB)) (HB) (compWeight L a₁) ν)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {x₀ : CTorus d L N₁ m₁ (k + 1)}
    (hZ : readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) ⊆ ↑X₁f)
    (hBM : BlockMargin (GA) X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) :
        Set (CTorus d L N₁ m₁ (k + 1))))
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evTerm (fun i : ParIdx (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ j 𝒦X')
        (fun u s => (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k
          (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀))) (F₁' (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s,
          u.1))
          (Sol' (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s,
            flEdat (GB) (HB) (F₁' (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1)))
              s, u.1)) u.1.1 (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) s) u.1 u.2))
        (bm '' Y) (rawOf D', ψh') =
      evTerm (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (GA) m₀
        (X1 (GA) m₀ j 𝒦X)
        (fun u s => (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k
          (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) (F₁ (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          (Sol (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))
        Y (rawOf D, ψh) := by
  have h := evDec_blockEnergy_twoTorus hC hC' hk hGA hGB cc hcψ hconn hconn' hrow hrow' hMX hmar hαK
    hsm hF₁ hF₁' hSol hSol' hcov hX₁ hcov' hX₁' hZ hBM hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw
    hψh hψh' hhat (Zm := ∅) (Zm' := ∅) (fun x _ => by simp) (um := 1) (tm := 0)
    (by rw [norm_one, norm_zero, add_zero, one_mul]; exact hrad)
  unfold evDec at h
  rw [FFmarked_one_zero, FFmarked_one_zero] at h
  exact h

end Coef

end Balaban.Polymer.TwoTorusStep
