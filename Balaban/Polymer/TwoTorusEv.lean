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

end Balaban.Polymer.TwoTorusStep
