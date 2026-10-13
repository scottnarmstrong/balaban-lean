/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyActivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The assembly of a rooted cut expansion into polymer activities, for a general function

`DetCauchyGraph` and `DetCauchyActivity` assemble the mixed differences of the rooted trace at
fixed fields into polymer activities.  The assembly uses only two properties of the function `F` of
the cut parameters:

* **support**: if `Δ_J F ≠ 0` then every parameter cube of `J` lies in the footprint of a centre
  joined to a root block by a chain of centres with footprints in `J` (`RootChain`);
* **bound**: `‖Δ_J F‖ ≤ M t^{|J|}`.

This file states the assembly for an arbitrary `F : DecParams G → ℂ` with these two properties (as
plain hypotheses, no structure), so that it can be applied to the rooted trace with cut-dependent
backgrounds (`DetCauchyBgActivity`).

* `rooted_of_cutSupport`, `card_cutSupport_le`: the cut sets with `Δ_J F ≠ 0` are rooted sets of
  `paramGraph G`; at most `Δ^{2n}` of them have `n` elements, `Δ = max (detDeg d L + 1) |B|`.
* `sum_norm_mixDiff_le_of_cutSupport`, `tail_norm_mixDiff_le_of_cutSupport`: the sum of all
  `‖Δ_J F‖` and its tail over `|J| ≥ n`.
* `cutActivity m₀ F y Y`: the sum of `Δ_J F` over the cut sets `J` whose hull (for the root index
  of the block `y`) is the polymer `Y`.
* `sum_cutActivity_eq`: `F(1) = ∑_Y cutActivity m₀ F y Y` (no hypothesis on `F`).
* `cutActivity_ne_zero_imp`, `norm_cutActivity_le`, `sum_norm_cutActivity_le`: support on polymers
  containing the root cube, the bound `M / (1 - z) · exp((log z / (2 d L)) dExt Y)` with
  `z = (detDeg d L + 1)² t < 1`, and the summed form.
* `log_cutRate`, `cutRate_mul_exp_lt_one`: for `t = 2 / e^κ`, `log z = -(κ - log 2 - 2 log Δ)`.

As a check, the fixed-field theorems of `DetCauchyActivity` are obtained again as the instance
`F = rootTrace … {y} · φ α` (`detActivity_eq_cutActivity`, `norm_detActivity_le_assembly`,
`sum_norm_detActivity_le_assembly`, `detActivity_ne_zero_imp_assembly`).

Nothing is said here about any particular `F`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField.Def6 Finset Matrix

/-! ### The rate for `t = 2 / e^κ` -/

section Rates

/-- With `z = Δ² · 2 / e^κ`: `log z = -(κ - log 2 - 2 log Δ)`. -/
theorem log_cutRate {Δ : ℝ} (hΔ : 0 < Δ) (κ : ℝ) :
    Real.log (Δ ^ 2 * (2 / Real.exp κ)) = -(κ - Real.log 2 - 2 * Real.log Δ) := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_div (by norm_num)
    (by positivity), Real.log_exp]
  push_cast; ring

/-- If `x < κ - log 2 - 2 log Δ` then `Δ² · (2 / e^κ) · e^x < 1`. -/
theorem cutRate_mul_exp_lt_one {Δ κ x : ℝ} (hΔ : 0 < Δ)
    (h : x < κ - Real.log 2 - 2 * Real.log Δ) :
    Δ ^ 2 * (2 / Real.exp κ * Real.exp x) < 1 := by
  have h0 : 0 < Δ ^ 2 * (2 / Real.exp κ * Real.exp x) := by positivity
  have hl : Real.log (Δ ^ 2 * (2 / Real.exp κ * Real.exp x)) =
      2 * Real.log Δ + (Real.log 2 - κ) + x := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (by positivity), Real.log_div (by norm_num) (by positivity),
      Real.log_exp, Real.log_exp]
    push_cast; ring
  have : Real.log (Δ ^ 2 * (2 / Real.exp κ * Real.exp x)) < 0 := by rw [hl]; linarith
  exact (Real.log_neg_iff h0).1 this

end Rates

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

/-! ### Counting and sums -/

section Counts

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **A cut set with non-zero mixed difference is rooted in the parameter graph**, for a function
`F` whose mixed differences have root-chain support in the blocks of `B`. -/
theorem rooted_of_cutSupport (S : DGSetting G a ν) {F : DecParams G → ℂ}
    {B : Finset (unitPts G)}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {J : Finset (cubeIdx G)} (hne : mixDiff J F ≠ 0) :
    Polymer.Rooted (paramGraph G)
      ((B.biUnion (rootParam G) : Finset (cubeIdx G)) : Set (cubeIdx G)) J := by
  obtain ⟨y, hy, hJ⟩ := hsupp J hne
  refine Polymer.Rooted.mono ?_ (rooted_of_rootChain S.aligned hJ)
  intro P hP
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨y, hy, hP⟩)

open Classical in
/-- **The count of cut sets.** At most `Δ^(2n)` cut sets `J` with `|J| = n` have `Δ_J F ≠ 0`,
`Δ = max (detDeg d L + 1) |B|`. -/
theorem card_cutSupport_le (S : DGSetting G a ν) {F : DecParams G → ℂ} {B : Finset (unitPts G)}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q) (n : ℕ) :
    (((Finset.univ : Finset (cubeIdx G)).powerset.filter fun J =>
        J.card = n ∧ mixDiff J F ≠ 0)).card ≤ (max (detDeg d L + 1) B.card) ^ (2 * n) := by
  have hdeg := fun P => paramGraph_degree_le (G := G) S.aligned S.cover_sep S.hM
    (by have := S.hL; omega) P
  have hN : (B.biUnion (rootParam G)).card ≤ B.card :=
    Finset.card_biUnion_le_card_mul B (rootParam G) 1 (fun y _ => card_rootParam_le S.aligned y)
      |>.trans (by simp)
  refine le_trans ?_ (Polymer.card_rooted_le hdeg (B.biUnion (rootParam G)) hN n)
  refine Finset.card_le_card fun J hJ => ?_
  obtain ⟨-, hcard, hne⟩ := Finset.mem_filter.1 hJ
  exact Finset.mem_filter.2 ⟨Polymer.mem_rootedSets.2 (rooted_of_cutSupport S hsupp hne), hcard⟩

open Classical in
/-- **The sum of all mixed differences.** If `‖Δ_J F‖ ≤ M t^{|J|}` and
`(detDeg d L + 1)² t < 1` then `∑_J ‖Δ_J F‖ ≤ M (1 - (detDeg d L + 1)² t)^{-|B|}`. -/
theorem sum_norm_mixDiff_le_of_cutSupport (S : DGSetting G a ν) {F : DecParams G → ℂ}
    {B : Finset (unitPts G)}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {M t : ℝ} (ht : 0 ≤ t) (hbd : ∀ J : Finset (cubeIdx G), ‖mixDiff J F‖ ≤ M * t ^ J.card)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, ‖mixDiff J F‖ ≤
      M * (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t)) ^ B.card := by
  have hM0 : 0 ≤ M := by
    have := hbd ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hdeg := fun P => paramGraph_degree_le (G := G) S.aligned S.cover_sep S.hM
    (by have := S.hL; omega) P
  have hmax : max (detDeg d L + 1) 1 = detDeg d L + 1 := max_eq_left (by omega)
  have hfam := Polymer.sum_rooted_le (G := paramGraph G) (b := detDeg d L) (b_root := 1) hdeg
    (rootParam G) (fun y => card_rootParam_le S.aligned y) ht (by rw [hmax]; exact hz) B
  rw [hmax] at hfam
  set R := Polymer.rootedSets (G := paramGraph G) (⋃ y ∈ B, ((rootParam G y : Finset (cubeIdx G)) :
    Set (cubeIdx G))) with hR
  have hRsub : R ⊆ (Finset.univ : Finset (cubeIdx G)).powerset :=
    fun J _ => Finset.mem_powerset.2 (Finset.subset_univ _)
  have hzero : ∀ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, J ∉ R →
      ‖mixDiff J F‖ = 0 := by
    intro J _ hJR
    by_contra hne
    apply hJR
    have hne' := norm_ne_zero_iff.1 hne
    refine Polymer.mem_rootedSets.2 (Polymer.Rooted.mono ?_ (rooted_of_cutSupport S hsupp hne'))
    intro P hP
    simp only [Finset.coe_biUnion, Set.mem_iUnion] at hP ⊢
    exact hP
  rw [← Finset.sum_subset hRsub hzero]
  calc _ ≤ ∑ J ∈ R, M * t ^ J.card := Finset.sum_le_sum fun J _ => hbd J
    _ = M * ∑ J ∈ R, t ^ J.card := by rw [Finset.mul_sum]
    _ ≤ M * (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t)) ^ B.card :=
        mul_le_mul_of_nonneg_left hfam hM0

open Classical in
/-- **The tail of the expansion.** With `Δ = max (detDeg d L + 1) |B|` and `z = Δ² t < 1`:
`∑_{|J| ≥ n} ‖Δ_J F‖ ≤ M z^n / (1 - z)`. -/
theorem tail_norm_mixDiff_le_of_cutSupport (S : DGSetting G a ν) {F : DecParams G → ℂ}
    {B : Finset (unitPts G)}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {M t : ℝ} (ht : 0 ≤ t) (hbd : ∀ J : Finset (cubeIdx G), ‖mixDiff J F‖ ≤ M * t ^ J.card)
    (n : ℕ) (hz : ((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card),
        ‖mixDiff J F‖ ≤
      M * ((((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * t) ^ n /
          (1 - ((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * t)) := by
  have hM0 : 0 ≤ M := by
    have := hbd ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hdeg := fun P => paramGraph_degree_le (G := G) S.aligned S.cover_sep S.hM
    (by have := S.hL; omega) P
  have hN : (B.biUnion (rootParam G)).card ≤ B.card :=
    Finset.card_biUnion_le_card_mul B (rootParam G) 1 (fun y _ => card_rootParam_le S.aligned y)
      |>.trans (by simp)
  have htail := rooted_tail_sum_le hdeg (B.biUnion (rootParam G)) hN ht hz n
  set R := (Polymer.rootedSets (G := paramGraph G)
    ((B.biUnion (rootParam G) : Finset (cubeIdx G)) : Set (cubeIdx G))).filter
      (fun J => n ≤ J.card) with hR
  have hRsub : R ⊆ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card) :=
    fun J hJ => Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
      (Finset.mem_filter.1 hJ).2⟩
  have hzero : ∀ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card),
      J ∉ R → ‖mixDiff J F‖ = 0 := by
    intro J hJ hJR
    by_contra hne
    apply hJR
    exact Finset.mem_filter.2 ⟨Polymer.mem_rootedSets.2
      (rooted_of_cutSupport S hsupp (norm_ne_zero_iff.1 hne)), (Finset.mem_filter.1 hJ).2⟩
  rw [← Finset.sum_subset hRsub hzero]
  calc _ ≤ ∑ J ∈ R, M * t ^ J.card := Finset.sum_le_sum fun J _ => hbd J
    _ = M * ∑ J ∈ R, t ^ J.card := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htail hM0

end Counts

/-! ### The activity of a polymer -/

section Activity

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- **The activity of the polymer `Y` for the root block `y` and a function `F` of the cut
parameters**: the sum of the mixed differences `Δ_J F` over the sets `J` of parameter cubes whose
hull (assigned to the root index of `y` and the patches of `J`) is `Y`. -/
noncomputable def cutActivity (m₀ : ℕ) (F : DecParams G → ℂ) (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
      (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), mixDiff J F

open Classical in
/-- **Resummation.**  `F(1)` is the sum over all polymers of the activities (for every `F`; the
empty set `J = ∅` contributes to the hull of the root cube alone). -/
theorem sum_cutActivity_eq (F : DecParams G → ℂ) (y : unitPts G) :
    F (fun _ => 1) = ∑ Y, cutActivity m₀ F y Y := by
  rw [sum_mixDiff F]
  unfold cutActivity
  exact (Finset.sum_fiberwise (Finset.univ : Finset (cubeIdx G)).powerset
    (fun J => hullOf m₀ (rootIdxOf y) (patches J)) (fun J => mixDiff J F)).symm

/-- **The hull of a cut set with non-zero mixed difference** contains the root cube, is a polymer,
and has size at most `2 d L |J|`. -/
theorem hull_facts_of_cutSupport (S : DGSetting G a ν) (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁)
    {F : DecParams G → ℂ} {y : unitPts G}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {J : Finset (cubeIdx G)} (hne : mixDiff J F ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ hullOf m₀ (rootIdxOf y) (patches J) ∧
      IsPolyDom m₀ (k + 1) (sitesOf (hullOf m₀ (rootIdxOf y) (patches J))) ∧
      dExt (hullOf m₀ (rootIdxOf y) (patches J)) ≤ (2 * d * L : ℝ) * J.card := by
  have hRC := rootConnected_of_rootChain (m₀ := m₀) S hconn (hsupp J hne)
  have hL : 2 ≤ L := by have := S.hL; omega
  refine ⟨rootCube_mem_hullOf _ _, isPolyDom_hullOf hN hL _ _ layer_le_of_mem_patches hRC, ?_⟩
  have h1 := dExt_hullOf_le hN hL (rootIdxOf y) (patches J) layer_le_of_mem_patches hRC
  have h2 : ((patches J).card : ℝ) ≤ J.card := by exact_mod_cast card_patches_le J
  have h3 : (0 : ℝ) ≤ 2 * d * L := by positivity
  nlinarith

open Classical in
/-- **Support.**  A non-zero activity is supported on a polymer containing the root cube. -/
theorem cutActivity_ne_zero_imp (S : DGSetting G a ν) (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁)
    {F : DecParams G → ℂ} {y : unitPts G}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (h : cutActivity m₀ F y Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) := by
  unfold cutActivity at h
  obtain ⟨J, hJ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hY := (Finset.mem_filter.1 hJ).2
  obtain ⟨h1, h2, -⟩ := hull_facts_of_cutSupport (m₀ := m₀) S hconn hN hsupp hne
  rw [hY] at h1 h2
  exact ⟨h1, h2⟩

open Classical in
/-- **Exponential decay of the activity in the size of the polymer.**  If `‖Δ_J F‖ ≤ M t^{|J|}`,
`t > 0` and `z = (detDeg d L + 1)² t < 1`, then
`‖cutActivity F y Y‖ ≤ M / (1 - z) · exp((log z / (2 d L)) dExt Y)` (note `log z < 0`). -/
theorem norm_cutActivity_le (S : DGSetting G a ν) (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁)
    {F : DecParams G → ℂ} {y : unitPts G}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {M t : ℝ} (ht : 0 < t) (hbd : ∀ J : Finset (cubeIdx G), ‖mixDiff J F‖ ≤ M * t ^ J.card)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ‖cutActivity m₀ F y Y‖ ≤ M / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t) *
      Real.exp (Real.log (((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t) / (2 * d * L) * dExt Y) := by
  set Δ : ℝ := ((detDeg d L + 1 : ℕ) : ℝ) with hΔ
  set zz : ℝ := Δ ^ 2 * t with hzz
  have hΔ1 : (1 : ℝ) ≤ Δ := by rw [hΔ]; exact_mod_cast Nat.le_add_left 1 _
  have hzz0 : 0 < zz := by positivity
  have hd : (0 : ℝ) < 2 * d * L := by
    have h1 := S.hd; have h2 := S.hL
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hM0 : 0 ≤ M := by
    have := hbd ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set x : ℝ := dExt Y / (2 * d * L) with hx
  set n : ℕ := ⌈x⌉₊ with hn
  have hlt0 : Real.log zz < 0 := Real.log_neg hzz0 hz
  have hsuppB : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∃ y' ∈ ({y} : Finset (unitPts G)), ∀ p ∈ J, ∃ q, RootChain G J y' q ∧ p ∈ QsetP G q :=
    fun J h => ⟨y, Finset.mem_singleton_self y, hsupp J h⟩
  have hmax : max (detDeg d L + 1) ({y} : Finset (unitPts G)).card = detDeg d L + 1 := by
    rw [Finset.card_singleton]; exact max_eq_left (by omega)
  have hz' : ((max (detDeg d L + 1) ({y} : Finset (unitPts G)).card : ℕ) : ℝ) ^ 2 * t < 1 := by
    rw [hmax]; exact hz
  have htail := tail_norm_mixDiff_le_of_cutSupport S hsuppB ht.le hbd n hz'
  rw [hmax] at htail
  have hstep1 : ‖cutActivity m₀ F y Y‖ ≤
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), ‖mixDiff J F‖ :=
    norm_sum_le _ _
  have hstep2 : ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), ‖mixDiff J F‖ ≤
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card),
        ‖mixDiff J F‖ := by
    rw [← Finset.sum_filter_ne_zero]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
    intro J hJ
    obtain ⟨hJ1, hJ2⟩ := Finset.mem_filter.1 hJ
    have hne : mixDiff J F ≠ 0 := norm_ne_zero_iff.1 hJ2
    obtain ⟨-, -, hd'⟩ := hull_facts_of_cutSupport (m₀ := m₀) S hconn hN hsupp hne
    rw [(Finset.mem_filter.1 hJ1).2] at hd'
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    rw [hn]
    refine Nat.ceil_le.2 ?_
    rw [hx, div_le_iff₀ hd]
    linarith
  -- z ^ n ≤ exp (x log z)
  have hpow : zz ^ n ≤ Real.exp (x * Real.log zz) := by
    rw [← Real.exp_log hzz0, ← Real.exp_nat_mul, Real.exp_log hzz0]
    refine Real.exp_le_exp.2 ?_
    have hxn : x ≤ n := Nat.le_ceil x
    nlinarith
  have hxl : x * Real.log zz = Real.log zz / (2 * d * L) * dExt Y := by
    rw [hx]; ring
  have h1z : 0 < 1 - zz := by linarith
  refine hstep1.trans (hstep2.trans (htail.trans ?_))
  rw [← hxl]
  calc M * (zz ^ n / (1 - zz)) ≤ M * (Real.exp (x * Real.log zz) / (1 - zz)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow h1z.le) hM0
    _ = _ := by ring

open Classical in
/-- **Summed form.**  If `‖Δ_J F‖ ≤ M t^{|J|}`, `κ'' ≥ 0` and
`(detDeg d L + 1)² · t · e^{2 d L κ''} < 1`, the sum over all polymers of
`‖cutActivity F y Y‖ · exp(κ'' dExt Y)` is at most
`M / (1 - (detDeg d L + 1)² · t · e^{2 d L κ''})`. -/
theorem sum_norm_cutActivity_le (S : DGSetting G a ν) (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁)
    {F : DecParams G → ℂ} {y : unitPts G}
    (hsupp : ∀ J : Finset (cubeIdx G), mixDiff J F ≠ 0 →
      ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q)
    {M t : ℝ} (ht : 0 ≤ t) (hbd : ∀ J : Finset (cubeIdx G), ‖mixDiff J F‖ ≤ M * t ^ J.card)
    {κ'' : ℝ} (hκ0 : 0 ≤ κ'')
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (t * Real.exp (κ'' * (2 * d * L))) < 1) :
    ∑ Y, ‖cutActivity m₀ F y Y‖ * Real.exp (κ'' * dExt Y) ≤
      M / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (t * Real.exp (κ'' * (2 * d * L)))) := by
  set Δ : ℝ := ((detDeg d L + 1 : ℕ) : ℝ) with hΔ
  set E : ℝ := Real.exp (κ'' * (2 * d * L)) with hE
  set t' : ℝ := t * E with ht'
  have ht0 : 0 ≤ t' := by positivity
  have hM0 : 0 ≤ M := by
    have := hbd ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  -- per-polymer bound
  have hY : ∀ Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ), ‖cutActivity m₀ F y Y‖ * Real.exp (κ'' * dExt Y) ≤
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), ‖mixDiff J F‖ * E ^ J.card := by
    intro Y
    calc _ ≤ (∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
          (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), ‖mixDiff J F‖) *
          Real.exp (κ'' * dExt Y) :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
          (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
          ‖mixDiff J F‖ * Real.exp (κ'' * dExt Y) := Finset.sum_mul _ _ _
      _ ≤ _ := by
        refine Finset.sum_le_sum fun J hJ => ?_
        by_cases hne : mixDiff J F = 0
        · rw [hne]; simp
        · obtain ⟨-, -, hd'⟩ := hull_facts_of_cutSupport (m₀ := m₀) S hconn hN hsupp hne
          rw [(Finset.mem_filter.1 hJ).2] at hd'
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hE, ← Real.exp_nat_mul]
          refine Real.exp_le_exp.2 ?_
          nlinarith
  -- resum over the polymers
  have hfib := Finset.sum_fiberwise (Finset.univ : Finset (cubeIdx G)).powerset
    (fun J => hullOf m₀ (rootIdxOf y) (patches J)) (fun J => ‖mixDiff J F‖ * E ^ J.card)
  have hdeg := fun P => paramGraph_degree_le (G := G) S.aligned S.cover_sep S.hM
    (by have := S.hL; omega) P
  have hmax : max (detDeg d L + 1) 1 = detDeg d L + 1 := max_eq_left (by omega)
  have hfam := Polymer.sum_rooted_le_one (G := paramGraph G) (b := detDeg d L) (b_root := 1) hdeg
    (rootParam G y) (card_rootParam_le S.aligned y) ht0 (by rw [hmax]; exact hz)
  rw [hmax] at hfam
  set R := Polymer.rootedSets (G := paramGraph G)
    ((rootParam G y : Finset (cubeIdx G)) : Set (cubeIdx G)) with hR
  have hRsub : R ⊆ (Finset.univ : Finset (cubeIdx G)).powerset :=
    fun J _ => Finset.mem_powerset.2 (Finset.subset_univ _)
  have hzero : ∀ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, J ∉ R →
      ‖mixDiff J F‖ * E ^ J.card = 0 := by
    intro J _ hJR
    by_contra hne
    apply hJR
    have hne' : mixDiff J F ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    exact Polymer.mem_rootedSets.2 (rooted_of_rootChain S.aligned (hsupp J hne'))
  calc _ ≤ ∑ Y, ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), ‖mixDiff J F‖ * E ^ J.card :=
        Finset.sum_le_sum fun Y _ => hY Y
    _ = ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, ‖mixDiff J F‖ * E ^ J.card := hfib
    _ = ∑ J ∈ R, ‖mixDiff J F‖ * E ^ J.card := (Finset.sum_subset hRsub hzero).symm
    _ ≤ ∑ J ∈ R, M * t' ^ J.card := by
        refine Finset.sum_le_sum fun J _ => ?_
        calc _ ≤ M * t ^ J.card * E ^ J.card :=
              mul_le_mul_of_nonneg_right (hbd J) (by positivity)
          _ = M * t' ^ J.card := by rw [ht', mul_pow]; ring
    _ = M * ∑ J ∈ R, t' ^ J.card := by rw [Finset.mul_sum]
    _ ≤ M * (1 / (1 - Δ ^ 2 * t')) := mul_le_mul_of_nonneg_left hfam hM0
    _ = _ := by rw [mul_one_div]

end Activity

/-! ### Check: the fixed-field theorems as an instance -/

section FixedFields

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}

/-- The fixed-field activity of `DetCauchyActivity` is the activity of the function
`s ↦ rootTrace … {y} s φ α`. -/
theorem detActivity_eq_cutActivity (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivity m₀ a aT ν φ α y Y =
      cutActivity m₀ (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) y Y := rfl

variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
  {α : G.Ω 1 → ℂ}
  (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))

include S hκ hM hδ hsm hφ hα

/-- The two properties used by the assembly, for the rooted trace of one block at fixed fields:
root-chain support and the bound `½ N covBLog · (2 / e^κ)^{|J|}`. -/
theorem rootTrace_cutSupport_and_bound (hconn : HatConn G) (y : unitPts G) :
    (∀ J : Finset (cubeIdx G),
      mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) ≠ 0 →
        ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q) ∧
    ∀ J : Finset (cubeIdx G),
      ‖mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α)‖ ≤
        (1 / 2 : ℝ) * N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ * (2 / Real.exp κ) ^ J.card := by
  constructor
  · intro J hne
    obtain ⟨y', hy', hJ⟩ := exists_rootChain_of_mixDiff_ne_zero S hκ hM hδ hsm hφ hα hconn {y} hne
    rw [Finset.mem_singleton] at hy'
    subst hy'
    exact hJ
  · intro J
    have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
    obtain ⟨-, hbound⟩ := rootTrace_cut_expansion (N := N) S hκ hM hδ hsm hU {y} hφ hα
    have := hbound J
    simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using this

open Classical in
/-- `detActivity_ne_zero_imp` of `DetCauchyActivity`, from the assembly. -/
theorem detActivity_ne_zero_imp_assembly (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) {y : unitPts G}
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (h : detActivity m₀ a aT ν φ α y Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) :=
  cutActivity_ne_zero_imp S.dg hconn hN
    (rootTrace_cutSupport_and_bound S hκ hM hδ hsm hφ hα hconn y).1 h

open Classical in
/-- `norm_detActivity_le` of `DetCauchyActivity`, from the assembly. -/
theorem norm_detActivity_le_assembly (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) (y : unitPts G)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ‖detActivity m₀ a aT ν φ α y Y‖ ≤
      (1 / 2 : ℝ) * N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
      Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt Y) := by
  obtain ⟨hsupp, hbd⟩ := rootTrace_cutSupport_and_bound S hκ hM hδ hsm hφ hα hconn y
  have hΔ0 : (0 : ℝ) < ((detDeg d L + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  have h := norm_cutActivity_le (m₀ := m₀) S.dg hconn hN hsupp (by positivity) hbd hz Y
  rw [log_cutRate hΔ0 κ] at h
  have e : -(κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L) =
      -((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) := by ring
  rw [e] at h
  exact h

open Classical in
/-- `sum_norm_detActivity_le` of `DetCauchyActivity`, from the assembly. -/
theorem sum_norm_detActivity_le_assembly (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) (y : unitPts G)
    {κ'' : ℝ} (hκ0 : 0 ≤ κ'')
    (hκ'' : κ'' * (2 * d * L) < κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) :
    ∑ Y, ‖detActivity m₀ a aT ν φ α y Y‖ * Real.exp (κ'' * dExt Y) ≤
      (1 / 2 : ℝ) * N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ * Real.exp (κ'' * (2 * d * L)))) := by
  obtain ⟨hsupp, hbd⟩ := rootTrace_cutSupport_and_bound S hκ hM hδ hsm hφ hα hconn y
  have hΔ0 : (0 : ℝ) < ((detDeg d L + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  exact sum_norm_cutActivity_le (m₀ := m₀) S.dg hconn hN hsupp (by positivity) hbd hκ0
    (cutRate_mul_exp_lt_one hΔ0 hκ'')

end FixedFields

end Balaban.Fluctuation
