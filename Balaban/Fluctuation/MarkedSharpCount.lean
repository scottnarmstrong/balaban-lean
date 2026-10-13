/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedCubicTaylor
public import Balaban.Fluctuation.MarkedRootGeometry
public import Balaban.Fluctuation.Prop33Bound
public import Balaban.Fluctuation.Prop33Level
public import Balaban.Fluctuation.HatLabelsExpansion
public import Balaban.Fluctuation.InteractionEnergyScaled
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The count of the marked terms (package 5 of `MARKCUBIC.md`, input `MARK-SCALED-COUNT`)

The marked difference of the potential of the zero class is a finite sum, over the blocks `b` and
the labels `Y` of the landed block expansion (`vblock_expansion_scaled`), of the terms
`markedBlockTerm (E_{b,Y}) ω a c Θ`, analytic in the marked parameter `t`
(`MarkedCubicTaylor.lean`).  This file sums the `t`-derivatives at `0` of these terms, after the
bridge to the root of `MarkedRootGeometry.lean`.

* `markedOut`: for a marked block `z` and a domain `Y'`, the sum of
  `∂_t (markedBlockTerm (E_{b,Y}) ω a c Θ)|_{t=0}` over the pairs `(b, Y)` with `psiThick Y`
  meeting `B(z)` and `bridge z Y = Y'`.  A literal finite sum.
* `sum_markedOut_eq` (resummation): the sum of `markedOut` over the family `bridgeFamily` is the
  sum of all the derivatives, and is the `t`-derivative at `0` of the sum of all the marked block
  terms (`deriv_sum_markedBlockTerm`).
* `deriv_markedBlockTerm_eq_zero_of_local`: if the term reads the tangent only on a set that the
  mask misses, the derivative vanishes.
* `norm_markedOut_le` (the count): the bound `3 E* e^{-2 κ_dec d(Y)}/(r³ t₀)` of
  `marked_term_cauchy`, the number of blocks through a domain (`card_blocks_filter_le`, at most
  `c₁ M^d (1 + d(Y))`) and the fibre of the bridge (`fibre_weighted_le`) give
  `‖markedOut z Y'‖ ≤ F₀ e^{-(2κ_dec - 1) d(Y')}`.
* `marked_count_scaled`: the assembled statement for the step, with the rooted sum
  `∑_{Y'} ‖markedOut z Y'‖ e^{a'' d(Y')} ≤ F₁`.

The size function of the block theorem is `treeLenCov Gp m₀ Y`; that of the bridge is
`treeLenCovOne m₀ (k+1) Y`; they agree at `IsLevel Gp (k+1)` (`treeLenCov_eq_treeLenCovOne`).

## Scope

Undecoupled level only (the tangent `markedTangentC`, no cut parameters).  `MARK-ROWS`,
`MARK-ASSEMBLY` and `MARK-PARAM` are NOT proved; no mark family is constructed; nothing depends on
a choice of generating sets for the class terms.  The index `markedIdx` of `MarkedRootGeometry`
is used with the trivial read set (`reads b = Set.univ`): the reading of the block energy through
the fluctuation solver is not local, so no block can be dropped before the expansion in `Y`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory Filter
  Balaban.SmallField.Def6 Balaban.Background Balaban.SmallField Set

/-! ### The output-indexed sum -/

section Out

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {β : Type*} [Fintype β]
  {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

open Classical in
/-- **The marked terms attached to the rooted domain `Y'`.**  For the marked block `z`, the sum of
the derivatives `∂_t (markedBlockTerm (E_{b,Y}) ω a c Θ)|_{t=0}` over the pairs `(b, Y)` of
`markedIdx reads dom z` whose bridge to the root is `Y'`. -/
noncomputable def markedOut (m₀ : ℕ) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ)
    (Y' : Set (CTorus d L N₁ m₁ K)) : ℂ :=
  ∑ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'),
    deriv (markedBlockTerm (Ev q.1 q.2) ω a c Θ) 0

variable {m₀ : ℕ}

open Classical in
/-- **Resummation over the output polymers.**  Every pair of `markedIdx` has its bridge in
`bridgeFamily`, so the fibres over `bridgeFamily` partition `markedIdx`. -/
theorem sum_fibre_bridgeFamily (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (g : β × Set (CTorus d L N₁ m₁ K) → ℂ) :
    ∑ Y' ∈ bridgeFamily m₀ reads dom z,
        ∑ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'), g q =
      ∑ q ∈ markedIdx reads dom z, g q := by
  refine Finset.sum_fiberwise_of_maps_to (g := fun q : β × Set (CTorus d L N₁ m₁ K) => bridge m₀ z q.2) (fun q hq => ?_) g
  obtain ⟨b, Y⟩ := q
  obtain ⟨h1, h2, h3⟩ := mem_markedIdx.1 hq
  exact mem_bridgeFamily.2 ⟨b, Y, h1, h2, h3, rfl⟩

theorem sum_markedOut_eq (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ) :
    ∑ Y' ∈ bridgeFamily m₀ reads dom z, markedOut m₀ reads dom z Ev ω a c Θ Y' =
      ∑ q ∈ markedIdx reads dom z, deriv (markedBlockTerm (Ev q.1 q.2) ω a c Θ) 0 :=
  sum_fibre_bridgeFamily reads dom z _

/-- **A non-zero output polymer is in the label family.** -/
theorem mem_bridgeFamily_of_markedOut_ne_zero (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ)
    {Y' : Set (CTorus d L N₁ m₁ K)} (h : markedOut m₀ reads dom z Ev ω a c Θ Y' ≠ 0) :
    Y' ∈ bridgeFamily m₀ reads dom z := by
  classical
  by_contra hn
  apply h
  unfold markedOut
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
  obtain ⟨b, Y⟩ := q
  obtain ⟨h1, h2, h3⟩ := mem_markedIdx.1 hq1
  exact absurd (mem_bridgeFamily.2 ⟨b, Y, h1, h2, h3, hq2⟩) hn

/-- **Anchoring.**  A non-zero `markedOut z Y'` has the root cube among the cubes of `Y'`. -/
theorem rootCube_mem_of_markedOut_ne_zero (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ)
    {Y' : Set (CTorus d L N₁ m₁ K)} (h : markedOut m₀ reads dom z Ev ω a c Θ Y' ≠ 0) :
    IsDj m₀ K Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y' := by
  have hm := mem_bridgeFamily_of_markedOut_ne_zero reads dom z Ev ω a c Θ h
  exact ⟨(bridgeFamily_spec hN hL hdom z hm).1, (bridgeFamily_spec hN hL hdom z hm).2.1⟩

omit [Fintype β] in
open Classical in
/-- **The count over a fibre of the bridge.**  Let `I` be a finite set of pairs `(b, Y)` with
`Y ∈ 𝒟_K`, `g` bounded on `I` by `C₀ e^{-a d(Y)}`, and suppose at most `m(Y)` pairs of `I` share
the domain `Y`, with `m(Y) e^{-a d(Y)} ≤ M e^{-a' d(Y)}`, `a' ≥ 0`.  Then the sum of `g` over the
pairs sent to `Y'` is at most `C₀ M nFibre e^{a' cBr} e^{-a' d(Y')}`. -/
theorem norm_fibre_sum_le_of_finset (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    (I : Finset (β × Set (CTorus d L N₁ m₁ K))) (hI : ∀ q ∈ I, IsDj m₀ K q.2)
    (g : β × Set (CTorus d L N₁ m₁ K) → ℂ) {C₀ a a' M : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M)
    (ha' : 0 ≤ a')
    (hg : ∀ q ∈ I, ‖g q‖ ≤ C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2))
    (hmult : ∀ Y, ((I.filter (fun q => q.2 = Y)).card : ℝ) *
      Real.exp (-a * treeLenCovOne m₀ K Y) ≤ M * Real.exp (-a' * treeLenCovOne m₀ K Y))
    (Y' : Set (CTorus d L N₁ m₁ K)) :
    ‖∑ q ∈ I.filter (fun q => bridge m₀ z q.2 = Y'), g q‖ ≤
      C₀ * M * ((nFibre d L : ℝ) *
        (Real.exp (a' * cBr d L) * Real.exp (-a' * treeLenCovOne m₀ K Y'))) := by
  have h𝒴dj : ∀ Y ∈ I.image (fun q => q.2), IsDj m₀ K Y := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hY
    exact hI q hq
  have hfib := fibre_weighted_le hN z (I.image (fun q => q.2)) h𝒴dj Y' ha'
  have hmap : ∀ q ∈ I.filter (fun q => bridge m₀ z q.2 = Y'),
      q.2 ∈ (I.image (fun q => q.2)).filter (fun Y => bridge m₀ z Y = Y') := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hq1, hq2⟩
  have hterm : ∀ Y ∈ (I.image (fun q => q.2)).filter (fun Y => bridge m₀ z Y = Y'),
      ∑ q ∈ (I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y),
        C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2) ≤
      C₀ * M * Real.exp (-a' * treeLenCovOne m₀ K Y) := by
    intro Y _
    have e : ∑ q ∈ (I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y),
        C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2) =
        (((I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y)).card : ℝ) *
          (C₀ * Real.exp (-a * treeLenCovOne m₀ K Y)) := by
      rw [Finset.sum_congr rfl (g := fun _ => C₀ * Real.exp (-a * treeLenCovOne m₀ K Y))]
      · simp
      · intro q hq
        rw [(Finset.mem_filter.1 hq).2]
    rw [e]
    have hsub : (I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y) ⊆
        I.filter (fun q => q.2 = Y) := by
      intro q hq
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h1).1, h2⟩
    have hcard : (((I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y)).card : ℝ) ≤
        ((I.filter (fun q => q.2 = Y)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h0 := hmult Y
    have hE : 0 ≤ Real.exp (-a * treeLenCovOne m₀ K Y) := (Real.exp_pos _).le
    calc (((I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y)).card : ℝ) *
          (C₀ * Real.exp (-a * treeLenCovOne m₀ K Y))
        = C₀ * ((((I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y)).card : ℝ) *
          Real.exp (-a * treeLenCovOne m₀ K Y)) := by ring
      _ ≤ C₀ * (((I.filter (fun q => q.2 = Y)).card : ℝ) *
          Real.exp (-a * treeLenCovOne m₀ K Y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hE) hC₀
      _ ≤ C₀ * (M * Real.exp (-a' * treeLenCovOne m₀ K Y)) :=
        mul_le_mul_of_nonneg_left h0 hC₀
      _ = C₀ * M * Real.exp (-a' * treeLenCovOne m₀ K Y) := by ring
  calc ‖∑ q ∈ I.filter (fun q => bridge m₀ z q.2 = Y'), g q‖
      ≤ ∑ q ∈ I.filter (fun q => bridge m₀ z q.2 = Y'), ‖g q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ I.filter (fun q => bridge m₀ z q.2 = Y'),
          C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2) :=
        Finset.sum_le_sum fun q hq => hg q (Finset.mem_filter.1 hq).1
    _ = ∑ Y ∈ (I.image (fun q => q.2)).filter (fun Y => bridge m₀ z Y = Y'),
          ∑ q ∈ (I.filter (fun q => bridge m₀ z q.2 = Y')).filter (fun q => q.2 = Y),
            C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2) :=
        (Finset.sum_fiberwise_of_maps_to (g := fun q : β × Set (CTorus d L N₁ m₁ K) => q.2) hmap
          (fun q => C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2))).symm
    _ ≤ ∑ Y ∈ (I.image (fun q => q.2)).filter (fun Y => bridge m₀ z Y = Y'),
          C₀ * M * Real.exp (-a' * treeLenCovOne m₀ K Y) := Finset.sum_le_sum hterm
    _ = C₀ * M * ∑ Y ∈ (I.image (fun q => q.2)).filter (fun Y => bridge m₀ z Y = Y'),
          Real.exp (-a' * treeLenCovOne m₀ K Y) := by rw [Finset.mul_sum]
    _ ≤ C₀ * M * ((nFibre d L : ℝ) *
        (Real.exp (a' * cBr d L) * Real.exp (-a' * treeLenCovOne m₀ K Y'))) :=
        mul_le_mul_of_nonneg_left hfib (mul_nonneg hC₀ hM)

/-- **The count over a fibre of the bridge, for `markedIdx`.** -/
theorem norm_fibre_sum_le (hN : L ^ m₀ ∣ N₁) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (g : β × Set (CTorus d L N₁ m₁ K) → ℂ) {C₀ a a' M : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M)
    (ha' : 0 ≤ a')
    (hg : ∀ q ∈ markedIdx reads dom z, ‖g q‖ ≤ C₀ * Real.exp (-a * treeLenCovOne m₀ K q.2))
    (hmult : ∀ Y, (((markedIdx reads dom z).filter (fun q => q.2 = Y)).card : ℝ) *
      Real.exp (-a * treeLenCovOne m₀ K Y) ≤ M * Real.exp (-a' * treeLenCovOne m₀ K Y))
    (Y' : Set (CTorus d L N₁ m₁ K)) :
    ‖∑ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'), g q‖ ≤
      C₀ * M * ((nFibre d L : ℝ) *
        (Real.exp (a' * cBr d L) * Real.exp (-a' * treeLenCovOne m₀ K Y'))) :=
  norm_fibre_sum_le_of_finset hN z _ (fun q hq => by
    obtain ⟨b, Y⟩ := q
    exact hdom b Y (mem_markedIdx.1 hq).1) g hC₀ hM ha' hg hmult Y'

omit [NeZero N₁] [NeZero L] in
open Classical in
/-- Sum of a function over `markedIdx` is the sum over all pairs `(b, Y)`, `Y ∈ dom b`, when the
function vanishes at the pairs left out. -/
theorem sum_markedIdx_eq (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (f : β × Set (CTorus d L N₁ m₁ K) → ℂ)
    (hf : ∀ b, ∀ Y ∈ dom b, (b, Y) ∉ markedIdx reads dom z → f (b, Y) = 0) :
    ∑ q ∈ markedIdx reads dom z, f q = ∑ b, ∑ Y ∈ dom b, f (b, Y) := by
  have e1 : ∑ b, ∑ Y ∈ dom b, f (b, Y) =
      ∑ q ∈ (Finset.univ : Finset β).biUnion (fun b => (dom b).image fun Y => (b, Y)), f q := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_image]
      intro Y _ Y' _ h
      exact (Prod.mk.inj h).2
    · intro b _ b' _ hbb'
      refine Finset.disjoint_left.2 fun q hq hq' => ?_
      obtain ⟨Y, _, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨Y', _, h⟩ := Finset.mem_image.1 hq'
      exact hbb' (Prod.mk.inj h).1.symm
  rw [e1]
  unfold markedIdx
  refine Finset.sum_filter_of_ne fun q hq hne => ?_
  by_contra hn
  obtain ⟨b, Y⟩ := q
  obtain ⟨b', hb', hq'⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨Y', hY', h⟩ := Finset.mem_image.1 hq'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  apply hne
  refine hf b' Y' hY' ?_
  intro hm
  exact hn (Finset.mem_filter.1 hm).2

open Classical in
/-- **The count (undecoupled, abstract terms).**  Let the `t`-derivatives of the marked block terms
of the pairs of `markedIdx` be bounded by `C₀ e^{-2κ d(Y)}`, and let at most `M (1 + d(Y))` pairs
of `markedIdx` share a domain `Y` (the number of blocks through a domain, (G1)).  Then
`‖markedOut z Y'‖ ≤ C₀ M nFibre e^{a cBr} e^{-a d(Y')}` with `a = 2κ - 1 ≥ 0`. -/
theorem norm_markedOut_le_of_term_bounds (hN : L ^ m₀ ∣ N₁)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ)
    {C₀ M κdec : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hκ : 1 ≤ 2 * κdec)
    (hbd : ∀ q ∈ markedIdx reads dom z, ‖deriv (markedBlockTerm (Ev q.1 q.2) ω a c Θ) 0‖ ≤
      C₀ * Real.exp (-(2 * κdec) * treeLenCovOne m₀ K q.2))
    (hcount : ∀ Y, (((markedIdx reads dom z).filter (fun q => q.2 = Y)).card : ℝ) ≤
      M * (1 + treeLenCovOne m₀ K Y))
    (Y' : Set (CTorus d L N₁ m₁ K)) :
    ‖markedOut m₀ reads dom z Ev ω a c Θ Y'‖ ≤ C₀ * M * ((nFibre d L : ℝ) *
      (Real.exp ((2 * κdec - 1) * cBr d L) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ K Y'))) := by
  refine norm_fibre_sum_le hN reads dom hdom z _ hC₀ hM (by linarith) hbd (fun Y => ?_) Y'
  have ht0 : 0 ≤ treeLenCovOne m₀ K Y := treeLenCovOne_nonneg m₀ K Y
  have key := one_add_mul_exp_le (treeLenCovOne m₀ K Y) κdec
  have e : Real.exp (-(2 * κdec) * treeLenCovOne m₀ K Y) =
      Real.exp (-2 * κdec * treeLenCovOne m₀ K Y) := by congr 1; ring
  rw [e]
  calc _ ≤ M * (1 + treeLenCovOne m₀ K Y) * Real.exp (-2 * κdec * treeLenCovOne m₀ K Y) :=
        mul_le_mul_of_nonneg_right (hcount Y) (Real.exp_pos _).le
    _ = M * ((1 + treeLenCovOne m₀ K Y) * Real.exp (-2 * κdec * treeLenCovOne m₀ K Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hM

open Classical in
/-- **The anchored sum, independent of the volume.**  If `‖markedOut z Y'‖ ≤ F₀ e^{-a d(Y')}` for
all `Y'` of `bridgeFamily`, then for `0 ≤ a''` and `aEnt + 1 ≤ a - a''` the sum of
`‖markedOut z Y'‖ e^{a'' d(Y')}` over `bridgeFamily` is at most `F₀ K₀(d, L, a - a'')`, a constant
independent of the root, the scale and the torus. -/
theorem sum_norm_markedOut_le_of_bound (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ)
    {F₀ a₀ a'' : ℝ} (hF₀ : 0 ≤ F₀)
    (hb : ∀ Y', ‖markedOut m₀ reads dom z Ev ω a c Θ Y'‖ ≤
      F₀ * Real.exp (-a₀ * treeLenCovOne m₀ K Y'))
    (ha : aEnt d L + 1 ≤ a₀ - a'') :
    ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
        ‖markedOut m₀ reads dom z Ev ω a c Θ Y'.1‖ * Real.exp (a'' * treeLenCovOne m₀ K Y'.1) ≤
      F₀ * K0 d L (a₀ - a'') := by
  refine le_trans (Finset.sum_le_sum fun Y' _ => ?_)
    (bridgeFamily_entropy hN hL (reads := reads) (dom := dom) hdom z ha hF₀)
  calc ‖markedOut m₀ reads dom z Ev ω a c Θ Y'.1‖ * Real.exp (a'' * treeLenCovOne m₀ K Y'.1)
      ≤ F₀ * Real.exp (-a₀ * treeLenCovOne m₀ K Y'.1) *
        Real.exp (a'' * treeLenCovOne m₀ K Y'.1) :=
        mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le
    _ = F₀ * Real.exp (-(a₀ - a'') * treeLenCovOne m₀ K Y'.1) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

omit [NeZero N₁] [NeZero L] in
/-- The derivative of a finite sum of terms differentiable at `0` is the sum of the derivatives
(here for the marked block terms indexed by `(b, Y)`, `Y ∈ dom b`). -/
theorem deriv_sum_sum_of_differentiableAt {ι : Type*} (s : Finset ι) {γ : Type*}
    (dom : ι → Finset γ) (T : ι → γ → ℂ → ℂ)
    (h : ∀ b ∈ s, ∀ Y ∈ dom b, DifferentiableAt ℂ (T b Y) 0) :
    deriv (fun t : ℂ => ∑ b ∈ s, ∑ Y ∈ dom b, T b Y t) 0 =
      ∑ b ∈ s, ∑ Y ∈ dom b, deriv (T b Y) 0 := by
  have := HasDerivAt.fun_sum (u := s) (A := fun b => fun t : ℂ => ∑ Y ∈ dom b, T b Y t)
    (A' := fun b => ∑ Y ∈ dom b, deriv (T b Y) 0) (x := (0 : ℂ))
    (fun b hb => HasDerivAt.fun_sum (fun Y hY => (h b hb Y hY).hasDerivAt))
  exact this.deriv

end Out

/-! ### Locality of the marked term -/

section Local

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {a c : F} {Θ : Λ} {R₁ r t₁ : ℝ}

/-- **Locality: a term that does not see the mask is constant in `t`.**  If
`Ev(Θ, σ (a + t c)) = Ev(Θ, σ a)` for `|t| < t₁`, `|σ| < R₁ + r`, then every marked term is the
same function of `σ`, its third derivatives agree, and `t ↦ markedBlockTerm Ev ω a c Θ t` is
constant on `|t| < t₁`, so its derivative at `0` vanishes. -/
theorem deriv_markedBlockTerm_eq_zero_of_local (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁)
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : Θ ∈ S)
    (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    (hloc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      Ev (Θ, σ • (a + t • c)) = Ev (Θ, σ • a)) :
    deriv (markedBlockTerm Ev ω a c Θ) 0 = 0 := by
  have hconst : ∀ t : ℂ, ‖t‖ < t₁ →
      markedBlockTerm Ev ω a c Θ t = markedBlockTerm Ev ω a c Θ 0 := by
    intro t ht
    have h0 : ‖(0 : ℂ)‖ < t₁ := by simpa using ht₁
    unfold markedBlockTerm rayTerm
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    congr 1
    have hs' : ‖(1 : ℂ) * (s : ℂ)‖ ≤ 1 := by
      rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    have hf : ∀ t' : ℂ, ‖t'‖ < t₁ → ∀ τ : ℂ, ‖τ‖ < r →
        AnalyticAt ℂ Ev (Θ, ((1 : ℂ) * (s : ℂ)) • (a + t' • c) + τ • (a + t' • c)) := by
      intro t' ht' τ hτ
      rw [← add_smul]
      refine hEv _ ⟨hΘ, hdom t' ht' _ ?_⟩
      calc ‖(1 : ℂ) * (s : ℂ) + τ‖ ≤ ‖(1 : ℂ) * (s : ℂ)‖ + ‖τ‖ := norm_add_le _ _
        _ < R₁ + r := by linarith
    rw [dl3_apply, dl3_apply, dirL3_eq hr (hf t ht), dirL3_eq hr (hf 0 h0)]
    unfold dirS3
    refine Filter.EventuallyEq.iteratedDeriv_eq 3 ?_
    have hball : Metric.ball (0 : ℂ) r ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds _ hr
    filter_upwards [hball] with τ hτ
    have hτ' : ‖τ‖ < r := by simpa using hτ
    have hn : ‖(1 : ℂ) * (s : ℂ) + τ‖ < R₁ + r := by
      calc ‖(1 : ℂ) * (s : ℂ) + τ‖ ≤ ‖(1 : ℂ) * (s : ℂ)‖ + ‖τ‖ := norm_add_le _ _
        _ < R₁ + r := by linarith
    rw [← add_smul, ← add_smul, hloc t ht _ hn, hloc 0 h0 _ hn]
  have hev : markedBlockTerm Ev ω a c Θ =ᶠ[nhds (0 : ℂ)]
      fun _ => markedBlockTerm Ev ω a c Θ 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ht₁] with t ht
    exact hconst t (by simpa using ht)
  rw [hev.deriv_eq]
  simp

end Local

/-! ### The step: the mask and the count -/

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- The lift of the masked field vanishes outside the fine block `B(z)`. -/
theorem liftC_maskUC_apply_of_notMem (v : S.EC) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∉ fineBlock z) : liftC S.hG' (S.maskUC z v) y = 0 := by
  funext i
  rw [liftC_apply]
  have h : unitPt S.hG' y ∉ S.blockU z := by
    intro hm
    apply hy
    refine (mem_fineBlock_iff_unitBlock1 (k := k)).2 ?_
    unfold blockU at hm
    have := (Finset.mem_filter.1 hm).2
    exact this
  simp [maskUC, h]

section Count

open Balaban.Multiscale

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The number of blocks through a domain** (G1): the pairs `(b, Y)` of `markedIdx` with a given
`Y` have distinct blocks `b`, all contained in `Y` (since `readSites ⊆ X₁ ⊆ Y`), so there are at
most `c₁ M^d (1 + d(Y))` of them (`card_blocks_filter_le`). -/
theorem card_markedIdx_fibre_le (hd : 3 ≤ d)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b)) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    ((((markedIdx (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z).filter (fun q => q.2 = Y)).card : ℕ) :
        ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCovOne m₀ (k + 1) Y) := by
  classical
  have hN : L ^ m₀ ∣ N₁ := (hcovV z).hN
  set P := (markedIdx (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z).filter (fun q => q.2 = Y) with hP
  have hmem : ∀ q ∈ P, Y ∈ polyDom S.G' (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    have := (mem_markedIdx.1 hq1).1
    rw [hq2] at this
    exact this
  by_cases hne : P.Nonempty
  · obtain ⟨q0, hq0⟩ := hne
    have hMD := polyDom_isMultiDom (hcovV q0.1) hd (hoptV q0.1) (hmem q0 hq0)
    have hinj : Set.InjOn (fun q : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) ×
        Set (CTorus d L N₁ m₁ (k + 1)) => q.1) (P : Set _) := by
      intro q hq q' hq' h
      have h1 := (Finset.mem_filter.1 hq).2
      have h2 := (Finset.mem_filter.1 hq').2
      exact Prod.ext h (h1.trans h2.symm)
    have hcard : P.card = (P.image (fun q => q.1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    have hS : ∀ b ∈ P.image (fun q => q.1),
        (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ Y := by
      intro b hb
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
      have hsub := subset_polyDom (hmem q hq)
      rw [← hX₁V q.1] at hsub
      intro x hx
      exact hsub (hZV q.1 ⟨x, hx, Or.inl rfl⟩)
    have := card_blocks_filter_le S.hG' le_rfl hN hMD (P.image (fun q => q.1)) hS
    rw [treeLenCov_eq_treeLenCovOne S.hG' m₀ Y] at this
    rw [hcard]; exact this
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h0 := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Y
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity

/-- **Locality of the marked term (undecoupled).**  If the block term `Ev` is analytic on
`XiCRaw × FlBall`, local in the sense of `vblock_expansion_scaled` (it reads the tangent only on
`psiThick Y`), and `psiThick Y` misses the fine block `B(z)`, the `t`-derivative at `0` of the
marked block term vanishes.  The mask `lift (M_z ψ')` is zero outside `B(z)`. -/
theorem deriv_markedBlockTerm_eq_zero_of_psiThick_disjoint_of_local
    {δ₁ Y₀ R₁ r t₁ : ℝ} {x : S.E} {u : ℂ} {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    {eps : ℝ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁)
    (hY0 : 0 ≤ Y₀) (hY : ∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁) (hHm : IsLevel Hm k)
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (han : AnalyticOnNhd ℂ Ev (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    (hloc : ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev u = Ev u')
    (hmiss : ∀ y ∈ psiThick Y, y ∉ fineBlock z) :
    deriv (markedBlockTerm Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
      (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0 = 0 := by
  have hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall Hm δ₁ := fun t ht σ hσ => S.markedDisc_hdom hHm hY0 hY hrad ht hσ
  refine deriv_markedBlockTerm_eq_zero_of_local hR₁ hr ht₁ han hΘ hdisc ?_
  intro t ht σ hσ
  have h0 : ‖(0 : ℂ)‖ < t₁ := by simpa using ht₁
  have hu : (Θ, σ • (liftC S.hG' (u • S.shiftUC x) +
      t • liftC S.hG' (S.maskUC z (S.shiftUC x)))) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁ :=
    ⟨hΘ, hdisc t ht σ hσ⟩
  have hu' : (Θ, σ • liftC S.hG' (u • S.shiftUC x)) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁ := by
    have := hdisc 0 h0 σ hσ
    rw [zero_smul, add_zero] at this
    exact ⟨hΘ, this⟩
  refine hloc _ hu _ hu' (agreeOn_refl _ Θ) fun y hy => ?_
  have hc := S.liftC_maskUC_apply_of_notMem z (S.shiftUC x) (hmiss y hy)
  show (σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x)))) y =
    (σ • liftC S.hG' (u • S.shiftUC x)) y
  rw [Pi.smul_apply, Pi.add_apply, Pi.smul_apply, hc, smul_zero, add_zero, Pi.smul_apply]

/-- **The Cauchy bound for the marked terms of the block expansion** (`marked_term_cauchy` with the
block term `Ev` of `vblock_expansion_scaled`, bound `E* e^{-2κ_dec d(Y)}`). -/
theorem norm_deriv_markedBlockTerm_le_of_vblock
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hHm : IsLevel Hm k)
    {δ₁ Y₀ R₁ r t₁ t₀ E κdec : ℝ} {x : S.E} {u : ℂ}
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} {eps a₁ ν : ℝ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hY0 : 0 ≤ Y₀) (hY : ∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₀ : 0 < t₀)
    (ht₀₁ : t₀ < t₁)
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (han : AnalyticOnNhd ℂ Ev (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    (hbd : ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
      ‖Ev w‖ ≤ E * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) :
    ‖deriv (markedBlockTerm Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
      (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0‖ ≤
      (3 * ‖E‖ / (r ^ 3 * t₀)) * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
  have h := (S.marked_term_cauchy z hHm hY0 hY hrad hR₁ hr ht₀ ht₀₁ han hbd hΘ).2
  have e : (fun t : ℂ => rayTerm (dl3 Ev (liftC S.hG' (S.markedTangentC z u t x)))
      taylorWeight (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ) =
      markedBlockTerm Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
        (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ := by
    funext t; exact (S.markedBlockTerm_marked_eq z Ev taylorWeight Θ u t x).symm
  rw [e] at h
  refine h.trans ?_
  rw [treeLenCov_eq_treeLenCovOne S.hG' m₀ Y]
  have hex : Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y) =
      Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by congr 1; ring
  rw [hex]
  have hr3 : 0 < r ^ 3 * t₀ := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr3]
  nlinarith [Real.exp_pos (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y), le_abs_self E,
    Real.norm_eq_abs E]

/-- The assembled count for given block terms (`marked_count_scaled` after the choice of
`Ev`).  The hypotheses `han`, `hbd`, `hloc` are the analyticity, bound and locality clauses of
`vblock_expansion_scaled` for the terms `Ev`. -/
theorem marked_count_scaled_of_vblock (hd : 3 ≤ d)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    {κdec : ℝ} (hκ1 : 1 ≤ 2 * κdec) (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b)) (hL : 2 ≤ L)
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hloc : ∀ b, ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev b Y u = Ev b Y u')
    (hbd : ∀ b, ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev b Y u‖ ≤ energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y))
    (han : ∀ b, ∀ Y, AnalyticOnNhd ℂ (Ev b Y)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁)) :
      ∀ {Y₀ R₁ r t₁ t₀ : ℝ}, 0 ≤ Y₀ → ∀ {x : S.E} {u : ℂ},
        (∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀) →
        (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
          Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        (∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
            markedOut m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0 ∧
          deriv (fun t : ℂ => ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ t) 0 =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0) ∧
        (∀ Y', ‖markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'‖ ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
        (∀ Y', markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' ≠ 0 →
            IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
        (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
          ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z},
            ‖markedOut m₀ (fun _ => Set.univ)
                (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
                Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'.1‖ *
              Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              K0 d L (2 * κdec - 1 - a'')) := by
  classical
  intro Y₀ R₁ r t₁ t₀ hY0 x u hY hrad hR₁ hr ht₀ ht₀₁ Θ hΘ
  have ht₁ : 0 < t₁ := ht₀.trans ht₀₁
  have hN : L ^ m₀ ∣ N₁ := (hcovV z).hN
  have hdom : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y :=
    fun b Y hY => isDj_of_polymerDomains (fun i : ParIdx S.G' (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.hG' (hcovV b) hd (fun i => i.1.2) (hoptV b) hY
  have hterm := fun b Y => norm_deriv_markedBlockTerm_le_of_vblock S z hHm hY0 hY hrad hR₁ hr ht₀ ht₀₁ hΘ
    (han b Y) (hbd b Y)
  have hcount := card_markedIdx_fibre_le S z hd hcovV hX₁V hoptV hZV
  have hzero : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
      (b, Y) ∉ markedIdx (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z →
      deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
        (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0 = 0 := by
    intro b Y hY' hnot
    refine S.deriv_markedBlockTerm_eq_zero_of_psiThick_disjoint_of_local z hR₁ hr ht₁ hY0 hY hrad hHm hΘ
      (han b Y) (hloc b Y) ?_
    intro y hy hyz
    exact hnot (mem_markedIdx.2 ⟨hY', ⟨rootSite z, trivial, rootSite_mem_fineBlock z⟩, ⟨y, hy, hyz⟩⟩)
  have hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall Hm δ₁ := fun t ht σ hσ => S.markedDisc_hdom hHm hY0 hY hrad ht hσ
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hM : 0 ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hbound := fun Y' => norm_markedOut_le_of_term_bounds hN (fun _ => Set.univ)
    (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdom z Ev taylorWeight
    (liftC S.hG' (u • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ
    (by positivity) hM hκ1 (fun q _ => hterm q.1 q.2) hcount Y'
  have hB : ∀ Y', ‖markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'‖ ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y') := by
    intro Y'
    refine (hbound Y').trans (le_of_eq ?_)
    ring
  refine ⟨⟨?_, ?_⟩, hB, fun Y' h => rootCube_mem_of_markedOut_ne_zero hN hL hdom z Ev taylorWeight _ _ Θ h,
    fun {a''} ha => sum_norm_markedOut_le_of_bound hN hL (fun _ => Set.univ)
      (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) hdom z Ev taylorWeight _ _ Θ
      (by positivity) hB ha⟩
  · rw [sum_markedOut_eq]
    exact sum_markedIdx_eq _ _ z _ hzero
  · exact deriv_sum_sum_of_differentiableAt _ _ _ fun b _ Y _ =>
      ((analyticOnNhd_markedBlockTerm hR₁ hr (analyticOnNhd_taylorWeight _) (han b Y) hΘ hdisc)
        0 (Metric.mem_ball_self ht₁)).differentiableAt

/-- **`MARK-SCALED-COUNT`, undecoupled level.**  The hypotheses are those of
`vblock_expansion_scaled` (as used in `marked_vblock_term_cauchy`) for every block `b`, the radius
condition (2) of `MARKCUBIC.md` of `marked_term_cauchy`, and `2 ≤ L`.  There are block terms
`E_{b,Y}` (`Ev b Y`) summing to the block energy (`vblock_expansion_scaled`), such that, writing
`a = lift (u ψ')`, `c = lift (M_z ψ')`, `dom b = polyDom (X₁ b, j b, 𝒦X b)` and
`F₀ = 3‖E*‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}`:

1. `∑_{Y' ∈ 𝒴_z} markedOut z Y' = ∑_b ∑_{Y ∈ dom b} ∂_t(markedBlockTerm …)|₀`, and this is the
   `t`-derivative at `0` of the sum of all the marked block terms;
2. `‖markedOut z Y'‖ ≤ F₀ e^{-(2κ_dec-1) d(Y')}` for every `Y'`;
3. `markedOut z Y' ≠ 0` implies `Y' ∈ 𝒟_K` and the root cube is a cube of `Y'`;
4. for `0 ≤ a''` and `aEnt + 1 ≤ 2κ_dec - 1 - a''`,
   `∑_{Y' ∈ 𝒴_z} ‖markedOut z Y'‖ e^{a'' d(Y')} ≤ F₀ K₀(d, L, 2κ_dec - 1 - a'')`.

`E* = energyBdScaled …`, `M = L^{m₀+m₁}`, `d(Y) = treeLenCovOne m₀ (k+1) Y`.  The index is
`markedIdx` with the trivial read set `Set.univ`. -/
theorem marked_count_scaled
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hΔV : ∀ b, treeLenCovOne m₀ (jV b) (XV b) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hmarV : ∀ b, BlockMargin S.G' (X₁V b)
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hL : 2 ≤ L) :
    ∃ Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      (∀ b, ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock S.G' Hm (compWeight L a₁) ν k (bgMultC S.G' (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') ψ' b =
        ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), Ev b Y (rawOf D, ψ')) ∧
      ∀ {Y₀ R₁ r t₁ t₀ : ℝ}, 0 ≤ Y₀ → ∀ {x : S.E} {u : ℂ},
        (∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀) →
        (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
          Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        (∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
            markedOut m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0 ∧
          deriv (fun t : ℂ => ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ t) 0 =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0) ∧
        (∀ Y', ‖markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'‖ ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
        (∀ Y', markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' ≠ 0 →
            IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
        (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
          ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z},
            ‖markedOut m₀ (fun _ => Set.univ)
                (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
                Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'.1‖ *
              Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              K0 d L (2 * κdec - 1 - a'')) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hex := fun b => vblock_expansion_scaled hC (hcovV b) (hX₁V b) hconn hrow (hoptV b) (hΔV b)
    hκ₀ hκdec hκ h1 hlog S.hk1 le_rfl hHm S.hG' b (hZV b) (hmarV b)
  choose Ev hsum hloc hbd han using hex
  exact ⟨Ev, fun b => hsum b, marked_count_scaled_of_vblock S z hd hcovV hX₁V hoptV
    (by linarith) hHm hZV hL Ev hloc hbd han⟩

end Count

end StepSetting

end Balaban.Fluctuation
