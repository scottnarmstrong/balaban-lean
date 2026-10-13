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

end StepSetting

end Balaban.Fluctuation
