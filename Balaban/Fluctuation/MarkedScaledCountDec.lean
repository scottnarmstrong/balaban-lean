/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedVBlockDec
public import Balaban.Fluctuation.MarkedSharpCount

/-!
# The count of the marked terms at the decoupled level (`MARK-COUNT`, decoupled)

The decoupled counterpart of `MarkedSharpCount.lean`.  The block functionals along the masked
decoupled tangent have the localized terms `evDec` of `MarkedVBlockDec.lean`
(`vblock_expansion_hat_marked_scaled`); this file sums the `t`-derivatives at `0` of these terms,
after the bridge to the root of `MarkedRootGeometry.lean`.

* `markedOutDec`: for a root `z` and a domain `Y'`, the sum of `∂_t T_{b,Y}|_{t=0}` over the pairs
  `(b, Y)` of `markedIdx` with `bridge z Y = Y'`.  A literal finite sum, for a family of terms
  `T b Y : ℂ → ℂ`; the application takes `T b Y t = evDec … Zm um t Y u`.  The index is `markedIdx`
  with the trivial read set (`reads b = Set.univ`), as in `MarkedSharpCount.lean`.
* `marked_count_scaled_dec` (the count): the block terms are those of
  `vblock_expansion_hat_marked_scaled`; (i) the sum of the `t`-derivatives of the block functionals
  along the masked tangent is the double sum of the derivatives of the terms (unconditional), and
  the sum of `markedOutDec` over `bridgeFamily` is that double sum provided the derivatives of the
  pairs left out of `markedIdx` vanish; (ii) `‖markedOutDec z Y'‖ ≤ F₀ e^{-(2κ_dec-1) d(Y')}`;
  (iii) a nonzero `markedOutDec z Y'` has `Y'` in `𝒟_K` with the root cube among its cubes;
  (iv) the weighted sum over `bridgeFamily` is bounded independently of the volume.
* `markedOutDec_empty`: for the empty mask every `markedOutDec` vanishes.

`F₀ = ‖E*‖/t₀ · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}`, `E* = energyBdScaled …`, `M = L^{m₀+m₁}`.
The quantity bounded is the derivative of the localized terms of the block functionals (the cubic
Taylor step is not part of this file).

## Scope

`MARK-PARAM` and the marked family are NOT proved here; zero class only; nothing depends on a
choice of generating sets for the class terms.  The vanishing of `∂_t T_{b,Y}|₀` for the pairs with
`psiThick Y` disjoint from the fine block of the root is NOT proved: the landed locality clause is
locality in the data at fixed marks; the vanishing needs locality of the localized term in the
marks, which requires a two-mark version of `fanHL_local_marked`.  It is the hypothesis of the
resummation identity (`_of_vanishing`) and of nothing else.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory Filter
  Balaban.SmallField.Def6 Balaban.Background Balaban.SmallField Set

/-! ### The output-indexed sum -/

section Out

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {β : Type*} [Fintype β]

open Classical in
/-- **The decoupled marked terms attached to the rooted domain `Y'`.**  For the root `z` and a
family of terms `T b Y : ℂ → ℂ` (functions of the mark `t`), the sum of the derivatives
`∂_t T_{b,Y}|_{t=0}` over the pairs `(b, Y)` of `markedIdx reads dom z` whose bridge to the root
is `Y'`. -/
noncomputable def markedOutDec (m₀ : ℕ) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ) (Y' : Set (CTorus d L N₁ m₁ K)) : ℂ :=
  ∑ q ∈ (markedIdx reads dom z).filter (fun q => bridge m₀ z q.2 = Y'), deriv (T q.1 q.2) 0

variable {m₀ : ℕ}

/-- **Resummation over the output polymers.** -/
theorem sum_markedOutDec_eq (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ) :
    ∑ Y' ∈ bridgeFamily m₀ reads dom z, markedOutDec m₀ reads dom z T Y' =
      ∑ q ∈ markedIdx reads dom z, deriv (T q.1 q.2) 0 :=
  sum_fibre_bridgeFamily reads dom z _

/-- A nonzero `markedOutDec` has its output polymer in the label family. -/
theorem mem_bridgeFamily_of_markedOutDec_ne_zero (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ)
    {Y' : Set (CTorus d L N₁ m₁ K)} (h : markedOutDec m₀ reads dom z T Y' ≠ 0) :
    Y' ∈ bridgeFamily m₀ reads dom z := by
  classical
  by_contra hn
  apply h
  unfold markedOutDec
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
  obtain ⟨b, Y⟩ := q
  obtain ⟨h1, h2, h3⟩ := mem_markedIdx.1 hq1
  exact absurd (mem_bridgeFamily.2 ⟨b, Y, h1, h2, h3, hq2⟩) hn

/-- **Anchoring.**  A nonzero `markedOutDec z Y'` has the root cube among the cubes of `Y'`. -/
theorem rootCube_mem_of_markedOutDec_ne_zero (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ)
    {Y' : Set (CTorus d L N₁ m₁ K)} (h : markedOutDec m₀ reads dom z T Y' ≠ 0) :
    IsDj m₀ K Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y' := by
  have hm := mem_bridgeFamily_of_markedOutDec_ne_zero reads dom z T h
  exact ⟨(bridgeFamily_spec hN hL hdom z hm).1, (bridgeFamily_spec hN hL hdom z hm).2.1⟩

open Classical in
/-- **The count (abstract terms).**  If the `t`-derivatives of the terms of the pairs of
`markedIdx` are bounded by `C₀ e^{-2κ d(Y)}` and at most `M (1 + d(Y))` pairs of `markedIdx` share
a domain `Y`, then `‖markedOutDec z Y'‖ ≤ C₀ M nFibre e^{a cBr} e^{-a d(Y')}`, `a = 2κ - 1 ≥ 0`. -/
theorem norm_markedOutDec_le_of_term_bounds (hN : L ^ m₀ ∣ N₁)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ)
    {C₀ M κdec : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hκ : 1 ≤ 2 * κdec)
    (hbd : ∀ q ∈ markedIdx reads dom z, ‖deriv (T q.1 q.2) 0‖ ≤
      C₀ * Real.exp (-(2 * κdec) * treeLenCovOne m₀ K q.2))
    (hcount : ∀ Y, (((markedIdx reads dom z).filter (fun q => q.2 = Y)).card : ℝ) ≤
      M * (1 + treeLenCovOne m₀ K Y))
    (Y' : Set (CTorus d L N₁ m₁ K)) :
    ‖markedOutDec m₀ reads dom z T Y'‖ ≤ C₀ * M * ((nFibre d L : ℝ) *
      (Real.exp ((2 * κdec - 1) * cBr d L) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ K Y'))) := by
  refine norm_fibre_sum_le hN reads dom hdom z (fun q => deriv (T q.1 q.2) 0) hC₀ hM
    (by linarith) hbd (fun Y => ?_) Y'
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
/-- **The anchored sum, independent of the volume.**  If `‖markedOutDec z Y'‖ ≤ F₀ e^{-a₀ d(Y')}`
for all `Y'`, then for `aEnt + 1 ≤ a₀ - a''` the sum of `‖markedOutDec z Y'‖ e^{a'' d(Y')}` over
`bridgeFamily` is at most `F₀ K₀(d, L, a₀ - a'')`. -/
theorem sum_norm_markedOutDec_le_of_bound (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ)
    {F₀ a₀ a'' : ℝ} (hF₀ : 0 ≤ F₀)
    (hb : ∀ Y', ‖markedOutDec m₀ reads dom z T Y'‖ ≤
      F₀ * Real.exp (-a₀ * treeLenCovOne m₀ K Y'))
    (ha : aEnt d L + 1 ≤ a₀ - a'') :
    ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
        ‖markedOutDec m₀ reads dom z T Y'.1‖ * Real.exp (a'' * treeLenCovOne m₀ K Y'.1) ≤
      F₀ * K0 d L (a₀ - a'') := by
  refine le_trans (Finset.sum_le_sum fun Y' _ => ?_)
    (bridgeFamily_entropy hN hL (reads := reads) (dom := dom) hdom z ha hF₀)
  calc ‖markedOutDec m₀ reads dom z T Y'.1‖ * Real.exp (a'' * treeLenCovOne m₀ K Y'.1)
      ≤ F₀ * Real.exp (-a₀ * treeLenCovOne m₀ K Y'.1) *
        Real.exp (a'' * treeLenCovOne m₀ K Y'.1) :=
        mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le
    _ = F₀ * Real.exp (-(a₀ - a'') * treeLenCovOne m₀ K Y'.1) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **The resummation identity, conditional on the vanishing.**  If the derivative vanishes for the
pairs `(b, Y)`, `Y ∈ dom b`, left out of `markedIdx`, the sum of `markedOutDec` over
`bridgeFamily` is the double sum of all the derivatives. -/
theorem sum_markedOutDec_eq_sum_of_vanishing (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ)
    (hzero : ∀ b, ∀ Y ∈ dom b, (b, Y) ∉ markedIdx reads dom z → deriv (T b Y) 0 = 0) :
    ∑ Y' ∈ bridgeFamily m₀ reads dom z, markedOutDec m₀ reads dom z T Y' =
      ∑ b, ∑ Y ∈ dom b, deriv (T b Y) 0 := by
  rw [sum_markedOutDec_eq]
  exact sum_markedIdx_eq reads dom z (fun q => deriv (T q.1 q.2) 0) hzero

/-- **The empty mask** (consistency).  If every term is constant in the mark, in particular for
the empty mask `Zm = ∅` (`deriv_evTerm_marked_empty`), then every `markedOutDec` vanishes. -/
theorem markedOutDec_eq_zero_of_deriv_zero (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K)
    (T : β → Set (CTorus d L N₁ m₁ K) → ℂ → ℂ) (h : ∀ b Y, deriv (T b Y) 0 = 0)
    (Y' : Set (CTorus d L N₁ m₁ K)) : markedOutDec m₀ reads dom z T Y' = 0 := by
  unfold markedOutDec
  exact Finset.sum_eq_zero fun q _ => h q.1 q.2

end Out

/-! ### The number of blocks through a domain -/

section Count

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The number of blocks through a domain** (G1), for a general level-`(k+1)` generating set
(`card_markedIdx_fibre_le` of `MarkedSharpCount.lean` without the step setting). -/
theorem card_markedIdx_fibre_le_dec (hG' : IsLevel Gp (k + 1)) (hd : 3 ≤ d)
    (z : RootIdx d L N₁ m₁ (k + 1))
    (hcovV : ∀ b, CovSetup Gp m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b)) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    ((((markedIdx (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) z).filter (fun q => q.2 = Y)).card : ℕ) :
        ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCovOne m₀ (k + 1) Y) := by
  classical
  have hN : L ^ m₀ ∣ N₁ := (hcovV z).hN
  set P := (markedIdx (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) z).filter (fun q => q.2 = Y) with hP
  have hmem : ∀ q ∈ P, Y ∈ polyDom Gp (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) := by
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
    have := card_blocks_filter_le hG' le_rfl hN hMD (P.image (fun q => q.1)) hS
    rw [treeLenCov_eq_treeLenCovOne hG' m₀ Y] at this
    rw [hcard]; exact this
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h0 := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Y
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity

end Count

/-! ### The assembled count -/

section Main

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The family of block terms along the masked tangent**, at the fixed data `u` and fixed
`um`: `T b Y t = evDec … (F₁ b) (Sol b) (blockEnergyFun … b) Zm um t Y u`. -/
noncomputable abbrev evDecFam (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ) (a₁ ν : ℝ) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Zm : Finset (unitPts Gp)) (um : ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) :
    Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) → ℂ → ℂ :=
  fun b Y t => evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν hG' cc (F₁ b) (Sol b)
    (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) Zm um t Y u

/-- **`MARK-COUNT`, decoupled level.**  The hypotheses are those of
`vblock_expansion_hat_marked_scaled` for every old block `b` (with the radius inequality on the
marks in the conclusion), `2 ≤ L`.  There are maps `F₁ b`, `Sol b` such that the block functionals
`blockEnergyFun … b` along the masked tangent have the localized terms `evDec …` of
`vblock_expansion_hat_marked_scaled` (sum identity and locality for every `b`), and for
`T b Y t = evDec … (F₁ b) (Sol b) … Zm um t Y (rawOf D, ψh)`, `dom b = polyDom (X₁ b, j b, 𝒦X b)`,
a root `zr`, marks `‖um‖ + b₀` in the radius set and `0 < t₀ ≤ b₀`, and
`F₀ = ‖E*‖/t₀ · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}` (`E* = energyBdScaled …`, `M = L^{m₀+m₁}`):

1. the `t`-derivative at `0` of the sum over `b` of the block functionals along the masked tangent
   is `∑_b ∑_{Y ∈ dom b} ∂_t T_{b,Y}|₀`; and if the derivatives of the pairs left out of
   `markedIdx` vanish, this is also `∑_{Y' ∈ 𝒴_zr} markedOutDec zr Y'`;
2. `‖markedOutDec zr Y'‖ ≤ F₀ e^{-(2κ_dec-1) d(Y')}` for every `Y'`;
3. `markedOutDec zr Y' ≠ 0` implies `Y' ∈ 𝒟_{k+1}` and the root cube is a cube of `Y'`;
4. for `aEnt + 1 ≤ 2κ_dec - 1 - a''`, the sum over `𝒴_zr` of
   `‖markedOutDec zr Y'‖ e^{a'' d(Y')}` is at most `F₀ K₀(d, L, 2κ_dec - 1 - a'')`. -/
theorem marked_count_scaled_dec
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcovV : ∀ b, CovSetup Gp m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jV b) (𝒦XV b))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hΔV : ∀ b, treeLenCovOne m₀ (jV b) (XV b) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hmarV : ∀ b, BlockMargin Gp (X₁V b)
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hL : 2 ≤ L) (zr : RootIdx d L N₁ m₁ (k + 1)) :
    ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      (∀ b, ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) D ψh =
        ∑ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b),
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν hG' cc (F₁ b) (Sol b)
            (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) Zm um tm Y (rawOf D, ψh)) ∧
      (∀ b, ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' →
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν hG' cc (F₁ b) (Sol b)
            (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) Zm um tm Y u =
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν hG' cc (F₁ b) (Sol b)
            (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) Zm um tm Y u') ∧
      ∀ (um : ℂ) (b₀ t₀ : ℝ), 0 < t₀ → t₀ ≤ b₀ →
        (‖um‖ + b₀) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        (deriv (fun tm : ℂ => ∑ b,
            markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm
              (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) D ψh) 0 =
          ∑ b, ∑ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b),
            deriv (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh) b Y) 0 ∧
          ((∀ b, ∀ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b),
              (psiThick Y ∩ fineBlock zr) = ∅ →
              deriv (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh) b Y) 0 = 0) →
            ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
                (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr,
              markedOutDec m₀ (fun _ => Set.univ)
                (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr
                (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh)) Y' =
              ∑ b, ∑ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b),
                deriv (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh) b Y) 0)) ∧
        (∀ Y', ‖markedOutDec m₀ (fun _ => Set.univ)
              (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr
              (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh)) Y'‖ ≤
            (‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / t₀) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
        (∀ Y', markedOutDec m₀ (fun _ => Set.univ)
              (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr
              (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh)) Y' ≠ 0 →
            IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) zr ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
        (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
          ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr},
            ‖markedOutDec m₀ (fun _ => Set.univ)
                (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr
                (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh)) Y'.1‖ *
              Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
            (‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / t₀) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              K0 d L (2 * κdec - 1 - a'')) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hex := fun b => vblock_expansion_hat_marked_scaled hC hk hG hG' cc hcψ Zm hMX hdm hα hsm
    (hcovV b) (hX₁V b) hconn hrow (hoptV b) (hΔV b) hκ₀ hκdec hκ h1 hlog b (hZV b) (hmarV b)
  choose F₁ Sol hA hB hC' hD hE hF using hex
  refine ⟨F₁, Sol, hA, hB, ?_⟩
  intro um b₀ t₀ ht₀ htb hrad D hDd ψh hψh
  have hb₀ : 0 ≤ b₀ := ht₀.le.trans htb
  have hN : L ^ m₀ ∣ N₁ := (hcovV zr).hN
  have hu : (rawOf D, ψh) ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := ⟨⟨D, hDd, rfl⟩, hψh⟩
  have hdom : ∀ b, ∀ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y :=
    fun b Y hY => isDj_of_polymerDomains (fun i : ParIdx Gp (↑(X₁V b) :
      Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) hG' (hcovV b) hd (fun i => i.1.2) (hoptV b) hY
  -- the radius facts
  have hrad0 : (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ :=
    mem_markedRadiusSet_of_pos hC.δ₁_pos hrad (le_refl ‖um‖) (show ‖(0 : ℂ)‖ ≤ b₀ by
      simpa using hb₀)
  have hmem0 : (um, (0 : ℂ)) ∈ {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    hrad0
  -- differentiability of the block functionals at `t = 0`
  have hdiffT : ∀ b, ∀ Y, DifferentiableAt ℂ (fun t : ℂ =>
      evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh) b Y t) 0 :=
    fun b Y => differentiableAt_mark_slice (um := um)
      (g := fun w : ℂ × ℂ => evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν hG' cc (F₁ b) (Sol b)
        (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) Zm w.1 w.2 Y (rawOf D, ψh))
      ((hD b Y _ hu) (um, 0) hmem0)
  have hnhds : {t : ℂ | (um, t) ∈ {w : ℂ × ℂ |
      (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}} ∈ nhds (0 : ℂ) :=
    ((isOpen_markedRadiusSet (markedRad d L N k a₁ κ cψ cc) δ₁).preimage
      (continuous_const.prodMk continuous_id)).mem_nhds hmem0
  have hdiffF : ∀ b, DifferentiableAt ℂ (fun tm : ℂ =>
      markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) D ψh)
      0 := by
    intro b
    have hev : (fun tm : ℂ =>
        markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) D
          ψh) =ᶠ[nhds (0 : ℂ)] fun t => ∑ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b),
          evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh) b Y t := by
      filter_upwards [hnhds] with t ht using hA b um t ht D hDd ψh hψh
    exact (hev.differentiableAt_iff).2 (DifferentiableAt.fun_sum fun Y _ => hdiffT b Y)
  have hderiv : deriv (fun tm : ℂ => ∑ b,
      markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) D ψh)
      0 = ∑ b, ∑ Y ∈ polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b),
        deriv (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh) b Y) 0 := by
    rw [deriv_fun_sum fun b _ => hdiffF b]
    exact Finset.sum_congr rfl fun b _ => hF b um hrad0 D hDd ψh hψh
  -- the counting data
  have hterm : ∀ b, ∀ Y, ‖deriv (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um
      (rawOf D, ψh) b Y) 0‖ ≤ (‖energyBdScaled d L N (compWeight L a₁) k
        (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / t₀) *
        Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
    intro b Y
    have h5 := hE b ‖um‖ b₀ t₀ (norm_nonneg _) hb₀ ht₀ htb hrad um le_rfl Y _ hu
    refine h5.trans ?_
    rw [treeLenCov_eq_treeLenCovOne hG' m₀ Y]
    have hex : Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y) =
        Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by congr 1; ring
    rw [hex, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.le_norm_self _) (Real.exp_pos _).le) ht₀.le
  have hcount := card_markedIdx_fibre_le_dec hG' hd zr hcovV hX₁V hoptV hZV (Hm := Hm)
  have hM : 0 ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hκ1 : 1 ≤ 2 * κdec := by
    have : (0 : ℝ) ≤ κ₀ := hκ₀
    linarith
  have hbound := fun Y' => norm_markedOutDec_le_of_term_bounds hN (fun _ => Set.univ)
    (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) hdom zr
    (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh))
    (by positivity) hM hκ1 (fun q _ => hterm q.1 q.2) hcount Y'
  have hB : ∀ Y', ‖markedOutDec m₀ (fun _ => Set.univ)
              (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) zr
              (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol Zm um (rawOf D, ψh)) Y'‖ ≤
            (‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / t₀) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y') := by
    intro Y'
    refine (hbound Y').trans (le_of_eq ?_)
    ring
  refine ⟨⟨hderiv, fun hz => ?_⟩, hB,
    fun Y' h => rootCube_mem_of_markedOutDec_ne_zero hN hL hdom zr _ h,
    fun {a''} ha => sum_norm_markedOutDec_le_of_bound hN hL (fun _ => Set.univ)
      (fun b => polyDom Gp (X₁V b) m₀ (jV b) (𝒦XV b)) hdom zr _ (by positivity) hB ha⟩
  refine sum_markedOutDec_eq_sum_of_vanishing _ _ zr _ fun b Y hY hnot => hz b Y hY ?_
  by_contra hne
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
  exact hnot (mem_markedIdx.2 ⟨hY, ⟨rootSite zr, trivial, rootSite_mem_fineBlock zr⟩, ⟨y, hy⟩⟩)

/-- **Consistency at the empty mask** (`deriv_evTerm_marked_empty`): with `Zm = ∅` the tangent does
not depend on `t`, every `t`-derivative of a localized term vanishes, and `markedOutDec` is `0`. -/
theorem markedOutDec_empty (reads : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Set (CTorus d L N₁ m₁ (k + 1)))
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (zr : RootIdx d L N₁ m₁ (k + 1)) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (um : ℂ) (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ))
    (Y' : Set (CTorus d L N₁ m₁ (k + 1))) :
    markedOutDec m₀ reads dom zr
      (evDecFam X₁V jV 𝒦XV m₀ a₁ ν hG' cc F₁ Sol (∅ : Finset (unitPts Gp)) um u) Y' = 0 :=
  markedOutDec_eq_zero_of_deriv_zero reads dom zr _ (fun b Y =>
    deriv_evTerm_marked_empty (Hm := Hm) hG' cc (F₁ b) (Sol b)
      (blockEnergyFun Gp Hm (compWeight L a₁) ν k b) um Y u) Y'

end Main

end Balaban.Fluctuation
