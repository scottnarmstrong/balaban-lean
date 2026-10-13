/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LabelSum
public import Balaban.Fluctuation.HatLabelsAct
public import Balaban.Fluctuation.MarkedRootGeometry
public import Balaban.Fluctuation.Theorem42Geom
public import Balaban.Fluctuation.ObsMeanBlock
public import Balaban.Inhabited.HatExpansionWitnessLabels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Extension of a label activity by zero, and the labels of single cubes

A label activity `A` on a label system `Lab` is extended to the sum `Lab.sum Lab'` (the landed
`CubeLabels.sum`) by the value `0` on the new labels (`LabelAct.extendZero`).  The entropy constant
becomes `Kc + K'`, where `K'` bounds the entropy sum of the new labels; the total over all labels is
unchanged (`LabelAct.extendZero_total`), so an identity "exponent = sum of the activities"
holding almost everywhere transfers verbatim (`LabelAct.extendZero_hW`, in the shapes of
`InterpMarks.hW` and `ObsMarks.hW`).

Two families of new labels occur: the bridge domains of one root (`bridgeLabels`, entropy constant
`K0 d L κ0`) and all single cubes (`cubeLabels`; the label of the aligned cube `c` is the box
`box c (L a)`, of size `0`, entropy constant `K0 d L κ0`, or the number of cubes for any `κ0`).
The size `0` discharges the hypothesis `dl y = 0` of `blockMark_fields`.

The physical marks family and the `E1MarksC` / `ObsMarks` inhabitants are NOT constructed here.
Everything is independent of the datum, the chart and the choice of generators.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory
open scoped Classical

section Extend

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb'] {Lab : CubeLabels m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

/-- **Extension by zero**: the activity of a label of `Lab` is that of `A`; the labels of `Lab'`
have activity `0`.  The entropy constant is `Kc + K'`. -/
noncomputable def LabelAct.extendZero (A : LabelAct Lab Ωb εH κH κ0 Kc)
    (Lab' : CubeLabels m₀ j Ω Lb') (hεH : 0 ≤ εH) (K' : ℝ)
    (hent' : ∀ b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω,
      ∑ y : Lb', (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab'.ysite y then
        Real.exp (-κ0 * Lab'.dl y) else 0) ≤ K') :
    LabelAct (Lab.sum Lab') Ωb εH κH κ0 (Kc + K') where
  H := Sum.elim A.H (fun _ _ => 0)
  meas := fun y => by cases y with
    | inl y => exact A.meas y
    | inr y => exact measurable_const
  dep := fun y => by cases y with
    | inl y => exact A.dep y
    | inr y => exact fun _ _ _ => rfl
  bound := fun y Φ => by
    cases y with
    | inl y => exact A.bound y Φ
    | inr y =>
      show ‖(0 : ℂ)‖ ≤ _
      rw [norm_zero]; exact mul_nonneg hεH (Real.exp_nonneg _)
  entropy := fun b => by
    rw [Fintype.sum_sum_type]
    exact add_le_add (A.entropy b) (hent' b)

variable (A : LabelAct Lab Ωb εH κH κ0 Kc) (Lab' : CubeLabels m₀ j Ω Lb') (hεH : 0 ≤ εH) (K' : ℝ)
  (hent' : ∀ b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω,
      ∑ y : Lb', (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab'.ysite y then
        Real.exp (-κ0 * Lab'.dl y) else 0) ≤ K')

@[simp] theorem LabelAct.extendZero_H_inl (y : Lb) :
    (A.extendZero Lab' hεH K' hent').H (Sum.inl y) = A.H y := rfl

@[simp] theorem LabelAct.extendZero_H_inr (y : Lb') (Φ : ∀ b, Ωb b) :
    (A.extendZero Lab' hεH K' hent').H (Sum.inr y) Φ = 0 := rfl

/-- **The label sum is unchanged** by the extension by zero. -/
theorem LabelAct.extendZero_total (Φ : ∀ b, Ωb b) :
    ∑ y, (A.extendZero Lab' hεH K' hent').H y Φ = ∑ y, A.H y Φ := by
  rw [Fintype.sum_sum_type]
  simp [LabelAct.extendZero]

/-- **Transfer of an almost-everywhere identity** `W x = ∑ y, A.H y (restr x)`. -/
theorem LabelAct.extendZero_hW {X : Type*} [MeasurableSpace X] {ν : Measure X} {W : X → ℂ}
    {restr : X → ∀ b, Ωb b} (h : ∀ᵐ x ∂ν, W x = ∑ y, A.H y (restr x)) :
    ∀ᵐ x ∂ν, W x = ∑ y, (A.extendZero Lab' hεH K' hent').H y (restr x) :=
  h.mono fun x hx => by rw [hx, LabelAct.extendZero_total]

end Extend

section Families

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb'] {Lab : CubeLabels m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}
  {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **The exact shape of `InterpMarks.hW`**: for a family `A : ℂ → LabelAct …` and the exponent
`W s`, the identity along `s ∈ [0,1]` transfers to the family `fun u => (A u).extendZero …`. -/
theorem LabelAct.extendZero_hW_interp (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Lab' : CubeLabels m₀ j Ω Lb') (hεH : 0 ≤ εH) (K' : ℝ)
    (hent' : ∀ b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω,
      ∑ y : Lb', (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab'.ysite y then
        Real.exp (-κ0 * Lab'.dl y) else 0) ≤ K')
    {W : ℝ → X → ℂ} {restr : X → ∀ b, Ωb b}
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (A (s : ℂ)).H y (restr x)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, ((A (s : ℂ)).extendZero Lab' hεH K' hent').H y (restr x) :=
  fun s hs => LabelAct.extendZero_hW _ Lab' hεH K' hent' (hW s hs)

/-- **The exact shape of `ObsMarks.hW`** (the activity at the parameters `(s, 1)`). -/
theorem LabelAct.extendZero_hW_obs (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Lab' : CubeLabels m₀ j Ω Lb') (hεH : 0 ≤ εH) (K' : ℝ)
    (hent' : ∀ b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω,
      ∑ y : Lb', (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab'.ysite y then
        Real.exp (-κ0 * Lab'.dl y) else 0) ≤ K')
    {W : ℝ → X → ℂ} {restr : X → ∀ b, Ωb b}
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (A (s : ℂ) 1).H y (restr x)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, ((A (s : ℂ) 1).extendZero Lab' hεH K' hent').H y (restr x) :=
  fun s hs => LabelAct.extendZero_hW _ Lab' hεH K' hent' (hW s hs)

end Families

section Labels

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The root-bridge labels**: the labels of the finite family `𝒴_z` of the bridge domains of one
root, each of its own size `d^cov_K`. -/
noncomputable def bridgeLabels {β : Type*} [Fintype β] (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ
      {Y' // Y' ∈ bridgeFamily m₀ reads dom z} :=
  thickLabels _ (bridgeFamily_isDj hN hL hdom z)

/-- **Entropy of the root-bridge labels**: for `κ₀ ≥ a_ent + 1`, every cube lies in labels of total
weight at most `K0 d L κ0` (independent of the root, the scale and the torus). -/
theorem bridgeLabels_entropy {β : Type*} [Fintype β] (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) {κ0 : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :
    ∑ y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
      (if box b.1 (cellSide L m₀ m₁ K) ⊆ (bridgeLabels hN hL reads dom hdom z).ysite y then
        Real.exp (-κ0 * (bridgeLabels hN hL reads dom hdom z).dl y) else 0) ≤ K0 d L κ0 :=
  entropy_thick hN le_rfl _ (bridgeFamily_isDj hN hL hdom z) hκ0 b

/-- The family of the single cubes at scale `j`: the boxes `box c (L a)` of the aligned `c`. -/
noncomputable def cubeFamily (j : ℕ) : Finset (Set (CTorus d L N₁ m₁ K)) :=
  (Finset.univ.filter fun c : CTorus d L N₁ m₁ K => Aligned (cellSide L m₀ m₁ j) c).image
    fun c => box c (L * cellSide L m₀ m₁ j)

theorem mem_cubeFamily {j : ℕ} {Z : Set (CTorus d L N₁ m₁ K)} :
    Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j ↔
      ∃ c, Aligned (cellSide L m₀ m₁ j) c ∧ Z = box c (L * cellSide L m₀ m₁ j) := by
  classical
  simp only [cubeFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

theorem cubeFamily_isDj {j : ℕ} : ∀ Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j,
    IsDj m₀ j Z := by
  intro Z hZ
  obtain ⟨c, hc, rfl⟩ := mem_cubeFamily.1 hZ
  exact isDj_box hc

/-- **The single-cube labels** at scale `j` on `Ω = univ`: one label for each aligned `π′_j`-cube
(the box `box c (L a)`), of size `d^cov_j = 0`. -/
noncomputable def cubeLabels (j : ℕ) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ
      {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j} :=
  thickLabels _ cubeFamily_isDj

/-- **The size of a one-cube label is `0`.** -/
theorem cubeLabels_dl {j : ℕ} (Z : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j}) :
    (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j).dl Z = 0 := by
  obtain ⟨c, hc, hZ⟩ := mem_cubeFamily.1 Z.2
  show treeLenCovOne m₀ j Z.1 = 0
  rw [hZ]; exact treeLenCovOne_box c hc

/-- **Entropy of the single-cube labels**, `κ₀ ≥ a_ent + 1`: constant `K0 d L κ0`. -/
theorem cubeLabels_entropy {j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {κ0 : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ) :
    ∑ y : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j},
      (if box b.1 (cellSide L m₀ m₁ j) ⊆ (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j).ysite y then
        Real.exp (-κ0 * (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j).dl y) else 0) ≤ K0 d L κ0 :=
  entropy_thick hN hj _ cubeFamily_isDj hκ0 b

/-- **Entropy of the single-cube labels for every `κ₀`** (all sizes are `0`): the number of cubes. -/
theorem cubeLabels_entropy_card {j : ℕ} (κ0 : ℝ)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ) :
    ∑ y : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j},
      (if box b.1 (cellSide L m₀ m₁ j) ⊆ (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j).ysite y then
        Real.exp (-κ0 * (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j).dl y) else 0) ≤
      (Nat.card {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j} : ℝ) := by
  classical
  calc _ ≤ ∑ _y : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j}, (1 : ℝ) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [cubeLabels_dl]
        split_ifs <;> simp
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- The single-cube labels of the aligned cube `c`: the label containing the block `c`. -/
theorem block_mem_cubeLabel {j : ℕ} (c : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j
      Set.univ) :
    ∃ y : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j}, c ∈ blocksOf m₀ j Set.univ
      ((cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j).ysite y) := by
  refine ⟨⟨box c.1 (L * cellSide L m₀ m₁ j), mem_cubeFamily.2 ⟨c.1, c.2.1, rfl⟩⟩, ?_⟩
  rw [mem_blocksOf]
  exact box_mono c.1 (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L)))

theorem cubeFamily_nonempty {j : ℕ} :
    Nonempty {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) j} := by
  refine ⟨⟨box 0 (L * cellSide L m₀ m₁ j), mem_cubeFamily.2 ⟨0, fun μ => ?_, rfl⟩⟩⟩
  simp

end Labels

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **`blockMark_fields` with the single-cube labels**: the hypothesis `dl y = 0` and the block
membership are discharged by `cubeLabels`. -/
theorem blockMark_fields_cubeLabels (hp : 0 < S.p₁) (u : S.U) (a : Fin N) (κG : ℝ) :
    ∃ y : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1)},
      Measurable (blockMark S m₀ hp u a) ∧
      DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ ((cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1)).ysite y))
        (blockMark S m₀ hp u a) ∧
      0 < S.p₁ ∧
      (∀ Φ, ‖blockMark S m₀ hp u a Φ‖ ≤
        S.p₁ * Real.exp (-κG * (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1)).dl y)) ∧
      ∫ Φ, blockMark S m₀ hp u a Φ ∂Measure.pi (S.blockSplit m₀ hp).μ = 0 := by
  obtain ⟨y, hy⟩ := block_mem_cubeLabel (m₀ := m₀) (m₁ := m₁) (K := k + 1) (d := d) (L := L)
    (N₁ := N₁) (S.cellOf m₀ u)
  exact ⟨y, blockMark_fields S m₀ hp u a (cubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (m₀ := m₀) (k + 1)) y hy
    (cubeLabels_dl y) κG⟩

end Block

section Witness

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **Non-vacuity at the landed witness step.**  The landed label activity of
`labelAct_of_interaction_expansion_hat_hyps_nonempty` (at `hatWitnessStep`, `d = L = 3`, `N₁ = 9`,
`k = 1`, `m₀ = 1`) is extended by zero to the sum with the single-cube labels; the label sum is
unchanged and the extended label type is nonempty. -/
theorem labelAct_extendZero_cubeLabels_witness (N : ℕ) (hN0 : 0 < N) :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 9 m₁ 1 N (rhoSep m₁)) (hp : 0 < S.p₁) (Lb : Type)
      (_ : Fintype Lb) (Lab : CubeLabels (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1) 1
        (1 + 1) Set.univ Lb) (εH κH κ0 Kc : ℝ)
      (A : LabelAct Lab (S.blockSplit 1 hp).Ωb εH κH κ0 Kc)
      (B : LabelAct (Lab.sum (cubeLabels (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1)
          (m₀ := 1) (1 + 1))) (S.blockSplit 1 hp).Ωb εH κH κ0
        (Kc + (Nat.card {Z // Z ∈ cubeFamily (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁)
          (K := 1 + 1) (m₀ := 1) (1 + 1)} : ℝ))),
      (∀ Φ, ∑ y, B.H y Φ = ∑ y, A.H y Φ) ∧
      Nonempty (Lb ⊕ {Z // Z ∈ cubeFamily (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁)
          (K := 1 + 1) (m₀ := 1) (1 + 1)}) := by
  obtain ⟨m₁, c, BG, κ, eps, c₂, BG₂, κdec, κ0, κ', Kc', εU, cψ, S, -, cβ, cν, hp, Θ₀, -, -, -,
    -, -, -, -, Lb, hfin, Lab, A, -, -, hpos, -, -⟩ :=
    labelAct_of_interaction_expansion_hat_hyps_nonempty N hN0
  refine ⟨m₁, S, hp, Lb, hfin, Lab, _, _, κ0, Kc', A 0, (A 0).extendZero _ hpos.le _
    (cubeLabels_entropy_card κ0), fun Φ => (A 0).extendZero_total _ hpos.le _
    (cubeLabels_entropy_card κ0) Φ, ?_⟩
  obtain ⟨z⟩ := cubeFamily_nonempty (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1)
    (m₀ := 1) (j := 1 + 1)
  exact ⟨Sum.inr z⟩

end Witness

end Balaban.Fluctuation
