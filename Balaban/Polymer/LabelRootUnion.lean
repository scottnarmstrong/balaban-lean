/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LabelExtend
public import Balaban.Fluctuation.HatLabelsGeom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One label system for the marks of all roots

The bridge domains of the roots `z` (`bridgeFamily`) are combined into the label system on the
sigma type of all pairs `(z, Y′)` with `Y′` a bridge domain of `z` (`rootUnionLabels`): the site set
of `(z, Y′)` is `Y′`, its size is `d^cov_K(Y′)`.

* `CubeLabels.sigma`: a finite family of label systems gives one on the sigma type.
* `rootUnion_entropy_sum`: the entropy sum of the union is the sum over the roots of the entropy
  sums of their bridge labels.
* `rootUnion_entropy`: for `κ₀ ≥ a_ent + 2` the entropy sum at every block is at most
  `K_all = c₁ · (L^(m₀+m₁))^d · K₀(κ₀ - 1)`.  The proof: a domain `Y′` is a bridge domain of
  `z` only if it contains the root cube of `z`; the number of such `z` is at most the number of
  cubes of `Y′` (`c₁(1 + d^cov(Y′))`) times the number of roots over one root cube
  (`card_rootCube_fibre_le`, at most `(L^(m₀+m₁))^d`); then `1 + x ≤ e^x` and the rooted entropy
  bound `entropy_thick` with the rate `κ₀ - 1`.
* `LabelAct.extendRootUnion`: an activity on `Lab` extended by zero to the root-union labels; the
  label sum is unchanged, the identity `hW` transfers, and the bridge labels of each root embed
  with the same site set and size (`rootUnionIncl`).
* `labelAct_extendRootUnion_witness`: non-vacuity at the landed witness step.

The marks family and the `E1MarksC` inhabitant are NOT constructed here.  Everything is
independent of the datum, the chart and the choice of generators.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory
open scoped Classical

section Sigma

variable {d L N₁ m₁ K : ℕ} {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {ι : Type*} {Lb : ι → Type*}

/-- **Sigma of label systems**: the labels `(i, y)` with `y` a label of the `i`-th system. -/
def CubeLabels.sigma (Lab : ∀ i, CubeLabels m₀ j Ω (Lb i)) :
    CubeLabels m₀ j Ω (Σ i, Lb i) where
  ysite y := (Lab y.1).ysite y.2
  dl y := (Lab y.1).dl y.2
  isDj y := (Lab y.1).isDj y.2
  meets y := (Lab y.1).meets y.2
  size y := (Lab y.1).size y.2

@[simp] theorem CubeLabels.sigma_ysite (Lab : ∀ i, CubeLabels m₀ j Ω (Lb i)) (i : ι) (y : Lb i) :
    (CubeLabels.sigma Lab).ysite ⟨i, y⟩ = (Lab i).ysite y := rfl

@[simp] theorem CubeLabels.sigma_dl (Lab : ∀ i, CubeLabels m₀ j Ω (Lb i)) (i : ι) (y : Lb i) :
    (CubeLabels.sigma Lab).dl ⟨i, y⟩ = (Lab i).dl y := rfl

/-- The entropy sum of the sigma system is the sum over `i` of the entropy sums. -/
theorem CubeLabels.sigma_entropy_sum [Fintype ι] [∀ i, Fintype (Lb i)]
    (Lab : ∀ i, CubeLabels m₀ j Ω (Lb i)) (κ0 : ℝ)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) :
    ∑ y : (Σ i, Lb i), (if box b.1 (cellSide L m₀ m₁ j) ⊆ (CubeLabels.sigma Lab).ysite y then
        Real.exp (-κ0 * (CubeLabels.sigma Lab).dl y) else 0) =
      ∑ i, ∑ y : Lb i, (if box b.1 (cellSide L m₀ m₁ j) ⊆ (Lab i).ysite y then
        Real.exp (-κ0 * (Lab i).dl y) else 0) :=
  Fintype.sum_sigma _

end Sigma

section Fibre

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **Roots over one root cube.**  The root cube is `rootCube z`, the cell of side `L^(K+m₀+m₁)`
containing the block of side `L^K` of `z`; at most `(L^(m₀+m₁))^d` roots lie over one cube. -/
theorem card_rootCube_fibre_le
    (c : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :
    (Finset.univ.filter fun z : RootIdx d L N₁ m₁ K => rootCube (m₀ := m₀) z = c).card ≤
      (L ^ (m₀ + m₁)) ^ d := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have hc : 0 < L ^ (m₀ + m₁) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hside : cellSide L m₀ m₁ K = L ^ K * L ^ (m₀ + m₁) := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  calc _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range (L ^ (m₀ + m₁))).card := by
        refine Finset.card_le_card_of_injOn (fun z μ => (z μ).val % L ^ (m₀ + m₁))
          (fun z _ => ?_) (fun z hz z' hz' h => ?_)
        · rw [Finset.mem_coe, Fintype.mem_piFinset]
          exact fun μ => Finset.mem_range.2 (Nat.mod_lt _ hc)
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz hz'
          have hcube : (rootCube (m₀ := m₀) z).1 = (rootCube (m₀ := m₀) z').1 := by
            rw [hz, hz']
          funext μ
          have h1 := congrArg (fun t : CTorus d L N₁ m₁ K => (t μ).val) hcube
          simp only [rootCube, cbase_val, rootSite_val, hside] at h1
          rw [Nat.mul_div_mul_left _ _ hL, Nat.mul_div_mul_left _ _ hL] at h1
          have h1' := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hL hc) h1
          have h2 := congrFun h μ
          simp only at h2
          apply ZMod.val_injective
          rw [← Nat.div_add_mod (z μ).val (L ^ (m₀ + m₁)),
            ← Nat.div_add_mod (z' μ).val (L ^ (m₀ + m₁)), h1', h2]
    _ = (L ^ (m₀ + m₁)) ^ d := by simp [Fintype.card_piFinset]

end Fibre

section Union

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {β : Type*} [Fintype β]

/-- **The labels of all roots**: the pairs `(z, Y′)` with `Y′` a bridge domain of the root `z`. -/
abbrev RootUnionLb (m₀ : ℕ) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) : Type _ :=
  Σ z : RootIdx d L N₁ m₁ K, {Y' // Y' ∈ bridgeFamily m₀ reads dom z}

/-- **The root-union label system**: `ysite (z, Y′) = Y′`, `dl (z, Y′) = d^cov_K(Y′)`. -/
noncomputable def rootUnionLabels (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ
      (RootUnionLb m₀ reads dom) :=
  CubeLabels.sigma fun z => bridgeLabels hN hL reads dom hdom z

/-- The embedding of the bridge labels of one root into the common label type. -/
def rootUnionIncl (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K) :
    {Y' // Y' ∈ bridgeFamily m₀ reads dom z} → RootUnionLb m₀ reads dom :=
  fun y => ⟨z, y⟩

theorem rootUnionIncl_injective (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K) :
    Function.Injective (rootUnionIncl (m₀ := m₀) reads dom z) := fun _ _ h => by
  simpa [rootUnionIncl] using h

theorem rootUnionLabels_ysite (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) :
    (rootUnionLabels hN hL reads dom hdom).ysite (rootUnionIncl reads dom z y) = y.1 := rfl

theorem rootUnionLabels_ysite_bridge (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) :
    (rootUnionLabels hN hL reads dom hdom).ysite (rootUnionIncl reads dom z y) =
      (bridgeLabels hN hL reads dom hdom z).ysite y := rfl

theorem rootUnionLabels_dl_bridge (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    (y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) :
    (rootUnionLabels hN hL reads dom hdom).dl (rootUnionIncl reads dom z y) =
      (bridgeLabels hN hL reads dom hdom z).dl y := rfl

/-- **T2.**  The entropy sum of the root-union labels at a block is the sum over the roots of the
entropy sums of their bridge labels. -/
theorem rootUnion_entropy_sum (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (κ0 : ℝ)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :
    ∑ y : RootUnionLb m₀ reads dom,
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ (rootUnionLabels hN hL reads dom hdom).ysite y then
          Real.exp (-κ0 * (rootUnionLabels hN hL reads dom hdom).dl y) else 0) =
      ∑ z : RootIdx d L N₁ m₁ K, ∑ y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ (bridgeLabels hN hL reads dom hdom z).ysite y then
          Real.exp (-κ0 * (bridgeLabels hN hL reads dom hdom z).dl y) else 0) :=
  CubeLabels.sigma_entropy_sum (fun z => bridgeLabels hN hL reads dom hdom z) κ0 b

/-- The constant `K_all = c₁ · (L^(m₀+m₁))^d · K₀(κ₀ - 1)`. -/
noncomputable def rootUnionK (d L m₀ m₁ : ℕ) (κ0 : ℝ) : ℝ :=
  c1 d L * (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) * K0 d L (κ0 - 1)

/-- The number of roots whose bridge family contains a given domain `Y` (a domain of `𝒟_K`) is at
most the number of cubes of `Y` times the number of roots over one root cube. -/
theorem card_roots_bridgeFamily_le (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (Y : Set (CTorus d L N₁ m₁ K)) :
    (Finset.univ.filter fun z : RootIdx d L N₁ m₁ K => Y ∈ bridgeFamily m₀ reads dom z).card ≤
      (L ^ (m₀ + m₁)) ^ d * (blocksOf m₀ K Set.univ Y).card := by
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun z => rootCube (m₀ := m₀) z)
    (t := blocksOf m₀ K Set.univ Y) (fun z hz => ?_) _ (fun c _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact (bridgeFamily_spec hN hL hdom z hz).2.1
  · exact (Finset.card_le_card (fun z hz => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; exact hz.2)).trans
      (card_rootCube_fibre_le c)

/-- **T3 (weighted roots per block).**  For `κ₀ ≥ a_ent + 2`, every block lies in the labels
`(z, Y′)` of total weight at most `K_all = c₁ (L^(m₀+m₁))^d K₀(κ₀ - 1)`. -/
theorem rootUnion_entropy (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) {κ0 : ℝ} (hκ0 : aEnt d L + 2 ≤ κ0)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :
    ∑ y : RootUnionLb m₀ reads dom,
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ (rootUnionLabels hN hL reads dom hdom).ysite y then
          Real.exp (-κ0 * (rootUnionLabels hN hL reads dom hdom).dl y) else 0) ≤
      rootUnionK d L m₀ m₁ κ0 := by
  rw [rootUnion_entropy_sum]
  set 𝒵 : Finset (Set (CTorus d L N₁ m₁ K)) :=
    Finset.univ.biUnion fun z => bridgeFamily m₀ reads dom z with h𝒵
  have hZdj : ∀ Z ∈ 𝒵, IsDj m₀ K Z := by
    intro Z hZ
    obtain ⟨z, -, hz⟩ := Finset.mem_biUnion.1 hZ
    exact bridgeFamily_isDj hN hL hdom z Z hz
  set f : Set (CTorus d L N₁ m₁ K) → ℝ := fun Z =>
    if box b.1 (cellSide L m₀ m₁ K) ⊆ Z then Real.exp (-κ0 * treeLenCovOne m₀ K Z) else 0
    with hf
  have hf0 : ∀ Z, 0 ≤ f Z := fun Z => by
    simp only [hf]; split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have step1 : ∀ z : RootIdx d L N₁ m₁ K,
      ∑ y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ (bridgeLabels hN hL reads dom hdom z).ysite y then
          Real.exp (-κ0 * (bridgeLabels hN hL reads dom hdom z).dl y) else 0) =
      ∑ Z ∈ 𝒵, if Z ∈ bridgeFamily m₀ reads dom z then f Z else 0 := by
    intro z
    have e1 : ∑ y : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ (bridgeLabels hN hL reads dom hdom z).ysite y then
          Real.exp (-κ0 * (bridgeLabels hN hL reads dom hdom z).dl y) else 0) =
        ∑ Y ∈ bridgeFamily m₀ reads dom z, f Y :=
      Finset.sum_coe_sort (bridgeFamily m₀ reads dom z) f
    rw [e1, Finset.sum_ite_mem 𝒵 (bridgeFamily m₀ reads dom z) f,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem
        (fun z => bridgeFamily m₀ reads dom z) (Finset.mem_univ z))]
  simp_rw [step1]
  rw [Finset.sum_comm]
  have step2 : ∀ Z ∈ 𝒵, ∑ z : RootIdx d L N₁ m₁ K,
      (if Z ∈ bridgeFamily m₀ reads dom z then f Z else 0) ≤
      c1 d L * (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) *
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ Z then
          Real.exp (-(κ0 - 1) * treeLenCovOne m₀ K Z) else 0) := by
    intro Z hZ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hb : box b.1 (cellSide L m₀ m₁ K) ⊆ Z
    · have hc := card_roots_bridgeFamily_le hN hL reads dom hdom Z
      have hbl := card_blocksOf_le hN le_rfl (hZdj Z hZ)
      have ht := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Z
      have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
      have hcard : ((Finset.univ.filter fun z : RootIdx d L N₁ m₁ K =>
          Z ∈ bridgeFamily m₀ reads dom z).card : ℝ) ≤
          (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) * (c1 d L * (1 + treeLenCovOne m₀ K Z)) := by
        calc _ ≤ (((L ^ (m₀ + m₁)) ^ d * (blocksOf m₀ K Set.univ Z).card : ℕ) : ℝ) :=
              by exact_mod_cast hc
          _ ≤ _ := by
              push_cast
              exact mul_le_mul_of_nonneg_left hbl (by positivity)
      have hexp : (1 + treeLenCovOne m₀ K Z) * Real.exp (-κ0 * treeLenCovOne m₀ K Z) ≤
          Real.exp (-(κ0 - 1) * treeLenCovOne m₀ K Z) := by
        have h1 := Real.add_one_le_exp (treeLenCovOne m₀ K Z)
        have h2 : Real.exp (-(κ0 - 1) * treeLenCovOne m₀ K Z) =
            Real.exp (treeLenCovOne m₀ K Z) * Real.exp (-κ0 * treeLenCovOne m₀ K Z) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h2]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      simp only [hf, hb, ite_true]
      calc _ ≤ (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) * (c1 d L * (1 + treeLenCovOne m₀ K Z)) *
            Real.exp (-κ0 * treeLenCovOne m₀ K Z) :=
            mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ = c1 d L * (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) *
            ((1 + treeLenCovOne m₀ K Z) * Real.exp (-κ0 * treeLenCovOne m₀ K Z)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
    · simp [hf, hb]
  calc _ ≤ ∑ Z ∈ 𝒵, c1 d L * (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) *
        (if box b.1 (cellSide L m₀ m₁ K) ⊆ Z then
          Real.exp (-(κ0 - 1) * treeLenCovOne m₀ K Z) else 0) :=
        Finset.sum_le_sum step2
    _ = c1 d L * (((L ^ (m₀ + m₁)) ^ d : ℕ) : ℝ) *
        ∑ Z : {Z // Z ∈ 𝒵}, (if box b.1 (cellSide L m₀ m₁ K) ⊆ Z.1 then
          Real.exp (-(κ0 - 1) * treeLenCovOne m₀ K Z.1) else 0) := by
        rw [← Finset.mul_sum]
        congr 1
        exact (Finset.sum_coe_sort 𝒵 (fun Z => if box b.1 (cellSide L m₀ m₁ K) ⊆ Z then
          Real.exp (-(κ0 - 1) * treeLenCovOne m₀ K Z) else 0)).symm
    _ ≤ _ := by
        have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
        exact mul_le_mul_of_nonneg_left (entropy_thick hN le_rfl 𝒵 hZdj (by linarith) b)
          (by positivity)

end Union

section Act

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {β : Type*} [Fintype β]
  {Lb : Type*} [Fintype Lb] {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    m₀ K Set.univ Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

/-- **T4.  The activity extended by zero to the labels of all roots.**  The entropy constant is
`Kc + K_all`. -/
noncomputable def LabelAct.extendRootUnion (A : LabelAct Lab Ωb εH κH κ0 Kc)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (hεH : 0 ≤ εH) (hκ0 : aEnt d L + 2 ≤ κ0) :
    LabelAct (Lab.sum (rootUnionLabels hN hL reads dom hdom)) Ωb εH κH κ0
      (Kc + rootUnionK d L m₀ m₁ κ0) :=
  A.extendZero _ hεH _ (fun b => rootUnion_entropy hN hL reads dom hdom hκ0 b)

/-- The label sum is unchanged by the extension to the labels of all roots. -/
theorem LabelAct.extendRootUnion_total (A : LabelAct Lab Ωb εH κH κ0 Kc)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (hεH : 0 ≤ εH) (hκ0 : aEnt d L + 2 ≤ κ0)
    (Φ : ∀ b, Ωb b) :
    ∑ y, (A.extendRootUnion hN hL reads dom hdom hεH hκ0).H y Φ = ∑ y, A.H y Φ :=
  LabelAct.extendZero_total _ _ _ _ _ Φ

/-- **The exact shape of `InterpMarks.hW`** transfers to the extension by zero to the labels of
all roots. -/
theorem LabelAct.extendRootUnion_hW_interp {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (hεH : 0 ≤ εH) (hκ0 : aEnt d L + 2 ≤ κ0)
    {W : ℝ → X → ℂ} {restr : X → ∀ b, Ωb b}
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (A (s : ℂ)).H y (restr x)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, ((A (s : ℂ)).extendRootUnion hN hL reads dom hdom hεH hκ0).H y (restr x) :=
  LabelAct.extendZero_hW_interp A _ hεH _ _ hW

omit [Fintype Lb] [∀ b, MeasurableSpace (Ωb b)] in
/-- **The marks of one root in the common label system.**  A family of marks `G i` whose label
`y0 i` is a bridge label of the root `z`, with the `dep` and `bound` fields for the labels
`bridgeLabels … z`, satisfies the same fields for the labels `Sum.inr (z, y0 i)` of the common
label system `Lab.sum (rootUnionLabels …)`. -/
theorem rootUnion_marks_fields (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    {ι : Type*} (y0 : ι → {Y' // Y' ∈ bridgeFamily m₀ reads dom z}) (F0 : ι → ℝ) (κG : ℝ)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hdep : ∀ i u, DepOn (Ω := Ωb) (blocksOf m₀ K Set.univ
      ((bridgeLabels hN hL reads dom hdom z).ysite (y0 i))) (G i u))
    (hbound : ∀ i u Φ, ‖G i u Φ‖ ≤
      F0 i * Real.exp (-κG * (bridgeLabels hN hL reads dom hdom z).dl (y0 i))) :
    (∀ i u, DepOn (Ω := Ωb) (blocksOf m₀ K Set.univ
      ((Lab.sum (rootUnionLabels hN hL reads dom hdom)).ysite
        (Sum.inr (rootUnionIncl reads dom z (y0 i))))) (G i u)) ∧
    (∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG *
      (Lab.sum (rootUnionLabels hN hL reads dom hdom)).dl
        (Sum.inr (rootUnionIncl reads dom z (y0 i))))) :=
  ⟨hdep, hbound⟩

end Act

section Injective

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **T5.**  If `m₀ = m₁ = 0` (cells of the size of the blocks), the root cube determines the
root.  In general the fibre has at most `(L^(m₀+m₁))^d` roots (`card_rootCube_fibre_le`). -/
theorem rootCube_injective_of_zero (h0 : m₀ = 0) (h1 : m₁ = 0) :
    Function.Injective (fun z : RootIdx d L N₁ m₁ K => rootCube (m₀ := m₀) z) := by
  intro z z' h
  have hc := card_rootCube_fibre_le (m₀ := m₀) (rootCube (m₀ := m₀) z')
  subst h0 h1
  simp only [add_zero, pow_zero, one_pow] at hc
  have := Finset.card_le_one.1 hc z (by simpa using h) z' (by simp)
  exact this

end Injective

section Witness

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **Non-vacuity at the landed witness step.**  At the step of
`labelAct_of_interaction_expansion_hat_hyps_nonempty` (`d = L = 3`, `N₁ = 9`, `K = 2`, `m₀ = 1`),
with one block whose single domain is the cube of the root `0` and which reads every site, the
label activity (with `κ₀` raised to at least `a_ent + 2`) is extended by zero to the labels of all
roots; the label sum is unchanged and the extended label type is nonempty. -/
theorem labelAct_extendRootUnion_witness (N : ℕ) (hN0 : 0 < N) :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 9 m₁ 1 N (rhoSep m₁)) (hp : 0 < S.p₁) (Lb : Type)
      (_ : Fintype Lb) (Lab : CubeLabels (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1) 1
        (1 + 1) Set.univ Lb) (εH κH κ0 Kc : ℝ)
      (reads : Unit → Set (CTorus 3 3 9 m₁ (1 + 1)))
      (dom : Unit → Finset (Set (CTorus 3 3 9 m₁ (1 + 1))))
      (hdom : ∀ b, ∀ Y ∈ dom b, IsDj 1 (1 + 1) Y)
      (A : LabelAct Lab (S.blockSplit 1 hp).Ωb εH κH κ0 Kc)
      (B : LabelAct (Lab.sum (rootUnionLabels (by norm_num : 3 ^ 1 ∣ 9) (by norm_num : 2 ≤ 3)
          reads dom hdom)) (S.blockSplit 1 hp).Ωb εH κH κ0
        (Kc + rootUnionK 3 3 1 m₁ κ0)),
      aEnt 3 3 + 2 ≤ κ0 ∧ (∀ Φ, ∑ y, B.H y Φ = ∑ y, A.H y Φ) ∧
      Nonempty (Lb ⊕ RootUnionLb 1 reads dom) := by
  obtain ⟨m₁, c, BG, κ, eps, c₂, BG₂, κdec, κ0, κ', Kc', εU, cψ, S, -, cβ, cν, hp, Θ₀, -, -, -,
    -, -, -, -, Lb, hfin, Lab, A, -, -, hpos, -, -⟩ :=
    labelAct_of_interaction_expansion_hat_hyps_nonempty N hN0
  have hN : 3 ^ 1 ∣ 9 := by norm_num
  have hL : 2 ≤ 3 := by norm_num
  set z0 : RootIdx 3 3 9 m₁ (1 + 1) := 0 with hz0
  set Y0 : Set (CTorus 3 3 9 m₁ (1 + 1)) :=
    box (rootCube (m₀ := 1) z0).1 (3 * cellSide 3 1 m₁ (1 + 1)) with hY0
  have hdom : ∀ b, ∀ Y ∈ (fun _ : Unit => ({Y0} : Finset _)) b, IsDj 1 (1 + 1) Y := by
    intro b Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact isDj_box (rootCube (m₀ := 1) z0).2.1
  have hmem : rootSite z0 ∈ Y0 :=
    box_mono _ (Nat.le_mul_of_pos_left _ (by norm_num))
      (rootSite_mem_box_rootCube (m₀ := 1) z0)
  have hfb : rootSite z0 ∈ fineBlock z0 := blockIndex_rootSite z0
  have hκ : aEnt 3 3 + 2 ≤ max κ0 (aEnt 3 3 + 2) := le_max_right _ _
  refine ⟨m₁, S, hp, Lb, hfin, Lab, _, _, max κ0 (aEnt 3 3 + 2), Kc', (fun _ => Set.univ),
    (fun _ => {Y0}), hdom, (A 0).mono hpos.le le_rfl le_rfl (le_max_left _ _) le_rfl,
    ((A 0).mono hpos.le le_rfl le_rfl (le_max_left _ _) le_rfl).extendRootUnion hN hL _ _ hdom
      hpos.le hκ, hκ, fun Φ => LabelAct.extendRootUnion_total _ hN hL _ _ hdom hpos.le hκ Φ, ?_⟩
  refine ⟨Sum.inr ⟨z0, ⟨bridge 1 z0 Y0, ?_⟩⟩⟩
  rw [mem_bridgeFamily]
  exact ⟨(), Y0, Finset.mem_singleton_self _, ⟨rootSite z0, Set.mem_univ _, hfb⟩,
    ⟨rootSite z0, Or.inl hmem, hfb⟩, rfl⟩

end Witness

end Balaban.Fluctuation
