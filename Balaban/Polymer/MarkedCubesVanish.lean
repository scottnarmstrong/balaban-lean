/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 3.4: vanishing when `d_Ω(S) = +∞` (FLUCTUATION.md §3.4)

`P(S) = 0` and `G*(Y₀, S) = 0` for every `S` with `d_Ω(S) = +∞` (that is, `Ŷ(S)` disconnected or
of infinite modular covering size).  The cluster terms only see sets `S` which are unions of
connected families of terms, each of which comes from a label and so has `d_Ω < ∞`; `d_Ω < ∞`
is stable under unions of overlapping sets (`G3_dOmega`).
-/

@[expose] public section

namespace Balaban.Polymer

open MeasureTheory

section Generic

open scoped Classical

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {B : Type*} [Fintype B] (supp : P → Finset B)

omit [Fintype B] in
/-- The cluster terms of order `n + 1` with union `Y` vanish if every connected cluster with
union `Y` contains a polymer with vanishing activity. -/
theorem Pterm_eq_zero_of_forall (K : P → ℂ) (Y : Finset B) (n : ℕ)
    (h : ∀ X : Fin (n + 1) → P, unionOf supp X = Y → (clusterGraph inc X).Connected →
      ∏ i, K (X i) = 0) : Pterm inc supp K Y n = 0 := by
  unfold Pterm
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero (fun X hX => ?_)
  rw [Finset.mem_filter] at hX
  by_cases hc : (clusterGraph inc X).Connected
  · rw [h X hX.2 hc, mul_zero]
  · have h0 := aaw_eq_zero_of_not_connected inc X hc
    have : ‖(clusterUrsell inc X Finset.univ : ℂ)‖ = 0 := by
      rw [norm_ursell_eq]; exact h0
    rw [norm_eq_zero.mp this, zero_mul]

omit [Fintype B] in
theorem PY_eq_zero_of_forall (K : P → ℂ) (Y : Finset B)
    (h : ∀ (n : ℕ) (X : Fin (n + 1) → P), unionOf supp X = Y →
      (clusterGraph inc X).Connected → ∏ i, K (X i) = 0) : PY inc supp K Y = 0 := by
  unfold PY
  simp [Pterm_eq_zero_of_forall inc supp K Y _ (h _)]

end Generic

end Balaban.Polymer

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Finite

/-- `d_Ω(S) < ∞` for a set of blocks. -/
def FinSet (m₀ j : ℕ) (Ω : Set (CTorus d L N₁ m₁ K)) (S : Finset 𝔅) : Prop :=
  dOmega m₀ j Ω (sitesOf S) ≠ ⊤

theorem finSet_union {X Y : Finset 𝔅} (hXY : ¬ Disjoint X Y) (hX : FinSet m₀ j Ω X)
    (hY : FinSet m₀ j Ω Y) : FinSet m₀ j Ω (X ∪ Y) := by
  obtain ⟨b, hbX, hbY⟩ := Finset.not_disjoint_iff.1 hXY
  have hne : (sitesOf X ∩ sitesOf Y).Nonempty := by
    have ha0 := cellSide_pos (L := L) m₀ m₁ j
    exact ⟨b.1, mem_sitesOf.2 ⟨b, hbX, mem_box_self _ ha0⟩, mem_sitesOf.2 ⟨b, hbY, mem_box_self _ ha0⟩⟩
  have h3 := G3_dOmega (m₀ := m₀) (j := j) (sitesOf_subset X) hne (S₂ := sitesOf Y)
  rw [← sitesOf_union] at h3
  have hfinR : dOmega m₀ j Ω (sitesOf X) + dOmega m₀ j Ω (sitesOf Y) + ENNReal.ofReal (cG d L) ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hX, hY⟩, ENNReal.ofReal_ne_top⟩
  exact ne_top_of_le_ne_top hfinR h3

omit [NeZero N₁] [NeZero L] in
/-- The finiteness indicator `0` / `1`. -/
noncomputable def finInd (m₀ j : ℕ) (Ω : Set (CTorus d L N₁ m₁ K)) (S : Finset 𝔅) : ℝ :=
  open Classical in if FinSet m₀ j Ω S then 0 else 1

theorem finInd_union_le (X Y : Finset 𝔅) (hXY : ¬ Disjoint X Y) :
    finInd m₀ j Ω (X ∪ Y) ≤ finInd m₀ j Ω X + finInd m₀ j Ω Y + 0 := by
  classical
  unfold finInd
  by_cases hX : FinSet m₀ j Ω X
  · by_cases hY : FinSet m₀ j Ω Y
    · simp [hX, hY, finSet_union hXY hX hY]
    · simp [hX, hY]; split_ifs <;> norm_num
  · simp [hX]; split_ifs <;> norm_num

omit [NeZero N₁] [NeZero L] in
theorem finInd_nonneg (S : Finset 𝔅) : 0 ≤ finInd m₀ j Ω S := by
  unfold finInd; split_ifs <;> norm_num

omit [NeZero N₁] [NeZero L] in
theorem finSet_of_finInd_le_zero {S : Finset 𝔅} (h : finInd m₀ j Ω S ≤ 0) : FinSet m₀ j Ω S := by
  classical
  by_contra hS
  simp [finInd, hS] at h
  norm_num at h

/-- A connected family of terms with finite `d_Ω` has finite `d_Ω` of its union. -/
theorem finSet_unionCs (C : Finset (NePoly 𝔅))
    (hC : ConnSet (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) (h : ∀ t ∈ C, FinSet m₀ j Ω t.1) :
    FinSet m₀ j Ω (unionCs (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) := by
  classical
  obtain ⟨hne, hreach⟩ := hC
  let Gc : SimpleGraph (NePoly 𝔅) := SimpleGraph.fromRel (Contact (Subtype.val : NePoly 𝔅 → Finset 𝔅))
  have hconn : (Gc.induce (C : Set (NePoly 𝔅))).Connected := by
    obtain ⟨x₀, hx₀⟩ := hne
    have : Nonempty (C : Set (NePoly 𝔅)) := ⟨⟨x₀, hx₀⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have key : ∀ y, Relation.ReflTransGen
        (fun x y => x ∈ C ∧ y ∈ C ∧ Contact (Subtype.val : NePoly 𝔅 → Finset 𝔅) x y) a y →
        ∀ hy : y ∈ C, (Gc.induce (C : Set (NePoly 𝔅))).Reachable ⟨a, ha⟩ ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail u v _ huv ih =>
        intro hv
        have hu : u ∈ C := huv.1
        refine (ih hu).trans ?_
        by_cases heq : u = v
        · subst heq; exact SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable (show Gc.Adj u v from by
            rw [SimpleGraph.fromRel_adj]; exact ⟨heq, Or.inl huv.2.2⟩)
    exact key b (hreach a ha b hb) hb
  have := phi_union_le (fun S : Finset 𝔅 => finInd m₀ j Ω S) 0
    (fun X Y _ _ h => finInd_union_le X Y h) Gc (fun t => t.1) (fun t => t.2)
    (fun i j hij => by
      rw [SimpleGraph.fromRel_adj] at hij
      rcases hij.2 with h | h
      · exact h
      · exact fun hd => h hd.symm) (C.card - 1) C
    (Nat.sub_add_cancel (Finset.card_pos.2 hne)).symm hconn
  have hz : ∑ t ∈ C, finInd m₀ j Ω t.1 = 0 :=
    Finset.sum_eq_zero (fun t ht => by simp [finInd, h t ht])
  rw [hz, zero_mul, add_zero] at this
  refine finSet_of_finInd_le_zero (le_trans (le_of_eq ?_) this)
  congr 1
  ext x; simp [unionCs]

/-- A connected cluster of finite terms has finite union. -/
theorem finSet_unionOf {n : ℕ} (X : Fin (n + 1) → NePoly 𝔅)
    (hc : (clusterGraph (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) X).Connected)
    (h : ∀ i, FinSet m₀ j Ω (X i).1) :
    FinSet m₀ j Ω (unionOf (Subtype.val : NePoly 𝔅 → Finset 𝔅) X) := by
  classical
  have key := phi_union_le (fun S : Finset 𝔅 => finInd m₀ j Ω S) 0
    (fun X Y _ _ h => finInd_union_le X Y h)
    (clusterGraph (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) X) (fun i => (X i).1)
    (fun i => (X i).2) (fun i j hij => by
      have := ((clusterGraph_adj _ X i j).1 hij).2
      exact (lnk_shareBlock _ _ _).1 this) n Finset.univ (by simp)
    (by
      rw [Finset.coe_univ]
      exact (SimpleGraph.induceUnivIso _).connected_iff.2 hc)
  have hz : ∑ i ∈ Finset.univ, finInd m₀ j Ω (X i).1 = 0 :=
    Finset.sum_eq_zero (fun i _ => by simp [finInd, h i])
  rw [hz, zero_mul, add_zero] at key
  refine finSet_of_finInd_le_zero (le_trans (le_of_eq ?_) key)
  congr 1
  ext x; simp [unionOf]

theorem finSet_label {Lb : Type*} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) (y : Lb) :
    FinSet m₀ j Ω (blocksOf m₀ j Ω (Lab.ysite y)) := by
  classical
  have hs := sitesOf_blocksOf hN hj hΩ (Lab.isDj y).2.1
  have hle : dOmega m₀ j Ω (sitesOf (blocksOf m₀ j Ω (Lab.ysite y))) ≤
      ENNReal.ofReal (Lab.dl y) := by
    rw [hs]
    rcases Lab.size y with h | ⟨hm, h⟩
    · rw [h]; exact G4_dOmega_le (Lab.isDj y) (Lab.meets y)
    · rw [h]; exact G4_dOmega_le_mod hm (Lab.meets y)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end Finite

section Vanishing

variable {Lb : Type*} [Fintype Lb]

theorem mayerK_eq_zero_of_not_finSet {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b))
    (H : NePoly 𝔅 → (∀ b, Ωb b) → ℂ) (hH : ∀ t : NePoly 𝔅, FinSet m₀ j Ω t.1 ∨ H t = 0)
    (Z : NePoly 𝔅) (hZ : ¬ FinSet m₀ j Ω Z.1) :
    mayerK μ Subtype.val H Z = 0 := by
  classical
  unfold mayerK
  have : mayerAct (Subtype.val : NePoly 𝔅 → Finset 𝔅) H Z = fun _ => 0 := by
    funext Φ
    unfold mayerAct polyAct
    refine Finset.sum_eq_zero (fun C hC => ?_)
    obtain ⟨hconn, -, hun⟩ := mem_Cfam.1 hC
    by_contra hne
    apply hZ
    rw [← hun]
    refine finSet_unionCs C hconn (fun t ht => ?_)
    rcases hH t with h | h
    · exact h
    · exact absurd (Finset.prod_eq_zero ht (by simp [h])) hne
  rw [this]
  simp

theorem presum_finSet {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (Lab : CubeLabels m₀ j Ω Lb) (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (hΩ : IsPiUnion m₀ j Ω) (H : Lb → (∀ b, Ωb b) → ℂ) (t : NePoly 𝔅) :
    FinSet m₀ j Ω t.1 ∨ presum Lab H t = 0 := by
  classical
  by_cases hy : ∃ y, blocksOf m₀ j Ω (Lab.ysite y) = t.1
  · obtain ⟨y, hy⟩ := hy
    exact Or.inl (hy ▸ finSet_label hN hj hΩ Lab y)
  · refine Or.inr (funext fun Φ => ?_)
    unfold presum
    refine Finset.sum_eq_zero (fun y hy' => ?_)
    exact absurd ⟨y, (Finset.mem_filter.1 hy').2⟩ hy

/-- **`P(S) = 0` when `d_Ω(S) = +∞`.** -/
theorem Pst_eq_zero_of_dOmega_top {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) (H : Lb → (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hS : dOmega m₀ j Ω (sitesOf S) = ⊤) : Pst μ Lab H S = 0 := by
  classical
  unfold Pst
  refine PY_eq_zero_of_forall _ _ _ S (fun n X hXS hconn => ?_)
  by_contra hne
  apply (show ¬ FinSet m₀ j Ω S from fun h => h hS)
  rw [← hXS]
  refine finSet_unionOf X hconn (fun i => ?_)
  by_contra hi
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
    (mayerK_eq_zero_of_not_finSet μ (presum Lab H) (presum_finSet Lab hN hj hΩ H) (X i) hi))

/-- **`G*(Y₀, S) = 0` when `d_Ω(S) = +∞`.** -/
theorem Gst_eq_zero_of_dOmega_top {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    (Lab : CubeLabels m₀ j Ω Lb) (H : Lb → (∀ b, Ωb b) → ℂ) (y0 : Lb)
    (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hS : dOmega m₀ j Ω (sitesOf S) = ⊤) :
    Gst μ Lab H (blocksOf m₀ j Ω (Lab.ysite y0)) G S = 0 := by
  classical
  unfold Gst
  have hF : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark (blocksOf m₀ j Ω (Lab.ysite y0)) G)) S =
      fun _ => 0 := by
    funext l
    unfold Ff
    refine PY_eq_zero_of_forall _ _ _ S (fun n X hXS hconn => ?_)
    by_contra hne
    apply (show ¬ FinSet m₀ j Ω S from fun h => h hS)
    rw [← hXS]
    refine finSet_unionOf X hconn (fun i => ?_)
    by_contra hi
    refine hne (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    unfold marksK
    refine mayerK_eq_zero_of_not_finSet μ _ (fun t => ?_) (X i) hi
    by_cases ht : t.1 = blocksOf m₀ j Ω (Lab.ysite y0)
    · exact Or.inl (ht ▸ finSet_label hN hj hΩ Lab y0)
    · rcases presum_finSet Lab hN hj hΩ H t with h | h
      · exact Or.inl h
      · refine Or.inr (funext fun Φ => ?_)
        simp [Hlam, h, gMark, ht]
  rw [hF]
  simp [D1]

end Vanishing

end Balaban.Fluctuation
