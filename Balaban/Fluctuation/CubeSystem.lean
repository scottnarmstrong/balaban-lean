/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeMod
public import Balaban.Fluctuation.ClusterUnion
public import Balaban.Polymer.Decomposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cube system of Theorem 3.4 (FLUCTUATION.md §3.4)

The blocks are the `π_j`-cubes of `Ω` (`CubeB`), a polymer is a nonempty set of blocks, with the
size `d_Ω` of Definition 1.1 on the union of its cubes.  The polymer expansion works with real
sizes on *all* nonempty sets of blocks, while `d_Ω(S) = +∞` when `Ŷ(S)` is not connected; the
size `dExt` replaces `+∞` by the constant `Mbig = |sites|² + 1`, which exceeds every finite value
of `d_Ω` (`dOmega_toReal_le`).  The properties (G1), (G2), (G3) of Lemma 1.2 hold for `dExt`
(`card_le_dExt`, `sum_exp_dExt_le`, `dExt_union_le`, `dExt_union_cluster`), with the constants
`c1`, `cG`, and `K0 + 1` for the entropy sum (the extra `1` bounds the contribution of the sets
of size `Mbig`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (m₀ j : ℕ) (Ω : Set (CTorus d L N₁ m₁ K))

/-- The blocks: the `π_j`-cubes (aligned bases of cells) contained in `Ω`. -/
abbrev CubeB := {b : CTorus d L N₁ m₁ K //
  Aligned (cellSide L m₀ m₁ j) b ∧ box b (cellSide L m₀ m₁ j) ⊆ Ω}

noncomputable instance : Fintype (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) := by
  classical exact Subtype.fintype _

variable {m₀ j Ω}

/-- The sites of a set of blocks. -/
def sitesOf (S : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    Set (CTorus d L N₁ m₁ K) :=
  ⋃ b ∈ S, box b.1 (cellSide L m₀ m₁ j)

omit [NeZero N₁] [NeZero L] in
theorem mem_sitesOf {S : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)}
    {z : CTorus d L N₁ m₁ K} : z ∈ sitesOf S ↔ ∃ b ∈ S, z ∈ box b.1 (cellSide L m₀ m₁ j) := by
  simp [sitesOf]

omit [NeZero N₁] [NeZero L] in
theorem sitesOf_union [DecidableEq (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)]
    (X Y : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    sitesOf (X ∪ Y) = sitesOf X ∪ sitesOf Y := by
  ext z
  simp only [mem_sitesOf, Set.mem_union, Finset.mem_union]
  constructor
  · rintro ⟨b, hb | hb, hz⟩
    · exact Or.inl ⟨b, hb, hz⟩
    · exact Or.inr ⟨b, hb, hz⟩
  · rintro (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩)
    · exact ⟨b, Or.inl hb, hz⟩
    · exact ⟨b, Or.inr hb, hz⟩

omit [NeZero N₁] [NeZero L] in
theorem sitesOf_subset (S : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    sitesOf S ⊆ Ω := by
  intro z hz
  obtain ⟨b, -, hzb⟩ := mem_sitesOf.1 hz
  exact b.2.2 hzb

omit [NeZero N₁] [NeZero L] in
theorem isPiUnion_sitesOf (S : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    IsPiUnion m₀ j (sitesOf S) := by
  intro z hz
  obtain ⟨b, hb, hzb⟩ := mem_sitesOf.1 hz
  exact ⟨b.1, b.2.1, hzb, fun y hy => mem_sitesOf.2 ⟨b, hb, hy⟩⟩

theorem sitesOf_injective (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) :
    Function.Injective
      (sitesOf : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) → _) := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have key : ∀ (X Y : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)),
      sitesOf X ⊆ sitesOf Y → X ⊆ Y := by
    intro X Y h b hb
    have hbs : b.1 ∈ sitesOf Y := h (mem_sitesOf.2 ⟨b, hb, mem_box_self _ ha0⟩)
    obtain ⟨b', hb', hmem⟩ := mem_sitesOf.1 hbs
    have e1 := cbase_eq_of_mem_box hdvd b'.2.1 hmem
    have e2 := cbase_eq_of_mem_box hdvd b.2.1 (mem_box_self b.1 ha0)
    have : b = b' := Subtype.ext (e2.symm.trans e1)
    rwa [this]
  intro X Y h
  exact Finset.Subset.antisymm (key X Y h.le) (key Y X h.ge)

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- The constant replacing `+∞` in `d_Ω`: it exceeds every finite value of `d_Ω`. -/
noncomputable def Mbig (d L N₁ m₁ K : ℕ) [NeZero N₁] [NeZero L] : ℝ :=
  (Fintype.card (CTorus d L N₁ m₁ K) : ℝ) ^ 2 + 1

/-- **The real size `d_Ω` on sets of blocks**: `d_Ω(sitesOf S)` if finite, `Mbig` otherwise. -/
noncomputable def dExt (S : Finset 𝔅) : ℝ :=
  open Classical in
  if dOmega m₀ j Ω (sitesOf S) = ⊤ then Mbig d L N₁ m₁ K else (dOmega m₀ j Ω (sitesOf S)).toReal

theorem dOmega_exists_tuple {S : Set (CTorus d L N₁ m₁ K)} (h : dOmega m₀ j Ω S ≠ ⊤) :
    ∃ 𝒦 W E, ModAdmissible m₀ j Ω (Yhat Ω S) 𝒦 W E ∧
      bondCost (scaleW L m₀ m₁ j) E = (dOmega m₀ j Ω S).toReal := by
  classical
  have hdE : dOmega m₀ j Ω S = dcovModE m₀ j Ω (Yhat Ω S) := by
    unfold dOmega at h ⊢
    by_cases hcon : SiteConnected (Yhat Ω S)
    · simp [hcon]
    · simp [hcon] at h
  rw [hdE] at h ⊢
  obtain ⟨𝒦, W, E, hE, he⟩ := exists_admissible_eq_dcovModE (exists_admissible_of_ne_top h)
  refine ⟨𝒦, W, E, hE, ?_⟩
  rw [← he, ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E)]

theorem dOmega_toReal_le {S : Set (CTorus d L N₁ m₁ K)} (h : dOmega m₀ j Ω S ≠ ⊤) :
    (dOmega m₀ j Ω S).toReal ≤ (Fintype.card (CTorus d L N₁ m₁ K) : ℝ) ^ 2 := by
  classical
  obtain ⟨𝒦, W, E, -, hE⟩ := dOmega_exists_tuple (m₀ := m₀) (j := j) h
  rw [← hE]
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : ((L : ℝ) ^ (m₀ + m₁ + j))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  calc bondCost (scaleW L m₀ m₁ j) E ≤ ∑ _p ∈ E, (1 : ℝ) := Finset.sum_le_sum fun p _ => h1
    _ = E.card := by simp
    _ ≤ (Fintype.card (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K) : ℝ) := by
        exact_mod_cast Finset.card_le_univ E
    _ = _ := by rw [Fintype.card_prod]; push_cast; ring

theorem Mbig_pos : 0 < Mbig d L N₁ m₁ K := by unfold Mbig; positivity

theorem dExt_nonneg (S : Finset 𝔅) : 0 ≤ dExt S := by
  unfold dExt; split_ifs
  · exact Mbig_pos.le
  · exact ENNReal.toReal_nonneg

theorem dExt_le_Mbig (S : Finset 𝔅) : dExt S ≤ Mbig d L N₁ m₁ K := by
  unfold dExt; split_ifs with h
  · exact le_rfl
  · exact (dOmega_toReal_le h).trans (by unfold Mbig; linarith)

theorem one_le_c1 (d L : ℕ) [NeZero L] : 1 ≤ c1 d L := by
  unfold c1
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 3 * (2 * L - 1)))

/-- **(G1) for the cube system.** -/
theorem card_le_dExt (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (S : Finset 𝔅) :
    (S.card : ℝ) ≤ c1 d L * (1 + dExt S) := by
  classical
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  unfold dExt
  split_ifs with h
  · have hS : (S.card : ℝ) ≤ Fintype.card (CTorus d L N₁ m₁ K) := by
      have : S.card ≤ Fintype.card 𝔅 := Finset.card_le_univ S
      have h2 : Fintype.card 𝔅 ≤ Fintype.card (CTorus d L N₁ m₁ K) := Fintype.card_subtype_le _
      exact_mod_cast this.trans h2
    have hc1 := one_le_c1 d L
    have hM : (Fintype.card (CTorus d L N₁ m₁ K) : ℝ) ≤ Mbig d L N₁ m₁ K := by
      unfold Mbig
      have : (1 : ℝ) ≤ Fintype.card (CTorus d L N₁ m₁ K) := by
        exact_mod_cast Fintype.card_pos
      nlinarith
    nlinarith [Mbig_pos (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)]
  · obtain ⟨𝒦, W, E, hE, hcost⟩ := dOmega_exists_tuple (m₀ := m₀) (j := j) h
    have h1 := cellCount_le_of_admissible hN hj hE
    have hsub : cellCount (cellSide L m₀ m₁ j) (sitesOf S) ≤
        cellCount (cellSide L m₀ m₁ j) (Yhat Ω (sitesOf S) ∩ Ω) := by
      unfold cellCount
      refine Finset.card_le_card (fun t ht => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, fun y hy => ⟨subset_Yhat Ω _ (ht.2 hy), sitesOf_subset S (ht.2 hy)⟩⟩
    have hinj : S.card ≤ cellCount (cellSide L m₀ m₁ j) (sitesOf S) := by
      unfold cellCount
      refine Finset.card_le_card_of_injOn (fun b => b.1) (fun b hb => ?_) (fun a _ b _ h => Subtype.ext h)
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, b.2.1, fun y hy => mem_sitesOf.2 ⟨b, hb, hy⟩⟩
    rw [hcost] at h1
    calc (S.card : ℝ) ≤ (cellCount (cellSide L m₀ m₁ j) (sitesOf S) : ℝ) := by exact_mod_cast hinj
      _ ≤ (cellCount (cellSide L m₀ m₁ j) (Yhat Ω (sitesOf S) ∩ Ω) : ℝ) := by exact_mod_cast hsub
      _ ≤ _ := h1

theorem dExt_eq_Mbig {S : Finset 𝔅} (h : dOmega m₀ j Ω (sitesOf S) = ⊤) :
    dExt S = Mbig d L N₁ m₁ K := by
  unfold dExt; simp [h]

theorem dExt_eq_toReal {S : Finset 𝔅} (h : dOmega m₀ j Ω (sitesOf S) ≠ ⊤) :
    dExt S = (dOmega m₀ j Ω (sitesOf S)).toReal := by
  unfold dExt; simp [h]

/-- **(G3) for the cube system**, binary form. -/
theorem dExt_union_le (X Y : Finset 𝔅) (hXY : ¬ Disjoint X Y) :
    dExt (X ∪ Y) ≤ dExt X + dExt Y + cG d L := by
  classical
  have hg : 0 ≤ cG d L := by unfold cG; positivity
  by_cases hX : dOmega m₀ j Ω (sitesOf X) = ⊤
  · rw [dExt_eq_Mbig hX]
    linarith [dExt_le_Mbig (X ∪ Y), dExt_nonneg Y]
  by_cases hY : dOmega m₀ j Ω (sitesOf Y) = ⊤
  · rw [dExt_eq_Mbig hY]
    linarith [dExt_le_Mbig (X ∪ Y), dExt_nonneg X]
  obtain ⟨b, hbX, hbY⟩ := Finset.not_disjoint_iff.1 hXY
  have hne : (sitesOf X ∩ sitesOf Y).Nonempty := by
    have ha0 := cellSide_pos (L := L) m₀ m₁ j
    exact ⟨b.1, mem_sitesOf.2 ⟨b, hbX, mem_box_self _ ha0⟩, mem_sitesOf.2 ⟨b, hbY, mem_box_self _ ha0⟩⟩
  have h3 := G3_dOmega (m₀ := m₀) (j := j) (sitesOf_subset X) hne (S₂ := sitesOf Y)
  rw [← sitesOf_union] at h3
  have hfinR : dOmega m₀ j Ω (sitesOf X) + dOmega m₀ j Ω (sitesOf Y) + ENNReal.ofReal (cG d L) ≠ ⊤ := by
    simp [ENNReal.add_eq_top, hX, hY]
  have hfin : dOmega m₀ j Ω (sitesOf (X ∪ Y)) ≠ ⊤ := ne_top_of_le_ne_top hfinR h3
  rw [dExt_eq_toReal hfin, dExt_eq_toReal hX, dExt_eq_toReal hY]
  have := ENNReal.toReal_mono hfinR h3
  rwa [ENNReal.toReal_add (by simp [ENNReal.add_eq_top, hX, hY]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hX hY, ENNReal.toReal_ofReal hg] at this

/-- **(G3) for the cube system**, clusters with connected incompatibility graph (`hG3P`). -/
theorem dExt_union_cluster {n : ℕ} (X : Fin (n + 1) → NePoly 𝔅)
    (hc : (clusterGraph (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) X).Connected) :
    dExt (unionOf (Subtype.val : NePoly 𝔅 → Finset 𝔅) X) ≤
      ∑ i, dExt (X i).1 + cG d L * n := by
  classical
  have key := phi_union_le (dExt (m₀ := m₀) (j := j) (Ω := Ω)) (cG d L)
    (fun X Y _ _ h => dExt_union_le X Y h)
    (clusterGraph (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) X) (fun i => (X i).1)
    (fun i => (X i).2) (fun i j hij => by
      have := ((clusterGraph_adj _ X i j).1 hij).2
      exact (lnk_shareBlock _ _ _).1 this) n Finset.univ (by simp)
    (by
      rw [Finset.coe_univ]
      exact (SimpleGraph.induceUnivIso _).connected_iff.2 hc)
  convert key using 3
  ext x; simp [unionOf]

/-- **(G3) for the cube system**, connected families of terms (`hG3T`). -/
theorem dExt_unionCs_le (C : Finset (NePoly 𝔅))
    (hC : ConnSet (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) :
    dExt (unionCs (Subtype.val : NePoly 𝔅 → Finset 𝔅) C) ≤
      ∑ t ∈ C, dExt t.1 + cG d L * ((C.card : ℝ) - 1) := by
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
  have := phi_union_le (dExt (m₀ := m₀) (j := j) (Ω := Ω)) (cG d L)
    (fun X Y _ _ h => dExt_union_le X Y h) Gc (fun t => t.1) (fun t => t.2)
    (fun i j hij => by
      rw [SimpleGraph.fromRel_adj] at hij
      rcases hij.2 with h | h
      · exact h
      · exact fun hd => h hd.symm) (C.card - 1) C
    (Nat.sub_add_cancel (Finset.card_pos.2 hne)).symm hconn
  have hc : ((C.card - 1 : ℕ) : ℝ) = (C.card : ℝ) - 1 := by
    rw [Nat.cast_sub (Finset.card_pos.2 hne)]; simp
  rw [hc] at this
  convert this using 3
  ext x; simp [unionCs]

open Classical in
theorem sum_finite_part (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (b : 𝔅) {κ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ) :
    ∑ Y ∈ Finset.univ.filter (fun Y : NePoly 𝔅 =>
        dOmega m₀ j Ω (sitesOf Y.1) ≠ ⊤ ∧ b ∈ Y.1),
      Real.exp (-κ * (dOmega m₀ j Ω (sitesOf Y.1)).toReal) ≤ K0 d L κ := by
  set F := Finset.univ.filter (fun Y : NePoly 𝔅 => dOmega m₀ j Ω (sitesOf Y.1) ≠ ⊤ ∧ b ∈ Y.1)
    with hF
  have hinj : Set.InjOn (fun Y : NePoly 𝔅 => sitesOf Y.1) (F : Set (NePoly 𝔅)) :=
    fun Y _ Y' _ h => Subtype.ext (sitesOf_injective hN hj h)
  have himg := Finset.sum_image (f := fun S : Set (CTorus d L N₁ m₁ K) =>
    Real.exp (-κ * (dOmega m₀ j Ω S).toReal)) hinj
  rw [← himg]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Real.exp_nonneg _))
    (G2_S (Ω := Ω) hN hj b.2.1 hκ)
  intro S hS
  obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hS
  obtain ⟨hPY, hbY⟩ := (Finset.mem_filter.1 hY).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨isPiUnion_sitesOf Y.1, sitesOf_subset Y.1,
    fun y hy => mem_sitesOf.2 ⟨b, hbY, hy⟩, hPY⟩

open Classical in
/-- **(G2) for the cube system** (`hG2P`, and `hG2T` with `sup = val`): the entropy sum over all
nonempty sets of blocks through `b`, with the constant `K0 + 1`. -/
theorem sum_exp_dExt_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (b : 𝔅) {κ : ℝ}
    (hκ : aEnt d L + 1 ≤ κ) :
    ∑ Y : NePoly 𝔅, (if b ∈ Y.1 then Real.exp (-κ * dExt Y.1) else 0) ≤ K0 d L κ + 1 := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hκ1 : 1 ≤ κ := by linarith [aEnt_nonneg d L]
  set P : NePoly 𝔅 → Prop := fun Y => dOmega m₀ j Ω (sitesOf Y.1) ≠ ⊤ with hP
  have hA : ∀ Y : NePoly 𝔅, (if b ∈ Y.1 then Real.exp (-κ * dExt Y.1) else 0) ≤
      (if P Y ∧ b ∈ Y.1 then Real.exp (-κ * (dOmega m₀ j Ω (sitesOf Y.1)).toReal) else 0) +
      (if ¬ P Y then Real.exp (-κ * Mbig d L N₁ m₁ K) else 0) := by
    intro Y
    by_cases hY : dOmega m₀ j Ω (sitesOf Y.1) ≠ ⊤
    · have e := dExt_eq_toReal hY
      by_cases hb : b ∈ Y.1 <;> simp [hP, hY, hb, e]
    · have hY' : dOmega m₀ j Ω (sitesOf Y.1) = ⊤ := not_not.1 hY
      rw [dExt_eq_Mbig hY']
      by_cases hb : b ∈ Y.1 <;> simp [hP, hY', hb, Real.exp_nonneg]
  refine (Finset.sum_le_sum fun Y _ => hA Y).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ Y : NePoly 𝔅, (if P Y ∧ b ∈ Y.1 then
      Real.exp (-κ * (dOmega m₀ j Ω (sitesOf Y.1)).toReal) else 0) ≤ K0 d L κ := by
    rw [← Finset.sum_filter]
    exact sum_finite_part hN hj b hκ
  have h2 : ∑ Y : NePoly 𝔅, (if ¬ P Y then Real.exp (-κ * Mbig d L N₁ m₁ K) else 0) ≤ 1 := by
    calc _ ≤ ∑ _Y : NePoly 𝔅, Real.exp (-κ * Mbig d L N₁ m₁ K) :=
          Finset.sum_le_sum fun Y _ => by split_ifs <;> simp [Real.exp_nonneg]
      _ = (Fintype.card (NePoly 𝔅) : ℝ) * Real.exp (-κ * Mbig d L N₁ m₁ K) := by simp
      _ ≤ 1 := by
          set n := Fintype.card (CTorus d L N₁ m₁ K) with hn
          have hcard : Fintype.card (NePoly 𝔅) ≤ 2 ^ n := by
            have h1 : Fintype.card (NePoly 𝔅) ≤ Fintype.card (Finset 𝔅) := Fintype.card_subtype_le _
            rw [Fintype.card_finset] at h1
            exact h1.trans (Nat.pow_le_pow_right (by norm_num) (Fintype.card_subtype_le _))
          have hcardR : (Fintype.card (NePoly 𝔅) : ℝ) ≤ Real.exp n := by
            calc _ ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hcard
              _ = (2 : ℝ) ^ n := by push_cast; ring
              _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) (by
                  have := Real.add_one_le_exp (1 : ℝ); linarith) n
              _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
          calc _ ≤ Real.exp n * Real.exp (-κ * Mbig d L N₁ m₁ K) :=
                mul_le_mul_of_nonneg_right hcardR (Real.exp_nonneg _)
            _ = Real.exp (n + -κ * Mbig d L N₁ m₁ K) := (Real.exp_add _ _).symm
            _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by
                unfold Mbig
                nlinarith)
            _ = 1 := Real.exp_zero
  exact add_le_add h1 h2

end Balaban.Fluctuation
