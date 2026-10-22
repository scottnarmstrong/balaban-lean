/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.G0GasBasic
public import Balaban.LargeField.R.G0TorusGeom
public import Balaban.LargeField.R.GasIdentity

/-!
# G0: the geometry of the gas of a kept configuration

The geometric hypotheses of `decOp_pe_hole` for the gas of `G0Gas` (LFR Lemma III.10.5, the
geometric part of (H-op)), when the hole `S₀` lies in the kept region (`hS₀`):

* hole closures: `subset_holeCl`, `holeClosed_holeCl`, `isAnimal_holeCl`, `holeClosed_union`;
* `isAnimal_union_of_meet`: a union of animals meeting a common animal is an animal;
* removed clusters: `clCore_nonempty`, `clCore_subset_clSupp`, `disjoint_clCore_hole` (a removed
  component is at distance `≥ ω_k` from the kept members, `RemCluster.sepKept`), `isAnimal_clSupp`
  (the support `⋃ Z^{∼2ω_k}` of a cluster is connected: its members are linked and chained at
  distance `≤ 4ω_k`);
* the hypotheses `hz` (`decZs_nonempty`), `hnear` (`gasNear_contact`), `hSz`, `hSx`, `hclz`, `hclx`
  of the engine for this gas.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban Balaban.Polymer Balaban.LargeField.Def7

namespace Balaban.LargeField.G0

/-! ### Animals of a graph -/

section Animal

variable {B : Type*} {H : SimpleGraph B}

/-- **A union of animals that all meet a common animal is an animal.** -/
theorem isAnimal_union_of_meet {ι : Type*} {A : Finset B} (hA : IsAnimal H A) (T : Finset ι)
    (C : ι → Finset B) (hC : ∀ i ∈ T, IsAnimal H (C i)) (hmeet : ∀ i ∈ T, ¬ Disjoint A (C i)) :
    IsAnimal H (A ∪ T.biUnion C) := by
  set U := A ∪ T.biUnion C with hU
  set Rl : B → B → Prop := fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b with hRl
  have hAU : A ⊆ U := Finset.subset_union_left
  have hCU : ∀ i ∈ T, C i ⊆ U := fun i hi =>
    Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem C hi)
  have hmono : ∀ {X : Finset B}, X ⊆ U → ∀ {p q},
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ H.Adj a b) p q →
        Relation.ReflTransGen Rl p q := fun hX _ _ h =>
    Relation.ReflTransGen.mono (fun _ _ hab => ⟨hX hab.1, hX hab.2.1, hab.2.2⟩) _ _ h
  have hpA := ((isAnimal_iff H A).mp hA)
  rw [isAnimal_iff]
  obtain ⟨x₀, hx₀⟩ := hpA.1
  have hsymm : ∀ {a b}, Relation.ReflTransGen Rl a b → Relation.ReflTransGen Rl b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih
  have hbase : ∀ q ∈ U, Relation.ReflTransGen Rl x₀ q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqA | hqC
    · exact hmono hAU (hpA.2 x₀ hx₀ q hqA)
    · obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hqC
      obtain ⟨p, hpA', hpC⟩ := Finset.not_disjoint_iff.mp (hmeet i hi)
      exact (hmono hAU (hpA.2 x₀ hx₀ p hpA')).trans
        (hmono (hCU i hi) (((isAnimal_iff H _).mp (hC i hi)).2 p hpC q hqi))
  exact ⟨⟨x₀, hAU hx₀⟩, fun p hp q hq => (hsymm (hbase p hp)).trans (hbase q hq)⟩

/-- A union of sets closed under the hole is closed under the hole. -/
theorem holeClosed_union' {S₀ : Finset B} {ι : Type*} {A : Finset B} (hA : HoleClosed H S₀ A)
    (T : Finset ι) (C : ι → Finset B) (hC : ∀ i ∈ T, HoleClosed H S₀ (C i)) :
    HoleClosed H S₀ (A ∪ T.biUnion C) := by
  intro a b ha hb hab haU
  rcases Finset.mem_union.mp haU with haA | haC
  · exact Finset.mem_union_left _ (hA a b ha hb hab haA)
  · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haC
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hC i hi a b ha hb hab hai⟩)

/-- **A union of animals connected through overlaps is an animal.** -/
theorem isAnimal_biUnion_of_reach {ι : Type*} {D : Finset ι} (W : ι → Finset B)
    (hW : ∀ i ∈ D, IsAnimal H (W i)) {i₀ : ι} (hi₀ : i₀ ∈ D)
    (hconn : ∀ j ∈ D, Relation.ReflTransGen
      (fun a b => a ∈ D ∧ b ∈ D ∧ ¬ Disjoint (W a) (W b)) i₀ j) :
    IsAnimal H (D.biUnion W) := by
  set U := D.biUnion W with hU
  set Rl : B → B → Prop := fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b with hRl
  have hWU : ∀ i ∈ D, W i ⊆ U := fun i hi => Finset.subset_biUnion_of_mem W hi
  have hin : ∀ i ∈ D, ∀ p ∈ W i, ∀ q ∈ W i, Relation.ReflTransGen Rl p q := fun i hi p hp q hq =>
    Relation.ReflTransGen.mono (fun _ _ hab => ⟨hWU i hi hab.1, hWU i hi hab.2.1, hab.2.2⟩) _ _
      (((isAnimal_iff H _).mp (hW i hi)).2 p hp q hq)
  obtain ⟨x₀, hx₀⟩ := ((isAnimal_iff H _).mp (hW i₀ hi₀)).1
  have hreach : ∀ j ∈ D, ∀ q ∈ W j, Relation.ReflTransGen Rl x₀ q := by
    intro j hj
    induction hconn j hj with
    | refl => exact fun q hq => hin i₀ hi₀ x₀ hx₀ q hq
    | tail _ hab ih =>
      rename_i a b _
      intro q hq
      obtain ⟨p, hpa, hpb⟩ := Finset.not_disjoint_iff.mp hab.2.2
      exact (ih hab.1 p hpa).trans (hin b hab.2.1 p hpb q hq)
  have hsymm : ∀ {a b}, Relation.ReflTransGen Rl a b → Relation.ReflTransGen Rl b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih
  rw [isAnimal_iff]
  refine ⟨⟨x₀, hWU i₀ hi₀ hx₀⟩, fun p hp q hq => ?_⟩
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp hq
  exact (hsymm (hreach i hi p hpi)).trans (hreach j hj q hqj)

/-- **The Steiner size is subadditive over a family connected through contacts** (the hypothesis
`hG3` of the gas bounds, with `c = 0`), when every support lies in an animal. -/
theorem steiner_unionCs_le {E : Type*} (cs : E → Finset B) {C : Finset E}
    (hC : ConnSet cs C) (hY : ∀ t ∈ C, ∃ W : Finset B, IsAnimal H W ∧ cs t ⊆ W) :
    (steiner H (unionCs cs C) : ℝ) ≤ ∑ t ∈ C, (steiner H (cs t) : ℝ) := by
  set W : E → Finset B := fun t =>
    if h : t ∈ C then (steiner_spec (H := H) (hY t h)).choose else ∅ with hWdef
  have hWspec : ∀ t ∈ C, IsAnimal H (W t) ∧ cs t ⊆ W t ∧ (W t).card = steiner H (cs t) := by
    intro t ht
    simp only [hWdef, ht, ↓reduceDIte]
    exact (steiner_spec (H := H) (hY t ht)).choose_spec
  obtain ⟨t₀, ht₀⟩ := hC.1
  have hanim : IsAnimal H (C.biUnion W) := isAnimal_biUnion_of_reach W
    (fun t ht => (hWspec t ht).1) ht₀ (fun j hj => by
      have hr := hC.2 t₀ ht₀ j hj
      unfold Reach at hr
      exact Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, hab.2.1, fun hd => hab.2.2
        (Finset.disjoint_of_subset_left (hWspec a hab.1).2.1
          (Finset.disjoint_of_subset_right (hWspec b hab.2.1).2.1 hd))⟩) _ _ hr)
  have h1 : steiner H (unionCs cs C) ≤ (C.biUnion W).card :=
    steiner_le hanim (Finset.biUnion_mono fun t ht => (hWspec t ht).2.1)
  have h2 : (C.biUnion W).card ≤ ∑ t ∈ C, (W t).card := Finset.card_biUnion_le
  have h3 : ∑ t ∈ C, (W t).card = ∑ t ∈ C, steiner H (cs t) :=
    Finset.sum_congr rfl fun t ht => (hWspec t ht).2.2
  have := h1.trans (h2.trans h3.le)
  exact_mod_cast this

end Animal

/-! ### Hole closures on the cube graph -/

section HoleCl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k : ℕ}

theorem subset_holeCl (S₀ X : Finset (Torus S.d (n k))) : X ⊆ holeCl S₀ X :=
  Finset.subset_union_left

/-- **The hole closure is closed under the hole.** -/
theorem holeClosed_holeCl (S₀ X : Finset (Torus S.d (n k))) :
    HoleClosed (Localization.latGraph S.d (n k)) S₀ (holeCl S₀ X) := by
  intro a b ha hb hab haX
  have hnn : NNAdj a b := hab.2
  refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
  rcases Finset.mem_union.mp haX with haX' | haC
  · exact ⟨a, haX', ha, hb, Relation.ReflTransGen.single ⟨ha, hb, hnn⟩⟩
  · obtain ⟨a', ha'X, ha'S, haC'⟩ := (Finset.mem_filter.mp haC).2
    exact ⟨a', ha'X, ha'S, hb, haC'.2.tail ⟨ha, hb, hnn⟩⟩

/-- **The hole closure of an animal is an animal.** -/
theorem isAnimal_holeCl {S₀ X : Finset (Torus S.d (n k))}
    (hX : IsAnimal (Localization.latGraph S.d (n k)) X) :
    IsAnimal (Localization.latGraph S.d (n k)) (holeCl S₀ X) := by
  have hpX := (isAnimal_iff _ X).mp hX
  obtain ⟨x₀, hx₀⟩ := hpX.1
  have hsub := subset_holeCl S₀ X
  refine isAnimal_latGraph_of_base (hsub hx₀) fun q hq => ?_
  have hX' : ∀ p ∈ X, NNReach (holeCl S₀ X) x₀ p := fun p hp => by
    have := hpX.2 x₀ hx₀ p hp
    unfold NNReach
    exact Relation.ReflTransGen.mono (fun _ _ hab => ⟨hsub hab.1, hsub hab.2.1, hab.2.2.2⟩) _ _
      this
  rcases Finset.mem_union.mp hq with hqX | hqC
  · exact hX' q hqX
  · obtain ⟨a', ha'X, ha'S, hqS, hpath⟩ := (Finset.mem_filter.mp hqC).2
    refine (hX' a' ha'X).trans ?_
    unfold NNReach
    have hin : ∀ v, Relation.ReflTransGen
        (fun u w => u ∈ (S₀ : Set (Torus S.d (n k))) ∧ w ∈ (S₀ : Set (Torus S.d (n k))) ∧
          NNAdj u w) a' v → v ∈ (S₀ : Set (Torus S.d (n k))) → v ∈ holeCl S₀ X := by
      intro v hv hvS
      by_cases hv' : v = a'
      · rw [hv']; exact hsub ha'X
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a', ha'X, ha'S,
          hvS, hv⟩)
    have key : ∀ v, Relation.ReflTransGen
        (fun u w => u ∈ (S₀ : Set (Torus S.d (n k))) ∧ w ∈ (S₀ : Set (Torus S.d (n k))) ∧
          NNAdj u w) a' v →
        Relation.ReflTransGen (fun u w => u ∈ holeCl S₀ X ∧ w ∈ holeCl S₀ X ∧ NNAdj u w) a' v := by
      intro v hv
      induction hv with
      | refl => exact Relation.ReflTransGen.refl
      | tail hab hbc ih =>
        rename_i b c
        exact ih.tail ⟨hin b hab hbc.1, hin c (hab.tail hbc) hbc.2.1, hbc.2.2⟩
    exact key q hpath

end HoleCl

/-! ### Components are linked inside themselves -/

section Linked

variable {d n : ℕ} [NeZero n]

/-- Two points of a component are linked inside the component. -/
theorem linked_in_comp {ω : ℕ} {X Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) {x y : Torus d n}
    (hx : x ∈ Y) (hy : y ∈ Y) : Linked ω (Y : Set (Torus d n)) x y := by
  have h := ((mem_comp_iff hY hx).mp hy).2
  unfold Linked at h ⊢
  have key : ∀ v, Relation.ReflTransGen
      (fun a b => a ∈ (X : Set (Torus d n)) ∧ b ∈ (X : Set (Torus d n)) ∧ supDist a b < ω) x v →
      v ∈ Y ∧ Relation.ReflTransGen
        (fun a b => a ∈ (Y : Set (Torus d n)) ∧ b ∈ (Y : Set (Torus d n)) ∧ supDist a b < ω)
        x v := by
    intro v hv
    induction hv with
    | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
    | tail hab hbc ih =>
      rename_i b c
      have hcY : c ∈ Y := (mem_comp_iff hY hx).mpr ⟨hbc.2.1, hab.tail hbc⟩
      exact ⟨hcY, ih.2.tail ⟨Finset.mem_coe.mpr ih.1, Finset.mem_coe.mpr hcY, hbc.2.2⟩⟩
  exact (key y h).2

end Linked

/-! ### The removed clusters -/

section Cluster

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N k : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
  {rep : Rep S n R k0 K M N geo cs P k} {Kc : HistConfig S n R k0 K M k}

theorem mem_clCore {Cl : RemCl rep Kc} {b : Torus S.d (n k)} :
    b ∈ clCore Cl ↔ ∃ m ∈ memPairs Cl.1, b ∈ m.1 := by
  simp [clCore, clusterCore]

theorem mem_clSupp {Cl : RemCl rep Kc} {b : Torus S.d (n k)} :
    b ∈ clSupp Cl ↔ ∃ m ∈ memPairs Cl.1,
      b ∈ nbhd (2 * S.omega k) ((m.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) := by
  simp [clSupp, clusterSupp]

/-- The core of a removed cluster is nonempty. -/
theorem clCore_nonempty (Cl : RemCl rep Kc) : (clCore Cl).Nonempty := by
  obtain ⟨m, hm⟩ := Cl.2.nonempty
  obtain ⟨b, hb⟩ := pair_nonempty (Cl.2.mem_hist m hm)
  exact ⟨b, mem_clCore.mpr ⟨m, hm, hb⟩⟩

/-- The core of a removed cluster lies in its support. -/
theorem clCore_subset_clSupp (Cl : RemCl rep Kc) : clCore Cl ⊆ clSupp Cl := by
  intro b hb
  obtain ⟨m, hm, hbm⟩ := mem_clCore.mp hb
  exact mem_clSupp.mpr ⟨m, hm, mem_nbhd.mpr ⟨b, hbm, by rw [supDist_self]; exact Nat.zero_le _⟩⟩

/-- **The core of a removed cluster misses the kept region**, hence a hole inside it
(`RemCluster.sepKept`: removed components are at distance `≥ ω_k ≥ 11` from the kept members). -/
theorem disjoint_clCore_hole {S₀ : Finset (Torus S.d (n k))}
    (hS₀ : ∀ b ∈ S₀, ∃ m ∈ Kc.members, b ∈ m.1) (Cl : RemCl rep Kc) :
    Disjoint (clCore Cl) S₀ := by
  rw [Finset.disjoint_left]
  intro b hb hbS
  obtain ⟨m, hm, hbm⟩ := mem_clCore.mp hb
  obtain ⟨m', hm', hbm'⟩ := hS₀ b hbS
  have h1 := Cl.2.sepKept m hm m' hm' b hbm b hbm'
  rw [supDist_self] at h1
  have := omega_ge_eleven S k
  omega

omit [NeZero S.L] in
/-- The set of a member with a localized history in `𝔥_k(Z)` is linked inside itself. -/
theorem linked_of_mem_hist {m : ConfigPair S n M K k}
    (h : m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1) :
    ∀ x ∈ m.1, ∀ y ∈ m.1, Linked (S.omega k) ((m.1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k))) x y := by
  obtain ⟨H', -, c, hc, -⟩ := h
  rw [← hc]
  exact fun x hx y hy => linked_in_comp c.2 hx hy

/-- **The support of a removed cluster is connected**: the `2ω_k`-neighbourhoods of its members,
each linked at distance `< ω_k`, chained at distance `≤ 4ω_k` (`RemCluster.connected`). -/
theorem isAnimal_clSupp (Cl : RemCl rep Kc) :
    IsAnimal (Localization.latGraph S.d (n k)) (clSupp Cl) := by
  obtain ⟨m₀, hm₀⟩ := Cl.2.nonempty
  have h := isAnimal_biUnion_nbhd (C := memPairs Cl.1)
    (fun m : ConfigPair S n M K k => m.1) (ω := S.omega k) (r := 2 * S.omega k) (by omega) hm₀
    (fun m hm => pair_nonempty (Cl.2.mem_hist m hm))
    (fun m hm => linked_of_mem_hist (Cl.2.mem_hist m hm))
    (fun j hj => Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, hab.2.1, by
      obtain ⟨x, hx, y, hy, hxy⟩ := hab.2.2
      exact ⟨x, hx, y, hy, by omega⟩⟩) _ _ (Cl.2.connected m₀ hm₀ j hj))
  have e : clSupp Cl = Finset.univ.filter (· ∈ ⋃ i ∈ memPairs Cl.1,
      nbhd (2 * S.omega k) ((i.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))) := by
    ext b
    rw [mem_clSupp]
    simp
  rw [e]
  exact h

/-! ### The geometric hypotheses of the engine for the gas of a kept configuration -/

variable {S₀ : Finset (Torus S.d (n k))}

include rep in
/-- (`hz`) The charged support of a removed cluster is nonempty (it contains the core). -/
theorem gas_hz (hS₀ : ∀ b ∈ S₀, ∃ m ∈ Kc.members, b ∈ m.1) (Cl : RemCl rep Kc) :
    (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) Cl).Nonempty := by
  obtain ⟨b, hb⟩ := clCore_nonempty Cl
  refine ⟨b, ?_⟩
  simp only [decZs, Finset.mem_sdiff]
  exact ⟨subset_holeCl S₀ _ (clCore_subset_clSupp Cl hb),
    Finset.disjoint_left.mp (disjoint_clCore_hole hS₀ Cl) hb⟩

/-- (`hnear`) A domain meeting the core of a removed cluster is in charged contact with it. -/
theorem gas_hnear (hS₀ : ∀ b ∈ S₀, ∃ m ∈ Kc.members, b ∈ m.1) (X : LDom S n k)
    (Cl : RemCl rep Kc) (h : gasNear rep Kc X.1 Cl) :
    ¬ Disjoint (decZs S₀ (fun X' : LDom S n k => holeCl S₀ X'.1) X)
      (decZs S₀ (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl)) Cl) := by
  obtain ⟨b, hbx, hbc⟩ := Finset.not_disjoint_iff.mp h
  have hbS : b ∉ S₀ := Finset.disjoint_left.mp (disjoint_clCore_hole hS₀ Cl) hbc
  refine Finset.not_disjoint_iff.mpr ⟨b, ?_, ?_⟩
  · simp only [decZs, Finset.mem_sdiff]
    exact ⟨subset_holeCl S₀ _ hbx, hbS⟩
  · simp only [decZs, Finset.mem_sdiff]
    exact ⟨subset_holeCl S₀ _ (clCore_subset_clSupp Cl hbc), hbS⟩

/-- (`hSz`) The full support of a removed cluster is an animal. -/
theorem gas_hSz (Cl : RemCl rep Kc) :
    IsAnimal (Localization.latGraph S.d (n k)) (holeCl S₀ (clSupp Cl)) :=
  isAnimal_holeCl (isAnimal_clSupp Cl)

/-- (`hclz`) The full support of a removed cluster is closed under the hole. -/
theorem gas_hclz (Cl : RemCl rep Kc) :
    HoleClosed (Localization.latGraph S.d (n k)) S₀ (holeCl S₀ (clSupp Cl)) :=
  holeClosed_holeCl S₀ _

/-- (`hSx`) The full support of a decorated coupling is an animal: the hole closure of the
(connected) domain and those of the clusters it meets. -/
theorem gas_hSx
    (y : DecObj (fun (X' : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X'.1 Cl)) :
    IsAnimal (Localization.latGraph S.d (n k))
      (decCyF (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))
        (fun X' : LDom S n k => holeCl S₀ X'.1)
        (fun X' Cl => gasNear rep Kc X'.1 Cl) y) := by
  unfold decCyF
  refine isAnimal_union_of_meet (isAnimal_holeCl y.1.1.2) y.1.2 _ (fun Cl _ => gas_hSz Cl)
    (fun Cl hCl => ?_)
  obtain ⟨b, hbx, hbc⟩ := Finset.not_disjoint_iff.mp (y.2.2 Cl hCl)
  exact Finset.not_disjoint_iff.mpr ⟨b, subset_holeCl S₀ _ hbx,
    subset_holeCl S₀ _ (clCore_subset_clSupp Cl hbc)⟩

/-- (`hclx`) The full support of a decorated coupling is closed under the hole. -/
theorem gas_hclx
    (y : DecObj (fun (X' : LDom S n k) (Cl : RemCl rep Kc) => gasNear rep Kc X'.1 Cl)) :
    HoleClosed (Localization.latGraph S.d (n k)) S₀
      (decCyF (fun Cl : RemCl rep Kc => holeCl S₀ (clSupp Cl))
        (fun X' : LDom S n k => holeCl S₀ X'.1)
        (fun X' Cl => gasNear rep Kc X'.1 Cl) y) := by
  unfold decCyF
  exact holeClosed_union' (holeClosed_holeCl S₀ _) y.1.2 _ (fun Cl _ => gas_hclz Cl)

end Cluster

end Balaban.LargeField.G0
